from __future__ import annotations
from enum import IntEnum, Enum
from dataclasses import dataclass, field
from logging import INFO
import time
from typing import (
    Iterable,
    List,
    Set,
    Tuple,
    Any,
    Union,
    Dict,
    Callable,
    Optional,
    Sequence,
)

from amaya.automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from amaya import logger
from amaya.config import (
    BackendType,
    MinimizationAlgorithms,
    solver_config,
    SolutionDomain,
)
import amaya.presburger.constructions.naturals as relations_to_dfa
import amaya.presburger.constructions.integers as relations_to_nfa
from amaya import preprocessing
from amaya.preprocessing import (
    antiprenexing,
    eval as ast_eval_lib,
    prenexing,
)
from amaya.preprocessing.eval import VarInfo, divide_relation_by_gcd
import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.relations_structures import (
    AST_Atom,
    AST_Node_Names,
    AST_NaryNode,
    AST_Node,
    BoolLiteral,
    Congruence,
    FunctionSymbol,
    NodeEncounteredHandlerStatus,
    Relation,
    Var,
    VariableType,
    ast_get_node_type,
)
from amaya.tokenize import tokenize
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType,
)
from amaya import utils
from amaya.stats import (
    ParsingOperation,
    AutomatonInfo,
    OperationStartEntry,
    StatPoint,
    RunStats
)

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)


@dataclass
class IntrospectionData:
    automaton: NFA
    operation_id: int
    operation: ParsingOperation


IntrospectHandle = Callable[[IntrospectionData], None]


class EvaluationContext:
    def __init__(self,
                 emit_introspect: Optional[IntrospectHandle] = None,
                 alphabet: Optional[LSBF_Alphabet] = None,
                 var_table: Dict[Var, VarInfo] = {}):
        if emit_introspect:
            self.introspect_handle = emit_introspect
        else:
            self.introspect_handle = lambda info: None

        # Evaluation stats
        self.collect_stats = True
        self.stats = RunStats()
        self.pending_operations_stack: List[OperationStartEntry] = []
        self.operations_performed: int = 0

        self.var_table = var_table

        # Lazy load MTBDD automata module if needed
        self.automata_cls = NFA
        if solver_config.backend_type == BackendType.MTBDD:
            from amaya.mtbdd_automatons import MTBDD_NFA
            self.automata_cls = MTBDD_NFA

        self.alphabet = alphabet

    def get_alphabet(self) -> LSBF_Alphabet:
        if self.alphabet is None:
            raise ValueError('Requesting the overall alphabet from the evaluation context when None has been set.')
        return self.alphabet

    def stats_operation_starts(self, operation: ParsingOperation, input1: Optional[NFA], input2: Optional[NFA]):
        """Notify the context that an operation has started (statistics tracking)."""
        start = time.time_ns() if solver_config.track_operation_runtime else 0

        operand1_info = AutomatonInfo.from_automaton(input1)
        operand2_info = AutomatonInfo.from_automaton(input2)
        startpoint = OperationStartEntry(op_type=operation, operand1=operand1_info, operand2=operand2_info, start_ns=start)

        self.pending_operations_stack.append(startpoint)

    def stats_operation_ends(self, output: NFA) -> int:
        """
        Notify the context that an operation ended an a automaton has been produced.

        Returns:
            ID of the finished operation.
        """

        self.stats.max_automaton_size = max(self.stats.max_automaton_size, len(output.states))

        op_start = self.pending_operations_stack.pop(-1)  # Operation starting point

        operation_id = self.operations_performed
        output.operation_id = operation_id
        self.operations_performed += 1

        if self.introspect_handle:
            introspect_data = IntrospectionData(automaton=output, operation_id=operation_id, operation=op_start.op_type)
            self.introspect_handle(introspect_data)


        runtime = (time.time_ns() - op_start.start_ns) if solver_config.track_operation_runtime else 0
        output_info = AutomatonInfo.from_automaton(output)
        assert output_info
        stat = StatPoint(operation=op_start.op_type,
                         operand1=op_start.operand1,
                         operand2=op_start.operand2,
                         output=output_info,
                         operation_id=operation_id,
                         runtime_ns=runtime)

        logger.info(f"Operation finished: {stat}")
        self.stats.trace.append(stat)
        return operation_id

    def get_automaton_class_for_current_backend(self):
        return self.automata_cls


def emit_evaluation_progress_info(msg: str, depth: int):
    logger.info('  ' * depth + msg)


# @Cleanup: Remove this function or move it to the utils module
def pretty_print_smt_tree(tree, printer=None, depth=0):
    if printer is None:
        printer = print

    if tree is None:
        return

    node_name = tree[0]

    if node_name in ['exists', 'forall']:
        binders = tree[1]
        printer(PRETTY_PRINT_INDENT * depth + f'{node_name} (binding: {binders})')
        pretty_print_smt_tree(tree[2], printer=printer, depth=depth+1)
    # assert, not, and, or
    elif node_name in ['and', 'or']:
        printer(PRETTY_PRINT_INDENT * depth + f'{node_name}')
        pretty_print_smt_tree(tree[1], printer=printer, depth=depth+1)
        pretty_print_smt_tree(tree[2], printer=printer, depth=depth+1)
    elif node_name in ['assert', 'not']:
        printer(PRETTY_PRINT_INDENT * depth + f'{node_name}')
        pretty_print_smt_tree(tree[1], printer=printer, depth=depth+1)
    else:
        printer(PRETTY_PRINT_INDENT * depth + f'{tree}')


# @Cleanup: Rename this to something more readable, or do it in preprocessing
def parse_variable_bindings_list_to_internal_repr(bindings: List[Tuple[str, str]]) -> Dict[str, VariableType]:
    """Parse the given variable bindings."""
    var_info: Dict[str, VariableType] = {}
    for binding in bindings:
        var_name, var_type_smt_str = binding
        if var_type_smt_str == 'Int':
            var_type = VariableType.INT
        elif var_type_smt_str == 'Bool':
            var_type = VariableType.BOOL
        else:
            raise ValueError("Unknown datatype bound to a variable: {var_type_raw}")
        var_info[var_name] = var_type

    return var_info


def strip_comments(source: str) -> str:
    new_src = ''
    inside_comment = False
    for char in source:
        if char == ';':
            inside_comment = True
        elif char == '\n':
            inside_comment = False

        if not inside_comment:
            new_src += char
    return new_src


def build_syntax_tree(tokens: Iterable[str]):
    stack: List[Any] = []
    depth = -1
    for token in tokens:
        if token == '(':
            depth += 1
            stack.append([])
        elif token == ')':
            depth -= 1
            if depth >= 0:
                list_finished = stack.pop()
                stack[-1].append(list_finished)
        else:
            stack[-1].append(token)
    return stack


def optimize_formula_structure(formula_to_evaluate: AST_Node, var_table: Dict[Var, VarInfo]) -> AST_Node:
    if solver_config.optimizations.simplify_variable_bounds:
        logger.debug(f'Simplifying variable bounds of formula: %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.simplify_bounded_atoms(formula_to_evaluate)
        logger.debug(f'Simplified formula: %s', formula_to_evaluate)

    if solver_config.optimizations.rewrite_existential_equations_via_gcd:
        logger.debug(f'Rewriting: %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.simplify_unbounded_equations(formula_to_evaluate)
        logger.debug(f'Simplified formula: %s', formula_to_evaluate)

    if solver_config.optimizations.rewrite_congruences_with_unbound_terms:
        logger.debug(f'Rewriting congruence terms containing unbounded variables:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.simplify_congruences_on_unbounded_existential_vars(formula_to_evaluate, var_table)
        logger.debug(f'Congruences rewritten. Result:  %s', formula_to_evaluate)

    formula_to_evaluate = preprocessing.flatten_bool_nary_connectives(formula_to_evaluate)

    if solver_config.optimizations.push_negation_towards_atoms:
        logger.debug(f'Pushing negation towards atoms on:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.push_negations_towards_atoms(formula_to_evaluate)
        logger.debug(f'Negations pushed towards atoms. Result:  %s', formula_to_evaluate)

    if solver_config.optimizations.detect_isomorphic_conflicts:
        logger.debug(f'Detecting conflicts in conjuctive clauses using formula isomorphism:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.detect_conflics_on_isomorphic_fragments(formula_to_evaluate)
        logger.debug(f'Conflict detection done. Result:  %s', formula_to_evaluate)

    if solver_config.optimizations.do_light_sat_reasoning:
        formula_to_evaluate = var_bounds_lib.convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(formula_to_evaluate)

    return formula_to_evaluate



def parse_function_symbol_declaration(decl_ast: AST_NaryNode) -> FunctionSymbol:
    # Example: (declare-fun W_S1_V1 () Bool)
    if len(decl_ast) != 4:
        raise ValueError(f'Invalid syntax: declare-fun has invalid form: {decl_ast}')
    if not isinstance(decl_ast[1], str):
        raise ValueError(f'Invalid syntax: declare-fun expects a string literal on 1st place: {decl_ast}')
    if not isinstance(decl_ast[2], list) or not all(isinstance(fun_sort, str) for fun_sort in decl_ast[2]):
        raise ValueError(f'Invalid syntax: declare-fun expects a list of function '
                         f'sorts on 2nd place: {decl_ast}')
    if not isinstance(decl_ast[3], str):
        raise ValueError(f'Invalid syntax: declare-fun expects function\'s return sort'
                         f'on 3nd place: {decl_ast}')

    assert isinstance(decl_ast[1], str)
    assert isinstance(decl_ast[2], list)
    assert isinstance(decl_ast[3], str)
    input_sorts: List[str] = decl_ast[2]  # type: ignore

    sym_name: str = decl_ast[1]
    sym_args = [
        (arg_name, VariableType.from_smt_type_string(arg_type_raw)) for arg_name, arg_type_raw in input_sorts
    ]
    sym_ret_type = VariableType.from_smt_type_string(decl_ast[3])

    function_symbol = FunctionSymbol(name=sym_name, arity=len(sym_args), args=sym_args,
                                     return_type=sym_ret_type)
    return function_symbol


# @Cleanup: This should be renamed to something like evaluate_smt2
def perform_whole_evaluation_on_source_text(source_text: str,
                                            emit_introspect: Optional[IntrospectHandle] = None
                                            ) -> Tuple[NFA, Dict[str, str], RunStats]:
    """
    Parses the given SMT2 source code and runs the evaluation procedure.

    If multiple `assert` statements are found in the AST then the AST is modified
    so it contains only one `assert` that is a logical conjunction of all other
    formulas in the other assert trees.

    :param source_text: The SMT2 source text encoding the problem.
    :param emit_introspect: Introspection handle. If given it will be called with every automaton
                            produced during the evaluation procedure (in the order they are created).
    :returns: A tuple of the form (NFA, Dict) where NFA is the result of the evaluation
              of assert tree, and Dict is the smt-info collected when parsing.
    """

    tokens = tokenize(source_text)
    ast = build_syntax_tree(tokens)

    eval_result: Optional[NFA] = None
    smt_info: Dict[str, Any] = {}
    function_symbol_to_info_map: Dict[str, FunctionSymbol] = {}
    formulae_to_assert: List[AST_Node] = []

    for top_level_statement in ast:
        if not isinstance(top_level_statement, list):
            raise ValueError(f'Unknown top-level statement in given input file. Statement: {top_level_statement}')
        if len(top_level_statement) == 0:
            logger.warning(f'Unknown top-level S-Expression found in given input file - is the file malformed?')
            continue

        statement_root = top_level_statement[0]
        if statement_root == 'set-info':
            if not len(top_level_statement) == 3:
                raise ValueError(f'Invalid syntax for the smt-info S-expression. Expresssion: {top_level_statement}')
            smt_info[top_level_statement[1]] = top_level_statement[2]

        elif statement_root == 'assert':
            if not len(top_level_statement) == 2:
                raise ValueError(f'Invalid syntax for the assert S-expression. Expresssion: {top_level_statement}')
            formulae_to_assert.append(top_level_statement[1])

        elif statement_root == AST_Node_Names.DECLARE_FUN.value:
            function_symbol = parse_function_symbol_declaration(top_level_statement)
            function_symbol_to_info_map[function_symbol.name] = function_symbol
        elif statement_root == AST_Node_Names.CHECK_SAT.value:
            if eval_result:
                raise ValueError('Multiple check-sat commands are not supported!')

            logger.debug('Executing amaya (%d asserts collected) with smt-info: %s', len(formulae_to_assert), smt_info)
            if not formulae_to_assert:
                raise ValueError('Cannot check-sat without any asserts.')

            ctx = EvaluationContext()

            # If there are multiple assert statements, evaluate their conjunction
            formula_to_evaluate = formulae_to_assert[0] if len(formulae_to_assert) == 1 else ['and'] + formulae_to_assert

            const_fn_symbols = [fn_symbol for fn_symbol in function_symbol_to_info_map.values() if fn_symbol.arity == 0]
            formula_to_evaluate, var_table  = preprocessing.preprocess_ast(formula_to_evaluate,  # type: ignore
                                                                           global_fn_symbols=const_fn_symbols)

            logger.info('Preprocessing resulted in the following AST: %s', formula_to_evaluate)

            assert formula_to_evaluate
            formula_to_evaluate = optimize_formula_structure(formula_to_evaluate, var_table)

            if solver_config.preprocessing.show_preprocessed_formula:
                import pprint, sys
                pprint.pprint(formula_to_evaluate, stream=sys.stdout)
                sys.exit(0)

            alphabet = LSBF_Alphabet.from_vars(var_table.keys())

            eval_ctx = EvaluationContext(emit_introspect=emit_introspect, alphabet=alphabet, var_table=var_table)

            logger.info('Setup done. Proceeding to AST evaluation (backend: %s).', solver_config.backend_type.name)
            nfa = run_evaluation_procedure(formula_to_evaluate, eval_ctx)
            eval_result = nfa
        elif statement_root == 'exit':
            return (nfa, smt_info, eval_ctx.stats)
    return (nfa, smt_info, eval_ctx.stats)


def make_nfa_for_congruence(congruence: Congruence, ctx: EvaluationContext) -> NFA:
    """ Construct an automaton accepting the solutions of the given congruence """
    vars: List[Var] = []
    coefs: List[int] = []

    vars, coefs = zip(*sorted(zip(congruence.vars, congruence.coefs), key = lambda pair: pair[0]))

    ordered_congruence = Congruence(vars=vars, coefs=coefs, rhs=congruence.rhs, modulus=congruence.modulus)

    logger.debug(f'Reordered congruence from: %s to %s', congruence, ordered_congruence)

    # The alphabet might have only variable IDs but no names assigned to them yet, bind the variable names to IDs
    # so that we can do vizualization properly
    assert ctx.alphabet

    constr = ctx.get_automaton_class_for_current_backend()
    ctx.stats_operation_starts(ParsingOperation.BUILD_NFA_FROM_CONGRUENCE, None, None)
    nfa = relations_to_nfa.build_presburger_congruence_nfa(constr, ctx.alphabet, congruence)
    ctx.stats_operation_ends(nfa)

    return nfa


def build_automaton_from_presburger_relation_ast(relation: Relation, ctx: EvaluationContext, depth: int) -> NFA:
    """
    Construct an automaton corresponding to the given relation.

    The provided evalaution context `ctx` should have already an overall alphabet attached to it.

    Note: The automaton for sharp inequation (<) is not being directly built. Instead is is build as
    an an intersection of a complement of an automaton for the same relation but equation and non-sharp
    inequality -> (and (not <REL>[< -> =]) <REL>[< -> <=]).
    """
    building_handlers: Dict[SolutionDomain, Dict[str, Tuple[ParsingOperation, Callable]]] = {
        SolutionDomain.INTEGERS: {
            '<=': (ParsingOperation.BUILD_NFA_FROM_INEQ, relations_to_nfa.build_nfa_from_linear_inequality),
            '=':  (ParsingOperation.BUILD_NFA_FROM_EQ, relations_to_nfa.build_nfa_from_linear_equality)
        },
        SolutionDomain.NATURALS: {
            '<=': (ParsingOperation.BUILD_DFA_FROM_INEQ, relations_to_dfa.build_dfa_from_linear_inequality),
            '=':  (ParsingOperation.BUILD_DFA_FROM_EQ, relations_to_dfa.build_dfa_from_linear_equality)
        }
    }

    automaton_constr = ctx.get_automaton_class_for_current_backend()

    logger.debug('Building an automaton for: %s', relation)
    if relation.is_always_satisfied():
        raise ValueError(f'Found {relation} that is trivially always SAT, but preprocessing did not produce BoolLiteral.')

    # We should never encounter the '<' inequality as we are always converting it to the <=
    assert relation.predicate_symbol in ('<=', '=')
    operation, automaton_building_function = building_handlers[solver_config.solution_domain][relation.predicate_symbol]

    assert relation.vars == sorted(relation.vars)
    assert automaton_building_function

    ctx.stats_operation_starts(operation, None, None)
    nfa = automaton_building_function(automaton_constr, ctx.alphabet, relation)
    ctx.stats_operation_ends(nfa)

    emit_evaluation_progress_info(
        f' >> {operation.value}({relation}) (result size: {len(nfa.states)}, automaton_type={nfa.automaton_type})',
        depth
    )

    return nfa


# @Cleanup: Fold this function in if it is even used
def build_automaton_for_boolean_variable(var: Var, var_value: bool, ctx: EvaluationContext) -> NFA:
    """Construct an automaton corresponding the given boolean variable."""
    logger.debug(f'Building an equivalent automaton for the bool variable {var}, with value {var_value}.')
    return ctx.get_automaton_class_for_current_backend().for_bool_variable(ctx.get_alphabet(), var, var_value)


# @Cleanup: How is this function even used? We now have Relations in the AST, so we typically take the else branch.
def get_automaton_for_operand(operand_ast: AST_Node, ctx: EvaluationContext, _depth: int) -> NFA:
    """
    Construct automaton accepting solutions of the formula given by its AST.

    If the given ast is not a leaf, the evaluation procedure is ran to build the NFA encoding the AST.
    """
    if isinstance(operand_ast, str):
        logger.debug('Requested the automaton for an operand that is an AST Leaf (str).'
                     'Searching variable scopes for its definition.')
        print(operand_ast)
        variable_info = ctx.lookup_variable(operand_ast)
        if (variable_info and variable_info.type == VariableType.BOOL):
            logger.debug(f'Found definition for %s - symbol defined as a boolean variable.', operand_ast)
            variable_info.usage_count += 1
            return build_automaton_for_boolean_variable(operand_ast, True, ctx)

        raise ValueError(f'Found an AST Leaf that cannot be evaluated: {operand_ast}')

    else:
        # The operand in not an AST Leaf - evaluate it first
        return run_evaluation_procedure(operand_ast, ctx, _debug_recursion_depth=_depth+1)


def minimize_automaton_if_configured(nfa: NFA, ctx: EvaluationContext) -> NFA:
    """
    Perform the configured minimization on given NFA.

    Minimization result is monitored for runtime, and its results are emitted to context's introspection handle
    for visualization.

    :param nfa: Automaton to minimize.
    :param ctx: Evaluation context that will store information about measured timings.
    :returns: Minimized DFA equivalent to the given NFA.
    """
    if solver_config.minimization_method == MinimizationAlgorithms.NONE:
        return nfa

    ctx.stats_operation_starts(ParsingOperation.MINIMIZE, nfa, None)
    if solver_config.minimization_method == MinimizationAlgorithms.BRZOZOWSKI:
        minimized_dfa = nfa.minimize_brzozowski()
    else:
        if nfa.automaton_type != AutomatonType.DFA:
            ctx.stats_operation_starts(ParsingOperation.NFA_DETERMINIZE, nfa, None)
            nfa = nfa.determinize()
            ctx.stats_operation_ends(nfa)
        minimized_dfa = nfa.minimize_hopcroft()

    logger.info('Minimization applied - inputs has %d states, result %d.', len(nfa.states), len(minimized_dfa.states))
    ctx.stats_operation_ends(minimized_dfa)
    return minimized_dfa


def evaluate_binary_conjunction_expr(expr: AST_NaryNode,
                                     ctx: EvaluationContext,
                                     reduction_fn: Callable[[NFA, NFA], NFA],
                                     reduction_operation: ParsingOperation,
                                     _depth: int) -> NFA:
    """
    Abstract binary conjunction evaluation algorithm.

    Perform the evaluation of AND and OR expressions in an abstract fashion using the provided
    reduction function (used to compose the individual operands into a result).
    """
    assert type(expr) == list

    if len(expr) == 2:
        # There might be situation when we simplify variable bounds that we lift some atoms all the way to the root of the formula
        # while keeping their connectives intact - for example, a [and, <atom>] might come to exist in the formula
        return get_automaton_for_operand(expr[1], ctx, _depth)


    first_operand = expr[1]

    reduction_result = get_automaton_for_operand(first_operand, ctx, _depth)

    for next_operand in expr[2:]:
        if reduction_operation == ParsingOperation.NFA_INTERSECT and not reduction_result.final_states:
            return reduction_result

        next_operand_automaton = get_automaton_for_operand(next_operand, ctx, _depth)

        # Apply the provided reduction function.
        ctx.stats_operation_starts(reduction_operation, reduction_result, next_operand_automaton)
        reduction_result = reduction_fn(reduction_result, next_operand_automaton)

        # reduction_result = reduction_result.determinize()
        ctx.stats_operation_ends(reduction_result)

        reduction_result = minimize_automaton_if_configured(reduction_result, ctx)

        emit_evaluation_progress_info((f' >> {reduction_operation}(lhs, rhs) '
                                       f'(result size: {len(reduction_result.states)}, '
                                       f'automaton_type={reduction_result.automaton_type})'), _depth)

    return reduction_result


def evaluate_and_expr(and_expr: AST_NaryNode, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an automaton corresponding to the given conjuction."""

    result = evaluate_binary_conjunction_expr(
        and_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.intersection(nfa2),
        ParsingOperation.NFA_INTERSECT,
        _depth
    )

    return result


def evaluate_or_expr(or_expr: AST_NaryNode, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an automaton corresponding to the given disjunction."""

    return evaluate_binary_conjunction_expr(
        or_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.union(nfa2),
        ParsingOperation.NFA_UNION,
        _depth
    )


def evaluate_not_expr(not_expr: AST_NaryNode, ctx: EvaluationContext, _depth: int) -> NFA:
    """Return the automaton corresponding to the given SMT expression containing a negated formula."""

    assert len(not_expr) == 2
    operand = get_automaton_for_operand(not_expr[1], ctx, _depth)

    # @Cleanup: I think we don't have to handle Bool automatons in an explicit manner - check whether we need this code.
    if (operand.automaton_type & AutomatonType.BOOL):
        assert len(operand.used_variables) == 1

        variable_id: int = operand.used_variables[0]
        variable_value: bool = operand.extra_info['bool_var_value']
        logger.debug('Complementing an automaton for a bool variable {variable_id}, returninig direct complement.')
        ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
        result = ctx.get_automaton_class_for_current_backend().for_bool_variable(ctx.get_alphabet(), variable_id, not variable_value)
        ctx.stats_operation_ends(result)
        return result

    if (operand.automaton_type & AutomatonType.NFA):
        if False:
            import os
            output_folder = '/tmp/ondra-nfas-mata/UltimateAutomizer'
            if not os.path.exists(output_folder):
                os.makedirs(output_folder)
            if operand.check_nondeterminism():
                assert solver_config.current_formula_path
                formula_basename = os.path.basename(solver_config.current_formula_path)
                formula_basename = formula_basename.rsplit('.', 1)[0]
                formula_basename = f'{formula_basename}.{solver_config.export_counter}.mata'
                output_filepath = os.path.join(output_folder, formula_basename)
                solver_config.export_counter += 1
                with open(output_filepath, 'w') as output_file:
                    mata_text = operand.get_visualization_representation().into_mata()
                    output_file.write(mata_text)

        ctx.stats_operation_starts(ParsingOperation.NFA_DETERMINIZE, operand, None)
        operand = operand.determinize()
        ctx.stats_operation_ends(operand)
        emit_evaluation_progress_info(f' >> determinize into DFA (result size: {len(operand.states)})', _depth)

    ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
    assert operand.automaton_type & AutomatonType.DFA, f'{operand.automaton_type} {not_expr}'
    operand = operand.complement()
    ctx.stats_operation_ends(operand)

    operand = minimize_automaton_if_configured(operand, ctx)

    emit_evaluation_progress_info(f' >> complement(operand) - (result size: {len(operand.states)})', _depth)
    return operand


def try_lazy_construct_conjunction(exists_node: AST_NaryNode, ctx: EvaluationContext) -> Optional[NFA]:
    bound_vars: List[Var] = exists_node[1]  # type: ignore
    if not isinstance(exists_node[2], list):
        return

    and_node: AST_NaryNode = exists_node[2]
    if ast_get_node_type(and_node) != AST_Node_Names.AND.value:
        return

    if not all(isinstance(child, (Relation, Congruence)) for child in and_node[1:]):
        return

    logger.info('Lazy constructing %s', and_node)
    atoms: List[AST_Atom] = and_node[1:]  # type: ignore
    from amaya.mtbdd_transitions import MTBDDTransitionFn

    new_atoms = []
    for atom in atoms:
        if isinstance(atom, Relation):
            new_atom = divide_relation_by_gcd(atom)
            if isinstance(new_atom, BoolLiteral) and new_atom.value == False:
                assert ctx.alphabet
                return NFA.trivial_nonaccepting(ctx.alphabet)
        else:
            new_atom = atom
        new_atoms.append(new_atom)

    ctx.stats_operation_starts(ParsingOperation.LAZY_CONSTRUCT, None, None)
    nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(new_atoms, bound_vars, ctx.get_alphabet())
    ctx.stats_operation_ends(nfa)

    logger.info("Lazy construnction done, result has %d states", len(nfa.states))
    nfa = minimize_automaton_if_configured(nfa, ctx)
    return nfa


def evaluate_exists_expr(exists_expr: AST_NaryNode, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an NFA corresponding to the given formula of the form (exists (vars) (phi))."""
    assert len(exists_expr) == 3

    bound_vars: List[Var] = exists_expr[1]  # type: ignore

    # Perform a look-ahead to see whether we can construct the NFA for the entire conjunction using a lazy approach
    if solver_config.backend_type == BackendType.MTBDD and solver_config.optimizations.do_lazy_evaluation:
        nfa = try_lazy_construct_conjunction(exists_expr, ctx)
        if nfa:
            return nfa

    nfa = get_automaton_for_operand(exists_expr[2], ctx, _depth)

    # We need to establish an order of individual projections applied, so that we can tell when we are projecting away
    # the last variable in this quantifier, because we don't need to do padding closure after every single variable
    # projection - we have to do it only after the variable has been projected away.

    logger.debug(f'Established projection order: {bound_vars}')

    last_var_to_project = bound_vars[-1]
    for var in bound_vars:
        logger.debug(f'Projecting away variable {var}')
        ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)

        # It is sufficient to do the padding closure only after the last variable is projected away
        skip_pad_closure = False if var == last_var_to_project else True

        projection_result = nfa.do_projection(var, skip_pad_closure=skip_pad_closure)
        assert projection_result
        nfa = projection_result
        ctx.stats_operation_ends(nfa)
        logger.debug(f'Variable {var} projected away.')

    nfa = minimize_automaton_if_configured(nfa, ctx)

    emit_evaluation_progress_info(f' >> projection({bound_vars}) (result_size: {len(nfa.states)})', _depth)
    return nfa


def evaluate_bool_equivalence_expr(ast: AST_NaryNode, ctx: EvaluationContext, _depth: int = 0) -> NFA:
    """
    Constructs an automaton for the given equivalence of two Booleans.
    """
    left_nfa = get_automaton_for_operand(ast[1], ctx, _depth)
    right_nfa = get_automaton_for_operand(ast[2], ctx, _depth)
    positive_branch = left_nfa.intersection(right_nfa)

    if left_nfa.automaton_type & AutomatonType.NFA:
        left_nfa = left_nfa.determinize()
    if right_nfa.automaton_type & AutomatonType.NFA:
        right_nfa = right_nfa.determinize()

    not_left = left_nfa.complement()
    not_right = right_nfa.complement()
    negative_branch = not_left.intersection(not_right)
    return positive_branch.union(negative_branch)


def run_evaluation_procedure(ast: AST_Node,
                             ctx: EvaluationContext,
                             _debug_recursion_depth: int = 0) -> NFA:
    """
    Evaluates the entire SMT given SMT tree and returns the NFA accepting the solutions of the given formula.

    :param ast: The formula to evaluate into an automaton.
    :param ctx: The context of the performed evaluation.
    :param _debug_recursion_depth: Used to pretty print debugging information about the progress of evaluation.
    :returns: The NFA corresponding to the given formula.
    """

    if not isinstance(ast, list):
        if isinstance(ast, BoolLiteral):
            automaton_cls = ctx.get_automaton_class_for_current_backend()
            return automaton_cls.trivial_accepting(ctx.get_alphabet()) if ast.value else automaton_cls.trivial_nonaccepting(ctx.get_alphabet())

        if isinstance(ast, Congruence):
            return make_nfa_for_congruence(ast, ctx)

        if isinstance(ast, Relation):
            return build_automaton_from_presburger_relation_ast(ast, ctx, _debug_recursion_depth)

        if isinstance(ast, Var):
            if ctx.var_table[ast].type != VariableType.BOOL:
                raise ValueError(f'AST contains a freestanding non-boolean variable, don\'t know how to evaluate that. {ast}')
            return build_automaton_for_boolean_variable(var=ast, var_value=True, ctx=ctx)

        raise ValueError('Cannot evaluate atom: %s.', ast)

    node_name = ast[0]
    emit_evaluation_progress_info(f'eval_smt_tree({ast}), node_name={node_name}', _debug_recursion_depth)
    # Current node is a NFA operation
    evaluation_functions = {
        'and': evaluate_and_expr,
        'or': evaluate_or_expr,
        'not': evaluate_not_expr,
        'exists': evaluate_exists_expr,
        '=': evaluate_bool_equivalence_expr,
    }

    if node_name not in evaluation_functions:
        raise NotImplementedError(f'Don\'t know how to evaluate {node_name} when evaluating the formula: {ast}')

    evaluation_function = evaluation_functions[node_name]

    result = evaluation_function(ast, ctx, _debug_recursion_depth)
    return result
