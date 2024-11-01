from __future__ import annotations
from enum import IntEnum, Enum
from dataclasses import dataclass, field
from logging import INFO
import pprint
import time
from typing import (
    Iterable,
    List,
    Set,
    Tuple,
    Any,
    Type,
    Union,
    Dict,
    Callable,
    Optional,
    Sequence,
    cast,
)
import sys
from amaya.alphabet import LSBF_AlphabetSymbol

from amaya.automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from amaya import logger, shard_logger
from amaya.config import (
    BackendType,
    MinimizationAlgorithms,
    solver_config,
    SolutionDomain,
)
from amaya.mtbdd_automatons import MTBDD_NFA
import amaya.presburger.constructions.naturals as relations_to_dfa
import amaya.presburger.constructions.integers as relations_to_nfa
from amaya import preprocessing
from amaya.preprocessing import (
    antiprenexing,
    eval as ast_eval_lib,
    prenexing,
)
from amaya.preprocessing.eval import VarInfo, divide_relation_by_gcd, split_lin_terms_into_vars_and_coefs
import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.relations_structures import (
    AST_Atom,
    AST_Connective,
    AST_Negation,
    AST_Node_Names,
    AST_NaryNode,
    AST_Node,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    FunctionSymbol,
    NodeEncounteredHandlerStatus,
    Relation,
    Var,
    VariableType,
    ast_get_node_type,
    convert_ast_into_astp,
    pprint_formula,
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
UNKNOWN_AUTOMATON_SIZE = 10_000_000

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

        if solver_config.max_allowed_states is not None:
            if len(output.states) > solver_config.max_allowed_states:
                info = 'Manipulated automaton is larger then the configured hard limit: %d > %d'
                logger.critical(info, len(output.states), solver_config.max_allowed_states)
                sys.exit(f'Automaton size limit exceeded: {len(output.states)}/{solver_config.max_allowed_states}')

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


def optimize_formula_structure(formula_to_evaluate: AST_Node, var_table: Dict[Var, VarInfo]) -> ASTp_Node:
    if solver_config.optimizations.simplify_variable_bounds:
        logger.debug('Simplifying variable bounds of formula: %s', formula_to_evaluate)
        formula_to_evaluate = cast(AST_Node, var_bounds_lib.simplify_bounded_atoms(formula_to_evaluate))
        logger.debug('Simplified formula: %s', formula_to_evaluate)

    if solver_config.optimizations.rewrite_existential_equations_via_gcd:
        logger.debug('Rewriting: %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.simplify_unbounded_equations(formula_to_evaluate)
        logger.debug('Simplified formula: %s', formula_to_evaluate)

    if solver_config.optimizations.rewrite_congruences_with_unbound_terms:
        logger.debug('Rewriting congruence terms containing unbounded variables:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.simplify_congruences_on_unbounded_existential_vars(formula_to_evaluate, var_table)
        logger.debug('Congruences rewritten. Result:  %s', formula_to_evaluate)

    if solver_config.optimizations.push_negation_towards_atoms:
        logger.debug('Pushing negation towards atoms on:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.push_negations_towards_atoms(formula_to_evaluate)
        logger.debug('Negations pushed towards atoms. Result:  %s', formula_to_evaluate)

    if solver_config.optimizations.flatten_connectives:
        logger.debug('Flattening bool connectives into N-ary nodes.')
        formula_to_evaluate = preprocessing.flatten_bool_nary_connectives(formula_to_evaluate)

    if solver_config.optimizations.detect_isomorphic_conflicts:
        logger.debug('Detecting conflicts in conjuctive clauses using formula isomorphism:  %s', formula_to_evaluate)
        formula_to_evaluate = var_bounds_lib.detect_conflics_on_isomorphic_fragments(formula_to_evaluate)
        logger.debug('Conflict detection done. Result:  %s', formula_to_evaluate)

    if solver_config.optimizations.do_light_sat_reasoning:
        formula_to_evaluate = var_bounds_lib.convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(formula_to_evaluate)

    astp = convert_ast_into_astp(formula_to_evaluate)

    if solver_config.optimizations.do_interval_analysis:
        logger.debug('Detecting conflicts in formula using interval analysis:  %s', astp)
        astp = var_bounds_lib.prune_conjunctions_false_due_to_parent_context(astp)
        logger.debug('Interval analysis done. Result:  %s', astp)

    if solver_config.optimizations.do_miniscoping:
        astp = antiprenexing.miniscope_quantifiers(astp)

    if solver_config.optimizations.optimize_bottom_quantifiers:
        logger.debug('Optimizing bottom quantifier:  %s', astp)
        astp = var_bounds_lib.optimize_bottom_quantifiers(astp)
        logger.debug('Bottom quantifiers optimized. Result:  %s', astp)

    if solver_config.optimizations.linearize_congruences:
        astp = var_bounds_lib.linearize_congruences(astp)

    # Do an extra pass as quantifier elimination might have introduced new constraints to prune the tree with
    if solver_config.optimizations.do_interval_analysis and solver_config.optimizations.do_interval_reasonining_twice:
        astp = var_bounds_lib.prune_conjunctions_false_due_to_parent_context(astp)

    return astp


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


@dataclass
class Evaluation_Result:
    run_stats: RunStats
    model: Optional[Dict[Var, int]] = None
    shards: List[NFA] = field(default_factory=list)
    solutions_nfa: Optional[NFA] = None
    smt_info: Dict[str, str] = field(default_factory=dict)
    var_table: Dict[Var, VarInfo] = field(default_factory=dict)


# @Cleanup: This should be renamed to something like evaluate_smt2
def perform_whole_evaluation_on_source_text(source_text: str, emit_introspect: Optional[IntrospectHandle] = None) -> Evaluation_Result | None:
    """
    Parses the given SMT2 source code and runs the evaluation procedure.

    If multiple `assert` statements are found in the AST then the AST is modified
    so it contains only one `assert` that is a logical conjunction of all other
    formulas in the other assert trees.

    Parameters:
        source_text: The SMT2 source text encoding the problem.
        emit_introspect: Introspection handle. If given it will be called with every automaton
                         produced during the evaluation procedure (in the order they are created).
    Returns:
        Evaluation result (model + additional information), or
        None if there was no 'check-sat' directive in the source_text
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
            if not formulae_to_assert: # Empty formula
                alphabet = LSBF_Alphabet.from_vars([])
                return Evaluation_Result(run_stats=RunStats(), model={}, shards=[],
                                         solutions_nfa=NFA.trivial_accepting(alphabet))

            ctx = EvaluationContext()

            # If there are multiple assert statements, evaluate their conjunction
            ast_to_evaluate = formulae_to_assert[0] if len(formulae_to_assert) == 1 else ['and'] + formulae_to_assert

            const_fn_symbols = [fn_symbol for fn_symbol in function_symbol_to_info_map.values() if fn_symbol.arity == 0]
            ast_to_evaluate, var_table  = preprocessing.preprocess_ast(ast_to_evaluate,  # type: ignore
                                                                       global_fn_symbols=const_fn_symbols)

            logger.info('Preprocessing resulted in the following AST: %s', ast_to_evaluate)

            assert ast_to_evaluate
            astp = optimize_formula_structure(ast_to_evaluate, var_table)

            should_exit_without_evaluation = False
            if solver_config.preprocessing.show_preprocessed_formula:
                print(f'----- AST -----')
                pprint_formula(astp)
                should_exit_without_evaluation = True
            if solver_config.preprocessing.display_var_table:
                print(f'----- Var table -----')
                pprint.pprint(var_table)
                should_exit_without_evaluation = True

            if should_exit_without_evaluation:
                sys.exit(0)

            alphabet = LSBF_Alphabet.from_vars(var_table.keys())

            eval_ctx = EvaluationContext(emit_introspect=emit_introspect, alphabet=alphabet, var_table=var_table)

            logger.info('Setup done. Proceeding to AST evaluation (backend: %s).', solver_config.backend_type.name)

            if isinstance(astp, AST_Connective) and astp.type == Connective_Type.AND and solver_config.optimizations.allow_sharding:
                model = evaluate_using_sharding(astp, eval_ctx)
                result = Evaluation_Result(run_stats=eval_ctx.stats, model=model, shards=[], solutions_nfa=None, var_table=var_table)
                return result

            nfa = run_evaluation_procedure(astp, eval_ctx)
            binary_model = nfa.find_model()
            if binary_model:
                formula_params = tuple(var for var, var_info in var_table.items() if var_info.is_formula_param)
                decadic_model = convert_binary_model_into_decadic(binary_model, formula_params)
            else:
                decadic_model = None

            result = Evaluation_Result(run_stats=eval_ctx.stats, solutions_nfa=nfa, model=decadic_model, var_table=var_table)
            return result

        elif statement_root == 'exit':
            return None
    return None


def make_nfa_for_congruence(congruence: Congruence, ctx: EvaluationContext) -> NFA:
    """ Construct an automaton accepting the solutions of the given congruence """
    vars: List[Var] = []
    coefs: List[int] = []

    terms = sorted(zip(congruence.vars, congruence.coefs), key = lambda pair: pair[0])
    vars, coefs = [], []
    for var, coef in terms:
        vars.append(var)
        coefs.append(coef)

    normalized_rhs = congruence.rhs % congruence.modulus
    ordered_congruence = Congruence(vars=vars, coefs=coefs, rhs=normalized_rhs, modulus=congruence.modulus)

    logger.debug(f'Reordered congruence from: %s to %s', congruence, ordered_congruence)

    # The alphabet might have only variable IDs but no names assigned to them yet, bind the variable names to IDs
    # so that we can do vizualization properly
    assert ctx.alphabet

    using_mtbdds = (solver_config.backend_type == BackendType.MTBDD)
    solving_over_ints = (solver_config.solution_domain == SolutionDomain.INTEGERS)
    if solving_over_ints and using_mtbdds:
        from amaya import mtbdd_transitions
        ctx.stats_operation_starts(ParsingOperation.BUILD_NFA_FROM_CONGRUENCE, None, None)
        nfa = mtbdd_transitions.MTBDDTransitionFn.construct_nfa_for_congruence(ordered_congruence, ctx.alphabet)
        ctx.stats_operation_ends(nfa)
        return nfa

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
    using_mtbdds = (solver_config.backend_type == BackendType.MTBDD)
    solving_over_ints = (solver_config.solution_domain == SolutionDomain.INTEGERS)
    if solving_over_ints and using_mtbdds:
        from amaya import mtbdd_transitions
        assert ctx.alphabet
        if relation.predicate_symbol == '=':
            ctx.stats_operation_starts(ParsingOperation.BUILD_NFA_FROM_EQ, None, None)
            nfa = mtbdd_transitions.MTBDDTransitionFn.construct_nfa_for_eq(relation, ctx.alphabet)
            ctx.stats_operation_ends(nfa)
        else:
            ctx.stats_operation_starts(ParsingOperation.BUILD_NFA_FROM_INEQ, None, None)
            nfa = mtbdd_transitions.MTBDDTransitionFn.construct_nfa_for_ineq(relation, ctx.alphabet)
            ctx.stats_operation_ends(nfa)
        return nfa

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
def get_automaton_for_operand(operand_ast: ASTp_Node, ctx: EvaluationContext, _depth: int) -> NFA:
    """
    Construct automaton accepting solutions of the formula given by its AST.

    If the given ast is not a leaf, the evaluation procedure is ran to build the NFA encoding the AST.
    """
    if isinstance(operand_ast, str):
        assert False
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


def minimize_automaton_if_configured(ast: ASTp_Node, nfa: NFA, ctx: EvaluationContext) -> NFA:
    """
    Perform the configured minimization on given NFA.

    Minimization result is monitored for runtime, and its results are emitted to context's introspection handle
    for visualization.

    :param ast: Formula encoded by the given nfa.
    :param nfa: Automaton to minimize.
    :param ctx: Evaluation context that will store information about measured timings.
    :returns: Minimized DFA equivalent to the given NFA.
    """
    input_automaton_size = len(nfa.states)

    if solver_config.minimization_method == MinimizationAlgorithms.NONE:
        return nfa

    ctx.stats_operation_starts(ParsingOperation.MINIMIZE, nfa, None)
    if solver_config.minimization_method == MinimizationAlgorithms.BRZOZOWSKI:
        minimized_dfa = nfa.minimize_brzozowski()
    else:
        if nfa.automaton_type != AutomatonType.DFA:
            ctx.stats_operation_starts(ParsingOperation.NFA_DETERMINIZE, nfa, None)
            nfa = nfa.determinize()
            input_automaton_size = max(len(nfa.states), input_automaton_size)
            ctx.stats_operation_ends(nfa)
        minimized_dfa = nfa.minimize_hopcroft()

    logger.info('Minimization applied - inputs has %d states, result %d.', len(nfa.states), len(minimized_dfa.states))
    ctx.stats_operation_ends(minimized_dfa)

    if solver_config.report_highly_effective_minimizations:
        if len(minimized_dfa.states) / input_automaton_size < 0.2:
            import pprint, sys
            print('---- Ultra effective minimization. AST:', file=sys.stderr)
            pprint.pprint(ast, stream=sys.stderr)

    return minimized_dfa


def select_children_to_lazily_evaluate(and_expr: AST_Connective, density_treshold: float = 0.5) -> Tuple[List[AST_Atom], List[ASTp_Node]] | None:
    """
    Decompose the given and expression into atoms and non-atomic formulae.

    If the atoms do not share a lot of common variables, then None is returned.
    """
    atoms: List[Union[Relation, Congruence]] = []
    not_atoms: List[ASTp_Node] = []

    vars: Set[Var] = set()

    for child in and_expr.children:
        if isinstance(child, (Relation, Congruence)):
            atoms.append(child)
            vars.update(child.vars)
            continue
        not_atoms.append(child)

    if not atoms:
        return

    # Calculate density
    density = sum(len(atom.vars) for atom in atoms) / (len(vars)*len(atoms))
    if density < density_treshold:
        return

    return cast(List[AST_Atom], atoms), not_atoms


def estimate_automaton_size(expr: ASTp_Node) -> int:
    match expr:
        case Relation():
            return sum(abs(coef) for coef in expr.coefs)
        case Congruence():
            return abs(expr.modulus)
        case AST_Negation():
            negated_expr = expr.child
            match negated_expr:
                case Relation():
                    return 2*sum(abs(coef) for coef in negated_expr.coefs)
                case Congruence():
                    return 2*abs(negated_expr.modulus)
                case BoolLiteral():
                    return 2
        case BoolLiteral():
            return 2

    return UNKNOWN_AUTOMATON_SIZE


def reorder_conjunction_to_derive_conflict_more_quickly(conj: AST_Connective) -> AST_Connective:
    # return conj
    conjuncts_sorted_by_size = sorted(conj.children, key=estimate_automaton_size, reverse=True)

    new_conjunction_children = []

    def get_referenced_vars(node: ASTp_Node) -> Set[Var]:
        match node:
            case Relation() | Congruence():
                return set(node.vars)
            case BoolLiteral() | Var():
                return set()
            case _:
                return set(node.referenced_vars)

    while len(new_conjunction_children) != len(conj.children):
        pivot = conjuncts_sorted_by_size.pop(-1)
        pivot_vars: Set[Var] = get_referenced_vars(pivot)

        overlapping_children = [pivot]
        popped_indices = []
        for child_rev_idx, child in enumerate(reversed(conjuncts_sorted_by_size)):
            child_vars = get_referenced_vars(child)
            if pivot_vars.intersection(child_vars):
                overlapping_children.append(child)
                popped_indices.append(len(conjuncts_sorted_by_size) - 1 - child_rev_idx)
                pivot_vars.update(child_vars)

        for idx in popped_indices:
            conjuncts_sorted_by_size.pop(idx)

        new_conjunction_children.extend(overlapping_children)
    return AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=tuple(new_conjunction_children))


def evaluate_binary_conjunction_expr(expr: AST_Connective,
                                     ctx: EvaluationContext,
                                     reduction_fn: Callable[[NFA, NFA], NFA],
                                     reduction_operation: ParsingOperation,
                                     _depth: int) -> NFA:
    """
    Abstract binary conjunction evaluation algorithm.

    Perform the evaluation of AND and OR expressions in an abstract fashion using the provided
    reduction function (used to compose the individual operands into a result).
    """
    if len(expr.children) == 1:
        # There might be situation when we simplify variable bounds that we lift some atoms all the way to the root of the formula
        # while keeping their connectives intact - for example, a [and, <atom>] might come to exist in the formula
        return get_automaton_for_operand(expr.children[0], ctx, _depth)

    if reduction_operation == ParsingOperation.NFA_INTERSECT:
        expr = reorder_conjunction_to_derive_conflict_more_quickly(expr)

    if reduction_operation == ParsingOperation.NFA_INTERSECT and solver_config.optimizations.do_lazy_evaluation:
        separation = select_children_to_lazily_evaluate(expr)
        if separation:
            atoms, non_atoms = separation

            from amaya.mtbdd_transitions import MTBDDTransitionFn
            ctx.stats_operation_starts(ParsingOperation.LAZY_CONSTRUCT, None, None)
            atoms_aut = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, [], ctx.get_alphabet())
            ctx.stats_operation_ends(atoms_aut)

            node = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=cast(Tuple[ASTp_Node,...], tuple(atoms)))
            atoms_aut = minimize_automaton_if_configured(node, atoms_aut, ctx)

            reduction_result = atoms_aut
            remaining_subformulae = tuple(non_atoms)
        else:
            reduction_result = get_automaton_for_operand(expr.children[0], ctx, _depth)
            remaining_subformulae = expr.children[1:]
    else:
        reduction_result = get_automaton_for_operand(expr.children[0], ctx, _depth)
        remaining_subformulae = expr.children[1:]

    for operand_idx, next_operand in enumerate(remaining_subformulae):
        # If the top-level of the formula looks like (OR F1 F2 ...) then
        # terminate if we already see an automaton for Fi with a nonempty language
        if solver_config.minimization_method != MinimizationAlgorithms.NONE:
            if reduction_result.final_states and _depth == 0 and reduction_operation == ParsingOperation.NFA_UNION:
                return reduction_result

        if reduction_operation == ParsingOperation.NFA_INTERSECT and not reduction_result.final_states:
            return reduction_result

        next_operand_automaton = get_automaton_for_operand(next_operand, ctx, _depth)

        # Apply the provided reduction function.
        ctx.stats_operation_starts(reduction_operation, reduction_result, next_operand_automaton)
        reduction_result = reduction_fn(reduction_result, next_operand_automaton)

        # reduction_result = reduction_result.determinize()
        ctx.stats_operation_ends(reduction_result)

        captured_subformula = AST_Connective(referenced_vars=tuple(), type=expr.type, children=remaining_subformulae[:operand_idx+1])
        reduction_result = minimize_automaton_if_configured(captured_subformula, reduction_result, ctx)

        emit_evaluation_progress_info((f' >> {reduction_operation}(lhs, rhs) '
                                       f'(result size: {len(reduction_result.states)}, '
                                       f'automaton_type={reduction_result.automaton_type})'), _depth)

    return reduction_result


def split_conjunction_to_shards(and_expr: AST_Connective) -> Tuple[List[Tuple[int, ...]], List[Tuple[Var, ...]]]:
    variable_partitions: Dict[Var, Tuple[Set[Var], Set[int]]] = {var: ({var}, set()) for var in and_expr.referenced_vars}

    def update_partitions(joining_vars: Iterable[Var], atom_idx: int):
        partition_union: Set[Var] = set()
        partition_nodes: Set[int] = {atom_idx}
        for var in joining_vars:
            var_partition, var_nodes = variable_partitions[var]
            partition_union.update(var_partition)
            partition_nodes.update(var_nodes)
        for var in partition_union:
            variable_partitions[var] = (partition_union, partition_nodes)

    for node_idx, node in enumerate(and_expr.children):
        match node:
            case Relation() | Congruence():
                update_partitions(joining_vars=node.vars, atom_idx=node_idx)
            case AST_Connective() | AST_Negation() | AST_Quantifier():
                update_partitions(joining_vars=node.referenced_vars, atom_idx=node_idx)

    partitions_and_atom_indices = {}
    for partition, atom_indices in variable_partitions.values():
        partitions_and_atom_indices[tuple(sorted(partition))] = tuple(sorted(atom_indices))

    return list(partitions_and_atom_indices.values()), list(partitions_and_atom_indices.keys())


def convert_binary_model_into_decadic(model: Tuple[LSBF_AlphabetSymbol, ...], vars: Tuple[Var,...]) -> Dict[Var, int]:
    base = 1
    var_values: List[int] = [0] * len(vars)
    for symbol_idx, symbol in enumerate(model):
        if symbol_idx < len(model) - 1: # Nonsign bits
            for var_idx, var in enumerate(vars):
                bit_val = 1 if symbol[var.id-1] == 1 else 0
                var_values[var_idx] += bit_val * base
        else: # Sign bit
            for var_idx, var in enumerate(vars):
                bit_val = 1 if symbol[var.id-1] == 1 else 0
                var_values[var_idx] -= bit_val * base
        base *= 2

    var_assignment: Dict[Var, int] = {}
    for var, var_value in zip(vars, var_values):
        var_assignment[var] = var_value
    return var_assignment


def construct_automaton_from_var_assignment(assignment: Dict[Var, int], ctx: EvaluationContext) -> NFA:
    aut = ctx.get_automaton_class_for_current_backend().trivial_accepting(ctx.get_alphabet())
    for var, var_value in assignment.items():
        relation = Relation(vars=[var], coefs=[1], rhs=var_value, predicate_symbol='=')
        var_aut = relations_to_nfa.build_nfa_from_linear_equality(ctx.get_automaton_class_for_current_backend(),
                                                                  ctx.get_alphabet(),
                                                                  relation)
        aut = aut.intersection(var_aut)  # type: ignore
    return aut


def evaluate_using_sharding(and_expr: AST_Connective, ctx: EvaluationContext) -> Dict[Var, int] | None:
    alphabet = ctx.get_alphabet()
    shards, shard_vars = split_conjunction_to_shards(and_expr)
    shard_logger.info('Performing sharding. Shards created based on vars: %s', shard_vars)
    shard_automata: List[NFA] = []
    overall_model: Dict[Var, int] = {}

    # @Incomplete: not sure whether we even need tracing information when sharding
    dummy_subformula = AST_Connective(referenced_vars=tuple(), type=Connective_Type.AND, children=tuple())

    for shard, shard_vars in zip(shards, shard_vars):
        shard_logger.info('Processing shard consisting of subformulae with indices: %s', shard)

        shard_automaton = ctx.get_automaton_class_for_current_backend().trivial_accepting(alphabet)
        for shard_formula_idx in shard:
            shard_formula = and_expr.children[shard_formula_idx]
            shard_elem_automaton = run_evaluation_procedure(shard_formula, ctx, _debug_recursion_depth=1)
            shard_automaton = shard_automaton.intersection(shard_elem_automaton)  # type: ignore

            shard_automaton = minimize_automaton_if_configured(dummy_subformula, shard_automaton, ctx)
            if (shard_automaton.automaton_type & AutomatonType.DFA) and not shard_automaton.final_states:
                shard_logger.info(f'The shard {shard} has no model!')
                return None

        shard_automata.append(shard_automaton)

        model = shard_automaton.find_model()
        if model is None:
            shard_logger.info(f'The shard {shard} has no model!')
            return None

        var_assignment = convert_binary_model_into_decadic(model, shard_vars)
        overall_model.update(var_assignment)

    return overall_model


def evaluate_and_expr(and_expr: AST_Connective, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an automaton corresponding to the given conjuction."""

    result = evaluate_binary_conjunction_expr(
        and_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.intersection(nfa2),
        ParsingOperation.NFA_INTERSECT,
        _depth
    )

    return result


def evaluate_or_expr(or_expr: AST_Connective, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an automaton corresponding to the given disjunction."""

    return evaluate_binary_conjunction_expr(
        or_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.union(nfa2),
        ParsingOperation.NFA_UNION,
        _depth
    )


def evaluate_not_expr(not_expr: AST_Negation, ctx: EvaluationContext, _depth: int) -> NFA:
    """Return the automaton corresponding to the given SMT expression containing a negated formula."""

    operand = get_automaton_for_operand(not_expr.child, ctx, _depth)

    # @Cleanup: I think we don't have to handle Bool automatons in an explicit manner - check whether we need this code.
    if (operand.automaton_type & AutomatonType.BOOL):
        assert len(operand.used_variables) == 1

        variable_id = operand.used_variables[0]
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

    operand = minimize_automaton_if_configured(not_expr, operand, ctx)

    emit_evaluation_progress_info(f' >> complement(operand) - (result size: {len(operand.states)})', _depth)
    return operand


def try_lazy_construct_conjunction(exists_node: AST_Quantifier, ctx: EvaluationContext) -> Optional[NFA]:
    if not (isinstance(exists_node.child, AST_Connective) and exists_node.child.type == Connective_Type.AND):
        return

    and_node: AST_Connective = exists_node.child

    if not all(isinstance(child, (Relation, Congruence)) for child in and_node.children):
        return

    logger.info('Lazy constructing %s', and_node)
    atoms: List[Relation | Congruence] = list(and_node.children[0:])  # type: ignore
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
    nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(new_atoms, list(exists_node.bound_vars), ctx.get_alphabet())
    ctx.stats_operation_ends(nfa)

    logger.info("Lazy construnction done, result has %d states", len(nfa.states))
    nfa = minimize_automaton_if_configured(exists_node, nfa, ctx)
    return nfa


def evaluate_exists_expr(exists_expr: AST_Quantifier, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an NFA corresponding to the given formula of the form (exists (vars) (phi))."""

    # Perform a look-ahead to see whether we can construct the NFA for the entire conjunction using a lazy approach
    if solver_config.backend_type == BackendType.MTBDD and solver_config.optimizations.do_lazy_evaluation:
        nfa = try_lazy_construct_conjunction(exists_expr, ctx)
        if nfa:
            return nfa

    nfa = get_automaton_for_operand(exists_expr.child, ctx, _depth)

    # We need to establish an order of individual projections applied, so that we can tell when we are projecting away
    # the last variable in this quantifier, because we don't need to do padding closure after every single variable
    # projection - we have to do it only after the variable has been projected away.

    logger.debug(f'Established projection order: {exists_expr.bound_vars}')

    last_var_to_project = exists_expr.bound_vars[-1]
    for var in exists_expr.bound_vars:
        logger.debug(f'Projecting away variable {var}')
        ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)

        # It is sufficient to do the padding closure only after the last variable is projected away
        skip_pad_closure = False if var == last_var_to_project else True

        projection_result = nfa.do_projection(var, skip_pad_closure=skip_pad_closure)
        assert projection_result
        nfa = projection_result
        ctx.stats_operation_ends(nfa)
        logger.debug(f'Variable {var} projected away.')

    nfa = minimize_automaton_if_configured(exists_expr, nfa, ctx)

    emit_evaluation_progress_info(f' >> projection({exists_expr.bound_vars}) (result_size: {len(nfa.states)})', _depth)
    return nfa


def evaluate_bool_equivalence_expr(ast: AST_Connective, ctx: EvaluationContext, _depth: int = 0) -> NFA:
    """
    Constructs an automaton for the given equivalence of two Booleans.

    The Bool equivalence LEFT <=> RIGHT is evaluated as:
    LEFT -> RIGHT && RIGHT -> LEFT
    ((NOT LEFT) OR RIGHT) AND ((NOT RIGHT) OR LEFT)
    """
    assert len(ast.children) == 2, 'Equivalence with more than 2 children is currently not supported.'

    left_nfa = get_automaton_for_operand(ast.children[0], ctx, _depth)
    right_nfa = get_automaton_for_operand(ast.children[1], ctx, _depth)

    if left_nfa.automaton_type & AutomatonType.NFA:
        left_nfa = left_nfa.determinize()
    if right_nfa.automaton_type & AutomatonType.NFA:
        right_nfa = right_nfa.determinize()

    not_left = left_nfa.complement()
    not_right = right_nfa.complement()

    branch1 = not_left.union(right_nfa).determinize()
    branch2 = not_right.union(left_nfa).determinize()

    equivalence_nfa = branch1.intersection(branch2)
    return equivalence_nfa


def run_evaluation_procedure(ast: ASTp_Node,
                             ctx: EvaluationContext,
                             _debug_recursion_depth: int = 0) -> NFA:
    """
    Evaluates the entire SMT given SMT tree and returns the NFA accepting the solutions of the given formula.

    :param ast: The formula to evaluate into an automaton.
    :param ctx: The context of the performed evaluation.
    :param _debug_recursion_depth: Used to pretty print debugging information about the progress of evaluation.
    :returns: The NFA corresponding to the given formula.
    """

    match ast:
        case BoolLiteral():
            bool_vars = set(var for var in ctx.get_alphabet().all_vars if ctx.var_table[var].type == VariableType.BOOL)
            automaton_cls = ctx.get_automaton_class_for_current_backend()
            if ast.value:
                result = cast(Type[MTBDD_NFA], automaton_cls).trivial_accepting(ctx.get_alphabet())
            else:
                result = cast(Type[MTBDD_NFA], automaton_cls).trivial_nonaccepting(ctx.get_alphabet())
            return result

        case Congruence():
            return make_nfa_for_congruence(ast, ctx)

        case Relation():
            return build_automaton_from_presburger_relation_ast(ast, ctx, _debug_recursion_depth)

        case Var():
            if ctx.var_table[ast].type != VariableType.BOOL:
                raise ValueError(f'AST contains a freestanding non-boolean variable, don\'t know how to evaluate that. {ast}')
            return build_automaton_for_boolean_variable(var=ast, var_value=True, ctx=ctx)

        case AST_Connective():
            fn_table = {
                Connective_Type.AND:   evaluate_and_expr,
                Connective_Type.OR:    evaluate_or_expr,
                Connective_Type.EQUIV: evaluate_bool_equivalence_expr,
            }

            fn = fn_table[ast.type]
            result = fn(ast, ctx, _debug_recursion_depth)

        case AST_Quantifier():
            result = evaluate_exists_expr(ast, ctx, _debug_recursion_depth)

        case AST_Negation():
            result = evaluate_not_expr(ast, ctx, _debug_recursion_depth)

        case _:
            raise NotImplementedError(f'Don\'t know how to evaluate {ast}.')

    return result
