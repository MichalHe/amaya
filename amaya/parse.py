from __future__ import annotations
from enum import IntEnum, Enum
from dataclasses import dataclass
from logging import INFO
import time
from typing import (
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

from amaya.ast_definitions import (
    AST_NaryNode,
    AST_Node,
    FunctionSymbol,
    NodeEncounteredHandlerStatus,
    VariableType,
)
from amaya.ast_relations import (
    ModuloTerm,
    Relation,
    expand_relation_on_ite,
    try_retrieve_variable_if_literal,
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
import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.relations_structures import BoolLiteral
from amaya.tokenize import tokenize
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType,
)
from amaya import utils

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)


class ParsingOperation(Enum):
    BUILD_NFA_FROM_INEQ = 'build_nfa_from_ineq'
    BUILD_NFA_FROM_SHARP_INEQ = 'build_nfa_from_sharp_ineq'
    BUILD_NFA_FROM_EQ = 'build_nfa_from_eq'
    BUILD_NFA_FROM_CONGRUENCE = 'build_nfa_from_eq'
    BUILD_NFA_FROM_RELATION = 'build_nfa_from_relation'  # We don't know the relation type, or we do not care.
    NFA_UNION = 'union'
    NFA_PROJECTION = 'projection'
    NFA_COMPLEMENT = 'complement'
    NFA_DETERMINIZE = 'determinize'
    NFA_INTERSECT = 'intersection'
    BUILD_DFA_FROM_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_SHARP_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_EQ = 'build_dfa_from_ineq'
    MINIMIZE = 'minimization'


@dataclass
class EvaluationStat():
    operation: ParsingOperation
    input1_size: int
    input2_size: Optional[int]
    output_size: Optional[int]
    runtime_ns: int


IntrospectHandle = Callable[[NFA, ParsingOperation], None]


@dataclass
class VariableInfo:
    id: int
    name: str
    type: VariableType = VariableType.UNSET  # variable was found in a Presburger expr, but was not bound via exists
    usage_count: int = 0


class EvaluationContext:
    def __init__(self, emit_introspect=lambda nfa, operation: None, alphabet: Optional[LSBF_Alphabet] = None, global_scope: Optional[Dict[str, VariableInfo]] = None):
        self.introspect_handle = emit_introspect

        # Evaluation stats
        self.collect_stats = True
        self.stats: List[EvaluationStat] = []
        self.pending_operations_stack: List[Any] = []

        self.next_available_variable_id = 1  # Number them from 1, MTBDDs require
        self.variables_info_stack: List[Dict[str, VariableInfo]] = []
        self.global_variables: Dict[str, VariableInfo] = global_scope if global_scope is not None else {}

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

    def emit_evaluation_introspection_info(self, nfa: NFA, operation: ParsingOperation):
        self.introspect_handle(nfa, operation)

    def stats_operation_starts(self, operation: ParsingOperation, input1: Optional[NFA], input2: Optional[NFA]):
        """(performance tracking) Note the time at which the given operation with given params starts."""
        if not solver_config.track_operation_runtime:
            return

        startpoint = [
            operation,
            len(input1.states) if input1 is not None else None,
            len(input2.states) if input2 is not None else None,
            time.time_ns()
        ]

        self.pending_operations_stack.append(startpoint)

    def stats_operation_ends(self, output: NFA):
        """(performance tracking) Note the time at which the given operation with given params ends."""
        if not solver_config.track_operation_runtime:
            return

        op_startpoint = self.pending_operations_stack.pop(-1)  # Operation starting point
        op, size1, size2, start_ns = op_startpoint

        runtime = time.time_ns() - start_ns

        stat = EvaluationStat(op, size1, size2, len(output.states), runtime)
        logger.info(f"Operation finished: {stat}")
        self.stats.append(stat)

    def _generate_new_variable_id(self) -> int:
        variable_id = self.next_available_variable_id
        self.next_available_variable_id += 1
        return variable_id

    def push_new_variable_info_frame(self):
        logger.debug('Entering a new variable binding frame (\\exists).')
        self.variables_info_stack.append({})

    def pop_variable_frame(self):
        popped_frame = self.variables_info_stack.pop(-1)
        logger.debug(f'Exiting a variable binding frame (\\exists). Contents: {popped_frame}.')

    def add_variable_to_current_frame(self,
                                      variable_name: str,
                                      variable_type: VariableType = VariableType.UNSET):
        """
        Add a new variable with given name and type to the current variable frame.

        Creates and associates a new variable info entry in the current frame with given name and type.
        If a variable of the given name already exists in the current frame an exception is raised.
        """
        current_frame = self.variables_info_stack[-1]
        if variable_name not in current_frame:
            var_id = self._generate_new_variable_id()
            current_frame[variable_name] = VariableInfo(id=var_id, name=variable_name, type=variable_type)
        else:
            err_msg = (f'Attempting to add a variable "{variable_name}" to the current frame, '
                        'but it is already defined.')
            raise ValueError(err_msg)

    def get_variable_type_if_defined(self, variable_name: str) -> Optional[VariableType]:
        """
        Performs variable lookup in the variable frames (local -> enclosing -> global).

        :returns: the variable type if found, otherwise returns None.
        """
        maybe_variable = self.lookup_variable(variable_name)
        if maybe_variable is None:
            return None
        else:
            return maybe_variable.type

    def get_variables_info_for_current_frame(self) -> Dict[str, VariableInfo]:
        return self.variables_info_stack[-1]

    def add_multiple_variables_to_current_frame(self, variables: Dict[str, VariableType]):
        """Add the given variables with their type to the current frame."""
        for variable_name, variable_type in variables.items():
            self.add_variable_to_current_frame(variable_name, variable_type=variable_type)

    def get_variable_id(self, variable_name: str, variable_type: VariableType = VariableType.UNSET) -> int:
        """
        Get the ID associated with the given variable name.

        If the variable name was not previously bound in any way a new global
        variable will be associated with the name and its ID will be returned.
        """
        return self.get_variable_info(variable_name, variable_type).id

    def get_variable_info(self, variable_name: str,
                          variable_type: VariableType = VariableType.UNSET) -> VariableInfo:
        """
        Locate variable with given name in variable scopes and return its info.

        Searches for variable information associated with the given variable name in variable scopes
        (local -> enclosing -> global).

        If no entry matching given name is found a new variable entry in the global scope is created
        (with new id and unset type), and returned.
        """

        maybe_variable = self.lookup_variable(variable_name)
        if maybe_variable is not None:
            return maybe_variable

        variable_id = self._generate_new_variable_id()
        new_variable_info = VariableInfo(id=variable_id,
                                         name=variable_name,
                                         type=variable_type)

        self.global_variables[variable_name] = new_variable_info
        return new_variable_info

    def lookup_variable(self, variable_name: str) -> Optional[VariableInfo]:
        for variable_info_frame in reversed(self.variables_info_stack):
            if variable_name in variable_info_frame:
                return variable_info_frame[variable_name]

        # If we got here, we did not locate any frame where the pres. variable
        # is bound to a type -- maybe it is an unbound (global) variable that
        # was already encounted
        if variable_name in self.global_variables:
            return self.global_variables[variable_name]
        return None

    def get_multiple_variable_ids(self, variable_names: List[str]) -> List[Tuple[str, int]]:
        """Search variable scopes for given variable names and return their ids (along with their names)."""
        assigned_ids = []
        for variable_name in variable_names:
            assigned_ids.append((variable_name,
                                 self.get_variable_id(variable_name)))
        return assigned_ids

    def add_global_variable(self, var_name: str, var_type: VariableType = VariableType.UNSET) -> int:
        if var_name not in self.global_variables:
            var_id = self._generate_new_variable_id()
            self.global_variables[var_name] = VariableInfo(var_id, var_name,  var_type)
            return var_id
        else:
            # @Broken: Report an error about declaring a function symbol multiple times
            return self.global_variables[var_name].id

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


def get_all_used_variables(tree: AST_Node, ctx: EvaluationContext) -> Set[Tuple[str, int, VariableType]]:  # NOQA
    """
    Traverse the given AST and collect the variables that are referenced.

    The variables are collected in a context sensitive manner, recognizing that equally named variables
    are not the same when bound by different quantifiers.

    :returns: The set of all identified variables in form of (<variable_name>, <variable_id>, <variable_type>)
    """

    if not isinstance(tree, list):
        if isinstance(tree, BoolLiteral):
            return set()
        if isinstance(tree, Relation):
            # Register all the variables located in the Presburger formula
            variables_used: Set[Tuple[str, int, VariableType]] = set()
            for variable_name in tree.variable_names:
                var_info = ctx.get_variable_info(variable_name)
                var_info.usage_count += 1  # The variable was used somewhere
                variables_used.add((var_info.name, var_info.id, var_info.type))

            for modulo_term in tree.modulo_terms:
                for variable_name in modulo_term.variables:
                    var_info = ctx.get_variable_info(variable_name)
                    var_info.usage_count += 1  # The variable was used somewhere
                    variables_used.add((var_info.name, var_info.id, var_info.type))

            # @Broken: This does not consider div terms, however, it should.
            return variables_used

        # Tree is a reference to a normal variable, consult with context whether this is the first encounter
        # @FIXME: We should not declare a new variable on the spot as it has not been declared - we don't know its type.
        info = ctx.get_variable_info(tree)
        return set([(info.name, info.id, info.type)])

    root = tree[0]

    assert_failure_desc = 'Relations should be reduced into direcly evaluable leaves at this point.'
    assert root not in ['<', '<=', '>=', '>'], assert_failure_desc

    if root == '=':
        # Relations are preprocessed in a separate pass - this must be a Boolean equivalence
        return get_all_used_variables(tree[1], ctx).union(get_all_used_variables(tree[2], ctx))


    if root in ['exists']:
        ctx.push_new_variable_info_frame()
        variable_bindings = parse_variable_bindings_list_to_internal_repr(tree[1])
        ctx.add_multiple_variables_to_current_frame(variable_bindings)
        used_variables = get_all_used_variables(tree[2], ctx)
        ctx.pop_variable_frame()
        return used_variables

    elif root in ['not', 'assert']:
        return get_all_used_variables(tree[1], ctx)

    elif root in ['or', 'and']:
        vars: Set[Tuple[str, int, VariableType]] = set()
        for conj_term in tree[1:]:
            term_vars = get_all_used_variables(conj_term, ctx)
            vars = vars.union(term_vars)
        return vars

    else:
        # @Cleanup: This message is very ambiguous
        raise ValueError(f'Unhandled branch when exploring the SMT tree. Tree: {tree}')


def build_syntax_tree(tokens: List[str]):
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


def add_only_used_function_constants_to_context(ctx: EvaluationContext,
                                                used_variables: Set[Tuple[str, int, VariableType]],
                                                declared_function_symbols: Sequence[FunctionSymbol]):
    """Adds only used declared function constants to ctx."""
    starting_id = ctx.next_available_variable_id
    used_variable_ids = set(var_info[1] for var_info in used_variables)

    function_symbol_ids = [i + starting_id for i in range(len(declared_function_symbols))]
    for i, function_symb in enumerate(declared_function_symbols):
        variable_id = i + starting_id
        if variable_id in used_variable_ids:
            ctx.add_global_variable(var_name=function_symb.name, var_type=function_symb.return_type)


# @Cleanup: This should be renamed to something like evaluate_smt2
def perform_whole_evaluation_on_source_text(source_text: str,
                                            emit_introspect: IntrospectHandle = lambda nfa, op: None
                                            ) -> Tuple[NFA, Dict[str, str]]:
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

        elif statement_root == 'declare-fun':
            if len(top_level_statement) != 4:
                raise ValueError(f'Invalid syntax: declare-fun has invalid form: {top_level_statement}')
            decl_fun = top_level_statement

            sym_name: str = decl_fun[1]
            sym_args = [
                (arg_name, VariableType.from_smt_type_string(arg_type)) for arg_name, arg_type_raw in decl_fun[2]
            ]
            sym_ret_type = VariableType.from_smt_type_string(decl_fun[3])

            function_symbol_to_info_map[sym_name] = FunctionSymbol(name=sym_name, arity=len(sym_args), args=sym_args,
                                                                   return_type=sym_ret_type)

        elif statement_root == 'check-sat':
            if eval_result:
                raise ValueError('Multiple check-sat commands are not supported!')

            logger.debug('Executing amaya (%d asserts collected) with smt-info: %s', len(formulae_to_assert), smt_info)
            if not formulae_to_assert:
                raise ValueError('Cannot check-sat without any asserts.')

            ctx = EvaluationContext()
            function_symbols = sorted(function_symbol_to_info_map.values(), key=lambda symbol: symbol.name)

            # If there are multiple assert statements, evaluate their conjunction
            formula_to_evaluate = formulae_to_assert[0] if len(formulae_to_assert) == 1 else ['and'] + formulae_to_assert

            # @Note: Preprocessing will modify the given list
            function_symbols, formula_to_evaluate = preprocessing.preprocess_ast(formula_to_evaluate,
                                                                                 constant_function_symbols=function_symbols)

            for fun_symbol in function_symbols:
                ctx.add_global_variable(fun_symbol.name, var_type=fun_symbol.return_type)

            bool_symbols = {
                var_name for var_name, v_info in ctx.global_variables.items() if v_info.type == VariableType.BOOL
            }
            formula_to_evaluate, _ = ast_eval_lib.convert_ast_into_evaluable_form(formula_to_evaluate, bool_symbols)
            logger.info('Created following evaluable AST: %s', formula_to_evaluate)

            # formula_to_evaluate = preprocessing.rewrite_nonlinear_terms(formula_to_evaluate)

            if solver_config.preprocessing.simplify_variable_bounds:
                logger.info(f'Simplifying variable bounds of formula: %s', formula_to_evaluate)
                formula_to_evaluate = var_bounds_lib.simplify_bounded_atoms(formula_to_evaluate)
                logger.info(f'Simplified formula: %s', formula_to_evaluate)

            if solver_config.preprocessing.perform_antiprenexing:
                logger.info('Performing antiprenexing of: %s', formula_to_evaluate)
                formula_to_evaluate = preprocessing.antiprenexing.perform_antiprenexing(formula_to_evaluate)
                logger.info('Antiprenexing done, Result: %s', formula_to_evaluate)
            elif solver_config.preprocessing.perform_prenexing:
                logger.info('Performing prenexing on: %s', formula_to_evaluate)
                formula_to_evaluate = preprocessing.prenexing.convert_formula_to_pnf(formula_to_evaluate)
                logger.info('Prenexing performed. Result: %s', formula_to_evaluate)

            # Count all distinct variables in the formula
            all_vars = get_all_used_variables(formula_to_evaluate, ctx)

            # There might be declared global function constants that are not used in the formula. If the asserted
            # formula does not talk about these variables, they are not needed during the procedure and they would only
            # slow down the procedure. At the moment we don't generate values for these variables in a model.
            # @Note: Not sure whether they need to be a part of the generated model, check with Z3
            unused_global_function_constant_offset = min((var_info[1] for var_info in all_vars), default=1) - 1
            vars_with_ids = [
                (var_name, (var_id - unused_global_function_constant_offset)) for var_name, var_id, _ in all_vars
            ]
            alphabet = LSBF_Alphabet.from_variable_id_pairs(vars_with_ids)

            eval_ctx = EvaluationContext(emit_introspect=emit_introspect, alphabet=alphabet)
            add_only_used_function_constants_to_context(eval_ctx, all_vars, function_symbols)

            logger.info('Setup done. Proceeding to AST evaluation (backend: %s).', solver_config.backend_type.name)
            nfa = run_evaluation_procedure(formula_to_evaluate, eval_ctx)
            eval_result = nfa
        elif statement_root == 'exit':
            return (nfa, smt_info)
    return (nfa, smt_info)


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
        logger.info(f'Encountered relation that is always true: {relation}, returning trivial accepting automaton.')
        return automaton_constr.trivial_accepting(ctx.alphabet)

    # We should never encounter the '<' inequality as we are always converting it to the <=
    assert relation.predicate_symbol in ('<=', '=')
    operation, automaton_building_function = building_handlers[solver_config.solution_domain][relation.predicate_symbol]

    # Congruence relations of the form a.x ~ k must be handled differently - it is necessary to reorder
    # the modulo term inside, not the nonmodular variables
    if relation.is_congruence_equality():
        logger.debug(f'Given relation: %s is congruence equivalence. Reordering variables.', relation)
        modulo_term = relation.modulo_terms[0]
        variable_id_pairs = sorted(ctx.get_multiple_variable_ids(modulo_term.variables),
                                   key=lambda pair: pair[1])
        var_names, var_coefs = utils.reorder_variables_according_to_ids(
                variable_id_pairs,
                (modulo_term.variables, modulo_term.variable_coefficients))

        modulo_term_ordered = ModuloTerm(variables=var_names,
                                         variable_coefficients=var_coefs,
                                         constant=modulo_term.constant,
                                         modulo=modulo_term.modulo)

        relation.modulo_terms[0] = modulo_term_ordered

        logger.debug(f'Reordered modulo term from: %s to %s', modulo_term, modulo_term_ordered)

        # The alphabet might have only variable IDs but no names assigned to them yet, bind the variable names to IDs
        # so that we can do vizualization properly
        ctx.alphabet.assert_variable_names_to_ids_match(variable_id_pairs)

        nfa = relations_to_nfa.build_presburger_modulo_nfa(automaton_constr, ctx.alphabet, relation, variable_id_pairs)

        ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.BUILD_NFA_FROM_CONGRUENCE)
        return nfa

    else:
        assert not relation.modulo_terms
        assert not relation.div_terms

        # The extracted relation contains the list of variables and their
        # coefficients in an arbitrary order - we need to make sure that the order
        # of variables will be by ascending IDs (MTBDD requirement)
        variable_id_pairs = sorted(ctx.get_multiple_variable_ids(relation.variable_names),
                                   key=lambda pair: pair[1])
        var_names, var_coefs = utils.reorder_variables_according_to_ids(
                variable_id_pairs,
                (relation.variable_names, relation.variable_coefficients))

        # The alphabet might have only variable IDs but no names, inject
        # the variable names so that we can do vizualization properly
        ctx.alphabet.assert_variable_names_to_ids_match(variable_id_pairs)

        reordered_relation = Relation.new_lin_relation(variable_names=var_names, variable_coefficients=var_coefs,
                                                       absolute_part=relation.absolute_part,
                                                       predicate_symbol=relation.predicate_symbol)

        assert automaton_building_function
        nfa = automaton_building_function(automaton_constr, ctx.alphabet, reordered_relation, variable_id_pairs)
        ctx.emit_evaluation_introspection_info(nfa, operation)

        emit_evaluation_progress_info(
            f' >> {operation.value}({relation}) (result size: {len(nfa.states)}, automaton_type={nfa.automaton_type})',
            depth
        )

    # Finalization - increment variable usage counter and bind variable ID to a name in the alphabet (lazy binding)
    # as the variable IDs could not be determined beforehand.
    for var_name, var_id in variable_id_pairs:
        var_info = ctx.lookup_variable(var_name)
        assert var_info, ('Failed to retrieve variable info from evaluation context to increment variable usage '
                          'counter after an automaton for an atomic constraint was built.')
        var_info.usage_count += 1

    return nfa


# @Cleanup: Fold this function in if it is even used
def build_automaton_for_boolean_variable(var_name: str, var_value: bool, ctx: EvaluationContext) -> NFA:
    """Construct an automaton corresponding the given boolean variable."""
    logger.debug(f'Building an equivalent automaton for the bool variable {var_name}, with value {var_value}.')
    var_id = ctx.get_variable_id(var_name)
    return ctx.get_automaton_class_for_current_backend().for_bool_variable(ctx.get_alphabet(), var_id, var_value)


# @Cleanup: How is this function even used? We now have Relations in the AST, so we typically take the else branch.
def get_automaton_for_operand(operand_ast: AST_Node, ctx: EvaluationContext, _depth: int) -> NFA:
    """
    Construct automaton accepting solutions of the formula given by its AST.

    If the given ast is not a leaf, the evaluation procedure is ran to build the NFA encoding the AST.
    """
    if isinstance(operand_ast, str):
        logger.debug('Requested the automaton for an operand that is an AST Leaf (str).'
                     'Searching variable scopes for its definition.')

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
            nfa = nfa.determinize()
            ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.NFA_DETERMINIZE)
        minimized_dfa = nfa.minimize_hopcroft()

    logger.info('Minimization applied - inputs has %d states, result %d.', len(nfa.states), len(minimized_dfa.states))
    ctx.stats_operation_ends(minimized_dfa)
    ctx.emit_evaluation_introspection_info(minimized_dfa, ParsingOperation.MINIMIZE)
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
        expr = expr[1]  # type: ignore

    first_operand = expr[1]

    reduction_result = get_automaton_for_operand(first_operand, ctx, _depth)

    for next_operand in expr[2:]:
        next_operand_automaton = get_automaton_for_operand(next_operand, ctx, _depth)

        # Apply the provided reduction function.
        ctx.stats_operation_starts(reduction_operation, reduction_result, next_operand_automaton)
        reduction_result = reduction_fn(reduction_result, next_operand_automaton)

        # reduction_result = reduction_result.determinize()

        ctx.stats_operation_ends(reduction_result)

        # Emit the evaluation information before minimization
        ctx.emit_evaluation_introspection_info(reduction_result, reduction_operation)

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
        ctx.stats_operation_starts(ParsingOperation.NFA_DETERMINIZE, operand, None)
        operand = operand.determinize()
        ctx.stats_operation_ends(operand)
        ctx.emit_evaluation_introspection_info(operand, ParsingOperation.NFA_DETERMINIZE)
        emit_evaluation_progress_info(f' >> determinize into DFA (result size: {len(operand.states)})', _depth)

    ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
    assert operand.automaton_type & AutomatonType.DFA, f'{operand.automaton_type} {not_expr}'
    operand = operand.complement()
    ctx.stats_operation_ends(operand)

    operand = minimize_automaton_if_configured(operand, ctx)

    emit_evaluation_progress_info(f' >> complement(operand) - (result size: {len(operand.states)})', _depth)

    ctx.emit_evaluation_introspection_info(operand, ParsingOperation.NFA_COMPLEMENT)
    return operand


def evaluate_exists_expr(exists_expr: AST_NaryNode, ctx: EvaluationContext, _depth: int) -> NFA:
    """Construct an NFA corresponding to the given formula of the form (exists (vars) (phi))."""
    assert len(exists_expr) == 3

    # We are entering a new variable frame (only exists can bind variables to
    # types / manipulate FREE/BOUND sets)
    ctx.push_new_variable_info_frame()
    variable_bindings: Dict[str, VariableType] = parse_variable_bindings_list_to_internal_repr(exists_expr[1])
    logger.debug(f'Exists - Extracted variable type bindings for {variable_bindings.keys()}')
    ctx.add_multiple_variables_to_current_frame(variable_bindings)

    # Perform a look-ahead to see whether we can construct the NFA for the entire conjunction using a lazy approach
    if solver_config.backend_type == BackendType.MTBDD and solver_config.allow_lazy_evaluation:
        if isinstance(exists_expr[2], list) and exists_expr[2][0] == 'and':
            conjunction = exists_expr[2]
            if all(isinstance(child, Relation) for child in conjunction[1:]):
                atoms: List[Relation] = conjunction[1:]  # type: ignore
                from amaya.mtbdd_transitions import MTBDDTransitionFn
                quantified_vars: List[str] = [var for var in variable_bindings]
                nfa = MTBDDTransitionFn.construct_dfa_for_atom_conjunction(atoms, quantified_vars, ctx.get_alphabet(), ctx.get_variable_id)
                ctx.pop_variable_frame()
                return nfa

    nfa = get_automaton_for_operand(exists_expr[2], ctx, _depth)
    vars_info = ctx.get_variables_info_for_current_frame()

    # We need to establish an order of individual projections applied, so that we can tell when we are projecting away
    # the last variable in this quantifier, because we don't need to do padding closure after every single variable
    # projection - we have to do it only after the variable has been projected away.
    projected_var_ids: List[int] = list()
    for var_name in variable_bindings:
        current_var_info = vars_info[var_name]
        if current_var_info.usage_count > 0:
            projected_var_ids.append(current_var_info.id)
        else:
            logger.debug('Skipping projection of %s - 0 ussages found.', var_name)

    if not projected_var_ids:
        # No projection will occur
        ctx.pop_variable_frame()
        return nfa

    logger.debug(f'Established projection order: {projected_var_ids}')

    last_var_id: int = projected_var_ids[-1]
    for var_id in projected_var_ids:
        logger.debug(f'Projecting away variable {var_id}')
        ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)

        # It is sufficient to do the padding closure only after the last variable is projected away
        skip_pad_closure = False if var_id == last_var_id else True

        projection_result = nfa.do_projection(var_id, skip_pad_closure=skip_pad_closure)
        assert projection_result
        nfa = projection_result
        ctx.stats_operation_ends(nfa)
        logger.debug(f'Variable {var_id} projected away.')

        ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.NFA_PROJECTION)

    nfa = minimize_automaton_if_configured(nfa, ctx)

    emit_evaluation_progress_info(f' >> projection({variable_bindings}) (result_size: {len(nfa.states)})', _depth)

    ctx.pop_variable_frame()
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
            return NFA.trivial_accepting(ctx.get_alphabet()) if ast.value else NFA.trivial_nonaccepting(ctx.get_alphabet())
        if isinstance(ast, Relation):
            return build_automaton_from_presburger_relation_ast(ast, ctx, _debug_recursion_depth)

        # Check whether the thing we have encountered is a Boolean variable. If not, the input formula is malformed.
        # @Cleanup: This should all be done in preprocessing - instead of having a string for a boolean variable
        #           that we check every time, the tree should already be preprocessed to contain a Boolean variable,
        #           or the error should have been reported to the user.
        is_bool_var = False
        maybe_variable_type = ctx.get_variable_type_if_defined(ast)
        if maybe_variable_type is not None and maybe_variable_type == VariableType.BOOL:
            logger.debug('Reached a SMT2 term %s, which was queried as a boolean variable.', ast)
            return build_automaton_for_boolean_variable(var_name=ast, var_value=True, ctx=ctx)

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
