from __future__ import annotations
import presburger_algorithms as pa
from ast_relations import (
    extract_relation,
    expand_relation_on_ite,
    try_retrieve_variable_if_literal,
)

from automatons import NFA, AutomatonType, MTBDD_NFA, LSBF_Alphabet
from log import logger, formatter
from logging import INFO
from dataclasses import dataclass
import time
from typing import (
    List,
    Set,
    Tuple,
    Any,
    Union,
    Dict,
    Callable,
    Optional
)
from enum import IntEnum, Enum
import logging
import sys

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)


class SolutionDomain(IntEnum):
    NATURALS = 0
    INTEGERS = 1


class BackendType(IntEnum):
    NAIVE = 1
    MTBDD = 2


class ParsingOperation(Enum):
    BUILD_NFA_FROM_INEQ = 'build_nfa_from_ineq'
    BUILD_NFA_FROM_SHARP_INEQ = 'build_nfa_from_sharp_ineq'
    BUILD_NFA_FROM_EQ = 'build_nfa_from_eq'
    BUILD_NFA_FROM_RELATION = 'build_nfa_from_relation'  # We don't know the relation type, or we do not care.
    NFA_UNION = 'union'
    NFA_PROJECTION = 'projection'
    NFA_COMPLEMENT = 'complement'
    NFA_DETERMINIZE = 'determinize'
    NFA_INTERSECT = 'intersection'
    BUILD_DFA_FROM_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_SHARP_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_EQ = 'build_dfa_from_ineq'


class VariableType(IntEnum):
    INT = 1
    BOOL = 2
    UNSET = 3

    @staticmethod
    def from_smt_type_string(type_str: str) -> VariableType:
        m = {
            'Bool': VariableType.BOOL,
            'Int': VariableType.INT,
        }
        return m[type_str]


@dataclass
class EvaluationStat():
    operation: ParsingOperation
    input1_size: int
    input2_size: Optional[int]
    output_size: Optional[int]
    runtime_ns: int


@dataclass
class FunctionSymbol:
    name: str
    arity: int
    args: List[Tuple[str, VariableType]]
    return_type: VariableType


IntrospectHandle = Callable[[NFA, ParsingOperation], None]


@dataclass
class VariableInfo:
    id: int
    name: str
    type: VariableType = VariableType.UNSET  # variable was found in a Presburger expr, but was not bound via exists
    ussage_count: int = 0


@dataclass
class ExecutionConfig:
    solution_domain: SolutionDomain
    backend_type: BackendType


class EvaluationContext:
    def __init__(self,
                 domain: SolutionDomain,
                 backend=BackendType.NAIVE,
                 emit_introspect=lambda nfa, operation: None,
                 alphabet: Optional[LSBF_Alphabet] = None  # From previous passes
                 ):
        self.binding_stack: List[Dict[str, NFA]] = []
        self.domain = domain
        self.introspect_handle = emit_introspect

        # Evaluation stats
        self.collect_stats = True
        self.stats: List[EvaluationStat] = []
        self.pending_operations_stack: List[Any] = []

        # Variables (not the `let` ones)
        self.next_available_variable_id = 1  # Number them from 1, MTBDDs require
        self.variables_info_stack: List[Dict[str, VariableInfo]] = []
        self.global_variables: Dict[str, VariableInfo] = {}

        # Execution settings
        self.execution_config = ExecutionConfig(domain, backend)

        self.logger = logging.getLogger('EvaluationContext')
        self.logger.setLevel(logging.DEBUG)
        handler = logging.StreamHandler(sys.stdout)
        handler.setFormatter(formatter)
        self.logger.addHandler(handler)

        self.alphabet = alphabet

    def get_alphabet(self) -> LSBF_Alphabet:
        if self.alphabet is None:
            raise ValueError('Requesting an overall alphabet from the evaluation context when None has been set.')
        return self.alphabet

    def get_let_binding_value(self, var_name: str) -> Optional[NFA]:
        '''Retrieves the (possible) value of a lexical binding introduced via the
        SMTlib `let` construct. Currently we suppose the bindings bind names to the
        automatons.'''
        for binding_record in reversed(self.binding_stack):
            if var_name in binding_record:
                return binding_record[var_name]
        return None

    def new_let_binding_context(self):
        '''Creates a new binding frame/context.'''
        self.logger.debug('Entering a new binding context.')
        self.binding_stack.append(dict())

    def insert_let_binding(self, var_name: str, nfa: NFA):
        '''Insters a new `let` binding of the given var_name to the given nfa.'''
        self.binding_stack[-1][var_name] = nfa

    def insert_all_bindings_into_current_context(self, bindings: Dict[str, NFA]):
        '''A bulk transaction operation that inserts all the bindings represented
        in the given binding into the current let binding context.
        '''
        for var_name, nfa in bindings.items():
            self.insert_let_binding(var_name, nfa)

    def pop_binding_context(self):
        popped_ctx = self.binding_stack.pop(-1)
        self.logger.debug(f'Popping the current let binding context. Contents: {popped_ctx}')

    def emit_evaluation_introspection_info(self, nfa: NFA, operation: ParsingOperation):
        self.introspect_handle(nfa, operation)

    def stats_operation_starts(self, operation: ParsingOperation, input1: Optional[NFA], input2: Optional[NFA]):
        '''Notify the context that the parsing operation started.'''
        startpoint = [
            operation,
            len(input1.states) if input1 is not None else None,
            len(input2.states) if input2 is not None else None,
            time.time_ns()
        ]

        self.pending_operations_stack.append(startpoint)

    def stats_operation_ends(self, output: NFA):
        '''Notify the context that the parsing operation ended and it can create a new stat point.'''
        op_startpoint = self.pending_operations_stack.pop(-1)  # Operation starting point
        op, size1, size2, start_ns = op_startpoint

        runtime = time.time_ns() - start_ns

        stat = EvaluationStat(op, size1, size2, len(output.states), runtime)
        logger.critical(f"Operation finished: {stat}")
        self.stats.append(stat)

    def get_all_currently_available_variables() -> List[Tuple[str, str]]:
        '''Retrieves all variables (and their types) in the order they have been
        located by the smt parser.

        Returns:
            A list of all variables that have been encountered until the current
            point of execution, in the same order they have been encountered.
        '''

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
        '''Creates and associates a new variable info entry in the current frame.
        If a variable of the given name already exists in the current frame an
        exception is raised (cannot have duplicit exists?).
        .'''
        current_frame = self.variables_info_stack[-1]
        if variable_name not in current_frame:
            var_id = self._generate_new_variable_id()
            current_frame[variable_name] = VariableInfo(id=var_id,
                                                        name=variable_name,
                                                        type=variable_type)
        else:
            raise ValueError(
                f'DUPLICIT EXISTS: Attempting to add a variable "{variable_name}" to the current frame, but it is already defined.')

    def get_variable_type_if_defined(self, variable_name: str) -> Optional[VariableType]:
        '''Performs variable lookup in the variable frames (local -> enclosing -> global).
        If a binding for the given variable name is present returns the variable type,
        otherwise returns None. '''
        maybe_variable = self.lookup_variable(variable_name)
        if maybe_variable is None:
            return None
        else:
            return maybe_variable.type

    def was_variable_encountered(self, variable_name: str) -> bool:
        maybe_var = self.lookup_variable(variable_name)
        return maybe_var is not None

    def get_variables_info_for_current_frame(self) -> Dict[str, VariableInfo]:
        return self.variables_info_stack[-1]

    def add_multiple_variables_to_current_frame(self,
                                                variables: Dict[str, VariableType]):
        '''Bulk version of add_variable_to_current_frame.'''
        for variable_name, variable_type in variables.items():
            self.add_variable_to_current_frame(variable_name, variable_type=variable_type)

    def get_variable_id(self, variable_name: str, variable_type: VariableType = VariableType.UNSET) -> int:
        '''Retrives the variable ID associated with the given variable name.
        If the variable name was not previously bound in any way a new global
        variable will be associated with the name and its ID will be returned.
        '''
        return self.get_variable_info(variable_name, variable_type).id

    def get_variable_info(self, variable_name: str,
                          variable_type: VariableType = VariableType.UNSET) -> VariableInfo:
        '''Attempts to search for variable information associated with the given
        variable name in the internal structures in the following order: local
        variables, enclosing variables (etc.), global variables.

        If no variable information is located creates a new global variable info
        entry (with new id and unset type) and returns that.
        '''

        maybe_variable = self.lookup_variable(variable_name)
        if maybe_variable is not None:
            return maybe_variable

        self.logger.debug(f'Querying information for variable (variable_name="{variable_name}") which is unbound, creating global variable entry.')
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
        '''The bulk version of notify get_variable_id.'''
        assigned_ids = []
        for variable_name in variable_names:
            assigned_ids.append((variable_name,
                                 self.get_variable_id(variable_name)))
        return assigned_ids

    def add_global_variable(self, var_name: str, var_type: VariableType = VariableType.UNSET):
        var_id = self._generate_new_variable_id()
        self.global_variables[var_name] = VariableInfo(var_id, var_name,  var_type)


def _eval_info(msg, depth):
    logger.info('  ' * depth + msg)


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


def get_variable_binding_info(bindings: List[Tuple[str, str]]) -> Dict[str, VariableType]:
    var_info: Dict[str, VariableType] = {}
    for binding in bindings:
        var_name, var_type_raw = binding
        if var_type_raw == 'Int':
            var_type = VariableType.INT
        elif var_type_raw == 'Bool':
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


def can_tree_be_reduced_to_aritmetic_expr(tree) -> bool:
    '''Checks that the given `tree` contains only valid function symbols for an
    aritmetic expression. A valid aritmetic expression is also considered to be
    an expression that contains ITE that expand itself also to an aritmetic expr.'''
    if type(tree) == list:
        root = tree[0]
        if root in ['+', '*']:
            return can_tree_be_reduced_to_aritmetic_expr(tree[1]) and can_tree_be_reduced_to_aritmetic_expr(tree[2])
        elif root in ['-']:
            if len(tree) == 2:
                return can_tree_be_reduced_to_aritmetic_expr(tree[1])
            else:
                return can_tree_be_reduced_to_aritmetic_expr(tree[1]) and can_tree_be_reduced_to_aritmetic_expr(tree[2])
        elif root in ['ite']:
            return can_tree_be_reduced_to_aritmetic_expr(tree[2]) and can_tree_be_reduced_to_aritmetic_expr(tree[3])
        else:
            return False
    return True


def is_tree_presburger_equality(tree, ctx: EvaluationContext) -> bool:
    '''Checks whether the provided AST `tree` represents a an equality
    (Presburger atomic formula).
    To do so it first performs checks on the structure of the tree - whether it
    does contain only operators allowed in a such expression. If it does have
    a valid form performs further checks on whether it is not SMT equivalence
    check between a boolean variable and a `let` bound expression.'''

    def is_literal_from_let_or_boolean_var(literal_var: str) -> bool:
        if ctx.get_let_binding_value(literal_var) is not None:
            return True

        maybe_left_var_info = ctx.lookup_variable(maybe_left_literal_var)
        if maybe_left_var_info is not None:
            return maybe_left_var_info.type == VariableType.BOOL
        return False

    if type(tree) != list:
        return False

    if tree[0] != '=' or len(tree) != 3:
        return False

    if can_tree_be_reduced_to_aritmetic_expr(tree[1]) and can_tree_be_reduced_to_aritmetic_expr(tree[2]):
        maybe_left_literal_var = try_retrieve_variable_if_literal(tree[1])
        maybe_right_literal_var = try_retrieve_variable_if_literal(tree[2])

        return not (is_literal_from_let_or_boolean_var(maybe_left_literal_var) and is_literal_from_let_or_boolean_var(maybe_right_literal_var))

    return False


def get_all_used_variables(tree, ctx: EvaluationContext) -> Set[Tuple[str, int, VariableType]]:  # NOQA
    '''Traverses the whole AST `tree` and identifies all the variables used. Manages
    the variable contexts implaced by the ussage of \\exists, so that two
    variables with the same name, one of them bound via \\exists other is in
    FREE(\\psi) are treated as a two separate variables.

    Returns:
        The set of all identified variables in form of:
            (<variable_name>, <variable_id>, <variable_type>)
    '''

    if type(tree) != list:
        # Dealing with a standalone string
        if ctx.get_let_binding_value(tree) is not None:
            return set()
        else:
            info = ctx.get_variable_info(tree)
            return {(info.name, info.id, info.type)}

    root = tree[0]
    if root in ['<', '<=', '>=', '>', '=']:
        if root == '=':
            if not is_tree_presburger_equality(tree, ctx):
                # This is a SMT boolean equality check (all variables should be
                # defined beforhand (either let, or defun)
                return set()

        expanded_relation = expand_relation_on_ite(tree)
        if expanded_relation[0] == 'or':
            # The relation was successful and produced a new subtree.
            return get_all_used_variables(expanded_relation, ctx)

        apf = extract_relation(tree)  # Atomic Presburger Formula

        # Register all the variables located in the Presburger formula
        variables_used: Set[Tuple[str, int, VariableType]] = set()
        for variable_name in apf.variable_names:
            var_info = ctx.get_variable_info(variable_name)
            var_info.ussage_count += 1  # The variable was used somewhere
            variables_used.add((var_info.name, var_info.id, var_info.type))

        return variables_used

    elif root in ['exists']:
        # When we are entering the new context (\\exists) we can bound at max
        # only those variables that are bound by the \\exists, nothing more -
        # all other variables then belong to the enclosing scopes
        ctx.push_new_variable_info_frame()
        variable_bindings = get_variable_binding_info(tree[1])
        ctx.add_multiple_variables_to_current_frame(variable_bindings)
        used_variables = get_all_used_variables(tree[2], ctx)
        ctx.pop_variable_frame()
        return used_variables

    elif root in ['not', 'assert']:
        return get_all_used_variables(tree[1], ctx)

    elif root in ['or', 'and']:
        vars: Set[VariableInfo] = set()
        for conj_term in tree[1:]:
            term_vars = get_all_used_variables(conj_term, ctx)
            vars = vars.union(term_vars)
        return vars
    elif root in ['let']:
        # Let has the following structure:
        # (let (<variable_binding>+) <term>)
        ctx.new_let_binding_context()
        vars: Set[VariableInfo] = set()
        for variable_binding in tree[1]:
            variable_name, variable_tree = variable_binding
            ctx.insert_let_binding(variable_name, 'Prepass - automaton not expanded.')
            vars = vars.union(get_all_used_variables(variable_tree, ctx))
        term_vars = get_all_used_variables(tree[2], ctx)
        ctx.pop_binding_context()
        return term_vars.union(vars)
    else:
        raise ValueError(f'Unhandled branch when exploring the SMT tree. {tree}')


def get_declared_function_symbols(top_level_smt_statements: List) -> List[FunctionSymbol]:
    '''Retrieves the top-level declared function symbols from the internal smt representation.'''
    declared_function_symbols: List[FunctionSymbol] = []
    for statement in top_level_smt_statements:
        if statement[0] == 'declare-fun':
            symbol_name: str = statement[1]
            symbol_arg_list: List = statement[2]
            symbol_ret_type: VariableType = VariableType.from_smt_type_string(statement[3])
            symbol_args = []
            for arg_name, arg_type in symbol_arg_list:
                symbol_args.append((arg_name, VariableType.from_smt_type_string(arg_type)))

            declared_function_symbols.append(FunctionSymbol(symbol_name,
                                                            len(symbol_args),
                                                            symbol_args,
                                                            symbol_ret_type))
    return declared_function_symbols


def lex(source: str) -> List[str]:
    source = strip_comments(source)
    source = source.replace('(', ' ( ').replace(')', ' ) ')
    tokens = source.split()
    return tokens


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


def get_asserts_from_ast(ast):
    # TODO: Remove this
    _asserts = []
    for top_level_expr in ast:
        if top_level_expr[0] == 'assert':
            _asserts.append(top_level_expr)
    return _asserts


def check_result_matches(source_text: str,
                         emit_introspect=lambda nfa, op: None) -> bool:

    tokens = lex(source_text)
    ast = build_syntax_tree(tokens)

    smt_info = get_smt_info(ast)
    asserts = get_asserts_from_ast(ast)
    logger.info(f'Extracted smt-info: {smt_info}')
    logger.info(f'Extracted {len(asserts)} from source text.')

    eval_ctx = EvaluationContext(SolutionDomain.INTEGERS)

    function_symbols = get_declared_function_symbols(ast)
    constant_symbols = list(filter(lambda function_symbol: function_symbol.arity == 0, function_symbols))
    for constant_symbol in constant_symbols:
        eval_ctx.add_global_variable(constant_symbol.name, var_type=constant_symbol.return_type)

    assert_tree = asserts[0]
    replace_forall_with_exists(assert_tree)
    expand_implications(assert_tree)

    get_all_used_variables(asserts[0], eval_ctx)

    variable_ids = list(range(1, eval_ctx.next_available_variable_id))  # Discard the name and type information, keep only IDS
    logger.info(f'Extracted variables({len(variable_ids)}) ids: {variable_ids}')
    alphabet = LSBF_Alphabet.from_variable_ids(variable_ids)
    logger.info(f'Created alphabet: {alphabet}')

    eval_ctx = EvaluationContext(SolutionDomain.INTEGERS, emit_introspect, alphabet=alphabet)
    for constant_symbol in constant_symbols:
        eval_ctx.add_global_variable(constant_symbol.name, var_type=constant_symbol.return_type)

    nfa = eval_assert_tree(asserts[0], eval_ctx)

    should_be_sat = True  # Assume true, in case there is no info in the smt source
    if ':status' in smt_info:
        if smt_info[':status'] == 'unsat':
            should_be_sat = False

    is_sat, example_word = nfa.is_sat()
    sat_matches = is_sat == should_be_sat

    if sat_matches:
        if is_sat:
            logger.debug(f'The result\'s SAT is OK (as expected) (SAT={is_sat}, example: {example_word})')
        else:
            logger.debug(f'The result\'s SAT is OK (as expected) (SAT={is_sat})')
    else:
        logger.warn(f'The automaton\'s SAT didn\'t match expected: actual={is_sat}, given word: {example_word}, expected={should_be_sat}')

    return sat_matches


def build_automaton_from_presburger_relation_ast(relation_root,
                                                 ctx: EvaluationContext,
                                                 depth: int) -> NFA:
    # This is broken - the building algorithms take more params.
    building_handlers = {
        SolutionDomain.INTEGERS: {
            '<':  (ParsingOperation.BUILD_NFA_FROM_SHARP_INEQ,
                   pa.build_nfa_from_sharp_inequality),
            '<=': (ParsingOperation.BUILD_NFA_FROM_INEQ,
                   pa.build_nfa_from_inequality),
            '=':  (ParsingOperation.BUILD_NFA_FROM_EQ,
                   pa.build_nfa_from_equality)
        },
        SolutionDomain.NATURALS: {
            '<':  (ParsingOperation.BUILD_DFA_FROM_SHARP_INEQ,
                   pa.build_dfa_from_sharp_inequality),
            '<=': (ParsingOperation.BUILD_DFA_FROM_INEQ,
                   pa.build_dfa_from_inequality),
            '=':  (ParsingOperation.BUILD_DFA_FROM_EQ,
                   pa.build_dfa_from_sharp_inequality)
        }
    }

    automaton_constr = NFA
    if ctx.execution_config.backend_type == BackendType.MTBDD:
        automaton_constr = MTBDD_NFA

    logger.debug(f'Building an automaton for: {relation_root}')
    relation = extract_relation(relation_root)
    operation, automaton_building_function = building_handlers[ctx.execution_config.solution_domain][relation.operation]

    # The relation might have som yet-not-seen variables, add them if need be
    variables_with_ids = ctx.get_multiple_variable_ids(relation.variable_names)

    # The extracted relation contains the list of variables and their
    # coeficients in an arbitrary order - we need to make sure that the order
    # of variables will be by ascending IDs (MTBDD requirement)
    variables_with_ids_correct_order = sorted(variables_with_ids,
                                              key=lambda var_with_id: var_with_id[1])

    # Shuffle the variables in the extracted relation so that it matches the
    # alphabet
    variables_with_coeficients_dict = {}
    variables_with_coeficients_dict.update(zip(relation.variable_names, relation.variable_coeficients))
    variables_ordered = []
    coeficients_ordered = []
    for variable_name, _ in variables_with_ids_correct_order:
        variables_ordered.append(variable_name)
        coeficients_ordered.append(variables_with_coeficients_dict.get(variable_name))
    logger.debug(f'Reshufling the variables found in relation from: {0} to {1}'.format(
        list(zip(relation.variable_names, relation.variable_coeficients)),
        list(zip(variables_ordered, coeficients_ordered))
    ))
    relation.variable_names = variables_ordered
    relation.variable_coeficients = coeficients_ordered

    _, ordered_variable_ids = zip(*variables_with_ids_correct_order)

    logger.info(f'Variables with IDs used: {variables_with_ids_correct_order}')
    # We need to construct the alphabet for the automaton beforehand.
    # Use the variable ids for the alphabet
    # alphabet = LSBF_Alphabet.from_variable_names_with_ids(variables_with_ids_correct_order)
    automaton_building_function_args = (relation,
                                        list(ordered_variable_ids),
                                        ctx.get_alphabet(),
                                        automaton_constr)

    if relation.operation == '<':
        # We are going to evaluate this as '<' = ('<=' and (not '='))
        # First we build an automaton from the equality
        eq_op, equality_automaton_building_function = building_handlers[ctx.execution_config.solution_domain]['=']
        ineq_op, inequality_automaton_building_function = building_handlers[ctx.execution_config.solution_domain]['<=']

        equality_automaton = equality_automaton_building_function(*automaton_building_function_args)

        ctx.emit_evaluation_introspection_info(equality_automaton,
                                               eq_op)
        negated_equality_automaton = equality_automaton.determinize().complement()

        inquality_automaton = inequality_automaton_building_function(*automaton_building_function_args)
        ctx.emit_evaluation_introspection_info(inquality_automaton,
                                               ineq_op)
        automaton = negated_equality_automaton.intersection(inquality_automaton)
        ctx.emit_evaluation_introspection_info(automaton, ParsingOperation.NFA_INTERSECT)
    else:
        automaton = automaton_building_function(*automaton_building_function_args)
        ctx.emit_evaluation_introspection_info(automaton, operation)
    _eval_info(f' >> {operation.value}({relation_root}) (result size: {len(automaton.states)})', depth)

    for variable, _ in variables_with_ids:
        ctx.lookup_variable(variable).ussage_count += 1

    return automaton


def build_automaton_for_boolean_variable(var_name: str,
                                         var_value: bool,
                                         ctx: EvaluationContext) -> NFA:
    logger.debug(f'Building an equivalent automaton for the bool variable {var_name}, with value {var_value}.')
    var_id = ctx.get_variable_id(var_name)
    return NFA.for_bool_variable(ctx.get_alphabet(), var_id, var_value)


def evaluate_let_bindings(binding_list, ctx: EvaluationContext) -> Dict[str, NFA]:
    logger.debug(f'Evaluating binding list of size: {len(binding_list)}')
    binding: Dict[str, NFA] = {}
    for var_name, expr in binding_list:
        logger.debug(f'Building automaton for var {var_name} with expr: {expr}')
        nfa = eval_smt_tree(expr, ctx)  # Indirect recursion, here we go
        binding[var_name] = nfa

    return binding


def get_nfa_for_term(term: Union[str, List],
                     ctx: EvaluationContext,
                     _depth: int) -> NFA:
    if type(term) == str:
        # If it is a string, then it should reference a variable
        # previously bound to a value, or a bool variable which can be
        # converted to Automaton directly
        logger.debug('Found a usage of a bound variable in evaluated node.')

        is_bool_var = False
        variable_info = ctx.lookup_variable(term)
        if variable_info is not None:
            if variable_info.type == VariableType.BOOL:
                is_bool_var = True

        if is_bool_var:
            logger.debug(f'The reached variable {term} was queried as a boolean variable.')
            # We build an automaton for `var_name` with True value. Should
            # the boolean be considered False, it would be encoded
            # ['not', 'var_name'], which is equivalent to the complement of the
            # automaton.
            return build_automaton_for_boolean_variable(term, True, ctx)
        else:
            logger.debug(f'The variable {term} is not boolean, searching `let` bindings.')

        nfa = ctx.get_let_binding_value(term)
        if nfa is None:
            logger.fatal(f'A referenced variable: `{term}` was not found in any of the binding contexts, is SMT2 file malformed?.')
            logger.debug(f'Bound variables: `{ctx.binding_stack}`')
            raise ValueError(f'A variable `{term}` referenced inside AND could not be queried for its NFA.')
        else:
            logger.debug(f'Value query for variable `{term}` OK.')
        return nfa
    else:
        # The node must be evaluated first
        nfa = eval_smt_tree(term,
                            ctx,
                            _debug_recursion_depth=_depth+1)
        return nfa


def evaluate_binary_conjunction_term(term: Union[str, List],
                                     ctx: EvaluationContext,
                                     reduction_fn: Callable[[NFA, NFA], NFA],
                                     reduction_name: str,
                                     _depth: int) -> NFA:
    ''' Evaluates AND, OR terms'''
    assert len(term) >= 3
    lhs_term = term[1]

    op = ParsingOperation.NFA_INTERSECT if reduction_name == 'intersection' else ParsingOperation.NFA_UNION

    lhs = get_nfa_for_term(lhs_term, ctx, _depth)

    for term_i in range(2, len(term)):
        rhs_term = term[term_i]
        rhs = get_nfa_for_term(rhs_term, ctx, _depth)

        assert type(rhs) == NFA

        ctx.stats_operation_starts(op, lhs, rhs)
        lhs = reduction_fn(lhs, rhs)
        ctx.stats_operation_ends(lhs)

        _eval_info(f' >> {reduction_name}(lhs, rhs) (result size: {len(lhs.states)})', _depth)
        ctx.emit_evaluation_introspection_info(lhs, ParsingOperation.NFA_INTERSECT)

    return lhs


def evaluate_and_term(term: Union[str, List],
                      ctx: EvaluationContext,
                      _depth: int) -> NFA:

    result = evaluate_binary_conjunction_term(
        term,
        ctx,
        lambda nfa1, nfa2: nfa1.intersection(nfa2),
        'intersection',
        _depth
    )

    return result


def evaluate_or_term(term: Union[str, List],
                     ctx: EvaluationContext,
                     _depth: int) -> NFA:

    return evaluate_binary_conjunction_term(
        term,
        ctx,
        lambda nfa1, nfa2: nfa1.union(nfa2),
        'union',
        _depth
    )


def evaluate_not_term(term: Union[str, List],
                      ctx: EvaluationContext,
                      _depth: int) -> NFA:

    assert len(term) == 2
    operand = get_nfa_for_term(term[1], ctx, _depth)

    assert type(operand) == NFA

    if (operand.automaton_type & AutomatonType.BOOL):
        assert len(operand.used_variables) == 1

        variable_id: int = operand.used_variables[0]
        variable_value: bool = operand.extra_info['bool_var_value']
        logger.debug('Complementing an automaton for a bool variable {variable_id}, returninig direct complement.')
        ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
        result = NFA.for_bool_variable(ctx.get_alphabet(), variable_id, not variable_value)
        ctx.stats_operation_ends(result)
        return result

    if (operand.automaton_type & AutomatonType.NFA):
        ctx.stats_operation_starts(ParsingOperation.NFA_DETERMINIZE, operand, None)
        operand = operand.determinize()
        ctx.stats_operation_ends(operand)
        _eval_info(f' >> determinize into DFA (result size: {len(operand.states)})', _depth)

    # TODO(psyco): Here we should check, whether the automaton is Complete
    # (Determinism is not enough)

    ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
    operand = operand.complement()
    ctx.stats_operation_ends(operand)

    _eval_info(f' >> complement(operand) - (result size: {len(operand.states)})', _depth)

    ctx.emit_evaluation_introspection_info(operand, ParsingOperation.NFA_COMPLEMENT)
    return operand


def evaluate_exists_term(term: Union[str, List],
                         ctx: EvaluationContext,
                         _depth: int) -> NFA:
    assert len(term) == 3

    # We are entering a new variable frame (only exists can bind variables to
    # types / manipulate FREE/BOUND sets)
    ctx.push_new_variable_info_frame()
    variable_bindings: Dict[str, VariableType] = get_variable_binding_info(term[1])
    logger.debug(f'Exists - Extracted variable type bindings for {variable_bindings.keys()}')
    ctx.add_multiple_variables_to_current_frame(variable_bindings)

    nfa = get_nfa_for_term(term[2], ctx, _depth)

    vars_info = ctx.get_variables_info_for_current_frame()
    for var_name in variable_bindings:
        if vars_info[var_name].ussage_count == 0:
            # We are attemtping to project away a variable that is nowhere not
            # used in the tree nderneath - since an optimalization that removes
            # those kinds of variables from the alphabet is performed the
            # projection woul fail.
            logger.info(f'Skipping projecting away a variable "{var_name}" - the variable is not used anywhere in the tree underneath.')
            continue
        var_id = vars_info[var_name].id
        ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)
        nfa = nfa.do_projection(var_id)
        ctx.stats_operation_ends(nfa)

        ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.NFA_PROJECTION)

    _eval_info(f' >> projection({variable_bindings}) (result_size: {len(nfa.states)})', _depth)

    ctx.pop_variable_frame()
    return nfa


def eval_smt_tree(root,  # NOQA
                  ctx: EvaluationContext,
                  _debug_recursion_depth=0,
                  ) -> NFA:

    if not type(root) == list:
        # This means that either we hit a SMT2 term (boolean variable) or
        # the tree is malformed, and therefore we cannot continue.

        # TODO(psyco): This will be moved to get_nfa, replace this with a call to get_nfa.
        # Is the term a bool variable?
        is_bool_var = False
        maybe_variable_type = ctx.get_variable_type_if_defined(root)
        if maybe_variable_type is not None and maybe_variable_type == VariableType.BOOL:
            is_bool_var = True

        if is_bool_var:
            logger.debug('Reached a SMT2 term {0}, which was queried as a boolean variable.'.format(root))
            # We build an automaton for `var_name` with True value. Should
            # the boolean be considered False, it would be encoded
            # ['not', 'var_name'], which is equivalent to the complement of the
            # automaton.
            return build_automaton_for_boolean_variable(root, True)
        else:
            nfa = ctx.get_binding(root)
            if nfa is None:
                raise ValueError(f'Unknown SMT2 term: {root}.')
            else:
                return nfa

    node_name = root[0]
    if node_name in ['<', '>', '<=', '>=', '=']:
        # We have found node which needs to be translated into NFA
        logger.info('Reached relation root, performing ITE expansion...')

        expanded_tree = expand_relation_on_ite(root)

        # If the relation was indeed expanded, the root will be 'or'
        if expanded_tree[0] == 'or':
            return eval_smt_tree(expanded_tree, ctx, _debug_recursion_depth)
        else:
            # The relation was no expanded
            # (maybe a second evaluation pass, after the first expansion)

            ctx.stats_operation_starts(ParsingOperation.BUILD_NFA_FROM_RELATION, None, None)
            result = build_automaton_from_presburger_relation_ast(root,
                                                                  ctx,
                                                                  _debug_recursion_depth)
            ctx.stats_operation_ends(result)
            return result
    else:
        _eval_info(f'eval_smt_tree({root})', _debug_recursion_depth)
        # Current node is a NFA operation
        if node_name == 'and':
            return evaluate_and_term(root, ctx, _debug_recursion_depth)
        elif node_name == 'or':
            return evaluate_or_term(root, ctx, _debug_recursion_depth)
        elif node_name == 'not':
            return evaluate_not_term(root, ctx, _debug_recursion_depth)
        elif node_name == 'exists':
            return evaluate_exists_term(root, ctx, _debug_recursion_depth)
        elif node_name == 'let':
            # `let` has this structure [`let`, `<binding_list>`, <term>]
            assert len(root) == 3
            binding_list = root[1]
            term = root[2]

            ctx.new_let_binding_context()

            # The variables in bindings can be evaluated to their automatons.
            bindings = evaluate_let_bindings(binding_list, ctx)  # TODO(psyco): Lookup variables when evaluating bindings.
            logger.debug(f'Extracted bindings {bindings.keys()}')

            ctx.insert_all_bindings_into_current_context(bindings)

            # The we evaluate the term, in fact represents the value of the
            # whole `let` block
            term_nfa = eval_smt_tree(term, ctx, _debug_recursion_depth)

            ctx.pop_binding_context()  # We are leaving the `let` block
            return term_nfa

        else:
            raise NotImplementedError(f'Error while evaluating tree, unknown operation: {node_name}, assert_tree')


def eval_assert_tree(assert_tree,
                     ctx: EvaluationContext):
    assert assert_tree[0] == 'assert'
    forall_cnt = replace_forall_with_exists(assert_tree)
    logger.info(f'Replaced {forall_cnt} forall nodes in the AST.')
    implications_cnt = expand_implications(assert_tree)
    logger.info(f'Performed {implications_cnt} implications expansions in the AST.')
    return eval_smt_tree(assert_tree[1], ctx)


def expand_multivariable_bindings(assertion_tree):
    if assertion_tree[0] in ['exists', 'forall']:
        binding_type, bindings, term = assertion_tree
        assert len(bindings) > 0

        if len(bindings) >= 2:
            # We are dealing with multivariable exits
            # ["exists" [x Type, y Type, ...] TERM]]
            leftmost_binding = bindings[0]
            tail = bindings[1:]

            # Prepare substatement
            substmt = [binding_type, tail, term]

            # Update tree
            assertion_tree[1] = [leftmost_binding]
            assertion_tree[2] = substmt

    if assertion_tree[0] in ['exists', 'not', 'forall', 'assert']:
        expand_multivariable_bindings(assertion_tree[-1])


def replace_forall_with_exists(assertion_tree):
    '''
    The forall quantifiers (nodes) are replaced by not-exists-not inplace,
    mutating assertion tree.
    Params:
        assertion_tree @mutable
    Returns:
        The count of how many forall expansions occured.
    '''
    node_replaced_const = 0
    if assertion_tree[0] == 'forall':
        _, binders, stmt = assertion_tree

        not_stmt = ['not', stmt]
        exists = ['exists', binders, not_stmt]

        assertion_tree[0] = 'not'
        assertion_tree[1] = exists
        assertion_tree.pop(-1)  # Remove the original stmt from [forall, binders, stmt] -> [not, [exists, [not, stmt]]]
        node_replaced_const = 1

    if assertion_tree[0] in ['exists', 'not', 'forall', 'assert']:
        return node_replaced_const + replace_forall_with_exists(assertion_tree[-1])
    if assertion_tree[0] in ['let']:
        expansion_acc = node_replaced_const

        binding_list = assertion_tree[1]
        for var, expr in binding_list:
            expansion_acc += replace_forall_with_exists(expr)

        term = assertion_tree[2]
        expansion_acc += replace_forall_with_exists(term)
        return expansion_acc
    else:
        return node_replaced_const  # Bottom of the recursion


def expand_implications(assertion_tree) -> int:
    root_node_name = assertion_tree[0]
    if root_node_name == '=>':
        left_statement = assertion_tree[1]
        right_statement = assertion_tree[2]

        left_negated = ['not', left_statement]
        assertion_tree[0] = 'or'
        assertion_tree[1] = left_negated
        assertion_tree[2] = right_statement

        implications_expanded = 1
        # Implications might be used somewhere down the tree
        implications_expanded += expand_implications(assertion_tree[1])
        implications_expanded += expand_implications(assertion_tree[2])

        return implications_expanded
    else:
        if root_node_name in ['and', 'or', '=']:
            # Since and,or,= are n-ary, we need to descend into all of their
            # subterms
            implications_expanded = 0
            for term_i in range(1, len(assertion_tree)):
                implications_expanded += expand_implications(assertion_tree[term_i])
            return implications_expanded
        elif root_node_name in ['forall', 'exists', 'not', 'assert']:
            # Those contain only one formula - descend into it
            return expand_implications(assertion_tree[-1])
        else:
            return 0


def remove_multiple_negations(assertion_tree):
    pass


def get_formula(_assert):
    return _assert[1]


def get_smt_info(ast) -> Dict[str, Any]:
    smt_info: Dict[str, Any] = dict()
    for top_level_statement in ast:
        statement_fn = top_level_statement[0]
        if statement_fn == 'set-info':
            info_category = top_level_statement[1]
            info_value = top_level_statement[2]

            smt_info[info_category] = info_value

    return smt_info


S0_SMT_TREE = ['<=', 10, 'x']

S1_SMT_TREE = ['and',
               ['<=', 10, 'x'],
               ['<=', 10, 'y']]

S2_SMT_TREE = ['=', ['ite', 'b0', 'x', ['*', '2', 'x']], '0']
