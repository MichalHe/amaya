from __future__ import annotations
import presburger_algorithms as pa
from ast_relations import (
    extract_relation,
    ModuloTerm,
    Relation,
    expand_relation_on_ite,
    try_retrieve_variable_if_literal,
)

from automatons import NFA, AutomatonType, LSBF_Alphabet
from log import logger
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
    Optional,
    Generator
)
from enum import IntEnum, Enum
import utils
from utils import number_to_bit_tuple

import preprocessing

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)

from ast_definitions import (
        AST_Leaf,
        AST_Node,
        AST_NaryNode,
        NodeEncounteredHandler,
        NodeEncounteredHandlerStatus)


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
class EvaluationConfig:
    solution_domain: SolutionDomain
    backend_type: BackendType
    print_operation_runtime: bool = False


class EvaluationContext:
    def __init__(self,
                 evaluation_config: EvaluationConfig,
                 emit_introspect=lambda nfa, operation: None,
                 alphabet: Optional[LSBF_Alphabet] = None  # From previous passes
                 ):
        self.binding_stack: List[Dict[str, NFA]] = []
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
        self.execution_config = evaluation_config

        # Lazy load MTBDD automata module if needed
        self.automata_cls = NFA
        if self.execution_config.backend_type == BackendType.MTBDD:
            from mtbdd_automatons import MTBDD_NFA
            self.automata_cls = MTBDD_NFA

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
        self.binding_stack.pop(-1)

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
        if self.execution_config.print_operation_runtime:
            logger.critical(f"Operation finished: {stat}")
        self.stats.append(stat)

    def get_all_currently_available_variables(self) -> List[Tuple[str, str]]:
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
        exception is raised (cannot have duplicitous exists?).
        .'''
        current_frame = self.variables_info_stack[-1]
        if variable_name not in current_frame:
            var_id = self._generate_new_variable_id()
            current_frame[variable_name] = VariableInfo(id=var_id,
                                                        name=variable_name,
                                                        type=variable_type)
        else:
            raise ValueError(
                f'DUPLICITOUS EXISTS: Attempting to add a variable "{variable_name}" to the current frame, but it is already defined.')

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
        if var_name not in self.global_variables:
            var_id = self._generate_new_variable_id()
            self.global_variables[var_name] = VariableInfo(var_id, var_name,  var_type)

    def get_automaton_class_for_current_backend(self):
        return self.automata_cls


def emit_evaluation_progress_info(msg: str, depth: int):
    '''Logs the provided message with the correct indentation as is the current parser depth
    in the SMT tree. The logging level is INFO by default.
    '''
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


def parse_variable_bindings_list_to_internal_repr(bindings: List[Tuple[str, str]]) -> Dict[str, VariableType]:
    '''Converts the list of variable-to-type bindings (such as those found in \\exists)
    to the internal representations.
    '''
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


def can_tree_be_reduced_to_aritmetic_expr(tree) -> bool:
    '''Checks that the given `tree` contains only valid function symbols for an
    aritmetic expression. A valid aritmetic expression is also considered to be
    an expression that contains ITE that expands itself also to an aritmetic expr.'''
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
    check between a boolean variable and a `let` bound expression.
    '''

    def is_literal_from_let_or_boolean_var(literal_var: str) -> bool:
        if ctx.get_let_binding_value(literal_var) is not None:
            return True

        maybe_left_var_info = ctx.lookup_variable(literal_var)
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

        if maybe_left_literal_var is None or maybe_right_literal_var is None:
            return True

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

    if not isinstance(tree, list):
        if isinstance(tree, Relation):
            # Register all the variables located in the Presburger formula
            variables_used: Set[Tuple[str, int, VariableType]] = set()
            for variable_name in tree.variable_names:
                var_info = ctx.get_variable_info(variable_name)
                var_info.ussage_count += 1  # The variable was used somewhere
                variables_used.add((var_info.name, var_info.id, var_info.type))
            return variables_used
        # Dealing with a standalone string
        if ctx.get_let_binding_value(tree) is not None:
            return set()
        else:
            info = ctx.get_variable_info(tree)
            return set([(info.name, info.id, info.type)])

    root = tree[0]

    assert root not in ['<', '<=', '>=', '>', '='], 'Relations should get processed beforehand in a separate pass.'

    if root in ['exists']:
        # When we are entering the new context (\\exists) we can bound at max
        # only those variables that are bound by the \\exists, nothing more -
        # all other variables then belong to the enclosing scopes
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
    elif root in ['let']:
        # Let has the following structure:
        # (let (<variable_binding>+) <term>)
        ctx.new_let_binding_context()
        variables_inside_let_bindings: Set[Tuple[str, int, VariableType]] = set()
        for variable_binding in tree[1]:
            variable_name, variable_tree = variable_binding
            ctx.insert_let_binding(variable_name, NFA(LSBF_Alphabet({}, [], set()), AutomatonType.NFA))
            variables_inside_let_bindings = variables_inside_let_bindings.union(get_all_used_variables(variable_tree, ctx))
        term_vars = get_all_used_variables(tree[2], ctx)
        ctx.pop_binding_context()
        return term_vars.union(variables_inside_let_bindings)
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
    source = source.replace('(', ' ( ').replace(')', ' ) ').replace('|', ' | ')
    _tokens = source.split()

    inside_large_text = False
    large_text = ''
    tokens = []
    for token in _tokens:
        if token == '|':
            if inside_large_text:
                inside_large_text = False
                tokens.append(large_text)
                large_text = ''
            else:
                inside_large_text = True
        else:
            if inside_large_text:
                large_text += token
            else:
                tokens.append(token)
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


def replace_modulo_operators_in_expr(ast, already_replaced: List[int] = [0]) -> List[AST_NaryNode]:
    '''
    Recursively traverse given AST down to the leaves. Upon finding a modulo term, replace it with a new variable.
    The number of variables found so far is propagated via the `already_replaced` variable
    (it is a list to provide mutability).
    '''
    if type(ast) != list:
        return []
    node_name = ast[0]
    if node_name == 'mod':
        # (mod A B)  <<-->>  (- A (* Mod_Var B))
        assert ast[2].isdecimal(), 'The second operand in the `modulo` operator should be a constant!'

        B = ast[2]
        ast[0] = '-'
        ast[2] = ['*', f'Mod_Var_{already_replaced[0]}', B]
        already_replaced[0] += 1
        return [ast[:]] + \
            replace_modulo_operators_in_expr(ast[1], already_replaced) + \
            replace_modulo_operators_in_expr(ast[2], already_replaced)

    if node_name in ['*', '+', '-']:
        if node_name == '-' and len(ast) == 2:
            return replace_modulo_operators_in_expr(ast[1], already_replaced)

        return replace_modulo_operators_in_expr(ast[1], already_replaced) + replace_modulo_operators_in_expr(ast[2], already_replaced)
    return []


def replace_modulo_with_exists_handler(ast: AST_NaryNode, is_reeval: bool, ctx: Dict) -> NodeEncounteredHandlerStatus:
    '''Transform AST handler - traverse the given AST, count all modulos and create equivalent existential formula.

    Traverses the given AST in a recursive fashion looking for the occurrences of the modulo term. Upon finding such
    modulo terms the algorithm immediately replaces them with a multiplication with a new variable representing
    the modulo term. The original formula is put in conjunction with other formulas that put forward limits on how
    big can the variable representing modulo be.
    '''

    # Detect the special form of equality relation ((a.x + b.y .... mod P) = c) that can be converted
    # directly to an NFA
    if ast[0] == '=':
        lhs, rhs = ast[1], ast[2]
        if type(lhs) == int:
            lhs, rhs = rhs, lhs  # Swap equation sides so we don't have to check for the specific structure twice

        can_convert_modulo_relation_directly = (type(rhs) == int and type(lhs) == list and lhs[0] == 'mod')
        if can_convert_modulo_relation_directly:
            return
    modulo_exprs = replace_modulo_operators_in_expr(ast[1]) + replace_modulo_operators_in_expr(ast[2])
    modulo_count = len(modulo_exprs)
    if modulo_count > 0:
        # Perform the exist expansion:
        # (= (mod A B) C)   <<-->>   (exists ((M Int)) (= (- A (* B M) C)
        exists_binding_list = [[f'Mod_Var_{i}', 'Int'] for i in range(modulo_count)]
        expanded_relation = ast[:]

        reminders_greater_than_zero = [['<=', 0, mod_expr] for mod_expr in modulo_exprs]
        reminders_smaller_than_constant = [['<=', mod_expr, str(int(mod_expr[2][2]) - 1)] for mod_expr in modulo_exprs]

        ast[0] = 'exists'
        ast[1] = exists_binding_list
        ast[2] = ['and',
                  expanded_relation,
                  *reminders_greater_than_zero,
                  *reminders_smaller_than_constant
                  ]

        ctx['modulos_replaced_cnt'] += modulo_count

        return NodeEncounteredHandlerStatus(True, False)
    return NodeEncounteredHandlerStatus(False, False)


def expand_ite_expressions_inside_presburger_relation(relation_root: AST_NaryNode,
                                                      is_reeval: bool,
                                                      ctx: Dict) -> NodeEncounteredHandlerStatus:
    from ast_relations import evaluate_ite_for_var_assignment
    ite_control_variables = collect_ite_control_variables(relation_root)

    if not ite_control_variables:
        # There are no control variables, no modification to the AST needs to be performed.
        return NodeEncounteredHandlerStatus(False, False)

    # Generate the expanded ite-expression
    expanded_expr = ['or']
    for i in range(2**len(ite_control_variables)):
        control_variables_bit_values = number_to_bit_tuple(i, len(ite_control_variables))
        # Convert the bit values into corresponing formulas:
        # (A=0, B=0, C=1) --> ~A, ~B, C
        variable_literals = [variable if variable_bit else ['not', variable] for variable, variable_bit in zip(ite_control_variables, control_variables_bit_values)]

        variable_truth_assignment = dict(zip(ite_control_variables, map(bool, control_variables_bit_values)))

        conjuction = ['and', *variable_literals, evaluate_ite_for_var_assignment(relation_root, variable_truth_assignment)]
        expanded_expr.append(conjuction)

    # replace the contents of `relation_root` with the results.
    relation_root.pop(-1)
    relation_root.pop(-1)
    relation_root.pop(-1)

    for node in expanded_expr:
        relation_root.append(node)

    ctx['ite_expansions_cnt'] += len(ite_control_variables)

    return NodeEncounteredHandlerStatus(True, False)


def express_modulo_terms_with_modvars(relation, first_modvar_index: int = 0) -> List[Union[str,Relation]]:
    """
    Replace modulo terms with existencial variables.

    Convert the given relation containing modulo terms to an equivalent relation in which the modulos are expressed
    using the existencially quantified variables (modvars). The returned list further contains new relations that
    limit the reminders size.

    Example:
        x + (y mod 3) = 0   ---->   (x + z = 0) and (y - z ~ 0 (mod 3) and (0 <= z) and (z <= 2)

    :param int first_modvar_index: The (suffix) index to start number the used modvars from (Mod_Var_{first_modvar_index})
    """

    modulo_variables = ['Mod_Var_{0}'.format(i + first_modvar_index) for i in range(len(relation.modulo_terms))]
    modulo_terms, modulo_coeficients = relation.modulo_terms, relation.modulo_term_coeficients

    linear_var_to_coef_map = dict(zip(relation.variable_names, relation.variable_coeficients))
    reminder_size_limit_relations: List[Relation] = []

    # Edit the relation as if the modulo terms are expressed using the new modulo variables
    for modvar, coeficient, modulo_term in zip(modulo_variables, modulo_coeficients, modulo_terms):
        # Fold in the coeficient standing before the modulo term eg: 3*(x + y mod K)
        variable_coeficients = [coeficient * variable_coef for variable_coef in modulo_term.variable_coeficients]

        # Add the variables and their coeficients from reminders expressed via modulo variables
        # to the linear variables in the relation
        for variable_coef, variable_in_modulo in zip(variable_coeficients, modulo_term.variables):
            current_linear_variable_coef = linear_var_to_coef_map.get(variable_in_modulo, 0)
            new_linear_variable_coef = current_linear_variable_coef + variable_coef
            linear_var_to_coef_map[variable_in_modulo] = new_linear_variable_coef

        # Subtracted the modulo variable * overall modulo term coeficient
        modvar_coef = -1 * coeficient * modulo_term.modulo
        linear_var_to_coef_map[modvar] = modvar_coef

        # Move the multiplied constant to the other side of relation (rhs)
        relation.absolute_part -= coeficient * modulo_term.constant

        # FIXME(codeboy): This should be sorted so we keep the canoical form
        reminder_formulas_variable_names = list(modulo_term.variables) + [modvar]
        reminder_formulas_variable_coefs = variable_coeficients + [modvar_coef]
        reminder_greater_than_zero = Relation(
                variable_names=reminder_formulas_variable_names,
                # Multiply the whole relation by -1 so we have a.x >= 0 ---> -a.x <= 0
                variable_coeficients=[coef * -1 for coef in reminder_formulas_variable_coefs],
                modulo_terms=[],
                modulo_term_coeficients=[],
                absolute_part=0,
                operation='<=')

        reminder_smaller_than_modulo = Relation(
                variable_names=reminder_formulas_variable_names,
                variable_coeficients=reminder_formulas_variable_coefs,
                modulo_terms=[],
                modulo_term_coeficients=[],
                absolute_part=modulo_term.modulo - 1,
                operation='<=')

        reminder_size_limit_relations.append(reminder_greater_than_zero)
        reminder_size_limit_relations.append(reminder_smaller_than_modulo)

    # All modulos have been expressed with the new mod vars, reconstruct the relation
    variable_names, variable_coeficients = zip(*linear_var_to_coef_map.items())
    relation = Relation(variable_names=list(variable_names),
                        variable_coeficients=list(variable_coeficients),
                        modulo_terms=[], modulo_term_coeficients=[],
                        absolute_part=relation.absolute_part,
                        operation=relation.operation)
    relation.ensure_canoical_form_if_equation()

    return ['and', relation, ] + reminder_size_limit_relations


def perform_whole_evaluation_on_source_text(source_text: str,
                                            evaluation_config: EvaluationConfig,
                                            emit_introspect: IntrospectHandle = lambda nfa, op: None
                                            ) -> Tuple[NFA, Dict[str, str]]:
    '''
    Parses the given SMT2 source code and runs the evaluation procedure.

    If multiple `assert` statements are found in the AST then the AST is modified
    so it contains only one `assert` that is a logical conjunction of all other
    formulas in the other assert trees.

    :param source_text: The SMT2 source text encoding the problem.
    :param emit_introspect: Introspection handle. If given it will be called with every automaton
                            produced during the evaluation procedure (in the order they are created).
    :returns: A tuple of the form (NFA, Dict) where NFA is the result of the evaluation
              of assert tree, and Dict is the smt-info collected when parsing.
    '''

    tokens = lex(source_text)
    ast = build_syntax_tree(tokens)

    smt_info = get_smt_info(ast)
    asserts = get_asserts_from_ast(ast)

    assert len(asserts) > 0, 'Cannot perform evaluation without any asserts present in the SMT source.'

    logger.info(f'Extracted smt-info: {smt_info}')
    logger.info(f'Detected {len(asserts)} assert statements from the source text.')

    eval_ctx = EvaluationContext(EvaluationConfig(SolutionDomain.INTEGERS, BackendType.NAIVE))

    function_symbols = get_declared_function_symbols(ast)
    constant_symbols = list(filter(lambda function_symbol: function_symbol.arity == 0, function_symbols))
    for constant_symbol in constant_symbols:
        eval_ctx.add_global_variable(constant_symbol.name, var_type=constant_symbol.return_type)

    if len(asserts) > 1:
        # There are more than one asserts, the resulting formula is SAT only
        # when all of them are --> conjunction
        assert_conjunction = ['and']
        for _assert in asserts:
            assert_conjunction.append(_assert[1])  # Append the formulae in asserts

        assert_tree_to_evaluate = ['assert', assert_conjunction]
    else:
        assert_tree_to_evaluate = asserts[0]  # If there is just 1, do not transform AST

    # preprocess_assert_tree(assert_tree_to_evaluate)  # Preprocessing is performed in place
    preprocessing.preprocess_ast(assert_tree_to_evaluate)  # Preprocessing is performed in place

    assert_tree_to_evaluate = preprocessing.reduce_relation_asts_to_evaluable_leaves(assert_tree_to_evaluate)
    # We are interested only in the number of different variables found in the
    # assert tree
    get_all_used_variables(assert_tree_to_evaluate, eval_ctx)

    # Generate consequent IDs to which the variable names will be bound at
    # later stages
    variable_ids = list(range(1, eval_ctx.next_available_variable_id))
    logger.info(f'Identified {len(variable_ids)} different variables in the assertion tree. Creating the overall alphabet.')
    alphabet = LSBF_Alphabet.from_variable_ids(variable_ids)
    logger.info(f'The created overall alphabet: {alphabet}')

    eval_ctx = EvaluationContext(evaluation_config, emit_introspect, alphabet=alphabet)
    for constant_symbol in constant_symbols:
        eval_ctx.add_global_variable(constant_symbol.name, var_type=constant_symbol.return_type)

    logger.info(f'Proceeding to assert tree evaluation (backend={eval_ctx.execution_config.backend_type.name})')
    nfa = run_evaluation_procedure(assert_tree_to_evaluate[1], eval_ctx)  # Evaluate the formula in the assert tree

    return (nfa, smt_info)


def build_automaton_from_presburger_relation_ast(relation: Relation,
                                                 ctx: EvaluationContext,
                                                 depth: int) -> NFA:
    '''Converts the provided relation to an automaton that encodes it. To do so it employs the algorithms
    provied by the module `presburger_algorithms`.

    The provided evalaution context `ctx` should have already an overall alphabet attached to it.

    Note: The automaton for sharp inequation (<) is not being directly built. Instead is is build as
    an an intersection of a complement of an automaton for the same relation but equation and non-sharp
    inequality -> (and (not <REL>[< -> =]) <REL>[< -> <=]).
    '''
    building_handlers: Dict[SolutionDomain, Dict[str, Tuple[ParsingOperation, Callable]]] = {
        SolutionDomain.INTEGERS: {
            '<=': (ParsingOperation.BUILD_NFA_FROM_INEQ,
                   pa.build_nfa_from_linear_inequality),
            '=':  (ParsingOperation.BUILD_NFA_FROM_EQ,
                   pa.build_nfa_from_linear_equality)
        },
        SolutionDomain.NATURALS: {
            '<=': (ParsingOperation.BUILD_DFA_FROM_INEQ,
                   pa.build_dfa_from_inequality),
            '=':  (ParsingOperation.BUILD_DFA_FROM_EQ,
                   pa.build_dfa_from_sharp_inequality)
        }
    }

    automaton_constr = ctx.get_automaton_class_for_current_backend()

    logger.debug(f'Building an automaton for: {relation}')
    if relation.is_always_satisfied():
        assert ctx.alphabet, 'The context must have alphabet already created in the second stage of evaluation'
        logger.info(f'Encountered relation that is always true: {relation}, returning trivial accepting automaton.')
        return automaton_constr.trivial_accepting(ctx.alphabet)


    # We should never encounter the '<' inequality as we are always converting it to the <=
    assert relation.operation in ['<=', '=']
    operation, automaton_building_function = building_handlers[ctx.execution_config.solution_domain].get(relation.operation)

    if relation.is_conguence_equality():
        logger.debug(f'Given relation: {relation} is congruence equivalence. Reordering variables.')
        modulo_term = relation.modulo_terms[0]
        variable_id_pairs = sorted(ctx.get_multiple_variable_ids(modulo_term.variables),
                                   key=lambda pair: pair[1])
        var_names, var_coefs = utils.reorder_variables_according_to_ids(
                variable_id_pairs,
                (modulo_term.variables, modulo_term.variable_coeficients))

        modulo_term_ordered = ModuloTerm(variables=var_names,
                                         variable_coeficients=var_coefs,
                                         constant=modulo_term.constant,
                                         modulo=modulo_term.constant)

        logger.debug(f'Reordered modulo term from: {modulo_term} to {modulo_term_ordered}')
        nfa = pa.build_presburger_modulo_nfa(relation, variable_id_pairs, ctx.get_alphabet(), automaton_constr)
        ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.BUILD_NFA_FROM_CONGRUENCE)
        return nfa

    else:
        assert not relation.modulo_terms

        # The extracted relation contains the list of variables and their
        # coeficients in an arbitrary order - we need to make sure that the order
        # of variables will be by ascending IDs (MTBDD requirement)
        variable_id_pairs = sorted(ctx.get_multiple_variable_ids(relation.variable_names),
                                   key=lambda pair: pair[1])
        var_names, var_coefs = utils.reorder_variables_according_to_ids(
                variable_id_pairs,
                (relation.variable_names, relation.variable_coeficients))

        reordered_relation = Relation(variable_names=var_names,
                                      variable_coeficients=var_coefs,
                                      modulo_terms=[],
                                      modulo_term_coeficients=[],
                                      absolute_part=relation.absolute_part,
                                      operation=relation.operation)

        assert automaton_building_function
        nfa = automaton_building_function(relation, variable_id_pairs, ctx.get_alphabet(), automaton_constr)
        ctx.emit_evaluation_introspection_info(nfa, operation)

        emit_evaluation_progress_info(f' >> {operation.value}({relation}) (result size: {len(nfa.states)}, automaton_type={nfa.automaton_type})', depth)

    # Finalization - increment variable ussage counter and bind variable ID to a name in the alphabet (lazy binding)
    # as the variable IDs could not be determined beforehand.
    for var_name, var_id in variable_id_pairs:
        assert ctx.alphabet
        if var_id not in ctx.alphabet.variable_names:
            ctx.alphabet.bind_variable_name_to_id(var_name, var_id)
        else:
            assert ctx.alphabet.variable_names[var_id] == var_name

        var_info = ctx.lookup_variable(var_name)
        assert var_info
        var_info.ussage_count += 1

    return nfa


def build_automaton_for_boolean_variable(var_name: str,
                                         var_value: bool,
                                         ctx: EvaluationContext) -> NFA:
    logger.debug(f'Building an equivalent automaton for the bool variable {var_name}, with value {var_value}.')
    var_id = ctx.get_variable_id(var_name)
    return ctx.get_automaton_class_for_current_backend().for_bool_variable(ctx.get_alphabet(), var_id, var_value)


def evaluate_let_bindings(binding_list, ctx: EvaluationContext) -> Dict[str, NFA]:
    logger.debug(f'Evaluating binding list of size: {len(binding_list)}')
    binding: Dict[str, NFA] = {}
    for var_name, expr in binding_list:
        logger.debug(f'Building automaton for var {var_name} with expr: {expr}')
        nfa = run_evaluation_procedure(expr, ctx)  # Indirect recursion, here we go
        binding[var_name] = nfa

    return binding


def get_automaton_for_operand(operand_value: Union[str, List],
                              ctx: EvaluationContext,
                              _depth: int) -> NFA:
    '''Tries to convert the given SMT subtree to a corresponding NFA. This is used on various places throughout
    the codebase e.g. and/or evaluation as this function provides capabilities of differentiating between
    evaluation of a string (a SMT bool var, or some `let` bound substitution) and a situation when there is
    really a real subtree.'''
    if type(operand_value) == str:
        # If it is a string, then it should reference a variable
        # previously bound to a value, or a bool variable which can be
        # converted to Automaton directly
        logger.debug('Found a usage of a bound variable in evaluated node.')

        is_bool_var = False
        variable_info = ctx.lookup_variable(str(operand_value))
        if variable_info is not None:
            if variable_info.type == VariableType.BOOL:
                is_bool_var = True

        if is_bool_var:
            logger.debug(f'The reached variable {operand_value} was queried as a boolean variable.')
            # We build an automaton for `var_name` with True value. Should
            # the boolean be considered False, it would be encoded
            # ['not', 'var_name'], which is equivalent to the complement of the
            # automaton.
            variable_info.ussage_count += 1
            return build_automaton_for_boolean_variable(str(operand_value), True, ctx)
        else:
            logger.debug(f'The variable {operand_value} is not boolean, searching `let` bindings.')

        nfa = ctx.get_let_binding_value(str(operand_value))
        if nfa is None:
            logger.fatal(f'A referenced variable: `{operand_value}` was not found in any of the binding contexts, is SMT2 file malformed?.')
            logger.debug(f'Bound variables: `{ctx.binding_stack}`')
            raise ValueError(f'A variable `{operand_value}` referenced inside AND could not be queried for its NFA.')
        else:
            logger.debug(f'Value query for variable `{operand_value}` OK.')
        return nfa
    else:
        # The node must be evaluated first
        nfa = run_evaluation_procedure(operand_value,
                                       ctx,
                                       _debug_recursion_depth=_depth+1)

        return nfa


def evaluate_binary_conjunction_expr(expr: List,
                                     ctx: EvaluationContext,
                                     reduction_fn: Callable[[NFA, NFA], NFA],
                                     reduction_operation: ParsingOperation,
                                     _depth: int) -> NFA:
    '''Perform the evaluation of AND and OR expressions in an abstract fashion using the provided
    reduction function (used to fold the operands into a result).'''
    assert type(expr) == list and len(expr) >= 3
    first_operand = expr[1]

    reduction_result = get_automaton_for_operand(first_operand, ctx, _depth)

    for next_operand in expr[2:]:
        next_operand_automaton = get_automaton_for_operand(next_operand, ctx, _depth)

        ctx.stats_operation_starts(reduction_operation, reduction_result, next_operand_automaton)
        reduction_result = reduction_fn(reduction_result, next_operand_automaton)
        ctx.stats_operation_ends(reduction_result)

        emit_evaluation_progress_info(f' >> {reduction_operation}(lhs, rhs) (result size: {len(reduction_result.states)}, automaton_type={reduction_result.automaton_type})', _depth)
        ctx.emit_evaluation_introspection_info(reduction_result, reduction_operation)

    return reduction_result


def evaluate_and_expr(and_expr: List,
                      ctx: EvaluationContext,
                      _depth: int) -> NFA:
    '''Evaluates the given AND SMT expression and returns the resulting NFA.'''

    result = evaluate_binary_conjunction_expr(
        and_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.intersection(nfa2),
        ParsingOperation.NFA_INTERSECT,
        _depth
    )

    return result


def evaluate_or_expr(or_expr: List,
                     ctx: EvaluationContext,
                     _depth: int) -> NFA:
    '''Evaluates the given OR SMT expression and returns the resulting NFA.'''

    return evaluate_binary_conjunction_expr(
        or_expr,
        ctx,
        lambda nfa1, nfa2: nfa1.union(nfa2),
        ParsingOperation.NFA_UNION,
        _depth
    )


def evaluate_not_expr(not_expr: List,
                      ctx: EvaluationContext,
                      _depth: int) -> NFA:
    '''Evaluates the given NOT SMT expression and returns the resulting NFA.'''

    assert len(not_expr) == 2
    operand = get_automaton_for_operand(not_expr[1], ctx, _depth)

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
        emit_evaluation_progress_info(f' >> determinize into DFA (result size: {len(operand.states)})', _depth)

    # TODO(psyco): Here we should check, whether the automaton is Complete
    # (Determinism is not enough)

    ctx.stats_operation_starts(ParsingOperation.NFA_COMPLEMENT, operand, None)
    operand = operand.complement()
    ctx.stats_operation_ends(operand)

    emit_evaluation_progress_info(f' >> complement(operand) - (result size: {len(operand.states)})', _depth)

    ctx.emit_evaluation_introspection_info(operand, ParsingOperation.NFA_COMPLEMENT)
    return operand


def evaluate_exists_expr(exists_expr: List,
                         ctx: EvaluationContext,
                         _depth: int) -> NFA:
    '''Evaluates the given EXISTS SMT expression and returns the resulting NFA.'''
    assert len(exists_expr) == 3

    # We are entering a new variable frame (only exists can bind variables to
    # types / manipulate FREE/BOUND sets)
    ctx.push_new_variable_info_frame()
    variable_bindings: Dict[str, VariableType] = parse_variable_bindings_list_to_internal_repr(exists_expr[1])
    logger.debug(f'Exists - Extracted variable type bindings for {variable_bindings.keys()}')
    ctx.add_multiple_variables_to_current_frame(variable_bindings)

    nfa = get_automaton_for_operand(exists_expr[2], ctx, _depth)

    vars_info = ctx.get_variables_info_for_current_frame()

    # We need to establish an order of individual projections applied, so that
    # we can tell when we are applying the last projection - after which we
    # will apply only one padding closure instead of after every projection
    projected_var_ids: List[int] = list()
    for var_name in variable_bindings:
        current_var_info = vars_info[var_name]
        if current_var_info.ussage_count == 0:
            logger.info(f'Skipping projecting away a variable "{var_name}" - the variable is not used anywhere in the tree underneath.')
            logger.debug(f'{exists_expr}')
        else:
            projected_var_ids.append(current_var_info.id)

    if not projected_var_ids:
        # No projection will occur
        return nfa

    logger.debug(f'Established projection order: {projected_var_ids}')

    last_var_id: int = projected_var_ids[-1]

    for var_id in projected_var_ids:
        ctx.stats_operation_starts(ParsingOperation.NFA_PROJECTION, nfa, None)

        # Do not skip only after the last projection
        skip_pad_closure = False if var_id == last_var_id else True
        projection_result = nfa.do_projection(var_id, skip_pad_closure=skip_pad_closure)
        assert projection_result
        nfa = projection_result
        ctx.stats_operation_ends(nfa)

        ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.NFA_PROJECTION)

    emit_evaluation_progress_info(f' >> projection({variable_bindings}) (result_size: {len(nfa.states)})', _depth)

    ctx.pop_variable_frame()
    return nfa


def evaluate_let_expr(let_expr: List,
                      ctx: EvaluationContext,
                      _depth: int) -> NFA:
    '''Evaluates the given let expression and returns the resulting automaton.

    The let expression itself does not perform no mutation on the tree underneath,
    however it introduces lexical bindings (variable to NFA).
    '''
    # `let` has this structure [`let`, `<binding_list>`, <term>]

    assert len(let_expr) == 3
    binding_list = let_expr[1]
    expr_using_let_bindings = let_expr[2]

    ctx.new_let_binding_context()

    # The variables in bindings can be evaluated to their automatons.
    bindings = evaluate_let_bindings(binding_list, ctx)
    logger.debug(f'Extracted bindings {bindings.keys()}')

    ctx.insert_all_bindings_into_current_context(bindings)

    # The we evaluate the term, in fact represents the value of the
    # whole `let` block
    term_nfa = run_evaluation_procedure(expr_using_let_bindings, ctx, _depth + 1)

    ctx.pop_binding_context()
    return term_nfa


def run_evaluation_procedure(root,  # NOQA
                  ctx: EvaluationContext,
                  _debug_recursion_depth=0,
                  ) -> NFA:
    '''Evaluates the SMT given SMT tree and returns the resulting NFA.'''

    if not type(root) == list:
        # This means that either we hit a SMT2 term (boolean variable) or
        # the tree is malformed, and therefore we cannot continue.

        # TODO(codeboy): Here we should handle atoms -> like the processed relations.
        if isinstance(root, Relation):
            return build_automaton_from_presburger_relation_ast(root, ctx, _debug_recursion_depth)

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
            return build_automaton_for_boolean_variable(root, True, ctx)
        else:
            nfa = ctx.get_let_binding_value(root)
            if nfa is None:
                raise ValueError(f'Unknown SMT2 expression: {root}.')
            else:
                return nfa

    node_name = root[0]
    if node_name in ['<', '>', '<=', '>=', '=']:
        # We have found a node which needs to be (directly) translated into NFA
        # @Problem: This implementation does not distinguish between
        # SMT equivalence of two boolean variables and presburger equation
        if node_name == '=' and not is_tree_presburger_equality(root, ctx):
            # Perform boolean equivalence expansion:
            # A = B  <<-->> (A & B) | (~A & ~B)
            logger.debug(f'Encountered boolean equivalence expression: {root} ')
            b = root.pop(-1)
            a = root.pop(-1)
            root[0] = 'or'
            root.append(['and', a, b])
            root.append(['and', ['not', a], ['not', b]])

            # remove_multiple_negations(root)

            logger.debug(f'Expression expanded into: {root}')

            return run_evaluation_procedure(root, ctx, _debug_recursion_depth)

        logger.info('Reached relation root, performing ITE expansion...')

        expanded_tree = expand_relation_on_ite(root)

        # If the relation was indeed expanded, the root will be 'or'
        if expanded_tree[0] == 'or':
            assert False, 'The ITE expansion should be done in preprocessing.'
            return run_evaluation_procedure(expanded_tree, ctx, _debug_recursion_depth)
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
        emit_evaluation_progress_info(f'eval_smt_tree({root}), node_name={node_name}', _debug_recursion_depth)
        # Current node is a NFA operation
        evaluation_functions = {
            'and': evaluate_and_expr,
            'or': evaluate_or_expr,
            'not': evaluate_not_expr,
            'exists': evaluate_exists_expr,
            'let': evaluate_let_expr,
        }

        if node_name not in evaluation_functions:
            raise NotImplementedError(f'Error while evaluating tree, unknown operation: {node_name}')

        evaluation_function = evaluation_functions[node_name]
        return evaluation_function(root, ctx, _debug_recursion_depth)


def expand_multivariable_bindings(assertion_tree):
    '''Preprocessing operation. In place expansion of multivariable \\exists and \\forall quantifiers to many
    single variable quantifiers.'''
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


def get_sat_value_from_smt_info(smt_info: Dict[str, str], default: Optional[bool] = True) -> Optional[bool]:
    '''
    Parse the information collected from the smt-info blocks for the expected SAT value.

    :param smt_info: A dictionary containing the parsed information from smt-info statements
    :param default:  If the SAT information is not present, the default (fallback) value is used.
    :returns:        True if the expected value is SAT, False if unsat or default if not present.
    '''
    if ':status' in smt_info:
        return smt_info[':status'] == 'sat'
    else:
        return default


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
