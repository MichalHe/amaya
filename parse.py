import pressburger_algorithms as pa
from ast_relations import extract_relation, expand_relation_on_ite
from automatons import NFA, AutomatonType
from log import logger
from logging import INFO
from typing import (
    List,
    Tuple,
    Any,
    Dict,
    Callable,
    Optional
)
from enum import IntEnum, Enum

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)


class SolutionDomain(IntEnum):
    NATURALS = 0
    INTEGERS = 1


class ParsingOperation(Enum):
    BUILD_NFA_FROM_INEQ = 'build_nfa_from_ineq'
    BUILD_NFA_FROM_SHARP_INEQ = 'build_nfa_from_sharp_ineq'
    BUILD_NFA_FROM_EQ = 'build_nfa_from_eq'
    NFA_UNION = 'union'
    NFA_PROJECTION = 'projection'
    NFA_COMPLEMENT = 'complement'
    NFA_DETERMINIZE = 'determinize'
    NFA_INTERSECT = 'intersection'
    BUILD_DFA_FROM_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_SHARP_INEQ = 'build_dfa_from_ineq'
    BUILD_DFA_FROM_EQ = 'build_dfa_from_ineq'


class VariableType(IntEnum):
    Int = 0x01
    Bool = 0x02


class EvaluationContext():
    def __init__(self,
                 domain: SolutionDomain,
                 emit_introspect=lambda nfa, operation: None,
                 ):
        self.binding_stack: List[Dict[str, NFA]] = dict()
        self.domain = domain
        self.introspect_handle = emit_introspect

    def get_binding(self, var_name: str) -> Optional[NFA]:
        for binding_record in reversed(self.binding_stack):
            if var_name in binding_record:
                return binding_record[var_name]
        return None

    def new_binding_context(self):
        self.binding_stack.append(dict())

    def insert_binding(self, var_name: str, nfa: NFA):
        self.binding_stack[-1][var_name] = nfa

    def pop_binding_context(self):
        self.binding_stack.pop(-1)

    def emit_evaluation_introspection_info(self, nfa: NFA, operation: ParsingOperation):
        self.introspect_handle(nfa, operation)


IntrospectHandle = Callable[[NFA, ParsingOperation], None]


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
            var_type = VariableType.Int
        elif var_type_raw == 'Bool':
            var_type = VariableType.Bool
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


def check_result_matches(source_text: str, emit_introspect=lambda nfa, op: None) -> bool:
    tokens = lex(source_text)
    ast = build_syntax_tree(tokens)

    smt_info = get_smt_info(ast)
    asserts = get_asserts_from_ast(ast)
    logger.info(f'Extracted smt-info: {smt_info}')
    logger.info(f'Extracted {len(asserts)} from source text.')

    eval_ctx = EvaluationContext(SolutionDomain.INTEGERS, emit_introspect)
    nfa = eval_assert_tree(asserts[0], eval_ctx)

    should_be_sat = True  # Assume true, in case there is no info in the smt source
    if ':status' in smt_info:
        if smt_info[':status'] == 'unsat':
            should_be_sat = False

    is_sat, example_word = nfa.is_sat()
    sat_matches = is_sat == should_be_sat

    if sat_matches:
        if is_sat:
            logger.debug(f'The automaton\'s SAT is as expected: {is_sat}, example: {example_word}')
        else:
            logger.debug(f'The automaton\'s SAT is as expected: {is_sat}')
    else:
        logger.warn(f'The automaton\'s SAT didn\'t match expected: actual={is_sat}, given word: {example_word}, expected={should_be_sat}')

    return sat_matches


def build_automaton_from_pressburger_relation_ast(relation_root,
                                                  variable_types: Dict[str, VariableType],
                                                  emit_introspect: IntrospectHandle,
                                                  domain: SolutionDomain,
                                                  depth: int) -> NFA:
    building_handlers = {
        SolutionDomain.INTEGERS: {
            '<':  (ParsingOperation.BUILD_NFA_FROM_SHARP_INEQ, pa.build_nfa_from_sharp_inequality),
            '<=': (ParsingOperation.BUILD_NFA_FROM_INEQ, pa.build_nfa_from_inequality),
            '=':  (ParsingOperation.BUILD_NFA_FROM_EQ, pa.build_nfa_from_equality)
        },
        SolutionDomain.NATURALS: {
            '<':  (ParsingOperation.BUILD_DFA_FROM_SHARP_INEQ, pa.build_dfa_from_sharp_inequality),
            '<=': (ParsingOperation.BUILD_DFA_FROM_INEQ, pa.build_dfa_from_inequality),
            '=':  (ParsingOperation.BUILD_DFA_FROM_EQ, pa.build_dfa_from_sharp_inequality)
        }
    }

    relation = extract_relation(relation_root)
    operation, handle = building_handlers[domain][relation.operation]

    if relation.operation == '<':
        eq = pa.build_nfa_from_equality(relation)
        emit_introspect(eq, ParsingOperation.BUILD_NFA_FROM_EQ)
        neq = eq.determinize().complement()
        ineq = pa.build_nfa_from_inequality(relation)
        emit_introspect(ineq, ParsingOperation.BUILD_DFA_FROM_INEQ)
        automaton = neq.intersection(ineq)
        emit_introspect(automaton, ParsingOperation.NFA_INTERSECT)
    else:
        automaton = handle(relation)
        emit_introspect(automaton, operation)
    _eval_info(f' >> {operation.value}({relation_root}) (result size: {len(automaton.states)})', depth)

    return automaton


def build_automaton_for_boolean_variable(var_name: str, var_value: bool) -> NFA:
    logger.debug(f'Building an equivalent automaton for the bool variable {var_name}, with value {var_value}.')
    return NFA.for_bool_variable(var_name, var_value)


def evaluate_bindings(binding_list) -> Dict[str, NFA]:
    logger.debug(f'Evaluating binding list of size: {len(binding_list)}')
    binding: Dict[str, NFA] = {}
    for var_name, expr in binding_list:
        logger.debug(f'Building automaton for var {var_name} with expr: {expr}')
        nfa = eval_smt_tree(expr)  # Indirect recursion, here we go
        binding[var_name] = nfa

    return binding


def eval_smt_tree(root,  # NOQA -- function is too complex -- its a parser, so?
                  ctx: EvaluationContext,
                  variable_types: Dict[str, VariableType] = dict(),
                  _debug_recursion_depth=0,
                  ) -> NFA:

    if not type(root) == list:
        # This means that either we hit a SMT2 term (boolean variable) or
        # the tree is malformed, and therefore we cannot continue.

        # Is the term a bool variable?
        is_bool_var = False
        if root in variable_types:
            if variable_types[root] == VariableType.Bool:
                is_bool_var = True

        if is_bool_var:
            logger.debug('Reached a SMT2 term {0}, which was queried as a boolean variable.'.format(root))
            # We build an automaton for `var_name` with True value. Should
            # the boolean be considered False, it would be encoded
            # ['not', 'var_name'], which is equivalent to the complement of the
            # automaton.
            return build_automaton_for_boolean_variable(root, True)
        else:
            raise ValueError(f'Unknown SMT2 term: {root}.')

    node_name = root[0]
    if node_name in ['<', '>', '<=', '>=', '=']:
        # We have found node which needs to be translated into NFA
        logger.info('Reached relation root, performing ITE expansion...')

        expanded_tree = expand_relation_on_ite(root)

        # If the relation was indeed expanded, the root will be 'or'
        if expanded_tree[0] == 'or':
            return eval_smt_tree(expanded_tree, ctx, variable_types, _debug_recursion_depth)
        else:
            # The relation was no expanded
            # (maybe a second evaluation pass, after the first expansion)
            return build_automaton_from_pressburger_relation_ast(root,
                                                                 variable_types,
                                                                 ctx.introspect_handle,
                                                                 ctx.domain,
                                                                 _debug_recursion_depth)
    else:
        _eval_info(f'eval_smt_tree({root})', _debug_recursion_depth)
        # Current node is NFA operation
        if node_name == 'and':
            assert len(root) >= 3
            lhs_term = root[1]
            lhs = eval_smt_tree(lhs_term,
                                ctx,
                                variable_types=variable_types,
                                _debug_recursion_depth=_debug_recursion_depth+1)

            for term_i in range(2, len(root)):
                rhs_term = root[term_i]
                rhs = eval_smt_tree(rhs_term,
                                    ctx,
                                    variable_types=variable_types,
                                    _debug_recursion_depth=_debug_recursion_depth+1)

                assert type(rhs) == NFA
                lhs = lhs.intersection(rhs)
                _eval_info(f' >> intersection(lhs, rhs) (result size: {len(lhs.states)})', _debug_recursion_depth)
                ctx.emit_evaluation_introspection_info(lhs, ParsingOperation.NFA_INTERSECT)
            return lhs
        elif node_name == 'or':
            assert len(root) >= 3
            lhs_term = root[1]
            lhs = eval_smt_tree(lhs_term,
                                ctx,
                                variable_types=variable_types,
                                _debug_recursion_depth=_debug_recursion_depth+1)

            for term_i in range(2, len(root)):
                rhs_term = root[2]
                rhs = eval_smt_tree(rhs_term,
                                    ctx,
                                    variable_types=variable_types,
                                    _debug_recursion_depth=_debug_recursion_depth+1)

                assert type(rhs) == NFA

                _eval_info(' >> union(lhs, rhs)', _debug_recursion_depth)
                lhs = lhs.union(rhs)
                ctx.emit_evaluation_introspection_info(lhs, ParsingOperation.NFA_UNION)
            return lhs
        elif node_name == 'not':
            assert len(root) == 2
            operand = eval_smt_tree(root[1],
                                    ctx,
                                    variable_types=variable_types,
                                    _debug_recursion_depth=_debug_recursion_depth+1)

            assert type(operand) == NFA

            if operand.automaton_type == AutomatonType.NFA:
                operand = operand.determinize()
                _eval_info(f' >> determinize into DFA (result size: {len(operand.states)})', _debug_recursion_depth)
            operand = operand.complement()
            _eval_info(f' >> complement(operand) - (result size: {len(operand.states)})', _debug_recursion_depth)
            ctx.emit_evaluation_introspection_info(operand, ParsingOperation.NFA_COMPLEMENT)
            return operand
        elif node_name == 'exists':
            assert len(root) == 3

            variable_bindings: Dict[str, VariableType] = get_variable_binding_info(root[1])

            # Maybe some variable information was already passed down to us -
            # in that case we want to merge the two dictionaries together
            if len(variable_types) > 0:
                variable_bindings.update(variable_types)

            nfa = eval_smt_tree(root[2],
                                ctx,
                                variable_types=variable_bindings,
                                _debug_recursion_depth=_debug_recursion_depth+1)

            # TODO: Check whether variables are in fact present in the alphabet
            for var_name in variable_bindings:
                nfa = nfa.do_projection(var_name)
                ctx.emit_evaluation_introspection_info(nfa, ParsingOperation.NFA_PROJECTION)

            _eval_info(f' >> projection({variable_bindings}) (result_size: {len(nfa.states)})', _debug_recursion_depth)
            return nfa

        elif node_name == 'let':
            binding_list = root[1]
            bindings = evaluate_bindings(binding_list)
            return bindings
        else:
            raise NotImplementedError(f'Error while evaluating tree, unknown operation: {node_name}, assert_tree')


def eval_assert_tree(assert_tree, ctx: EvaluationContext):
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
