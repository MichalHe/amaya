from inequations import (
    build_nfa_from_inequality,
    extract_inquality
)

from automatons import NFA
from log import logger
from logging import INFO
from typing import (
    List,
    Tuple,
    Any
)

PRETTY_PRINT_INDENT = ' ' * 2

logger.setLevel(INFO)


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


def get_variable_names_from_bindings(bindings: List[Tuple[str, str]]) -> List[str]:
    return list(map(lambda binding: binding[0], bindings))


def lex(source: str) -> List[str]:
    source = source.replace('(', '( ').replace(')', ' )')
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


def filter_asserts(ast):
    # TODO: Remove this
    _asserts = []
    for top_level_expr in ast:
        if top_level_expr[0] == 'assert':
            _asserts.append(top_level_expr)
    return _asserts


def eval_smt_tree(root, _debug_recursion_depth=0) -> NFA:
    # ['assert'
    #     ['not'
    #         ['exists,
    #             ['and',
    #                 [INEQ1]
    #                 [INEQ2]
    #              ]]]]
    node_name = root[0]
    if node_name in ['<', '>', '<=', '>=']:
        # We have found node which need to be translated into NFA
        _eval_info(f' >> build_nfa_from_inequality({root})', _debug_recursion_depth)

        inequality = extract_inquality(root)
        nfa = build_nfa_from_inequality(inequality)

        return nfa
    else:
        _eval_info(f'eval_smt_tree({root})', _debug_recursion_depth)
        # Current node is NFA operation
        if node_name == 'and':
            assert len(root) == 3
            lhs_term = root[1]
            rhs_term = root[2]
            lhs = eval_smt_tree(lhs_term, _debug_recursion_depth+1)
            rhs = eval_smt_tree(rhs_term, _debug_recursion_depth+1)

            assert type(lhs) == NFA
            assert type(rhs) == NFA

            _eval_info(' >> intersection(lhs, rhs)', _debug_recursion_depth)
            return lhs.intersection(rhs)
        elif node_name == 'or':
            lhs_term = root[1]
            rhs_term = root[2]
            lhs = eval_smt_tree(lhs_term, _debug_recursion_depth+1)
            rhs = eval_smt_tree(rhs_term, _debug_recursion_depth+1)

            assert type(lhs) == NFA
            assert type(rhs) == NFA

            _eval_info(' >> union(lhs, rhs)', _debug_recursion_depth)
            return lhs.union(rhs)
        elif node_name == 'not':
            assert len(root) == 2
            operand = eval_smt_tree(root[1], _debug_recursion_depth+1)

            assert type(operand) == NFA

            _eval_info(' >> complement(operand)', _debug_recursion_depth)
            return operand.complement()
        elif node_name == 'exists':
            assert len(root) == 3
            variable_names = get_variable_names_from_bindings(root[1])
            nfa = eval_smt_tree(root[2], _debug_recursion_depth+1)

            # TODO: Check whether variables are in fact present in alphabet
            _eval_info(f' >> projection({variable_names})', _debug_recursion_depth)
            for var in variable_names:
                nfa = nfa.do_projection(var)

            return nfa

        else:
            raise NotImplementedError(f'Error while evaluating tree, unknown operation: {node_name}, assert_tree')


def eval_assert_tree(assert_tree):
    assert assert_tree[0] == 'assert'
    return eval_smt_tree(assert_tree[1])


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
    if assertion_tree[0] == 'forall':
        forall_kw, binders, stmt = assertion_tree

        not_stmt = ['not', stmt]
        exists = ['exists', binders, not_stmt]

        assertion_tree[0] = 'not'
        assertion_tree[1] = exists
        assertion_tree.pop(-1)

    if assertion_tree[0] in ['exists', 'not', 'forall', 'assert']:
        replace_forall_with_exists(assertion_tree[-1])


def remove_multiple_negations(assertion_tree):
    pass


def get_formula(_assert):
    return _assert[1]
