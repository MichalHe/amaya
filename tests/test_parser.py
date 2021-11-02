import pytest
import parse
import preprocessing
import re
import utils
from typing import List


@pytest.fixture
def smt_formula():
    source_text = '''
    (set-info :category "industrial")
    (set-info :status unsat)
    (assert (not (exists ((?X Int)) (<= 2 ?X))))
    (check-sat)
    (exit)
    '''
    return source_text


@pytest.fixture
def smt_lex_output(smt_formula):
    return parse.lex(smt_formula)


@pytest.fixture
def plain_tree_multivar_exits():
    return ['assert',
            ['not',
             ['exists',
              [['X', 'TypeX'], ['Y', 'TypeY'], ['Z', 'TypeZ']],
              ['FORMULA']]]]


@pytest.fixture
def plain_tree_multivar_forall():
    return ['assert',
            ['forall',
             [['X', 'TypeX'], ['Y', 'TypeY']],
             ['FORMULA']]]


@pytest.fixture
def plain_tree_multivar_mixed():
    return ['assert',
            ['forall',
             [['X', 'TypeX'], ['Y', 'TypeY']],
             ['exists',
              [['Z', 'TypeZ'], ['W', 'TypeW']],
              ['forall',
               [['Q', 'TypeQ']],
               ['FORMULA']]
              ]]]


def get_node_name_sequence(root, size: int) -> List[str]:
    node_names: List[int] = []

    for i in range(size):
        node_names.append(root[0])
        root = root[-1]
        assert type(root) == list

    return node_names


def test_lex(smt_formula):
    brackets_not_alone_regex = re.compile(r'(.+\))|(.+\()|(\(.+)|(\).+)')
    tokens = parse.lex(smt_formula)

    assert tokens
    for token in tokens:
        assert not brackets_not_alone_regex.match(token)


def test_parse(smt_lex_output):
    expr_tree = parse.build_syntax_tree(smt_lex_output)
    assert expr_tree

    assert_expr_subtree = None
    for expr in expr_tree:
        assert len(expr) > 0
        if expr[0] == 'assert':
            assert_expr_subtree = expr

    assert assert_expr_subtree
    assert len(assert_expr_subtree) > 1  # Assert tree should not be empty

    assert ['check-sat'] in expr_tree
    assert ['exit'] in expr_tree

    assert utils.tree_depth(assert_expr_subtree) > 2


def test_expand_multivariable_bindings_simple(plain_tree_multivar_exits,
                                              plain_tree_multivar_forall):
    parse.expand_multivariable_bindings(plain_tree_multivar_exits[1])
    assert(plain_tree_multivar_exits)

    exists_subtree_root = plain_tree_multivar_exits[1][1]

    for i in range(3):
        assert 'exists' == exists_subtree_root[0]
        assert len(exists_subtree_root[1]) == 1

        exists_subtree_root = exists_subtree_root[2]

    parse.expand_multivariable_bindings(plain_tree_multivar_forall[1])
    assert(plain_tree_multivar_forall)

    forall_tree_root = plain_tree_multivar_forall[1]
    for i in range(2):
        assert 'forall' == forall_tree_root[0]
        assert len(forall_tree_root[1]) == 1


def test_expand_multivariable_bindings_mixed(plain_tree_multivar_mixed):
    parse.expand_multivariable_bindings(plain_tree_multivar_mixed[1])
    assert(plain_tree_multivar_mixed)

    overall_bindings_count = 5
    bindings_tree_root = plain_tree_multivar_mixed[1]
    expected_binders_seq = ['forall', 'forall', 'exists', 'exists', 'forall']
    for i in range(overall_bindings_count):
        assert expected_binders_seq[i] == bindings_tree_root[0]
        assert len(bindings_tree_root[1]) == 1

        bindings_tree_root = bindings_tree_root[2]

    assert 'FORMULA' == bindings_tree_root[0]


def test_replace_forall_with_exists_simple(plain_tree_multivar_forall):
    preprocessing.replace_forall_with_exists(plain_tree_multivar_forall)
    assert(plain_tree_multivar_forall)

    node_names = get_node_name_sequence(plain_tree_multivar_forall[1], 3)
    assert ['not', 'exists', 'not'] == node_names


def test_replace_forall_with_exists_mixed(plain_tree_multivar_mixed):
    preprocessing.replace_forall_with_exists(plain_tree_multivar_mixed)
    assert plain_tree_multivar_mixed
    node_names = get_node_name_sequence(plain_tree_multivar_mixed, 8)
    expected_node_seq = ['assert', 'not', 'exists', 'not', 'exists', 'not', 'exists', 'not']

    assert expected_node_seq == node_names


def test_formula_cleanup(plain_tree_multivar_mixed):
    preprocessing.replace_forall_with_exists(plain_tree_multivar_mixed)
    parse.expand_multivariable_bindings(plain_tree_multivar_mixed)

    expected = ['not', 'exists', 'exists', 'not', 'exists', 'exists', 'not', 'exists', 'not']
    actual = get_node_name_sequence(plain_tree_multivar_mixed[1], len(expected))

    assert expected == actual
