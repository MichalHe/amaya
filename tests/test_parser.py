import pytest
import parse
import re
import utils


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
