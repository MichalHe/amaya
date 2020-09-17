import pytest
import parse
import inequations
from utils import search_tree


@pytest.fixture
def inequality_tree():
    source_text = '''
    (set-info :category "industrial")
    (set-info :status unsat)
    (assert (not (exists ((?X Int)) (<= 2 ?X))))
    (check-sat)
    (exit)
    '''
    expr_tree = parse.build_syntax_tree(parse.lex(source_text))
    return search_tree(expr_tree, 'exists')[2]


@pytest.fixture
def sample_inequation(inequality_tree):
    return inequations.extract_inquality(inequality_tree)


def test_inequality_extraction(inequality_tree):
    # @TODO: Add more inequations to test agains
    ineq = inequations.extract_inquality(inequality_tree)

    print(ineq)
    assert ineq.variable_names
    assert ineq.absolute_part == -2

    coef_outside_allowed_range = list(filter(
        lambda coef: abs(coef) > 1,
        ineq.variable_coeficients))
    assert not coef_outside_allowed_range


def test_build_automaton_over_N(sample_inequation):
    assert inequations.build_dfa_from_inequality(sample_inequation)
