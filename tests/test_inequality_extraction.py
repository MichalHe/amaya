import pytest
import parse
import ast_relations
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
    return ast_relations.extract_inquality(inequality_tree)


@pytest.fixture
def inequation_source__valid_arithmetic_operations():
    source_text = '''
    (set-info :category "industrial")
    (set-info :status unsat)
    (assert
        (not
            (exists
                ((?X Int))
                (<=
                    (* (+ 2 (- 6 3)) 8)
                    (+ (* 3 (- ?X 10)) 12)
                )
            )
        )
    )
    (check-sat)
    (exit)
    '''
    return source_text


def test_inequality_extraction(inequality_tree):
    # @TODO: Add more inequations to test agains
    ineq = ast_relations.extract_relation(inequality_tree)
    assert ineq.operation == "<="

    print(ineq)
    assert ineq.variable_names
    assert ineq.absolute_part == -2

    coef_outside_allowed_range = list(filter(
        lambda coef: abs(coef) > 1,
        ineq.variable_coeficients))
    assert not coef_outside_allowed_range


def test_inequality_arithmetic_operations_evaluation(inequation_source__valid_arithmetic_operations):
    expr_tree = parse.build_syntax_tree(parse.lex(inequation_source__valid_arithmetic_operations))

    ineq = ast_relations.extract_relation(search_tree(expr_tree, 'exists')[2])
    assert ineq.operation == "<="

    assert ineq.absolute_part == -58
    assert len(ineq.variable_coeficients) == 1
    assert len(ineq.variable_names) == 1
    assert '?X' in ineq.variable_names
    assert ineq.variable_coeficients[0] == -3
    assert ineq.operation == '<='
