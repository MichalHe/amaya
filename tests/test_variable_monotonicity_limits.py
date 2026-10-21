"""
Tests for the variable limits recorded by `amaya.preprocessing.unbound_vars._determine_monotonicity_of_variables`
(through `_set_limit_on_interestring_var_if_bound`), which `optimize_bottom_quantifiers` uses to
instantiate a quantified variable with a known value or to detect a conflict.
"""
import pytest

import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.relations_structures import AST_Connective, AST_Quantifier, BoolLiteral, Connective_Type, Relation, Var


X, Y = Var(id=1), Var(id=2)


def _exists_y(*conjuncts) -> AST_Quantifier:
    quantifier = AST_Quantifier(referenced_vars=(), bound_vars=(Y,),
                                child=AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=conjuncts))
    fill_referenced_vars(quantifier)
    return quantifier


def _limits_of_y(formula):
    monotonicity = var_bounds_lib.Monotonicity_Info()
    var_bounds_lib._determine_monotonicity_of_variables(formula, monotonicity, is_positive=True)
    limits = monotonicity.seen_vars[Y].limits
    return limits.lower_limit, limits.upper_limit


@pytest.mark.parametrize('coef, rhs, expected_limits', [
    (7, 1, (1, 0)),       # no integer solution: empty interval; was recorded as the known value 0
    (-3, 1, (0, -1)),     # no integer solution; was recorded as the known value -1
    (7, 14, (2, 2)),
    (-3, 6, (-2, -2)),
])
def test_single_value_equation(coef, rhs, expected_limits):
    formula = _exists_y(Relation(vars=[Y], coefs=[coef], rhs=rhs, predicate_symbol='='),
                        Relation(vars=[X, Y], coefs=[1, -1], rhs=0, predicate_symbol='<='))
    assert _limits_of_y(formula) == expected_limits


def test_equation_without_integer_solution_makes_the_bottom_quantifier_false():
    formula = _exists_y(Relation(vars=[Y], coefs=[7], rhs=1, predicate_symbol='='),
                        Relation(vars=[X, Y], coefs=[1, -1], rhs=0, predicate_symbol='<='))
    assert var_bounds_lib.optimize_bottom_quantifiers(formula) == BoolLiteral(False)


@pytest.mark.parametrize('coef, rhs, expected_limits', [
    (3, 3 * 2**60 - 1, (None, 2**60 - 1)),        # float division rounds the quotient up to 2**60
    (-3, -(3 * 2**60 + 1), (2**60 + 1, None)),    # float division rounds the quotient down to 2**60
    (2, -3, (None, -2)),
    (-2, 3, (-1, None)),
])
def test_hard_bound_uses_exact_integer_division(coef, rhs, expected_limits):
    formula = _exists_y(Relation(vars=[Y], coefs=[coef], rhs=rhs, predicate_symbol='<='),
                        Relation(vars=[X, Y], coefs=[1, -1], rhs=0, predicate_symbol='<='))
    assert _limits_of_y(formula) == expected_limits
