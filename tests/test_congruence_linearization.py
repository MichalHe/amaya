"""
Tests for `amaya.preprocessing.unbound_vars.linearize_congruences`, which replaces a two-variable
congruence by a disjunction of linear equations (`_linearize_two_variable_congruence`) inside the box
its variables' bounds describe.

The rewrite is checked by brute force: with explicit bounds it must preserve the truth value of the
formula for every value of the free variable.
"""
import itertools

import pytest

import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.relations_structures import AST_Connective, AST_Quantifier, BoolLiteral, Congruence, Connective_Type, Relation, Var


X, Y = Var(id=1), Var(id=2)


def _evaluate(node, assignment) -> bool:
    if isinstance(node, BoolLiteral):
        return node.value
    if isinstance(node, (Relation, Congruence)):
        total = sum(coef * assignment[var] for coef, var in zip(node.coefs, node.vars))
        if isinstance(node, Congruence):
            return (total - node.rhs) % node.modulus == 0
        return total == node.rhs if node.predicate_symbol == '=' else total <= node.rhs
    if isinstance(node, AST_Quantifier):
        return any(_evaluate(node.child, {**assignment, **dict(zip(node.bound_vars, values))})
                   for values in itertools.product(range(-40, 41), repeat=len(node.bound_vars)))
    values = [_evaluate(child, assignment) for child in node.children]
    return all(values) if node.type == Connective_Type.AND else any(values)


def _le(pairs, rhs) -> Relation:
    return Relation(vars=[var for _, var in pairs], coefs=[coef for coef, _ in pairs], rhs=rhs, predicate_symbol='<=')


def _bounds(var, lower, upper):
    return (_le([(-1, var)], -lower), _le([(1, var)], upper))


def _assert_linearization_preserves_truth(formula, free_values):
    fill_referenced_vars(formula)
    result = var_bounds_lib.linearize_congruences(formula)
    assert result != formula, 'the congruence was not linearized, so the test does not exercise the rewrite'
    for value in free_values:
        assert _evaluate(formula, {X: value}) == _evaluate(result, {X: value}), f'x = {value}'


@pytest.mark.parametrize('x_bounds, y_bounds, coefs, rhs, modulus', [
    ((-3, 0), (0, 2), [1, 1], 0, 3),         # x = -1, y = 1 was rejected
    ((0, 3), (0, 2), [1, 1], 0, 3),
    ((1, 1), (0, 7), [1, 1], 0, 8),          # x + y = 0 (mod 8) with x = 1 required 7y = 1
    ((-3, 5), (0, 4), [2, 3], 1, 5),
    ((-83, -1), (1, 299908), [1, 299908], 0, 299909),
])
def test_linearization_with_explicit_bounds_preserves_the_formula(x_bounds, y_bounds, coefs, rhs, modulus):
    body = AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=(
        *_bounds(Y, *y_bounds), Congruence(vars=[X, Y], coefs=coefs, rhs=rhs, modulus=modulus)))
    formula = AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=(
        *_bounds(X, *x_bounds), AST_Quantifier(referenced_vars=(), bound_vars=(Y,), child=body)))
    _assert_linearization_preserves_truth(formula, free_values=range(x_bounds[0] - 2, min(x_bounds[1], x_bounds[0] + 20) + 3))


@pytest.mark.parametrize('coefs, rhs, modulus', [
    ([1, 2], 1, 4),     # coefficient of y not invertible, coefficient of x is: the roles are swapped
    ([2, 2], 2, 4),     # neither coefficient invertible
])
def test_non_invertible_coefficient_does_not_raise(coefs, rhs, modulus):
    """ `pow(y_coef, -1, modulus)` raised ValueError for a coefficient not coprime to the modulus. """
    formula = AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=(
        *_bounds(X, 0, 3), *_bounds(Y, 0, 3), Congruence(vars=[X, Y], coefs=coefs, rhs=rhs, modulus=modulus)))
    fill_referenced_vars(formula)
    result = var_bounds_lib.linearize_congruences(formula)
    for x_value, y_value in itertools.product(range(-2, 6), repeat=2):
        assert _evaluate(formula, {X: x_value, Y: y_value}) == _evaluate(result, {X: x_value, Y: y_value})


@pytest.mark.parametrize('y_upper_bound', [4, 0])
def test_linearization_of_a_quantified_variable_bounded_from_one_side(y_upper_bound):
    """
    `y` has only an upper bound, and `x - y <= 1` prefers it large, so the monotonicity argument confines it
    to the window of one modulus below its bound. An upper bound of 0 failed `assert var_bounds.upper_limit`.
    """
    body = AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=(
        _le([(1, Y)], y_upper_bound), _le([(1, X), (-1, Y)], 1), Congruence(vars=[X, Y], coefs=[2, 1], rhs=1, modulus=5)))
    formula = AST_Connective(referenced_vars=(), type=Connective_Type.AND, children=(
        *_bounds(X, -4, 2), AST_Quantifier(referenced_vars=(), bound_vars=(Y,), child=body)))
    _assert_linearization_preserves_truth(formula, free_values=range(-6, 5))
