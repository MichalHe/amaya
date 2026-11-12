from amaya import dsl
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.unit_coefficient_fourier_motzkin import eliminate_unit_coefficient_vars_by_fourier_motzkin
from amaya.relations_structures import (
    AST_Negation,
    BoolLiteral,
    Congruence,
    Relation,
    Var,
    VariableType,
)
from tests.test_conditional_equality_resolution import assert_semantically_equivalent


X, Y, C, R, V, W = (Var(i) for i in range(1, 7))


def _var_table(*int_vars: Var) -> dict:
    return {var: VarInfo(name=f'v{var.id}', type=VariableType.INT) for var in int_vars}


def _le(var_coef_pairs: list[tuple[int, Var]], rhs: int) -> Relation:
    """ sum(coef * var) <= rhs, with the variables sorted by id as `_linear_combo` produces them. """
    sorted_pairs = sorted(var_coef_pairs, key=lambda coef_var_pair: coef_var_pair[1])
    return Relation(vars=[var for _coef, var in sorted_pairs], coefs=[coef for coef, _var in sorted_pairs],
                    rhs=rhs, predicate_symbol='<=')


def _eliminate(formula, *int_vars: Var, quantified_vars_are_nonnegative: bool = False):
    fill_referenced_vars(formula)
    return eliminate_unit_coefficient_vars_by_fourier_motzkin(formula, _var_table(*int_vars), quantified_vars_are_nonnegative)


def test_lower_bounds_are_paired_with_upper_bound():
    # exists v. (v >= 5  and  v >= 2y + 5  and  v <= x)   --->   (x >= 5  and  x >= 2y + 5)
    formula = dsl._exists((V,), dsl._and(
        _le([(-1, V)], -5),
        _le([(-1, V), (2, Y)], -5),
        _le([(1, V), (-1, X)], 0),
    ))

    result = _eliminate(formula, X, Y, V)

    expected = dsl._and(
        _le([(-1, X)], -5),
        _le([(-1, X), (2, Y)], -5),
    )
    fill_referenced_vars(expected)
    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Y])


def test_unit_coefficient_equation_contributes_both_bounds():
    # exists v. (v - 5c - r = 0  and  v <= -1  and  v <= x)   --->   (5c + r <= -1  and  5c + r - x <= 0)
    formula = dsl._exists((V,), dsl._and(
        dsl._eq([(1, V), (-5, C), (-1, R)], 0),
        _le([(1, V)], -1),
        _le([(1, V), (-1, X)], 0),
    ))

    result = _eliminate(formula, X, C, R, V)

    expected = dsl._and(
        _le([(5, C), (1, R)], -1),
        _le([(-1, X), (5, C), (1, R)], 0),
    )
    fill_referenced_vars(expected)
    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, C, R])


def test_equation_with_negative_coefficient_at_eliminated_var():
    # exists v. (-v + 5c = 0  and  0 <= v  and  v <= x)  <=>  (0 <= 5c  and  5c <= x)
    formula = dsl._exists((V,), dsl._and(
        dsl._eq([(-1, V), (5, C)], 0),
        _le([(-1, V)], 0),
        _le([(1, V), (-1, X)], 0),
    ))

    result = _eliminate(formula, X, C, V)

    assert V not in result.referenced_vars
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, C])


def test_squeezed_variable_under_negation_with_outer_quantifier():
    # Conjunct 3 of Problem15_label00_false-unreach-call.c_17.smt2 with small constants:
    # not exists c. (c <= 2  and  y <= c  and  exists v. (0 <= v  and  v <= x  and  5c <= v  and  v <= 5c + 4))
    inner = dsl._exists((V,), dsl._and(
        _le([(-1, V)], 0),
        _le([(1, V), (-1, X)], 0),
        _le([(5, C), (-1, V)], 0),
        _le([(1, V), (-5, C)], 4),
    ))
    formula = dsl._neg(dsl._exists((C,), dsl._and(
        _le([(1, C)], 2),
        _le([(1, Y), (-1, C)], 0),
        inner,
    )))

    result = _eliminate(formula, X, Y, C, V)

    assert V not in result.referenced_vars
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Y])


def test_variable_with_only_lower_bounds_is_dropped_with_its_bounds():
    # exists v. (v >= x  and  v >= y  and  x <= 3)   --->   x <= 3
    x_le_3 = _le([(1, X)], 3)
    formula = dsl._exists((V,), dsl._and(
        _le([(-1, V), (1, X)], 0),
        _le([(-1, V), (1, Y)], 0),
        x_le_3,
    ))

    result = _eliminate(formula, X, Y, V)

    assert result == x_le_3


def test_contradictory_constant_bounds_yield_false():
    # exists v. (v >= 3  and  v <= 2)   --->   False
    formula = dsl._exists((V,), dsl._and(_le([(-1, V)], -3), _le([(1, V)], 2)))

    result = _eliminate(formula, V)

    assert result == BoolLiteral(False)


def test_eliminating_one_variable_enables_another():
    # exists v, w. (-v + w <= 0  and  v - 2w <= 0  and  w <= x)
    # w has coefficient -2 in the second atom; it becomes eliminable once v is eliminated: -w <= 0.
    formula = dsl._exists((V, W), dsl._and(
        _le([(-1, V), (1, W)], 0),
        _le([(1, V), (-2, W)], 0),
        _le([(1, W), (-1, X)], 0),
    ))

    result = _eliminate(formula, X, V, W)

    assert result == _le([(-1, X)], 0)
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X])


def test_non_unit_coefficient_is_left_unchanged():
    formula = dsl._exists((V,), dsl._and(_le([(-2, V)], 0), _le([(1, V), (-1, X)], 0)))

    result = _eliminate(formula, X, V)

    assert result == formula


def test_variable_in_congruence_is_left_unchanged():
    congruence = Congruence(vars=[V], coefs=[1], rhs=3, modulus=5)
    formula = dsl._exists((V,), dsl._and(congruence, _le([(-1, V)], 0), _le([(1, V), (-1, X)], 0)))

    result = _eliminate(formula, X, V)

    assert result == formula


def test_variable_in_negated_equation_is_left_unchanged():
    disequation = AST_Negation(referenced_vars=(), child=dsl._eq([(1, V), (-1, Y)], 0))
    formula = dsl._exists((V,), dsl._and(disequation, _le([(-1, V)], 0), _le([(1, V), (-1, X)], 0)))

    result = _eliminate(formula, X, Y, V)

    assert result == formula


def test_rewrite_increasing_the_number_of_atoms_is_not_applied():
    # 2 lower bounds and 3 upper bounds: 6 combined atoms replace 5.
    formula = dsl._exists((V,), dsl._and(
        _le([(-1, V)], 0),
        _le([(-1, V), (1, Y)], 0),
        _le([(1, V), (-1, X)], 0),
        _le([(1, V), (-1, C)], 0),
        _le([(1, V)], 10),
    ))

    result = _eliminate(formula, X, Y, C, V)

    assert result == formula


def test_natural_numbers_domain_adds_nonnegativity_of_eliminated_var():
    # exists v. v <= x   --->   True over the integers, 0 <= x over the natural numbers
    formula_over_integers = dsl._exists((V,), _le([(1, V), (-1, X)], 0))
    formula_over_naturals = dsl._exists((V,), _le([(1, V), (-1, X)], 0))

    assert _eliminate(formula_over_integers, X, V) == BoolLiteral(True)
    assert _eliminate(formula_over_naturals, X, V, quantified_vars_are_nonnegative=True) == _le([(-1, X)], 0)


def test_bool_variable_is_not_eliminated():
    formula = dsl._exists((V,), dsl._and(V, _le([(1, X)], 0)))
    fill_referenced_vars(formula)
    var_table = {X: VarInfo(name='x', type=VariableType.INT), V: VarInfo(name='v', type=VariableType.BOOL)}

    result = eliminate_unit_coefficient_vars_by_fourier_motzkin(formula, var_table)

    assert result == formula
