from amaya import dsl
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.inner_quantifier_squeeze_elimination import eliminate_inner_quantifier_squeezes
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)
from tests.test_conditional_equality_resolution import assert_semantically_equivalent


Y, X, A, B, Z, Z1, Z2, Z3, Z4, W = (Var(i) for i in range(1, 11))


def _var_table(*int_vars: Var, bool_vars: tuple = ()) -> dict:
    table = {var: VarInfo(name=f'v{var.id}', type=VariableType.INT) for var in int_vars}
    table.update({var: VarInfo(name=f'v{var.id}', type=VariableType.BOOL) for var in bool_vars})
    return table


def test_squeeze_pair_alone_becomes_true():
    # exists y. (10y <= 9x and 10y >= 9x - 9)
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    formula = dsl._exists((Y,), dsl._and(upper, lower))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X))

    assert result == BoolLiteral(True)


def test_worked_example_from_design_document():
    """ `docs/QSE.md` §5, verbatim. """
    x_ge_218 = Relation(vars=[X], coefs=[-1], rhs=-218, predicate_symbol='<=')  # x >= 218
    x_le_a = Relation(vars=[X, A], coefs=[1, -1], rhs=0, predicate_symbol='<=')  # x <= a
    y_bound = Relation(vars=[Y, B], coefs=[-1, 1], rhs=-554854, predicate_symbol='<=')  # y >= b + 554854
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')  # 10y <= 9x
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')  # 10y >= 9x - 9

    inner = dsl._exists((Y,), dsl._and(y_bound, upper, lower))
    formula = dsl._exists((X,), dsl._and(x_ge_218, x_le_a, inner))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(X, Y, A, B))

    expected_atom = Relation(vars=[X, B], coefs=[-9, 10], rhs=-5548540, predicate_symbol='<=')  # 9x >= 10b + 5548540
    expected = dsl._exists((X,), dsl._and(x_ge_218, x_le_a, expected_atom))
    fill_referenced_vars(expected)

    assert result == expected


def test_lower_bound_residual_substitution():
    """ C2: a `-y + T <= k` residual (`y >= T - k`). """
    upper = Relation(vars=[Y, X], coefs=[3, -2], rhs=0, predicate_symbol='<=')   # 3y <= 2x
    lower = Relation(vars=[Y, X], coefs=[-3, 2], rhs=2, predicate_symbol='<=')   # 3y >= 2x - 2
    residual = Relation(vars=[Y, Z], coefs=[-1, 1], rhs=0, predicate_symbol='<=')  # y >= z

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    expected = Relation(vars=[X, Z], coefs=[-2, 3], rhs=0, predicate_symbol='<=')
    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Z])


def test_upper_bound_residual_substitution():
    """ C1: a `y + T <= k` residual (`y <= k - T`). """
    upper = Relation(vars=[Y, X], coefs=[3, -2], rhs=0, predicate_symbol='<=')   # 3y <= 2x
    lower = Relation(vars=[Y, X], coefs=[-3, 2], rhs=2, predicate_symbol='<=')   # 3y >= 2x - 2
    residual = Relation(vars=[Y, Z], coefs=[1, -1], rhs=1, predicate_symbol='<=')  # y <= z + 1

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    expected = Relation(vars=[X, Z], coefs=[2, -3], rhs=5, predicate_symbol='<=')
    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Z])


def test_equality_residual_emits_two_atoms():
    """ C3/C4: a `y = T` residual becomes a conjunction of two atoms. """
    upper = Relation(vars=[Y, X], coefs=[3, -2], rhs=0, predicate_symbol='<=')   # 3y <= 2x
    lower = Relation(vars=[Y, X], coefs=[-3, 2], rhs=2, predicate_symbol='<=')   # 3y >= 2x - 2
    residual = Relation(vars=[Y, Z], coefs=[1, -1], rhs=0, predicate_symbol='=')  # y = z

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    atom_upper = Relation(vars=[X, Z], coefs=[2, -3], rhs=2, predicate_symbol='<=')
    atom_lower = Relation(vars=[X, Z], coefs=[-2, 3], rhs=0, predicate_symbol='<=')
    expected = AST_Connective(referenced_vars=(X, Z), type=Connective_Type.AND, children=(atom_upper, atom_lower))

    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Z])


def test_disequality_residual_emits_disjunction():
    """ C5: a `not (y = T)` residual becomes a disjunction of two negated atoms. """
    upper = Relation(vars=[Y, X], coefs=[3, -2], rhs=0, predicate_symbol='<=')   # 3y <= 2x
    lower = Relation(vars=[Y, X], coefs=[-3, 2], rhs=2, predicate_symbol='<=')   # 3y >= 2x - 2
    equality = Relation(vars=[Y, Z], coefs=[1, -1], rhs=0, predicate_symbol='=')  # y = z
    residual = AST_Negation(referenced_vars=(Y, Z), child=equality)

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    negated_upper = Relation(vars=[X, Z], coefs=[-2, 3], rhs=-3, predicate_symbol='<=')
    negated_lower = Relation(vars=[X, Z], coefs=[2, -3], rhs=-1, predicate_symbol='<=')
    expected = AST_Connective(referenced_vars=(X, Z), type=Connective_Type.OR, children=(negated_upper, negated_lower))

    assert result == expected
    assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Z])


def test_gap_off_by_one_is_not_a_squeeze():
    upper = Relation(vars=[Y, X], coefs=[4, -1], rhs=0, predicate_symbol='<=')  # 4y <= x

    lower_gap_a = Relation(vars=[Y, X], coefs=[-4, 1], rhs=4, predicate_symbol='<=')      # gap == A
    lower_gap_a_minus_2 = Relation(vars=[Y, X], coefs=[-4, 1], rhs=2, predicate_symbol='<=')  # gap == A - 2

    var_table = _var_table(Y, X)

    formula_gap_a = dsl._exists((Y,), dsl._and(upper, lower_gap_a))
    fill_referenced_vars(formula_gap_a)
    assert eliminate_inner_quantifier_squeezes(formula_gap_a, var_table) == formula_gap_a

    formula_gap_a_minus_2 = dsl._exists((Y,), dsl._and(upper, lower_gap_a_minus_2))
    fill_referenced_vars(formula_gap_a_minus_2)
    assert eliminate_inner_quantifier_squeezes(formula_gap_a_minus_2, var_table) == formula_gap_a_minus_2


def test_mismatched_residual_terms_are_not_a_squeeze():
    """ §4.2 condition 3 (the D2 regression test): `10y <= 9x` paired with `10y >= 9z - 9` involves
    a different free variable on each side, so the two bounds do not form a squeeze. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, Z], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    formula = dsl._exists((Y,), dsl._and(upper, lower))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    assert result == formula


def test_residual_with_coefficient_two_blocks_elimination():
    """ §5.1: a residual conjunct whose coefficient of `y` has absolute value > 1 aborts the rewrite. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    residual = Relation(vars=[Y], coefs=[2], rhs=5, predicate_symbol='<=')  # 2y <= 5

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X))

    assert result == formula


def test_congruence_on_squeezed_var_blocks_elimination():
    """ §5.2: a congruence mentioning the squeezed variable aborts the rewrite. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    congruence = Congruence(vars=[Y], coefs=[1], rhs=0, modulus=5)

    formula = dsl._exists((Y,), dsl._and(upper, lower, congruence))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X))

    assert result == formula


def test_squeezed_var_inside_disjunction_blocks_elimination():
    """ §4.3 abort rule: `y` occurring inside a nested disjunction is not an admissible shape. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    y_in_disjunction = dsl._or(W, Relation(vars=[Y], coefs=[1], rhs=5, predicate_symbol='<='))

    formula = dsl._exists((Y,), dsl._and(upper, lower, y_in_disjunction))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X))

    assert result == formula


def test_bool_sorted_var_is_not_eliminated():
    """ S2: a Bool-sorted bound variable is skipped even when the body superficially matches the
    squeeze shape. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    formula = dsl._exists((Y,), dsl._and(upper, lower))
    fill_referenced_vars(formula)

    var_table = _var_table(X, bool_vars=(Y,))

    result = eliminate_inner_quantifier_squeezes(formula, var_table)

    assert result == formula


def test_non_squeezed_bound_vars_are_retained():
    """ §4.5 step 5: a two-variable `bound_vars` tuple, with only one variable eliminated. """
    upper = Relation(vars=[Y, X], coefs=[10, -9], rhs=0, predicate_symbol='<=')
    lower = Relation(vars=[Y, X], coefs=[-10, 9], rhs=9, predicate_symbol='<=')
    w_bound = Relation(vars=[W], coefs=[1], rhs=5, predicate_symbol='<=')  # w <= 5, unrelated to the squeeze

    formula = dsl._exists((Y, W), dsl._and(upper, lower, w_bound))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, W, X))

    expected = AST_Quantifier(referenced_vars=(W,), bound_vars=(W,), child=w_bound)

    assert result == expected


def test_modulus_one_degenerates_to_substitution():
    """ §4.6: `A == 1` is plain substitution, no floor. """
    upper = Relation(vars=[Y, X], coefs=[1, -1], rhs=0, predicate_symbol='<=')   # y <= x
    lower = Relation(vars=[Y, X], coefs=[-1, 1], rhs=0, predicate_symbol='<=')   # y >= x
    residual = Relation(vars=[Y, Z], coefs=[1, -1], rhs=3, predicate_symbol='<=')  # y <= z + 3

    formula = dsl._exists((Y,), dsl._and(upper, lower, residual))
    fill_referenced_vars(formula)

    result = eliminate_inner_quantifier_squeezes(formula, _var_table(Y, X, Z))

    expected = Relation(vars=[X, Z], coefs=[1, -1], rhs=3, predicate_symbol='<=')  # x <= z + 3
    assert result == expected


def test_semantic_equivalence_bruteforce():
    """ T15 (§8): the load-bearing test. Exhaustive comparison against the original quantified
    formula, for every squeeze modulus and residual kind at once. """
    var_table = _var_table(Y, X, Z1, Z2, Z3, Z4)

    for squeeze_modulus in (1, 2, 3, 10):
        upper = Relation(vars=[Y, X], coefs=[squeeze_modulus, -1], rhs=0, predicate_symbol='<=')
        lower = Relation(vars=[Y, X], coefs=[-squeeze_modulus, 1], rhs=squeeze_modulus - 1, predicate_symbol='<=')

        residual_upper = Relation(vars=[Y, Z1], coefs=[1, -1], rhs=0, predicate_symbol='<=')   # y <= z1
        residual_lower = Relation(vars=[Y, Z2], coefs=[-1, 1], rhs=0, predicate_symbol='<=')   # y >= z2
        residual_eq = Relation(vars=[Y, Z3], coefs=[1, -1], rhs=0, predicate_symbol='=')       # y = z3
        residual_diseq = AST_Negation(
            referenced_vars=(Y, Z4),
            child=Relation(vars=[Y, Z4], coefs=[1, -1], rhs=0, predicate_symbol='='),
        )  # not (y = z4)

        formula = dsl._exists(
            (Y,),
            dsl._and(upper, lower, residual_upper, residual_lower, residual_eq, residual_diseq),
        )
        fill_referenced_vars(formula)

        result = eliminate_inner_quantifier_squeezes(formula, var_table)

        assert_semantically_equivalent(formula, result, bool_vars=[], int_vars=[X, Z1, Z2, Z3, Z4])
