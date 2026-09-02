import itertools

from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars, resolve_conditional_equalities
from amaya.relations_structures import (
    AST_Connective,
    AST_Negation,
    AST_Quantifier,
    ASTp_Node,
    BoolLiteral,
    Congruence,
    Connective_Type,
    Relation,
    Var,
)
from amaya import dsl


X, A, B, C, D, Y = Var(1), Var(2), Var(3), Var(4), Var(5), Var(6)
REMINDER_0, REMINDER_1, MAIN_C, MAIN_I = Var(7), Var(8), Var(9), Var(10)


def evaluate(node: ASTp_Node, env: dict) -> bool:
    """ Brute-force interpreter used to check semantic equivalence between a formula and its rewrite. """
    match node:
        case BoolLiteral():
            return node.value
        case Var():
            return env[node]
        case AST_Negation():
            return not evaluate(node.child, env)
        case Relation():
            lhs = sum(coef * env[v] for coef, v in zip(node.coefs, node.vars))
            return lhs == node.rhs if node.predicate_symbol == '=' else lhs <= node.rhs
        case Congruence():
            lhs = sum(coef * env[v] for coef, v in zip(node.coefs, node.vars))
            return lhs % node.modulus == node.rhs
        case AST_Connective():
            values = [evaluate(child, env) for child in node.children]
            if node.type == Connective_Type.AND:
                return all(values)
            if node.type == Connective_Type.OR:
                return any(values)
            return len(set(values)) == 1  # EQUIV
        case AST_Quantifier():
            search_range = range(-20, 21)
            return any(
                evaluate(node.child, {**env, **dict(zip(node.bound_vars, combo))})
                for combo in itertools.product(search_range, repeat=len(node.bound_vars))
            )
        case _:
            raise ValueError(f'Cannot evaluate {node}')


def assert_semantically_equivalent(original: ASTp_Node, rewritten: ASTp_Node, bool_vars: list, int_vars: list, int_range=range(-3, 4)):
    for bool_assignment in itertools.product([False, True], repeat=len(bool_vars)):
        for int_assignment in itertools.product(int_range, repeat=len(int_vars)):
            env = dict(zip(bool_vars, bool_assignment)) | dict(zip(int_vars, int_assignment))
            original_value = evaluate(original, env)
            rewritten_value = evaluate(rewritten, env)
            assert original_value == rewritten_value, f'Mismatch for {env}: original={original_value}, rewritten={rewritten_value}'


def _eq_x_to(rhs_var: Var | None, x: Var = X, rhs: int = 0) -> Relation:
    if rhs_var is None:
        return Relation(vars=[x], coefs=[1], rhs=rhs, predicate_symbol='=')
    return Relation(vars=[x, rhs_var], coefs=[1, -1], rhs=rhs, predicate_symbol='=')


def test_referenced_vars_extraction():
    formula = dsl._or(dsl._neg(A), _eq_x_to(B))
    fill_referenced_vars(formula)

    assert sorted(formula.referenced_vars) == sorted([A, B, X])


def test_simple_two_clause_resolution():
    # exists x. (not A or x = B) and (C or x = D)
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(dsl._neg(A), _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    expected = AST_Connective(
        referenced_vars=(),
        type=Connective_Type.OR,
        children=(dsl._neg(A), C, Relation(vars=[B, D], coefs=[-1, 1], rhs=0, predicate_symbol='=')),
    )

    assert result == expected


def test_leaves_quantifier_alone_when_var_leaks_outside_pattern():
    # exists x. (not A or x = B) and (x <= 3)   -- x appears outside the conditional-equality pattern
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(dsl._neg(A), _eq_x_to(B)),
            Relation(vars=[X], coefs=[1], rhs=3, predicate_symbol='<='),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert result == formula


def test_single_clause_is_not_touched():
    # exists x. (A or x = B) -- only one clause, must be left alone (formula is actually always True)
    formula = dsl._exists((X,), dsl._or(A, _eq_x_to(B)))
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert result == formula


def test_three_clause_resolution_produces_all_pairwise_equalities():
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(A, _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
            dsl._or(dsl._neg(A), _eq_x_to(None, rhs=5)),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert isinstance(result, AST_Connective) and result.type == Connective_Type.OR
    assert A in result.children
    assert C in result.children
    assert dsl._neg(A) in result.children
    assert Relation(vars=[B, D], coefs=[-1, 1], rhs=0, predicate_symbol='=') in result.children
    assert Relation(vars=[B], coefs=[-1], rhs=-5, predicate_symbol='=') in result.children
    assert Relation(vars=[D], coefs=[-1], rhs=-5, predicate_symbol='=') in result.children


def test_unrelated_conjunct_preserved():
    other = Relation(vars=[C], coefs=[1], rhs=0, predicate_symbol='<=')
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(dsl._neg(A), _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
            other,
        ),
    )

    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert isinstance(result, AST_Connective) and result.type == Connective_Type.AND
    assert other in result.children


def _has_quantifier(node: ASTp_Node) -> bool:
    if isinstance(node, AST_Quantifier):
        return True
    if isinstance(node, AST_Connective):
        return any(_has_quantifier(child) for child in node.children)
    if isinstance(node, AST_Negation):
        return _has_quantifier(node.child)
    return False


def _example_md_formula(bound_rhs: int) -> ASTp_Node:
    """ exists x. (x <= bound_rhs) and (A or x = B) and (C or x = D) - the shape from EXAMPLE.md. """
    bound = Relation(vars=[X], coefs=[1], rhs=bound_rhs, predicate_symbol='<=')
    formula = dsl._exists(
        (X,),
        dsl._and(
            bound,
            dsl._or(A, _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)
    return formula


def test_bound_plus_equalities_eliminates_quantifier():
    formula = _example_md_formula(bound_rhs=-1)
    result = resolve_conditional_equalities(formula)
    assert not _has_quantifier(result)


def test_bound_plus_equalities_semantically_equivalent_bruteforce():
    for bound_rhs in range(-3, 4):
        formula = _example_md_formula(bound_rhs)
        result = resolve_conditional_equalities(formula)
        assert_semantically_equivalent(formula, result, bool_vars=[A, C], int_vars=[B, D], int_range=range(-3, 4))


def test_example_md_naive_shortcut_is_unsound():
    """
    Regression test pinning down the exact counterexample to EXAMPLE.md's own worked derivation:

        exists x. (x <= -1) and (A or x=B) and (C or x=D)

    with A=True (clause 1 escapes), C=False (clause 2 forces x=D=10), B=5, D=10. Since x must
    equal 10 but the bound requires x<=-1, the correct answer is UNSAT. EXAMPLE.md's simplified
    formula `A or ((B<=-1) and (C or B=D))` evaluates to True here (because A=True short-circuits
    everything) which is wrong - it drops the requirement that D must also satisfy the bound
    when clause 1's escape doesn't apply to clause 2. Our pass must agree with the true value.
    """
    formula = _example_md_formula(bound_rhs=-1)
    result = resolve_conditional_equalities(formula)

    env = {A: True, C: False, B: 5, D: 10}
    assert evaluate(formula, env) is False
    assert evaluate(result, env) is False


def _general_inequality_formula(bound_rhs: int) -> ASTp_Node:
    """ exists x. (x + y <= bound_rhs) and (A or x=B) and (C or x=D) - the inequality also involves the free var y. """
    inequality = Relation(vars=[X, Y], coefs=[1, 1], rhs=bound_rhs, predicate_symbol='<=')
    formula = dsl._exists(
        (X,),
        dsl._and(
            inequality,
            dsl._or(A, _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)
    return formula


def test_general_inequality_eliminates_outer_quantifier():
    formula = _general_inequality_formula(bound_rhs=0)
    result = resolve_conditional_equalities(formula)
    # `x + y <= bound_rhs` only bounds x from one side (it's the only inequality on x here), so x
    # can always be pushed towards -infinity regardless of y - no residual quantifier is needed
    # at all, not even a small nested one.
    assert not _has_quantifier(result)


def test_general_inequality_semantically_equivalent_bruteforce():
    for bound_rhs in range(-2, 3):
        formula = _general_inequality_formula(bound_rhs)
        result = resolve_conditional_equalities(formula)
        assert_semantically_equivalent(formula, result, bool_vars=[A, C], int_vars=[B, D, Y], int_range=range(-2, 3))


def test_general_inequality_all_escapes_branch_respects_infeasible_conjunction():
    """
    Two general inequalities on x that are jointly infeasible for every y (x+y<=0 and x+y>=10) -
    the residual `exists x. D` synthesized for the all-escapes branch must correctly report UNSAT
    here, rather than assuming a conjunction of general inequalities is always satisfiable.
    """
    ineq1 = Relation(vars=[X, Y], coefs=[1, 1], rhs=0, predicate_symbol='<=')
    ineq2 = Relation(vars=[X, Y], coefs=[-1, -1], rhs=-10, predicate_symbol='<=')
    formula = dsl._exists(
        (X,),
        dsl._and(
            ineq1,
            ineq2,
            dsl._or(A, _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    env = {A: True, C: True, B: 0, D: 0, Y: 0}  # both escapes true -> only D's (in)feasibility matters
    assert evaluate(formula, env) is False
    assert evaluate(result, env) is False

    naive_example_md_formula = dsl._or(
        A,
        dsl._and(
            Relation(vars=[B], coefs=[1], rhs=-1, predicate_symbol='<='),
            dsl._or(C, Relation(vars=[B, D], coefs=[1, -1], rhs=0, predicate_symbol='=')),
        ),
    )
    assert evaluate(naive_example_md_formula, env) is True


def test_duplicate_equality_occurrence_in_clause_is_tolerated():
    """
    Regression test for a real formula fragment where a clause's defining equality (and some of
    its escape literals) showed up duplicated, e.g. `(or A (x=B) (x=B))` instead of `(or A (x=B))`
    - an artifact of how the formula was generated (repeated substitution paths), not a
    deliberate "two different equalities" clause. This must still match and eliminate `x`.
    """
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(A, _eq_x_to(B), _eq_x_to(B)),
            dsl._or(C, C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert not _has_quantifier(result)
    assert_semantically_equivalent(formula, result, bool_vars=[A, C], int_vars=[B, D])


def test_clause_with_genuinely_different_equalities_is_left_alone():
    """
    Unlike duplicates of the *same* equality, a clause pinning `x` to two different values
    disjunctively (`(x=B) or (x=D)`, with no escape literal at all) is a different pattern this
    pass doesn't handle - it must be left untouched rather than guessed at.
    """
    formula = dsl._exists(
        (X,),
        dsl._and(
            dsl._or(_eq_x_to(B), _eq_x_to(D)),
            dsl._or(A, _eq_x_to(B)),
        ),
    )
    fill_referenced_vars(formula) 

    result = resolve_conditional_equalities(formula)

    assert result == formula


def test_single_direction_general_inequality_needs_no_residual_quantifier():
    """
    Mirrors a real formula fragment: `x <= y - 1` only bounds x from one side, even though it
    involves the other free variable y. Since x's domain is unbounded, x can always be pushed
    towards -infinity regardless of y's value, so this must resolve with no residual quantifier
    left behind at all (unlike the two-sided general-inequality case, which does need one).
    """
    inequality = Relation(vars=[Y, X], coefs=[-1, 1], rhs=-1, predicate_symbol='<=')  # x <= y - 1
    formula = dsl._exists(
        (X,),
        dsl._and(
            inequality,
            dsl._or(A, _eq_x_to(B)),
            dsl._or(C, _eq_x_to(D)),
        ),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    assert not _has_quantifier(result)
    assert_semantically_equivalent(formula, result, bool_vars=[A, C], int_vars=[B, D, Y])


def test_congruence_conjunct_blocks_elimination():
    """
    Regression test for a real formula fragment:

        exists ((reminder_0 Int))
          (and
            (<= (* (- 1) reminder_0) (- 48))
            (<= (* 1 reminder_0) 57)
            (= (mod (+ (* 1 main_~c~0) (* (- 1) reminder_0)) 256) 0)
            (= (mod (+ (* 10 main_~i~0) (* (- 1) reminder_1) (* 1 reminder_0)) 4294967296) 48))
    """
    bound_lower = Relation(vars=[REMINDER_0], coefs=[-1], rhs=-48, predicate_symbol='<=')
    bound_upper = Relation(vars=[REMINDER_0], coefs=[1], rhs=57, predicate_symbol='<=')
    congruence_c = Congruence(vars=[MAIN_C, REMINDER_0], coefs=[1, -1], rhs=0, modulus=256)
    congruence_i = Congruence(vars=[MAIN_I, REMINDER_1, REMINDER_0], coefs=[10, -1, 1], rhs=48, modulus=4294967296)

    formula = dsl._exists(
        (REMINDER_0,),
        dsl._and(bound_lower, bound_upper, congruence_c, congruence_i),
    )
    fill_referenced_vars(formula)

    result = resolve_conditional_equalities(formula)

    # Left completely untouched: the congruences block elimination of `reminder_0`, so the
    # quantifier, its bounds and both congruences must all survive verbatim.
    assert result == formula
    assert _has_quantifier(result)
