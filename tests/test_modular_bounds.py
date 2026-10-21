"""
Tests for `amaya.preprocessing.modular_bounds` (the experimental modular-bound propagation pass).

The pass eliminates quantified variables that a congruence determines, carrying their windows forward
as modular interval facts. Two properties are load-bearing and are tested by brute force at a small
modulus rather than by inspection:

- the *derivation* may over-approximate (folding a shared variable widens an interval), so it is only
  ever required to be sound - every satisfying assignment still satisfies the derived facts;
- the *rewrite* may not over-approximate, since a weaker formula can be satisfiable where the original
  is not, so it is required to preserve the satisfying set exactly.
"""
import itertools

import pytest

from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.modular_bounds import (
    Modular_Bound_Fact,
    Modular_Bound_Rewrite_Stats,
    Modular_Interval,
    collect_congruence_system,
    derive_modular_bound_facts,
    propagate_modular_bounds,
    solve_congruence_for_variable,
)
from amaya.relations_structures import (
    AST_Connective,
    AST_Quantifier,
    Congruence,
    Connective_Type,
    Relation,
    Var,
    VariableType,
)

FREE_VAR_ID = 1


def _build_block(modulus, bounds, congruence_specs, bound_var_ids):
    conjuncts = []
    for var_id, (lower, upper) in bounds.items():
        conjuncts.append(Relation(vars=[Var(id=var_id)], coefs=[-1], rhs=-lower, predicate_symbol='<='))
        conjuncts.append(Relation(vars=[Var(id=var_id)], coefs=[1], rhs=upper, predicate_symbol='<='))
    for pairs, rhs in congruence_specs:
        conjuncts.append(Congruence(vars=[Var(id=var_id) for _, var_id in pairs],
                                    coefs=[coefficient for coefficient, _ in pairs],
                                    rhs=rhs, modulus=modulus))
    quantifier = AST_Quantifier(referenced_vars=(), bound_vars=tuple(Var(id=i) for i in bound_var_ids),
                                child=AST_Connective(referenced_vars=(), type=Connective_Type.AND,
                                                     children=tuple(conjuncts)))
    fill_referenced_vars(quantifier)
    return quantifier


def _make_var_table(var_ids):
    return {Var(id=var_id): VarInfo(name=f'v{var_id}', type=VariableType.INT,
                                    is_formula_param=(var_id == FREE_VAR_ID))
            for var_id in var_ids}


def _conjunct_holds(conjunct, assignment):
    total = sum(coefficient * assignment.get(var, 0)
                for coefficient, var in zip(conjunct.coefs, conjunct.vars))
    if isinstance(conjunct, Congruence):
        return (total - conjunct.rhs) % conjunct.modulus == 0
    return total <= conjunct.rhs


def _satisfying_free_values(quantifier, modulus, search_ranges):
    """ The free variable's values for which the block is satisfiable, by exhaustive search. """
    bound_vars = list(quantifier.bound_vars)
    conjuncts = quantifier.child.children
    satisfying = set()
    for free_value in range(modulus):
        assignment = {Var(id=FREE_VAR_ID): free_value}
        for combination in itertools.product(*(search_ranges[var] for var in bound_vars)):
            assignment.update(dict(zip(bound_vars, combination)))
            if all(_conjunct_holds(conjunct, assignment) for conjunct in conjuncts):
                satisfying.add(free_value)
                break
    return satisfying


MODULUS = 32
MOTIVATING_BOUNDS = {13: (4, 7), 14: (4, 7), 15: (MODULUS // 2, MODULUS - 1),
                     16: (MODULUS // 2, MODULUS - 1)}
MOTIVATING_CONGRUENCES = [([(10, FREE_VAR_ID), (1, 14), (MODULUS - 1, 15)], 4),
                          ([(1, 13), (10, 15), (MODULUS - 1, 16)], 4)]


# --- the interval domain -----------------------------------------------------------------------

def test_endpoints_stay_unreduced_so_vacuity_is_detectable():
    interval = Modular_Interval(-9, MODULUS - 1)
    assert interval.measure == MODULUS + 9
    assert interval.is_vacuous(MODULUS), 'a window wider than the modulus constrains nothing'
    assert not Modular_Interval(0, MODULUS - 2).is_vacuous(MODULUS)


def test_membership_reduces_the_value_never_the_window():
    """ Reducing the window instead of the value is the failure mode this convention exists to avoid. """
    interval = Modular_Interval(MODULUS - 4, MODULUS + 2)      # wraps past zero, unreduced
    assert interval.contains(MODULUS - 1, MODULUS)
    assert interval.contains(1, MODULUS), 'a value past the wrap must still be found'
    assert not interval.contains(MODULUS // 2, MODULUS)


def test_shifting_an_interval_is_exact():
    assert Modular_Interval(10, 20).shifted_by(-3, 5) == Modular_Interval(7, 25)


# --- solving a congruence for a variable ---------------------------------------------------------

def test_a_variable_with_an_invertible_coefficient_is_determined():
    congruence = Congruence(vars=[Var(id=1), Var(id=2)], coefs=[10, MODULUS - 1], rhs=4,
                            modulus=MODULUS)
    determined = solve_congruence_for_variable(congruence, Var(id=2))

    assert determined is not None
    for free_value in range(MODULUS):
        implied = determined.constant + sum(coefficient * free_value for var, coefficient
                                            in determined.term if var == Var(id=1))
        assert (10 * free_value + (MODULUS - 1) * implied - 4) % MODULUS == 0


def test_a_variable_with_a_non_invertible_coefficient_is_not_determined():
    congruence = Congruence(vars=[Var(id=1), Var(id=2)], coefs=[1, 2], rhs=4, modulus=MODULUS)
    assert solve_congruence_for_variable(congruence, Var(id=2)) is None


# --- the derivation ----------------------------------------------------------------------------

@pytest.mark.parametrize('description, bounds, congruences, bound_ids', [
    ('the motivating two-congruence block', MOTIVATING_BOUNDS, MOTIVATING_CONGRUENCES,
     [13, 14, 15, 16]),
    ('three congruences chained',
     {13: (4, 7), 15: (MODULUS // 2, MODULUS - 1), 16: (MODULUS // 2, MODULUS - 1),
      17: (MODULUS // 2, MODULUS - 1)},
     [([(3, FREE_VAR_ID), (MODULUS - 1, 15)], 7),
      ([(1, 15), (MODULUS - 1, 16)], 2),
      ([(1, 13), (5, 16), (MODULUS - 1, 17)], 4)],
     [13, 15, 16, 17]),
])
def test_the_derived_facts_hold_for_every_satisfying_assignment(description, bounds, congruences,
                                                                bound_ids):
    """ The derivation may over-approximate, so soundness is the requirement, not exactness. """
    quantifier = _build_block(MODULUS, bounds, congruences, bound_ids)
    derivation = derive_modular_bound_facts(quantifier)
    assert derivation is not None

    leftover = {var for fact in derivation.facts for var in fact.variables} - {Var(id=FREE_VAR_ID)}
    assert not leftover, f'folding should have removed {leftover}'

    search_ranges = {Var(id=var_id): range(lower, upper + 1) for var_id, (lower, upper) in bounds.items()}
    satisfying = _satisfying_free_values(quantifier, MODULUS, search_ranges)
    admitted = {value for value in range(MODULUS)
                if derivation.holds_for({Var(id=FREE_VAR_ID): value})}

    assert admitted >= satisfying, f'{description}: the derivation lost satisfying values'


def test_a_non_invertible_coefficient_blocks_the_derivation():
    quantifier = _build_block(MODULUS, {15: (MODULUS // 2, MODULUS - 1)},
                              [([(1, FREE_VAR_ID), (2, 15)], 4)], [15])
    derivation = derive_modular_bound_facts(quantifier)

    assert derivation is not None
    assert derivation.eliminated_vars == []
    assert len(derivation.surviving_congruences) == 1


def test_the_widest_window_is_eliminated_first():
    """
    Each congruence eliminates one variable, so spending one on a narrow window forces a wide one to be
    folded - and folding adds the variable's whole span to an interval, which can reach vacuity.
    """
    quantifier = _build_block(MODULUS, MOTIVATING_BOUNDS, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])
    derivation = derive_modular_bound_facts(quantifier)

    assert derivation.eliminated_vars == [Var(id=16), Var(id=15)]
    assert derivation.eliminated_congruences == 2


def test_an_unhandled_shape_is_declined():
    congruences = [([(1, FREE_VAR_ID), (1, 15)], 4)]
    quantifier = _build_block(MODULUS, {15: (0, 3)}, congruences, [15])
    quantifier = AST_Quantifier(referenced_vars=(), bound_vars=quantifier.bound_vars,
                                child=Relation(vars=[Var(id=FREE_VAR_ID)], coefs=[1], rhs=3,
                                               predicate_symbol='<='))
    assert collect_congruence_system(quantifier) is None
    assert derive_modular_bound_facts(quantifier) is None


# --- the rewrite -------------------------------------------------------------------------------

def _rewrite(bounds, congruences, bound_ids):
    quantifier = _build_block(MODULUS, bounds, congruences, bound_ids)
    var_table = _make_var_table([FREE_VAR_ID] + bound_ids)
    stats = Modular_Bound_Rewrite_Stats()
    rewritten = propagate_modular_bounds(quantifier, var_table, stats)
    return quantifier, rewritten, stats


def _assert_same_satisfying_set(original, rewritten, bounds):
    search_ranges = {Var(id=var_id): range(lower, upper + 1)
                     for var_id, (lower, upper) in bounds.items()}
    after_ranges = dict(search_ranges)
    for var in rewritten.bound_vars:
        after_ranges.setdefault(var, range(-2 * MODULUS, 2 * MODULUS))
    assert (_satisfying_free_values(original, MODULUS, search_ranges)
            == _satisfying_free_values(rewritten, MODULUS, after_ranges))


def test_the_rewrite_fires_when_a_window_spans_a_full_period():
    """
    A variable whose window covers every residue makes its congruence vacuous, so that congruence goes
    without a fact taking its place - the case where the rewrite is a strict win.
    """
    bounds = {**MOTIVATING_BOUNDS, 15: (0, MODULUS - 1)}
    original, rewritten, stats = _rewrite(bounds, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])

    assert stats.blocks_rewritten == 1
    assert stats.congruences_eliminated == 2 and stats.facts_emitted == 1
    assert len(rewritten.bound_vars) < len(original.bound_vars)
    _assert_same_satisfying_set(original, rewritten, bounds)


def test_the_rewrite_preserves_the_satisfying_set_exactly():
    """
    The rewrite must not over-approximate: a weaker formula is satisfiable where the original is not,
    which would turn UNSAT into SAT. This is why the rewrite path folds no shared variables.
    """
    bounds = {**MOTIVATING_BOUNDS, 15: (0, MODULUS - 1)}
    original, rewritten, _ = _rewrite(bounds, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])
    _assert_same_satisfying_set(original, rewritten, bounds)


def test_the_rewrite_declines_a_rename():
    """
    Two congruences in and two facts out costs one congruence and one witness variable each - no
    simplification, so the block is left alone.
    """
    original, rewritten, stats = _rewrite(MOTIVATING_BOUNDS, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])

    assert stats.blocks_examined == 1
    assert stats.blocks_rewritten == 0
    assert rewritten == original, 'the block must come back unchanged'


def test_the_rewrite_is_off_by_default():
    from amaya.config import solver_config
    assert solver_config.optimizations.propagate_modular_bounds is False


# --- regressions: rewrites that did not preserve the solution set ------------------------------
#
# Each case below is false for some value of the free variable while the rewrite produced by the
# pass before the fix was true. See docs/MODULAR_BOUNDS_KNOWN_BUGS.md for the derivations.

REGRESSION_MODULUS = 8
FREE_VAR, Y, Z, W = Var(id=FREE_VAR_ID), Var(id=2), Var(id=3), Var(id=4)


def _lower_bound(var, lower):
    return Relation(vars=[var], coefs=[-1], rhs=-lower, predicate_symbol='<=')


def _upper_bound(var, upper):
    return Relation(vars=[var], coefs=[1], rhs=upper, predicate_symbol='<=')


def _exists(bound_vars, *conjuncts):
    quantifier = AST_Quantifier(referenced_vars=(), bound_vars=tuple(bound_vars),
                                child=AST_Connective(referenced_vars=(), type=Connective_Type.AND,
                                                     children=tuple(conjuncts)))
    fill_referenced_vars(quantifier)
    return quantifier


def _evaluate(node, assignment, quantifier_search_range):
    """ Truth value of `node` under `assignment`; quantified variables range over `quantifier_search_range`. """
    if isinstance(node, (Relation, Congruence)):
        return _conjunct_holds(node, assignment)
    if isinstance(node, AST_Connective):
        assert node.type == Connective_Type.AND
        return all(_evaluate(child, assignment, quantifier_search_range) for child in node.children)
    assert isinstance(node, AST_Quantifier)
    return any(_evaluate(node.child, {**assignment, **dict(zip(node.bound_vars, values))}, quantifier_search_range)
               for values in itertools.product(quantifier_search_range, repeat=len(node.bound_vars)))


def _assert_rewrite_preserves_truth_for_every_free_value(formula):
    original_truth = {value: _evaluate(formula, {FREE_VAR: value}, range(-3 * REGRESSION_MODULUS, 3 * REGRESSION_MODULUS))
                      for value in range(-REGRESSION_MODULUS, REGRESSION_MODULUS)}
    var_table = _make_var_table([FREE_VAR_ID, 2, 3, 4])
    rewritten = propagate_modular_bounds(formula, var_table, Modular_Bound_Rewrite_Stats())

    def free_vars_of(node):
        if isinstance(node, (Relation, Congruence)):
            return set(node.vars)
        if isinstance(node, AST_Connective):
            return set().union(*(free_vars_of(child) for child in node.children))
        return free_vars_of(node.child) - set(node.bound_vars)

    assert free_vars_of(rewritten) <= {FREE_VAR}, 'a quantified variable escaped its quantifier'
    rewritten_truth = {value: _evaluate(rewritten, {FREE_VAR: value}, range(-3 * REGRESSION_MODULUS, 3 * REGRESSION_MODULUS))
                       for value in original_truth}
    assert rewritten_truth == original_truth


def _congruence(pairs, rhs, modulus=REGRESSION_MODULUS):
    return Congruence(vars=[var for _, var in pairs], coefs=[coefficient for coefficient, _ in pairs],
                      rhs=rhs, modulus=modulus)


def test_hard_bounds_on_free_variables_inside_the_block_are_kept():
    """ Bug A: `exists y. 0 <= y <= 7 and x + y = 0 (mod 8) and 0 <= x <= 2`. """
    formula = _exists([Y], _lower_bound(Y, 0), _upper_bound(Y, 7), _congruence([(1, FREE_VAR), (1, Y)], 0),
                      _lower_bound(FREE_VAR, 0), _upper_bound(FREE_VAR, 2))
    _assert_rewrite_preserves_truth_for_every_free_value(formula)


def test_one_sided_bounds_on_surviving_variables_are_kept():
    """ Bug B: `exists y, z. 0 <= y <= 7 and x + y = 0 (mod 8) and z >= 3 and z - x <= 0`. """
    formula = _exists([Y, Z], _lower_bound(Y, 0), _upper_bound(Y, 7), _congruence([(1, FREE_VAR), (1, Y)], 0),
                      _lower_bound(Z, 3), Relation(vars=[Z, FREE_VAR], coefs=[1, -1], rhs=0, predicate_symbol='<='))
    _assert_rewrite_preserves_truth_for_every_free_value(formula)


def test_a_variable_used_by_a_rewritten_nested_block_is_not_eliminated():
    """ Bug C: the inner block is rewritten first; the outer block must still see that it uses `y`. """
    inner = _exists([W], _lower_bound(W, 0), _upper_bound(W, 7), _congruence([(1, W), (1, Y)], 1),
                    Relation(vars=[FREE_VAR, Y], coefs=[1, 1], rhs=2, predicate_symbol='<='))
    formula = _exists([Y], _lower_bound(Y, 0), _upper_bound(Y, 7), _congruence([(1, FREE_VAR), (1, Y)], 0), inner)
    _assert_rewrite_preserves_truth_for_every_free_value(formula)


@pytest.mark.parametrize('lower, upper, congruence', [
    (0, 0, _congruence([(1, Y)], 1, modulus=2)),
    (0, 0, _congruence([(8, FREE_VAR), (1, Y)], 1)),
])
def test_a_false_variable_free_fact_is_not_dropped(lower, upper, congruence):
    """ Bug E: a fact with an empty term is a ground test, which can be false. """
    formula = _exists([Y], _lower_bound(Y, lower), _upper_bound(Y, upper), congruence)
    _assert_rewrite_preserves_truth_for_every_free_value(formula)


def test_repeated_variables_in_a_congruence_have_their_coefficients_summed():
    """ Bug G: `y + y + x = 0 (mod 8)` has coefficient 2 on `y`, which is not invertible modulo 8. """
    congruence = Congruence(vars=[Y, Y, FREE_VAR], coefs=[1, 1, 1], rhs=0, modulus=REGRESSION_MODULUS)
    assert solve_congruence_for_variable(congruence, Y) is None
    formula = _exists([Y], _lower_bound(Y, 0), _upper_bound(Y, 7), congruence)
    _assert_rewrite_preserves_truth_for_every_free_value(formula)
