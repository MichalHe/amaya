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
