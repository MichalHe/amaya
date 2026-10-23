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
    Modular_Interval_Union,
    _preimage_under_multiplication,
    _shift_union_by_multiples,
    collect_congruence_system,
    derive_modular_bound_facts,
    propagate_modular_bounds,
    solve_congruence_for_variable,
)
from amaya.relations_structures import (
    AST_Connective,
    AST_Quantifier,
    BoolLiteral,
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


def _holds(node, assignment, search_range_of_var):
    """
    Truth value of `node` under `assignment`. A quantified variable ranges over
    `search_range_of_var(var)`; the rewrite may emit `BoolLiteral`, OR connectives and bare conjunctions.
    """
    if isinstance(node, BoolLiteral):
        return node.value
    if isinstance(node, (Relation, Congruence)):
        return _conjunct_holds(node, assignment)
    if isinstance(node, AST_Connective):
        child_truths = (_holds(child, assignment, search_range_of_var) for child in node.children)
        return all(child_truths) if node.type == Connective_Type.AND else any(child_truths)
    assert isinstance(node, AST_Quantifier)
    bound_vars = list(node.bound_vars)
    return any(_holds(node.child, {**assignment, **dict(zip(bound_vars, values))}, search_range_of_var)
               for values in itertools.product(*(search_range_of_var(var) for var in bound_vars)))


def _satisfying_free_values(formula, modulus, search_ranges, default_search_range=None):
    """ The free variable's values for which `formula` is true, by exhaustive search. """
    def search_range_of_var(var):
        return search_ranges[var] if default_search_range is None else search_ranges.get(var, default_search_range)
    return {free_value for free_value in range(modulus)
            if _holds(formula, {Var(id=FREE_VAR_ID): free_value}, search_range_of_var)}


def _count_congruences(node):
    if isinstance(node, Congruence):
        return 1
    if isinstance(node, AST_Connective):
        return sum(_count_congruences(child) for child in node.children)
    if isinstance(node, AST_Quantifier):
        return _count_congruences(node.child)
    return 0


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
    assert (_satisfying_free_values(original, MODULUS, search_ranges)
            == _satisfying_free_values(rewritten, MODULUS, search_ranges,
                                       default_search_range=range(-2 * MODULUS, 2 * MODULUS)))


def test_the_rewrite_fires_when_a_window_spans_a_full_period():
    """
    A variable whose window covers every residue makes its congruence vacuous, so that congruence goes
    without a fact taking its place. The remaining fact over `100*x1 + 10*x14 + x13` covers every residue
    once `x13` and `x14` are folded, so the block is true for every `x1`.
    """
    bounds = {**MOTIVATING_BOUNDS, 15: (0, MODULUS - 1)}
    original, rewritten, stats = _rewrite(bounds, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])

    assert stats.blocks_rewritten == 1
    assert stats.congruences_eliminated == 2 and stats.facts_emitted == 0
    assert rewritten == BoolLiteral(value=True)
    _assert_same_satisfying_set(original, rewritten, bounds)


def test_the_rewrite_preserves_the_satisfying_set_exactly():
    """
    The rewrite must not over-approximate: a weaker formula is satisfiable where the original is not,
    which would turn UNSAT into SAT. This is why the rewrite path folds no shared variables.
    """
    bounds = {**MOTIVATING_BOUNDS, 15: (0, MODULUS - 1)}
    original, rewritten, _ = _rewrite(bounds, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])
    _assert_same_satisfying_set(original, rewritten, bounds)


def test_the_motivating_block_is_folded_into_one_congruence():
    """
    The derivation leaves two facts sharing `x13` and `x14`. `x13` occurs in one fact and is folded; the
    other fact's term is then 10 times the first's, so the two merge; `x14` is then folded.
    """
    original, rewritten, stats = _rewrite(MOTIVATING_BOUNDS, MOTIVATING_CONGRUENCES, [13, 14, 15, 16])

    assert stats.blocks_rewritten == 1
    assert stats.facts_merged == 1 and stats.vars_folded == 2
    assert _count_congruences(rewritten) == 1
    _assert_same_satisfying_set(original, rewritten, MOTIVATING_BOUNDS)


def test_the_rewrite_declines_facts_whose_terms_are_not_related():
    """
    Two facts over different free variables cannot merge; two congruences in and two facts out saves no
    congruence, so the block is left alone.
    """
    other_free_var_id = 5
    congruences = [([(1, FREE_VAR_ID), (1, 15)], 0), ([(1, other_free_var_id), (1, 16)], 1)]
    bounds = {15: (0, 3), 16: (0, 3)}
    quantifier = _build_block(MODULUS, bounds, congruences, [15, 16])
    stats = Modular_Bound_Rewrite_Stats()
    rewritten = propagate_modular_bounds(quantifier, _make_var_table([FREE_VAR_ID, other_free_var_id, 15, 16]), stats)

    assert stats.blocks_examined == 1
    assert stats.declined_no_congruence_saved == 1
    assert rewritten == quantifier, 'the block must come back unchanged'


def test_the_rewrite_is_off_by_default():
    from amaya.config import solver_config
    assert solver_config.optimizations.propagate_modular_bounds is False


# --- regressions: rewrites that did not preserve the solution set ------------------------------
#
# Each case below is false for some value of the free variable while the rewrite produced by the
# pass before the fix was true. See the message of commit dffbde2 for the derivations.

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
    return _holds(node, assignment, lambda var: quantifier_search_range)


def _assert_rewrite_preserves_truth_for_every_free_value(formula):
    original_truth = {value: _evaluate(formula, {FREE_VAR: value}, range(-3 * REGRESSION_MODULUS, 3 * REGRESSION_MODULUS))
                      for value in range(-REGRESSION_MODULUS, REGRESSION_MODULUS)}
    var_table = _make_var_table([FREE_VAR_ID, 2, 3, 4])
    rewritten = propagate_modular_bounds(formula, var_table, Modular_Bound_Rewrite_Stats())

    def free_vars_of(node):
        if isinstance(node, BoolLiteral):
            return set()
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


# --- exact folding over unions of intervals ----------------------------------------------------

def _random_union(random_generator, modulus):
    intervals = []
    for _ in range(random_generator.randint(1, 3)):
        lower = random_generator.randrange(-modulus, 2 * modulus)
        intervals.append((lower, lower + random_generator.randint(0, modulus // 2)))
    return Modular_Interval_Union.from_unreduced_intervals(intervals, modulus)


def _members(union):
    return {residue for residue in range(union.modulus) if union.contains(residue)}


@pytest.mark.parametrize('modulus', [30, 32])
def test_shifting_a_union_by_multiples_matches_enumeration(modulus):
    import random
    random_generator = random.Random(modulus)
    for _ in range(300):
        residues = _random_union(random_generator, modulus)
        coefficient = random_generator.choice([value for value in range(-modulus // 2, modulus // 2 + 1) if value])
        lower = random_generator.randint(-5, 5)
        upper = lower + random_generator.randint(0, 6)
        shifted = _shift_union_by_multiples(residues, coefficient, lower, upper)
        expected = {(member - coefficient * value) % modulus for member in _members(residues)
                    for value in range(lower, upper + 1)}
        assert shifted is not None and _members(shifted) == expected


@pytest.mark.parametrize('modulus', [30, 32])
def test_the_preimage_under_multiplication_matches_enumeration(modulus):
    import random
    random_generator = random.Random(modulus + 1)
    for _ in range(300):
        target, domain = _random_union(random_generator, modulus), _random_union(random_generator, modulus)
        multiplier = random_generator.choice([value for value in range(-12, 13) if value])
        constant = random_generator.randrange(-2 * modulus, 2 * modulus)
        preimage = _preimage_under_multiplication(target, multiplier, constant, domain)
        expected = {member for member in _members(domain) if target.contains(multiplier * member + constant)}
        assert preimage is not None and _members(preimage) == expected


def _decimal_step_block(modulus):
    """
    The block shape of a two-digit decimal step with signed wraparound, as reported for modulus `2**32`:

        48 <= x19, x20 <= 57,  0 <= x21 <= M/2 - 1,  M/2 <= x22 <= M - 1
        x20 + 10*x21 - x22 == 48 (mod M),   10*x1 + x19 - x21 == 48 (mod M)
    """
    half = modulus // 2
    bounds = {19: (48, 57), 20: (48, 57), 21: (0, half - 1), 22: (half, modulus - 1)}
    congruences = [([(1, 20), (10, 21), (modulus - 1, 22)], 48), ([(10, FREE_VAR_ID), (1, 19), (modulus - 1, 21)], 48)]
    return _build_block(modulus, bounds, congruences, [19, 20, 21, 22])


def _decimal_step_block_holds(x1, modulus):
    """
    Truth of `_decimal_step_block` for `x1`. C36 determines `x21` modulo M and its window is shorter than M,
    so `x21` exists exactly when the residue of `10*x1 + x19 - 48` lies in `[0, M/2 - 1]`; C35 determines
    `x22` the same way. Only `x19` and `x20` are enumerated.
    """
    half = modulus // 2
    for x19 in range(48, 58):
        x21 = (10 * x1 + x19 - 48) % modulus
        if x21 >= half:
            continue
        if any((x20 + 10 * x21 - 48) % modulus >= half for x20 in range(48, 58)):
            return True
    return False


def test_the_decimal_step_block_is_folded_exactly_at_a_reduced_modulus():
    modulus = 2**10
    quantifier = _decimal_step_block(modulus)
    stats = Modular_Bound_Rewrite_Stats()
    rewritten = propagate_modular_bounds(quantifier, _make_var_table([FREE_VAR_ID, 19, 20, 21, 22]), stats)

    assert stats.blocks_rewritten == 1 and stats.facts_emitted == 1
    assert _count_congruences(rewritten) == 1
    assert len(rewritten.bound_vars) == 1, 'only the witness of the single fact remains quantified'
    for x1 in range(modulus):
        assert _holds(rewritten, {Var(id=FREE_VAR_ID): x1}, lambda var: range(modulus)) \
            == _decimal_step_block_holds(x1, modulus), f'x1 = {x1}'


def test_the_decimal_step_block_is_folded_into_five_intervals_at_modulus_2_to_32():
    import random
    modulus = 2**32
    quantifier = _decimal_step_block(modulus)
    stats = Modular_Bound_Rewrite_Stats()
    rewritten = propagate_modular_bounds(quantifier, _make_var_table([FREE_VAR_ID, 19, 20, 21, 22]), stats)

    assert stats.blocks_rewritten == 1 and stats.facts_emitted == 1 and stats.intervals_emitted == 5
    congruence = next(child for child in rewritten.child.children if isinstance(child, Congruence))
    disjunction = next(child for child in rewritten.child.children
                       if isinstance(child, AST_Connective) and child.type == Connective_Type.OR)
    intervals = [(-alternative.children[0].rhs, alternative.children[1].rhs) for alternative in disjunction.children]

    def rewritten_holds(x1):
        witness_residue = (sum(coefficient * x1 for coefficient, var in zip(congruence.coefs, congruence.vars)
                               if var == Var(id=FREE_VAR_ID)) - congruence.rhs) % modulus
        return any(lower <= witness_residue <= upper for lower, upper in intervals)

    random_generator = random.Random(0)
    inverse_of_5 = pow(5, -1, 2**31)
    samples = [random_generator.randrange(modulus) for _ in range(2000)]
    for lower, upper in intervals:   # x1 values whose 10*x1 - 48 lands next to an interval endpoint
        for endpoint in (lower, upper):
            for offset in range(-12, 13):
                target = endpoint + 48 + offset
                if target % 2 == 0:
                    samples.append((target // 2 * inverse_of_5) % 2**31)
    for x1 in samples:
        assert rewritten_holds(x1) == _decimal_step_block_holds(x1, modulus), f'x1 = {x1}'


def test_random_blocks_keep_their_satisfying_sets():
    """ Random blocks over one free variable: every rewrite must preserve the satisfying set exactly. """
    import random
    random_generator = random.Random(7)
    rewritten_blocks = 0
    for _ in range(150):
        modulus = random_generator.choice([6, 8, 9, 10])
        bound_ids = [2, 3, 4, 5][:random_generator.randint(2, 4)]
        bounds = {}
        for var_id in bound_ids:
            lower = random_generator.randint(-2, modulus - 1)
            bounds[var_id] = (lower, lower + random_generator.randint(0, modulus // 2))
        congruences = []
        for _ in range(random_generator.randint(1, 3)):
            chosen = random_generator.sample([FREE_VAR_ID] + bound_ids, random_generator.randint(2, 3))
            congruences.append(([(random_generator.randint(-modulus + 1, modulus - 1) or 1, var_id) for var_id in chosen],
                                random_generator.randrange(modulus)))
        quantifier = _build_block(modulus, bounds, congruences, bound_ids)
        stats = Modular_Bound_Rewrite_Stats()
        rewritten = propagate_modular_bounds(quantifier, _make_var_table([FREE_VAR_ID] + bound_ids), stats)
        rewritten_blocks += stats.blocks_rewritten + stats.blocks_refuted

        search_ranges = {Var(id=var_id): range(lower, upper + 1) for var_id, (lower, upper) in bounds.items()}
        assert (_satisfying_free_values(quantifier, modulus, search_ranges)
                == _satisfying_free_values(rewritten, modulus, search_ranges,
                                           default_search_range=range(0, modulus))), (bounds, congruences)
    assert rewritten_blocks > 20, f'only {rewritten_blocks} of 150 blocks were rewritten'
