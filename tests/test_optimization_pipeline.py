"""
Tests for `amaya.preprocessing.pipeline.Optimization_Pipeline` (plan step 4).

These are driven by synthetic `Pass_Descriptor`s over hand-built trees, not the real passes -
the point is to pin down the scheduler's mechanics (fixpoint, cycle detection, growth guard,
budgets, self-triggering, determinism), independent of anything a real pass happens to do.

The "formula" the synthetic passes operate over is a single `AST_Connective` whose
`variable_bounds` dict is abused as a free-form counter/tag bag, since the scheduler only cares
about the tree's structural fingerprint (via `compute_structural_id`) and never inspects
`variable_bounds` itself. Each synthetic pass rebuilds the node with a different number of
`Relation` children to make the change (or non-change) visible to the fingerprint.
"""
from amaya.preprocessing.pipeline import (
    Optimization_Pipeline,
    Pass_Context,
    Pass_Descriptor,
    Pass_Tier,
    _default_max_pass_applications,
)
from amaya.relations_structures import AST_Connective, Connective_Type, Relation, Var


X = Var(id=1)


def _rel(rhs: int) -> Relation:
    """A distinct atom for every distinct `rhs`, so children can be told apart by the fingerprint."""
    return Relation(vars=[X], coefs=[1], rhs=rhs, predicate_symbol='<=')


def _tree(width: int) -> AST_Connective:
    """A conjunction of `width` structurally-distinct atoms."""
    return AST_Connective(referenced_vars=(X,), type=Connective_Type.AND,
                          children=tuple(_rel(i) for i in range(width)))


def _grow_pass(name: str, tier: Pass_Tier = Pass_Tier.CORE, **kwargs) -> Pass_Descriptor:
    """A pass that adds one fresh atom to the tree every time it runs, up to `stop_at` children -
    a controllable, non-idempotent-by-construction pass (`f(f(x)) != f(x)` until it saturates)."""
    stop_at = kwargs.pop('stop_at', 10**9)

    def run(ast: AST_Connective, ctx: Pass_Context) -> AST_Connective:
        if len(ast.children) >= stop_at:
            return ast
        new_child = _rel(len(ast.children) + 1000)
        return AST_Connective(referenced_vars=ast.referenced_vars, type=ast.type,
                              children=ast.children + (new_child,))

    return Pass_Descriptor(name=name, config_flag=None, run=run, tier=tier, **kwargs)


def _noop_pass(name: str, tier: Pass_Tier = Pass_Tier.CORE, **kwargs) -> Pass_Descriptor:
    def run(ast: AST_Connective, ctx: Pass_Context) -> AST_Connective:
        return ast

    return Pass_Descriptor(name=name, config_flag=None, run=run, tier=tier, **kwargs)


def test_fixpoint_is_reached_and_reported():
    registry = [_noop_pass('noop', consumes=frozenset(), produces=frozenset())]

    pipeline = Optimization_Pipeline(registry, var_table={})
    result = pipeline.run(_tree(3))

    assert pipeline.report.termination == 'fixpoint'
    assert result == _tree(3)


def test_self_triggering_pass_is_driven_to_its_own_fixpoint():
    # A pass needing several applications to saturate must actually receive them - this is the
    # direct regression test for `self_triggering` defaulting to True (design P1).
    grower = _grow_pass('grower', stop_at=5, consumes=frozenset({'grow'}), produces=frozenset({'grow'}))

    pipeline = Optimization_Pipeline([grower], var_table={})
    result = pipeline.run(_tree(1))

    assert pipeline.report.termination == 'fixpoint'
    assert len(result.children) == 5
    assert pipeline.report.pass_stats['grower'].productive == 4  # 1 -> 2 -> 3 -> 4 -> 5


def test_non_self_triggering_pass_runs_only_once_productively():
    grower = _grow_pass('grower', stop_at=5, self_triggering=False,
                        consumes=frozenset({'grow'}), produces=frozenset({'grow'}))

    pipeline = Optimization_Pipeline([grower], var_table={})
    result = pipeline.run(_tree(1))

    assert len(result.children) == 2  # only the first application ran
    assert pipeline.report.pass_stats['grower'].productive == 1


def test_cycle_detection_fires_and_returns_best():
    # Two passes that flip a tree of width 1 and width 2 back and forth forever.
    def to_two(ast, ctx):
        return _tree(2)

    def to_one(ast, ctx):
        return _tree(1)

    grow = Pass_Descriptor(name='grow', config_flag=None, run=to_two, tier=Pass_Tier.CORE,
                           consumes=frozenset({'shrink'}), produces=frozenset({'grow'}))
    shrink = Pass_Descriptor(name='shrink', config_flag=None, run=to_one, tier=Pass_Tier.CORE,
                             consumes=frozenset({'grow'}), produces=frozenset({'shrink'}))

    pipeline = Optimization_Pipeline([grow, shrink], var_table={})
    result = pipeline.run(_tree(1))

    assert pipeline.report.termination == 'cycle'
    # `best` is chosen by (node_count, quantifier_count); both candidates tie at 1 top-level
    # node count difference (width 1 vs width 2), so `best` must be the smaller of the two.
    assert len(result.children) == 1


def test_growth_guard_discards_result_but_still_charges_run_count():
    # `grower`'s output always exceeds its own growth budget, so on its own it would never be
    # re-enqueued past its first (discarded) run - discarding does not re-trigger anything. A
    # companion pass ('ticker') that legitimately grows the tree three times, and also produces
    # the fact `grower` consumes, is what repeatedly re-queues `grower` here; this mirrors the
    # real risk (OPTIMIZATION_PIPELINE.md's risk table): a heavy pass kept alive by *other*
    # passes' progress even though its own result is always thrown away.
    # `grower` is given priority (tier 0) over `ticker` (tier 1) so that whenever both are queued
    # in the same round, `grower` is the one popped and charged - otherwise `ticker`'s own
    # self-triggering re-enqueue would keep winning every tie-break and `grower` would starve.
    ticker = _grow_pass('ticker', tier=Pass_Tier.CORE, stop_at=4,
                        consumes=frozenset({'grow'}), produces=frozenset({'grow'}))
    grower = _grow_pass('grower', tier=Pass_Tier.NORMALIZE, growth_factor_limit=1.0, max_runs=3,
                        consumes=frozenset({'grow'}), produces=frozenset({'grow'}))

    pipeline = Optimization_Pipeline([ticker, grower], var_table={})
    pipeline.run(_tree(1))

    # The pass must be charged for every attempt, up to its cap, even though every one of those
    # attempts was discarded for growth.
    assert pipeline.report.pass_stats['grower'].invocations == 3
    assert pipeline.report.pass_stats['grower'].discarded_for_growth == 3
    assert pipeline.report.pass_stats['grower'].productive == 0


def test_budget_exhaustion_returns_best_clean_fixpoint_returns_current():
    # A pass that never saturates, so the loop can only stop via the budget.
    grower = _grow_pass('grower', stop_at=10**9,
                        consumes=frozenset({'grow'}), produces=frozenset({'grow'}))

    budgeted = Optimization_Pipeline([grower], var_table={}, max_pass_applications=3)
    input_tree = _tree(1)
    result = budgeted.run(input_tree)

    assert budgeted.report.termination == 'budget'
    assert budgeted.report.pass_stats['grower'].invocations == 3
    # `best` is picked by node count; a pass that only ever grows the tree never improves on the
    # input, so on an abnormal (budget) exit the pipeline must fall back to the input formula
    # rather than accept the larger `current`.
    assert result == input_tree

    # A pass that saturates within the budget reaches a real fixpoint and returns `current` (its
    # own, grown, output) instead of `best`.
    capped = _grow_pass('grower', stop_at=4, consumes=frozenset({'grow'}), produces=frozenset({'grow'}))
    clean = Optimization_Pipeline([capped], var_table={})
    clean_result = clean.run(_tree(1))

    assert clean.report.termination == 'fixpoint'
    assert len(clean_result.children) == 4


def test_pass_is_not_rerun_against_a_fingerprint_it_has_already_seen():
    calls = []

    def run(ast, ctx):
        calls.append(len(ast.children))
        return ast  # never changes anything

    other_calls = []

    def other_run(ast, ctx):
        other_calls.append(1)
        return ast

    noop = Pass_Descriptor(name='noop', config_flag=None, run=run, tier=Pass_Tier.CORE,
                           consumes=frozenset({'x'}), produces=frozenset({'x'}))
    # Re-triggers `noop` every round without ever changing the tree, to see whether `noop` is
    # actually skipped the second time it would see the same formula.
    retrigger = Pass_Descriptor(name='retrigger', config_flag=None, run=other_run, tier=Pass_Tier.CORE,
                                consumes=frozenset(), produces=frozenset({'x'}), self_triggering=False)

    pipeline = Optimization_Pipeline([noop, retrigger], var_table={})
    pipeline.run(_tree(2))

    # `noop` runs once on the initial enqueue; `retrigger`'s production of 'x' would ask for it
    # again, but `noop` already saw this exact fingerprint, so it must not run a second time.
    assert calls == [2]


def test_determinism_same_input_twice_yields_identical_pass_sequence():
    grower_a = _grow_pass('a', tier=Pass_Tier.NORMALIZE, stop_at=3,
                          consumes=frozenset({'x'}), produces=frozenset({'x'}))
    grower_b = _grow_pass('b', tier=Pass_Tier.CORE, stop_at=4,
                          consumes=frozenset({'x'}), produces=frozenset({'x'}))

    def run_once():
        pipeline = Optimization_Pipeline([grower_a, grower_b], var_table={})
        pipeline.run(_tree(1))
        return pipeline.report.pass_sequence

    assert run_once() == run_once()


def test_default_budget_floor_is_256_not_the_original_32():
    # Regression for a measured issue (see pipeline.py's docstring / PROGRESS.md step 9): with a
    # floor of 32, ~78% of a real benchmark sample was cut short by the budget before reaching a
    # genuine fixpoint, because ~20 registered passes each needing a few rounds already exceeds
    # 32 applications on formulae far smaller than 1000 nodes.
    assert _default_max_pass_applications(0) == 256
    assert _default_max_pass_applications(10) == 256
    assert _default_max_pass_applications(1000) == 256  # 32 per 1000 nodes is still below the floor
    assert _default_max_pass_applications(100_000) == 512  # clamped to the cap
