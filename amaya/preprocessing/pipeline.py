"""
A fixpoint scheduler for the formula-level optimization passes that
`amaya.parse.optimize_formula_structure` used to run as a hand-unrolled, fixed sequence.

See `OPTIMIZATION_PIPELINE.md` for the design and `OPTIMIZATION_PIPELINE_PLAN.md` for the
migration plan this module implements (steps 3-4). In short: every pass is wrapped behind one
uniform `Pass_Descriptor`, the passes are grouped into tiers by cost, and a worklist scheduler
re-runs a pass only when a fact it `consumes` may have been produced since it last ran. Change
detection is done with `structural_id.compute_structural_id`, using one `Structural_Id_Table` for
the whole pipeline run (a fresh table per measurement would make ids meaningless - see
`structural_id.py`'s docstring).
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from enum import IntEnum
from typing import Callable, Dict, List, Literal, Optional, Tuple

from amaya import logger
from amaya.config import OptimizationsConfig, SolverConfig
from amaya.preprocessing import flatten_bool_nary_connectives
from amaya.preprocessing.antiprenexing import miniscope_quantifiers
from amaya.preprocessing.conditional_equality_resolution import fill_referenced_vars, resolve_conditional_equalities
from amaya.preprocessing.connective_child_dedup import remove_duplicit_connective_children
from amaya.preprocessing.eval import VarInfo
from amaya.preprocessing.inner_quantifier_squeeze_elimination import eliminate_inner_quantifier_squeezes
from amaya.preprocessing.structural_id import Structural_Id_Table, compute_structural_id
from amaya.preprocessing.theory_reasoning import (
    Asserted_Model_Properties,
    Variable_Use_Info,
    remove_atoms_satisfied_by_unconstrained_vars,
    scan_variable_use,
    simplify_formula_using_model_properties,
)
import amaya.preprocessing.unbound_vars as var_bounds_lib
from amaya.relations_structures import AST_Connective, AST_Negation, AST_Quantifier, ASTp_Node, Var, format_formula


class Pass_Tier(IntEnum):
    NORMALIZE = 0   # re-run after every productive pass; ~free
    CORE = 1        # re-run whenever triggered
    HEAVY = 2       # rationed: at most `max_runs` times per pipeline run
    FINALIZE = 3    # run once, after the fixpoint loop has ended


@dataclass
class Pass_Context:
    """Immutable-ish side inputs threaded through every pass, plus scratch state for passes
    that need to carry something across their own consecutive invocations."""
    var_table: Dict[Var, VarInfo]
    scratch: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Pass_Descriptor:
    name: str
    """Stable identifier, used in reports, in the `-O` mapping and in tests."""

    config_flag: Optional[str]
    """Attribute on `OptimizationsConfig` gating this pass; None = unconditional."""

    run: Callable[[ASTp_Node, Pass_Context], ASTp_Node]
    """The pass itself, adapted to the uniform signature (see the `_pass_*` adapters below)."""

    tier: Pass_Tier

    consumes: frozenset
    """Facts whose (re)appearance makes this pass worth re-running."""

    produces: frozenset
    """Facts this pass may create when it fires."""

    max_runs: Optional[int] = None
    """Hard cap on invocations per pipeline run. None = unlimited (bounded by the fixpoint)."""

    growth_factor_limit: Optional[float] = None
    """
    If the pass increases the node count by more than this factor, its result is discarded.

    None disables the guard, which is right for a pass whose growth is the point rather than a symptom.
    Node count is a proxy for the cost of the formula, and it is a poor one wherever a rewrite trades
    nodes for something the node count does not see - the automaton for a congruence has states on the
    order of its modulus, so `linearize` removing one costs nodes and saves far more than it costs.
    """

    requires_referenced_vars: bool = False
    """Scheduler runs `fill_referenced_vars` first if the annotation may be stale."""

    self_triggering: bool = True
    """If True (the default), a productive run of this pass re-enqueues the pass itself, so it
    is driven to its own fixpoint: `f(f(x))` may differ from `f(x)` for most passes here (this is
    what the 9x CER / 2x model-reasoning / 3x unconstrained-vars hand-unrollings depended on).
    Set to False only for a pass *measured* to run productively at most once (see design §9)."""


def _pass_var_bounds(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    result = var_bounds_lib.simplify_bounded_atoms(ast)
    return ast if result is None else result  # signature is Optional; None never observed in practice


def _pass_congruences_on_unbound(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    return var_bounds_lib.simplify_congruences_on_unbounded_existential_vars(ast, ctx.var_table)


def _pass_infinite_domain(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    return var_bounds_lib.remove_vars_with_no_consequences_on_the_model(ast, ctx.var_table)


def _pass_model_properties(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    # `Asserted_Model_Properties` is a stateful accumulator. `parse.py`'s legacy body threads one
    # instance through two consecutive calls; here it is fresh per invocation, which is the safer
    # default (see OPTIMIZATION_PIPELINE.md §5.2 / §3 of the plan). This is a known, deliberate
    # deviation validated by the differential run (plan step 7). If that run shows a regression,
    # thread one accumulator via `ctx.scratch` instead.
    return simplify_formula_using_model_properties(ast, Asserted_Model_Properties())


def _pass_unconstrained_vars(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    # Fixes P3: the variable-use scan is redone against the *current* formula on every invocation,
    # instead of being computed once and consulted by three calls against a formula that has
    # since changed underneath it.
    var_uses = Variable_Use_Info()
    scan_variable_use(ast, var_uses)
    return remove_atoms_satisfied_by_unconstrained_vars(ast, var_uses, desired_polarity=True)


def _pass_dedup_connective_children(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    return remove_duplicit_connective_children(ast)


def _pass_squeeze_elimination(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    return eliminate_inner_quantifier_squeezes(ast, ctx.var_table)


def _pass_fill_referenced_vars(ast: ASTp_Node, ctx: Pass_Context) -> ASTp_Node:
    fill_referenced_vars(ast)
    return ast


# --- fact vocabulary (see OPTIMIZATION_PIPELINE.md §5.3) ----------------------------------------
# Deliberately coarse tags naming *kinds* of opportunity, not a fine-grained dependency calculus.
# Over-approximating a trigger costs one wasted traversal; under-approximating loses an
# optimization - so when in doubt a pass's `consumes`/`produces` should include the tag.

NARY_SHAPE = 'nary-shape'
BOOL_LITERAL = 'bool-literal'
DUPLICATE_CHILDREN = 'duplicate-children'
NEGATION_SHAPE = 'negation-shape'
ATOM_REWRITTEN = 'atom-rewritten'
BOUNDS_TIGHTENED = 'bounds-tightened'
VAR_ELIMINATED = 'var-eliminated'
QUANTIFIER_SHAPE = 'quantifier-shape'
EQUALITY_EXPOSED = 'equality-exposed'
SUBTREE_REMOVED = 'subtree-removed'


def _registry_definition() -> List[Pass_Descriptor]:
    """The full, unfiltered registry, in registration order. Tier 0 before tier 1 before tier 2
    before tier 3, and registration order within a tier, matching (tier, index) ordering used by
    the scheduler (§6.2) and preserving the intent of the legacy hand-written sequence: normalise,
    then cheap analyses, then expensive structural rewrites."""
    return [
        # --- Tier 0: NORMALIZE ------------------------------------------------------------------
        Pass_Descriptor(
            name='flatten-connectives', config_flag=None, run=lambda ast, ctx: flatten_bool_nary_connectives(ast),
            tier=Pass_Tier.NORMALIZE,
            consumes=frozenset({NARY_SHAPE, SUBTREE_REMOVED}),
            produces=frozenset({NARY_SHAPE, DUPLICATE_CHILDREN}),
        ),
        Pass_Descriptor(
            name='stomp-negations', config_flag='push_negation_towards_atoms',
            run=lambda ast, ctx: var_bounds_lib.push_negations_towards_atoms(ast),
            tier=Pass_Tier.NORMALIZE,
            consumes=frozenset({NEGATION_SHAPE, NARY_SHAPE}),
            produces=frozenset({NARY_SHAPE, ATOM_REWRITTEN, NEGATION_SHAPE}),
        ),
        Pass_Descriptor(
            name='dedup-connective-children', config_flag='deduplicate_connective_children',
            run=_pass_dedup_connective_children,
            tier=Pass_Tier.NORMALIZE,
            consumes=frozenset({DUPLICATE_CHILDREN, NARY_SHAPE}),
            produces=frozenset({NARY_SHAPE, SUBTREE_REMOVED}),
        ),

        # --- Tier 1: CORE ------------------------------------------------------------------------
        Pass_Descriptor(
            name='var-bounds', config_flag='simplify_variable_bounds', run=_pass_var_bounds,
            tier=Pass_Tier.CORE,
            consumes=frozenset({ATOM_REWRITTEN, BOUNDS_TIGHTENED, NARY_SHAPE}),
            produces=frozenset({ATOM_REWRITTEN, BOUNDS_TIGHTENED, BOOL_LITERAL}),
        ),
        Pass_Descriptor(
            name='interval-analysis', config_flag='do_interval_analysis',
            run=lambda ast, ctx: var_bounds_lib.prune_conjunctions_false_due_to_parent_context(ast),
            tier=Pass_Tier.CORE,
            consumes=frozenset({BOUNDS_TIGHTENED, ATOM_REWRITTEN, VAR_ELIMINATED, NARY_SHAPE}),
            produces=frozenset({BOOL_LITERAL, ATOM_REWRITTEN, NARY_SHAPE}),
        ),
        Pass_Descriptor(
            name='model-reasoning', config_flag='reason_about_models', run=_pass_model_properties,
            tier=Pass_Tier.CORE,
            consumes=frozenset({EQUALITY_EXPOSED, ATOM_REWRITTEN, BOOL_LITERAL, NARY_SHAPE}),
            produces=frozenset({BOOL_LITERAL, ATOM_REWRITTEN, SUBTREE_REMOVED}),
        ),
        Pass_Descriptor(
            name='unconstrained-vars', config_flag='reason_about_models', run=_pass_unconstrained_vars,
            tier=Pass_Tier.CORE,
            consumes=frozenset({VAR_ELIMINATED, SUBTREE_REMOVED, ATOM_REWRITTEN}),
            produces=frozenset({BOOL_LITERAL, SUBTREE_REMOVED}),
        ),
        Pass_Descriptor(
            name='inline-bool-definitions', config_flag='inline_bool_var_definitions',
            run=lambda ast, ctx: var_bounds_lib.inline_bool_var_definitions(ast),
            tier=Pass_Tier.CORE,
            consumes=frozenset({EQUALITY_EXPOSED, NARY_SHAPE, SUBTREE_REMOVED}),
            produces=frozenset({SUBTREE_REMOVED, NARY_SHAPE, VAR_ELIMINATED}),
        ),
        Pass_Descriptor(
            name='squeeze-elimination', config_flag='eliminate_squeezed_inner_quantifiers',
            run=_pass_squeeze_elimination,
            tier=Pass_Tier.CORE, growth_factor_limit=1.2,
            consumes=frozenset({QUANTIFIER_SHAPE, ATOM_REWRITTEN, NARY_SHAPE, BOUNDS_TIGHTENED}),
            produces=frozenset({VAR_ELIMINATED, QUANTIFIER_SHAPE, ATOM_REWRITTEN, NARY_SHAPE, BOOL_LITERAL}),
            requires_referenced_vars=True,
        ),
        Pass_Descriptor(
            name='rce', config_flag='resolve_conditional_equalities',
            run=lambda ast, ctx: resolve_conditional_equalities(ast),
            tier=Pass_Tier.CORE,
            consumes=frozenset({NARY_SHAPE, EQUALITY_EXPOSED, QUANTIFIER_SHAPE, VAR_ELIMINATED}),
            produces=frozenset({EQUALITY_EXPOSED, VAR_ELIMINATED, QUANTIFIER_SHAPE, NARY_SHAPE}),
            requires_referenced_vars=True,
        ),

        # --- Tier 2: HEAVY (rationed) --------------------------------------------------------------
        # `gcd-rewrite` and `infinite-domain` were originally tier 1 (design doc §5.4's initial
        # hypothesis); demoted here per plan step 9 after measuring a 0.9% and 2.0% hit rate
        # respectively over a ~160-formula sample of `benchmarks/formulae/**` (well under the
        # design's ~5% tier-0/1 threshold) - see PROGRESS.md. Neither pass grows the tree, so no
        # `growth_factor_limit`; `max_runs` alone rations the wasted-traversal cost of a pass that
        # rarely fires. This is a preliminary retuning from a partial (local, LIA-only, non-
        # containerized) sample, not the full corpus gate of step 7/9 - revisit once that lands.
        Pass_Descriptor(
            name='gcd-rewrite', config_flag='rewrite_existential_equations_via_gcd',
            run=lambda ast, ctx: var_bounds_lib.simplify_unbounded_equations(ast),
            tier=Pass_Tier.HEAVY, max_runs=3,
            consumes=frozenset({QUANTIFIER_SHAPE, EQUALITY_EXPOSED, ATOM_REWRITTEN}),
            produces=frozenset({ATOM_REWRITTEN, VAR_ELIMINATED, QUANTIFIER_SHAPE}),
        ),
        Pass_Descriptor(
            name='infinite-domain', config_flag='remove_vars_used_only_in_disequalities',
            run=_pass_infinite_domain,
            tier=Pass_Tier.HEAVY, max_runs=3,
            consumes=frozenset({VAR_ELIMINATED, QUANTIFIER_SHAPE, SUBTREE_REMOVED}),
            produces=frozenset({VAR_ELIMINATED, QUANTIFIER_SHAPE, SUBTREE_REMOVED}),
        ),
        Pass_Descriptor(
            name='miniscope', config_flag='do_miniscoping',
            run=lambda ast, ctx: miniscope_quantifiers(ast),
            tier=Pass_Tier.HEAVY, max_runs=2, growth_factor_limit=1.5,
            consumes=frozenset({QUANTIFIER_SHAPE, NARY_SHAPE, VAR_ELIMINATED}),
            produces=frozenset({QUANTIFIER_SHAPE, NARY_SHAPE}),
        ),
        Pass_Descriptor(
            name='opt-bottom-exists', config_flag='optimize_bottom_quantifiers',
            run=lambda ast, ctx: var_bounds_lib.optimize_bottom_quantifiers(ast),
            tier=Pass_Tier.HEAVY, max_runs=2, growth_factor_limit=1.2,
            consumes=frozenset({QUANTIFIER_SHAPE, BOUNDS_TIGHTENED, ATOM_REWRITTEN}),
            produces=frozenset({VAR_ELIMINATED, QUANTIFIER_SHAPE, ATOM_REWRITTEN, BOOL_LITERAL}),
        ),
        Pass_Descriptor(
            name='minimize-congruences', config_flag='rewrite_congruences_with_unbound_terms',
            run=_pass_congruences_on_unbound,
            tier=Pass_Tier.HEAVY, max_runs=2, growth_factor_limit=1.2,
            consumes=frozenset({QUANTIFIER_SHAPE, ATOM_REWRITTEN}),
            produces=frozenset({ATOM_REWRITTEN, VAR_ELIMINATED}),
        ),
        Pass_Descriptor(
            name='linearize', config_flag='linearize_congruences',
            run=lambda ast, ctx: var_bounds_lib.linearize_congruences(ast),
            # No growth guard: node count is not a proxy for what this pass costs or saves. The
            # automaton for a congruence has states on the order of its modulus, so replacing one of
            # modulus 299909 by an equation removes ~300k states in exchange for four nodes - the
            # growth is the point of the pass, not a symptom to ration. Its output is bounded anyway:
            # `unbound_vars._should_linearize` declines a congruence whose variable range spans more
            # than four strides, and `max_runs=1` bounds the applications.
            tier=Pass_Tier.HEAVY, max_runs=1, growth_factor_limit=None,
            consumes=frozenset({ATOM_REWRITTEN, BOUNDS_TIGHTENED}),
            produces=frozenset({ATOM_REWRITTEN, EQUALITY_EXPOSED}),
        ),
        Pass_Descriptor(
            name='iso-conflicts', config_flag='detect_isomorphic_conflicts',
            run=lambda ast, ctx: var_bounds_lib.detect_conflics_on_isomorphic_fragments(ast),
            tier=Pass_Tier.HEAVY, max_runs=1, growth_factor_limit=1.0,
            consumes=frozenset({NARY_SHAPE, SUBTREE_REMOVED}),
            produces=frozenset({BOOL_LITERAL, SUBTREE_REMOVED}),
        ),
        Pass_Descriptor(
            name='light-sat', config_flag='do_light_sat_reasoning',
            run=lambda ast, ctx: var_bounds_lib.convert_and_or_trees_to_dnf_if_talking_about_similar_atoms(ast),
            tier=Pass_Tier.HEAVY, max_runs=1, growth_factor_limit=2.0,
            consumes=frozenset({NARY_SHAPE, ATOM_REWRITTEN}),
            produces=frozenset({NARY_SHAPE, BOOL_LITERAL, SUBTREE_REMOVED}),
        ),

        # --- Tier 3: FINALIZE (run once, after the loop) -----------------------------------------
        Pass_Descriptor(
            name='finalize-flatten', config_flag=None, run=lambda ast, ctx: flatten_bool_nary_connectives(ast),
            tier=Pass_Tier.FINALIZE, consumes=frozenset(), produces=frozenset(),
        ),
        Pass_Descriptor(
            name='finalize-dedup', config_flag='deduplicate_connective_children',
            run=_pass_dedup_connective_children,
            tier=Pass_Tier.FINALIZE, consumes=frozenset(), produces=frozenset(),
        ),
        Pass_Descriptor(
            name='finalize-refvars', config_flag=None, run=_pass_fill_referenced_vars,
            tier=Pass_Tier.FINALIZE, consumes=frozenset(), produces=frozenset(),
        ),
    ]


def build_registry(solver_config: SolverConfig) -> List[Pass_Descriptor]:
    """
    Return the registered passes, in registration order, filtered to those enabled by
    `solver_config.optimizations` (a descriptor with `config_flag=None` is always included).
    """
    optimizations = solver_config.optimizations
    registry = []
    for descriptor in _registry_definition():
        if descriptor.config_flag is None or getattr(optimizations, descriptor.config_flag):
            registry.append(descriptor)
    return registry


def _quantifier_count(ast: ASTp_Node) -> int:
    match ast:
        case AST_Quantifier():
            return 1 + _quantifier_count(ast.child)
        case AST_Negation():
            return _quantifier_count(ast.child)
        case AST_Connective():
            return sum(_quantifier_count(child) for child in ast.children)
        case _:
            return 0


def _default_max_pass_applications(formula_size: int) -> int:
    """
    32 pass applications per 1000 formula nodes, clamped to [256, 512].

    The floor was originally 32 (design doc default); measured against a ~160-formula sample of
    `benchmarks/formulae/**` (6 to 16000 nodes), it reaches a clean fixpoint using at most ~216
    total pass applications *regardless of formula size* - the ceiling is driven by how many
    rounds it takes the ~20-pass registry to stop triggering each other, not by node count, so
    the per-1000-nodes scaling barely matters below very large formulas. With the original floor
    of 32, ~78% of that sample was cut short by the budget before reaching a real fixpoint. 256
    gives ~20% headroom over the observed maximum; see OPTIMIZATION_PIPELINE_PLAN.md step 9 /
    PROGRESS.md for the measurement this is based on.
    """
    raw = round(formula_size * 32 / 1000)
    return max(256, min(512, raw))


@dataclass
class Pass_Stats:
    name: str
    invocations: int = 0
    productive: int = 0
    discarded_for_growth: int = 0
    total_time_ns: int = 0
    nodes_removed: int = 0  # cumulative, over productive runs only


@dataclass
class Pipeline_Report:
    pass_stats: Dict[str, Pass_Stats]
    rounds: int
    termination: Literal['fixpoint', 'cycle', 'budget', 'time']
    input_size: int
    output_size: int
    pass_sequence: List[str]  # for reproducing / debugging a specific run
    trace: List[Tuple[str, ASTp_Node]] = field(default_factory=list)
    """
    (pass name, resulting formula) for every productive pass application, in the order they were
    applied, followed by one entry per finalizer - only populated when `Optimization_Pipeline.trace`
    is set. See `format_formula` to render an entry's formula.
    """


@dataclass
class Optimization_Pipeline:
    """
    A worklist scheduler over `registry` (as returned by `build_registry`, or a synthetic list of
    descriptors for testing): passes run to a fixpoint instead of a fixed, hand-unrolled sequence.
    See OPTIMIZATION_PIPELINE.md §6 for the design this implements.
    """
    registry: List[Pass_Descriptor]
    var_table: Dict[Var, VarInfo]
    max_pass_applications: Optional[int] = None
    max_wall_time_seconds: float = 0.0
    trace: bool = False
    """Log (and collect into `report.trace`) the formula produced by every productive pass
    application, alongside the name of the pass that produced it. See `OptimizationPipelineConfig.trace`."""

    report: Optional[Pipeline_Report] = field(default=None, init=False, compare=False)

    def run(self, astp: ASTp_Node) -> ASTp_Node:
        main_passes = [d for d in self.registry if d.tier != Pass_Tier.FINALIZE]
        finalization_passes = [d for d in self.registry if d.tier == Pass_Tier.FINALIZE]
        pass_by_name_table = {d.name: d for d in main_passes}
        pass_order_by_name = {d.name: i for i, d in enumerate(main_passes)}

        ctx = Pass_Context(var_table=self.var_table)
        id_table = Structural_Id_Table()

        stats = {d.name: Pass_Stats(name=d.name) for d in main_passes + finalization_passes}
        pass_sequence: List[str] = []
        trace: List[Tuple[str, ASTp_Node]] = []
        run_count: Dict[str, int] = {d.name: 0 for d in main_passes}
        last_run_fingerprint: Dict[str, int] = {}

        current = astp
        current_fingerprint, current_size = compute_structural_id(current, id_table)
        input_size = current_size
        seen_fingerprints = {current_fingerprint}

        def score(node: ASTp_Node, size: int):
            return (size, _quantifier_count(node))

        best, best_score = current, score(current, current_size)

        worklist = {d.name for d in main_passes}
        # Conservative on entry: a pass upstream of the pipeline may have left `referenced_vars`
        # stale (only `preprocess_ast` is guaranteed to maintain it), so the first pass that
        # requires it gets one repair for free, mirroring the legacy defensive call.
        refvars_stale = True

        max_applications = self.max_pass_applications
        if max_applications is None:
            max_applications = _default_max_pass_applications(current_size)

        total_applications = 0
        start_time = time.monotonic()
        termination: Literal['fixpoint', 'cycle', 'budget', 'time'] = 'fixpoint'

        while True:
            if not worklist:
                break

            if total_applications >= max_applications:
                termination = 'budget'
                logger.warning('Optimization pipeline exhausted its budget (%d applications) with '
                                '%d pass(es) still pending: %s', max_applications, len(worklist),
                                sorted(worklist))
                break

            if self.max_wall_time_seconds and (time.monotonic() - start_time) > self.max_wall_time_seconds:
                termination = 'time'
                logger.warning('Optimization pipeline exceeded its wall-time budget (%.2fs) with '
                                '%d pass(es) still pending: %s', self.max_wall_time_seconds,
                                len(worklist), sorted(worklist))
                break

            pass_name = min(worklist, key=lambda name: (pass_by_name_table[name].tier, pass_order_by_name[name]))
            worklist.discard(pass_name)
            _pass = pass_by_name_table[pass_name]

            if last_run_fingerprint.get(pass_name) == current_fingerprint:
                continue  # p has already run against exactly this formula

            if _pass.requires_referenced_vars and refvars_stale:
                fill_referenced_vars(current)
                refvars_stale = False

            pass_stats = stats[pass_name]
            t0 = time.perf_counter_ns()
            candidate_formula = _pass.run(current, ctx)
            pass_stats.total_time_ns += time.perf_counter_ns() - t0

            run_count[pass_name] += 1
            total_applications += 1
            last_run_fingerprint[pass_name] = current_fingerprint
            pass_stats.invocations += 1

            candidate_fingerprint, cand_size = compute_structural_id(candidate_formula, id_table)

            if _pass.growth_factor_limit is not None and cand_size > _pass.growth_factor_limit * current_size:
                pass_stats.discarded_for_growth += 1
                continue  # `current` untouched

            if candidate_fingerprint == current_fingerprint:
                continue  # no facts produced, nothing re-enqueued

            # --- the pass was productive ---
            pass_stats.productive += 1
            if cand_size < current_size:
                pass_stats.nodes_removed += current_size - cand_size
            pass_sequence.append(pass_name)

            if self.trace:
                trace.append((pass_name, candidate_formula))
                logger.info('Optimization pipeline trace - after %s:\n%s', pass_name, format_formula(candidate_formula))

            facts = set(_pass.produces)
            if cand_size < current_size:
                facts.add(SUBTREE_REMOVED)

            current, current_fingerprint, current_size = candidate_formula, candidate_fingerprint, cand_size
            refvars_stale = True

            current_score = score(current, current_size)
            if current_score < best_score:
                best, best_score = current, current_score

            if candidate_fingerprint in seen_fingerprints:
                termination = 'cycle'
                logger.warning('Optimization pipeline detected a cycle after %s; returning the '
                                'best formula seen so far.', pass_name)
                break
            seen_fingerprints.add(candidate_fingerprint)

            for pass_to_queue in main_passes:
                if not (facts & pass_to_queue.consumes):
                    continue
                if pass_to_queue.name == pass_name and not pass_to_queue.self_triggering:
                    continue
                if pass_to_queue.max_runs is not None and run_count[pass_to_queue.name] >= pass_to_queue.max_runs:
                    continue
                worklist.add(pass_to_queue.name)

        result = current if termination == 'fixpoint' else best

        for f in finalization_passes:
            fstat = stats[f.name]
            t0 = time.perf_counter_ns()
            result = f.run(result, ctx)
            fstat.total_time_ns += time.perf_counter_ns() - t0
            fstat.invocations += 1
            fstat.productive += 1

            if self.trace:
                trace.append((f.name, result))
                logger.info('Optimization pipeline trace - after %s:\n%s', f.name, format_formula(result))

        _, output_size = compute_structural_id(result, id_table)

        self.report = Pipeline_Report(
            pass_stats=stats,
            rounds=len(pass_sequence),
            termination=termination,
            input_size=input_size,
            output_size=output_size,
            pass_sequence=pass_sequence,
            trace=trace,
        )

        return result
