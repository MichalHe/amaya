from dataclasses import (
    dataclass,
    field,
)
from enum import IntEnum
from typing import Dict, Optional


class SolutionDomain(IntEnum):
    NATURALS = 0
    INTEGERS = 1


class BackendType(IntEnum):
    NATIVE = 1
    MTBDD = 2


class MinimizationAlgorithms(IntEnum):
    NONE = 0
    HOPCROFT = 1
    BRZOZOWSKI = 2


@dataclass
class BackendConfig(object):
    use_bit_set_pad_closure: bool = True
    """
    Represent the pad-closure frontier as a bit set indexed by state number instead of a sorted
    vector of states. Both implementations compute the same frontier with the same number of MTBDD
    applications; the bit set makes every leaf update a fixed-width word copy instead of copying and
    re-sorting a vector that grows with the frontier, which is where the old representation spent
    its time. Only worth turning off for automata so large that a full |Q|-bit frontier leaf costs
    more to copy than the handful of states the frontier actually holds.
    """


@dataclass
class OptimizationsConfig:
    allow_sharding: bool = False
    """ Perform top-level sharding. """

    simplify_variable_bounds: bool = False
    """Simplify hard variable bounds, e.g, x >= 0 && x != 0 ---> x >= 1."""

    rewrite_existential_equations_via_gcd: bool = False
    """Rewrite (exists x (= k*x y)) into (y mod k) = 0."""

    push_negation_towards_atoms: bool = False
    """Push negations as close to atoms as possible."""

    remove_vars_used_only_in_disequalities: bool = False
    """
    Drop existentially quantified variables (of an infinite sort) that occur only in disequalities.

    Example:
        (exists ((x Int)) (and (<= y 0) (not (= x 5))))   --->   (<= y 0)
    """

    do_interval_analysis: bool = True
    """
    Use interval analysis to prune the formula from simple conflicting clauses.

    Examle:
        parent asserts x >= 4 and a child asserts that x <= 2
    """

    do_light_sat_reasoning: bool = False
    """Detect AND-OR trees and convert them into DNF form and detect contradictions."""

    do_lazy_evaluation: bool = False
    """Enable lazy evaluation of subformulae of the form `(exists (..) (and atom1 atom2 ...))`"""

    do_miniscoping: bool = False
    """ Perform miniscoping (antiprenexing) on the formula. """

    do_gcd_divide: bool = True
    """ Divide atoms by the GCD of their coefficients. """

    rewrite_by_overapprox_relation_rhs: bool = False
    """ Compute overapproximation of relation's RHS and check whether the relation is always True/False. """

    rewrite_congruences_with_unbound_terms: bool = False
    """ Rewrite congruences a.x + b.y ~ k into a.x + gcd(b).y' ~ k """

    detect_isomorphic_conflicts: bool = False
    """
    Detect conflicts in (and A (not A)) if A and not A are the same modulo bound variable renaming.

    Isomorphism is underapproximated at the moment using the first naive permutation of quantified variables.
    """

    linearize_similar_mod_terms: bool = False
    """Introduce a linear relations between two variables for similar mod terms instead of using congruences."""

    reorder_conjunctions: bool = False
    """Reorder conjunctions to derive conflict more quickly."""

    do_interval_reasonining_twice: bool = False
    """If True, and do_interval_analysis is True, then an additional pass of tree pruning will be done at the end of preprocessing."""

    linearize_congruences: bool = False
    """Convert congruences to linear functions where possible."""

    optimize_bottom_quantifiers: bool = False
    """
    Optimize bottom existential quantifiers.

    Optimizations:
        - remove (exists x PHI) if PHI can be satisfied wlog by setting x to +Inf or -Inf
        - remove (exists x PHI) if a fixed "best" value can be determined for x
    """

    flatten_connectives: bool = False
    """ Convert sequances of (binary) ANDs/ORs into one N-ary node. """

    reason_about_models: bool = False
    """ Reason about models of a superformula to simplify subformulae. """

    inline_bool_var_definitions: bool = False
    """
    Inline unconditionally-true "definitions" of Bool variables, e.g. conjuncts of the form `(= bool_var phi)`,
    by substituting every occurrence of bool_var with phi and dropping the now-tautological equivalence.

    Example:
        (and (= b (or x y)) (or b z))   --->   (or x y z)
    """

    deduplicate_connective_children: bool = False
    """
    Remove duplicit children of the AND/OR/EQUIV connectives. The subformulae are identified using
    IDs assigned to them based on their structure, so the duplicities are detected modulo the ordering
    of the children of a connective and the ordering of the terms of an atom.

    Example:
        (and (<= x 0) (or A B) (<= x 0))   --->   (and (<= x 0) (or A B))
    """

    resolve_conditional_equalities: bool = False
    """
    Eliminate existentially quantified variables occurring only in "conditional equalities" hidden
    inside disjunctions.

    Example:
        (exists ((x Int)) (and (or A (= x t1)) (or B (= x t2))))   --->   (or A B (= t1 t2))
    """

    eliminate_squeezed_inner_quantifiers: bool = False
    """
    Eliminate an existentially quantified integer variable squeezed between two linear bounds
    whose gap is exactly `A - 1`, which forces the variable to a unique value `floor(E / A)`. See
    docs/QSE.md and docs/QSE_IMPLEMENTATION_PLAN.md.

    Example:
        (exists ((y Int)) (and (<= (* 10 y) (* 9 x)) (<= (* 9 x) (+ (* 10 y) 9))))   --->   True
    """

    use_bounded_congruence_construction: bool = False
    """
    Build the automaton for an existentially quantified variable that is bounded from both sides and
    occurs (besides the bounds themselves) only in a single congruence using a specialized construction
    instead of projecting the variable away afterwards. Requires -m MTBDD.

    Example:
        (exists ((x Int)) (and (<= 0 x) (<= x 3) (= (mod (+ (* 3 x) y) 8) 1)))

    All instantiations of the bounded variable share a single congruence state graph, so the resulting
    automaton is built in one sweep and holds at most `2*modulus` states regardless of how wide the
    bounds are. See BOUNDED_CONGRUENCE.md.
    """


@dataclass
class OptimizationPipelineConfig:
    """See OPTIMIZATION_PIPELINE.md / OPTIMIZATION_PIPELINE_PLAN.md."""

    enabled: bool = False
    """
    Run the registered optimizations to a fixpoint via `amaya.preprocessing.pipeline`, instead of
    the legacy hand-unrolled straight-line sequence.

    Defaults to False until the differential validation gate (plan step 7) is clean and step 9
    has re-tuned the tiers from real benchmark data - so that a bad merge here cannot affect a
    benchmark run or an SMT-COMP submission that does not explicitly ask for it.
    """

    max_pass_applications: Optional[int] = None
    """None = derive from formula size (32 per 1000 nodes, clamped to [256, 512] - see
    `pipeline._default_max_pass_applications`'s docstring for why the floor is 256, not 32)."""

    max_wall_time_seconds: float = 0.0
    """0 = no time limit."""

    tier_overrides: Dict[str, int] = field(default_factory=dict)
    """Pass name -> Pass_Tier value; for experimentation without editing the registry."""

    max_runs_overrides: Dict[str, int] = field(default_factory=dict)
    """Pass name -> max_runs; for experimentation without editing the registry."""

    report: bool = False
    """Log the per-pass statistics table after the pipeline finishes."""

    trace: bool = False
    """
    Log the formula produced by every productive pass application, in order, alongside the name of
    the pass that produced it - a step-by-step record of how the formula was simplified, for
    debugging a specific pipeline run. Also collected into `Pipeline_Report.trace` for programmatic
    inspection.
    """


@dataclass
class PreprocessingConfig:
    perform_antiprenexing: bool = False
    disambiguate_variables: bool = True
    assign_new_variable_names: bool = False
    """ Completely drop the variable names found in the AST and assign new ones. Implies disambiguation."""

    use_congruences_when_rewriting_modulo: bool = True
    """Use the congruence atom types to rewrite modulo terms."""

    use_two_vars_when_rewriting_nonlin_terms: bool = False
    """Use two variables <d> and <m> as in `K*<d> + <m> = y` when rewriting nonlinear terms."""

    show_preprocessed_formula: bool = False
    """Show preprocessed formula and exit; do not evaluate."""

    display_var_table: bool = False
    """Print variable table and exit."""


@dataclass
class SolverConfig(object):
    """Solver configuration options."""
    solution_domain: SolutionDomain = SolutionDomain.INTEGERS
    minimization_method: MinimizationAlgorithms = MinimizationAlgorithms.NONE
    # Performance tracking options
    backend_type: BackendType = BackendType.NATIVE
    track_operation_runtime: bool = False
    track_state_semantics: bool = False

    optimizations: OptimizationsConfig = field(default_factory=OptimizationsConfig)

    optimization_pipeline: OptimizationPipelineConfig = field(default_factory=OptimizationPipelineConfig)
    """Fixpoint scheduler configuration - see `OptimizationPipelineConfig`."""

    backend: BackendConfig = field(default_factory=BackendConfig)

    vis_display_only_free_vars: bool = False
    """Export transition symbols with bits only for the free variables in the corresponding automaton."""

    print_stats: bool = False
    """Print execution statistics"""

    preprocessing: PreprocessingConfig = field(default_factory=PreprocessingConfig)
    """Preprocessing configuration options."""

    current_formula_path: Optional[str] = None
    """Path to the input formula, if provided."""

    export_counter: int = 0
    """(Experimental) An execution-local repurposable counter."""

    disambiguation_scope_separator: str = '_'
    """String to use when disambiguating quantified variables, producing new var names of the form {old_name}{separator}{scope_id}."""

    report_highly_effective_minimizations: bool = False
    """Log subformula for which was the minimization highly effective (the resuld is smaller than 0.2* original size)."""

    max_allowed_states: int | None = None
    """Terminate the evaluation if any intermediate automaton gets larger than the given limit."""


solver_config = SolverConfig()
