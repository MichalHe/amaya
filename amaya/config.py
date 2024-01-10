from dataclasses import (
    dataclass,
    field,
)
from enum import IntEnum
from typing import Optional


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
class OptimizationsConfig:
    simplify_variable_bounds: bool = False
    """Simplify hard variable bounds, e.g, x >= 0 && x != 0 ---> x >= 1."""

    rewrite_existential_equations_via_gcd: bool = False
    """Rewrite (exists x (= k*x y)) into (y mod k) = 0."""

    push_negation_towards_atoms: bool = False
    """Push negations as close to atoms as possible."""

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


@dataclass
class PreprocessingConfig:
    perform_prenexing: bool = False
    perform_antiprenexing: bool = False
    disambiguate_variables: bool = True
    assign_new_variable_names: bool = False
    """ Completely drop the variable names found in the AST and assign new ones. Implies disambiguation."""

    use_congruences_when_rewriting_modulo: bool = True
    """Use the congruence atom types to rewrite modulo terms."""

    use_two_vars_when_rewriting_nonlin_terms: bool = False
    """Use two variables <d> and <m> as in `K*<d> + <m> = y` when rewriting nonlinear terms."""

    show_preprocessed_formula: bool = False
    """Pretty print the preprocessed formula before evaluating."""


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
    """Log subformula for which was the minimization highly effective (the resuld is smaller than 0.2* original size) """


solver_config = SolverConfig()
