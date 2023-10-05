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

    do_light_sat_reasoning: bool = False
    """Detect AND-OR trees and convert them into DNF form and detect contradictions."""

    do_lazy_evaluation: bool = False
    """Enable lazy evaluation of subformulae of the form `(exists (..) (and atom1 atom2 ...))`"""

    do_gcd_divide: bool = True
    """ Divide atoms by the GCD of their coefficients. """


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


solver_config = SolverConfig()
