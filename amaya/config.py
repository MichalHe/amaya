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
class PreprocessingConfig:
    perform_prenexing: bool = False
    perform_antiprenexing: bool = False
    disambiguate_variables: bool = True
    assign_new_variable_names: bool = False
    """ Completely drop the variable names found in the AST and assign new ones. Implies disambiguation."""
    simplify_variable_bounds: bool = False

    use_congruences_when_rewriting_modulo: bool = True
    """Use the congruence atom types to rewrite modulo terms."""

    use_two_vars_when_rewriting_nonlin_terms : bool = False
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

    allow_lazy_evaluation: bool = False
    """Enable lazy evaluation of subformulae of the form `(exists (..) (and atom1 atom2 ...))`"""

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
