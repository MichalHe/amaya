from dataclasses import (
    dataclass,
    field,
)
from enum import IntEnum


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
    simplify_variable_bounds: bool = False


@dataclass
class SolverConfig(object):
    """Solver configuration options."""
    solution_domain: SolutionDomain = SolutionDomain.INTEGERS
    minimization_method: MinimizationAlgorithms = MinimizationAlgorithms.NONE
    # Performance tracking options
    backend_type: BackendType = BackendType.NATIVE
    track_operation_runtime: bool = False
    track_state_semantics: bool = False

    vis_display_only_free_vars: bool = False
    """Export transition symbols with bits only for the free variables in the corresponding automaton."""

    preprocessing: PreprocessingConfig = field(default_factory=PreprocessingConfig)
    """Preprocessing configuration options."""


solver_config = SolverConfig()
