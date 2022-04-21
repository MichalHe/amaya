from dataclasses import dataclass
from enum import IntEnum


class SolutionDomain(IntEnum):
    NATURALS = 0
    INTEGERS = 1


class BackendType(IntEnum):
    NATIVE = 1
    MTBDD = 2


@dataclass
class SolverConfig(object):
    """Solver configuration options."""
    solution_domain: SolutionDomain = SolutionDomain.INTEGERS
    minimize_eagerly: bool = False
    # Performance tracking options
    backend_type: BackendType = BackendType.NATIVE
    track_operation_runtime: bool = False
    # Debug options
    track_state_semantics: bool = False

    vis_display_only_free_vars: bool = False
    """Export transition symbols with bits only for the free variables in the corresponding automaton."""


solver_config = SolverConfig()
