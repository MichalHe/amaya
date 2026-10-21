"""
End-to-end regressions for preprocessing steps that changed the satisfiability of the input formula.

Every formula below is unsatisfiable; the optimization named in each case answered sat before its fix.
Each case runs the whole solver on SMT-LIB text with exactly the listed optimizations enabled on top
of the defaults (`amaya.config.OptimizationsConfig`).
"""
import copy
import logging

import pytest

from amaya import logger as amaya_logger
from amaya import parse
from amaya.config import BackendType, SolutionDomain, solver_config


@pytest.fixture
def default_solver_config():
    """ Integers, native backend and default optimizations, restoring the global config afterwards. """
    saved_backend = solver_config.backend_type
    saved_domain = solver_config.solution_domain
    saved_optimizations = copy.deepcopy(solver_config.optimizations)
    saved_log_level = amaya_logger.level

    solver_config.backend_type = BackendType.NATIVE
    solver_config.solution_domain = SolutionDomain.INTEGERS
    amaya_logger.setLevel(logging.WARNING)

    yield solver_config

    solver_config.backend_type = saved_backend
    solver_config.solution_domain = saved_domain
    solver_config.optimizations = saved_optimizations
    amaya_logger.setLevel(saved_log_level)


def _is_sat(source_text: str, enabled_optimizations: tuple) -> bool:
    for optimization_field in enabled_optimizations:
        setattr(solver_config.optimizations, optimization_field, True)
    result = parse.perform_whole_evaluation_on_source_text(source_text)
    assert result is not None
    return result.model is not None


UNSAT_CASES = [
    pytest.param(
        # 2x + 3y takes the values 0, 2, 3, 5 on the box; 7 is not among them. The equation has no
        # unit coefficient, so model reasoning records it verbatim, and inside a top-level quantifier
        # it records it at the outermost frame, which outlives the call. A second simplification call
        # that shared the first call's `Asserted_Model_Properties` found that record and replaced the
        # equation by True.
        """
        (declare-fun x () Int)
        (assert (exists ((y Int)) (and (= (+ (* 2 x) (* 3 y)) 7) (<= 0 x) (<= x 1) (<= 0 y) (<= y 1))))
        (check-sat)
        """,
        ('reason_about_models',),
        id='model-reasoning-state-shared-between-calls',
    ),
    pytest.param(
        # Model reasoning substitutes x = 3 and obtains 3z = 1, which has no integer solution.
        """
        (declare-fun x () Int)
        (declare-fun z () Int)
        (assert (and (= (+ (* 2 x) (* 3 z)) 7) (<= 3 x) (<= x 3)))
        (check-sat)
        """,
        ('reason_about_models',),
        id='model-reasoning-unsat-equation-after-substitution',
    ),
]


@pytest.mark.parametrize('source_text, enabled_optimizations', UNSAT_CASES)
def test_unsatisfiable_formula_is_reported_unsat(default_solver_config, source_text, enabled_optimizations):
    assert not _is_sat(source_text, enabled_optimizations)
