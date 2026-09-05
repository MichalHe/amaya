"""
Tests for plan step 8 (report plumbing): `optimize_formula_structure`'s `report_sink` parameter,
and that `perform_whole_evaluation_on_source_text` attaches the resulting `Pipeline_Report` to
`Evaluation_Result.pipeline_report` only when the pipeline actually ran.
"""
import copy

import pytest

from amaya import parse
from amaya.config import solver_config
from amaya.preprocessing.pipeline import Pipeline_Report


SOURCE_TEXT = '''
(set-info :status sat)
(declare-fun x () Int)
(assert (and (<= x 5) (<= 0 x)))
(check-sat)
'''


@pytest.fixture
def restore_config():
    saved_optimizations = copy.deepcopy(solver_config.optimizations)
    saved_pipeline = copy.deepcopy(solver_config.optimization_pipeline)
    yield
    solver_config.optimizations = saved_optimizations
    solver_config.optimization_pipeline = saved_pipeline


def test_report_sink_is_untouched_on_the_legacy_path(restore_config):
    solver_config.optimization_pipeline.enabled = False
    sink = []

    parse.optimize_formula_structure(_trivial_ast(), {}, report_sink=sink)

    assert sink == []


def test_report_sink_receives_a_pipeline_report_when_enabled(restore_config):
    solver_config.optimization_pipeline.enabled = True
    sink = []

    parse.optimize_formula_structure(_trivial_ast(), {}, report_sink=sink)

    assert len(sink) == 1
    assert isinstance(sink[0], Pipeline_Report)


def test_evaluation_result_carries_the_report_only_when_pipeline_enabled(restore_config):
    solver_config.optimization_pipeline.enabled = False
    result_legacy = parse.perform_whole_evaluation_on_source_text(SOURCE_TEXT)
    assert result_legacy is not None
    assert result_legacy.pipeline_report is None

    solver_config.optimization_pipeline.enabled = True
    result_pipeline = parse.perform_whole_evaluation_on_source_text(SOURCE_TEXT)
    assert result_pipeline is not None
    assert isinstance(result_pipeline.pipeline_report, Pipeline_Report)


def _trivial_ast():
    from amaya.relations_structures import BoolLiteral
    return BoolLiteral(True)
