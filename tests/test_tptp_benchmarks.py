"""
Runs every TPTP benchmark in `benchmarks/formulae/tptp/` through the solver CLI (`run-amaya.py get-sat`)
on the MTBDD backend and compares the verdict with the benchmark's `(set-info :status ...)` annotation.

A verdict that contradicts the annotation is reported as unsound. A run that produces no verdict
(crash, timeout, unrecognised output) also fails, with a separate message.

Each benchmark runs in its own process, so the global `amaya.config.solver_config` and the MTBDD
backend's state do not carry over between benchmarks.
"""
import pathlib
import re
import subprocess
import sys

import pytest


REPOSITORY_ROOT = pathlib.Path(__file__).resolve().parents[1]
SOLVER_ENTRY_POINT = REPOSITORY_ROOT / 'run-amaya.py'
TPTP_BENCHMARK_DIRECTORY = REPOSITORY_ROOT / 'benchmarks' / 'formulae' / 'tptp'

PER_BENCHMARK_TIMEOUT_SECONDS = 120
SOLVER_BACKEND = 'MTBDD'

STATUS_ANNOTATION_PATTERN = re.compile(r'\(set-info\s+:status\s+(sat|unsat)\s*\)')


def read_expected_status(benchmark_path: pathlib.Path) -> str:
    match = STATUS_ANNOTATION_PATTERN.search(benchmark_path.read_text())
    if match is None:
        raise ValueError(f'{benchmark_path} has no (set-info :status sat|unsat) annotation')
    return match.group(1)


TPTP_BENCHMARK_PATHS = sorted(TPTP_BENCHMARK_DIRECTORY.glob('*.smt2'))


def test_tptp_benchmark_directory_is_not_empty():
    """ Guards against the parametrized test below silently collecting zero cases. """
    assert TPTP_BENCHMARK_PATHS, f'no .smt2 files found in {TPTP_BENCHMARK_DIRECTORY}'


@pytest.mark.parametrize('benchmark_path', TPTP_BENCHMARK_PATHS, ids=lambda path: path.stem)
def test_tptp_benchmark_verdict_matches_status_annotation(benchmark_path: pathlib.Path):
    expected_status = read_expected_status(benchmark_path)

    try:
        completed_process = subprocess.run(
            [sys.executable, str(SOLVER_ENTRY_POINT), '--backend', SOLVER_BACKEND, 'get-sat', str(benchmark_path)],
            capture_output=True,
            text=True,
            timeout=PER_BENCHMARK_TIMEOUT_SECONDS,
            cwd=REPOSITORY_ROOT,
        )
    except subprocess.TimeoutExpired:
        pytest.fail(f'NO VERDICT: {benchmark_path.name} ({SOLVER_BACKEND}) exceeded {PER_BENCHMARK_TIMEOUT_SECONDS} s')

    output_lines = completed_process.stdout.strip().splitlines()
    solver_verdict = output_lines[-1].strip() if output_lines else ''

    if solver_verdict not in ('sat', 'unsat'):
        pytest.fail(
            f'NO VERDICT: {benchmark_path.name} ({SOLVER_BACKEND}) exited with {completed_process.returncode}, '
            f'last stdout line {solver_verdict!r}\n'
            f'stderr (last 2000 chars):\n{completed_process.stderr[-2000:]}'
        )

    assert solver_verdict == expected_status, (
        f'UNSOUND: {benchmark_path.name} ({SOLVER_BACKEND}) answered {solver_verdict}, '
        f'annotated :status is {expected_status}'
    )
