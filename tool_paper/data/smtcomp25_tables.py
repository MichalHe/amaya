#!/usr/bin/env python3
"""
Regenerate every number that appears in the evaluation section of the tool paper.

The single source of truth is the official SMT-COMP 2025 single-query result dump that ships with
this repository (`smtcomp25-results/results-sq-2025.json`); nothing here re-runs any solver, so the
tables can be rebuilt on any machine in a second and diffed against the paper.

    ./tool_paper/data/smtcomp25_tables.py                 # human-readable summary
    ./tool_paper/data/smtcomp25_tables.py --latex         # the LaTeX table bodies used in the paper

Definitions used throughout (they match the competition's own conventions):
  * solved            - the solver answered `sat` or `unsat` (correctness is taken from the dump).
  * PAR-2             - sum over all instances of the CPU time of a solved instance, and of
                        2 * `timeout_seconds` for anything else (timeout, out-of-memory, unknown).
  * median solve time - median CPU time over the *solved* instances only, in seconds.
  * uniquely solved   - solved by the given solver and by no other entrant of that division.
  * VBS               - virtual best solver: the set of instances solved by at least one entrant.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import statistics
from typing import Dict, List, Set, Tuple

DEFAULT_RESULTS = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               '..', '..', 'smtcomp25-results', 'results-sq-2025.json')

TIMEOUT_SECONDS = 1200.0
SOLVED_RESULTS = ('sat', 'unsat')
DIVISIONS = ('LIA', 'NIA')
SOLVER_UNDER_STUDY = 'Amaya'

Instance = Tuple[Tuple[str, ...], str]


def load_results(path: str) -> List[dict]:
    with open(path) as results_file:
        return json.load(results_file)['results']


def instance_of(run: dict) -> Instance:
    """ The benchmark a run was performed on - family path plus file name. """
    return (tuple(run['file']['family']), run['file']['name'])


def runs_of_division(runs: List[dict], division: str) -> List[dict]:
    return [run for run in runs if run['file']['logic'] == division]


def summarize_division(runs: List[dict]) -> List[dict]:
    """ One row per solver, ordered by the number of solved instances (descending). """
    runs_by_solver: Dict[str, List[dict]] = collections.defaultdict(list)
    for run in runs:
        runs_by_solver[run['solver']].append(run)

    rows = []
    for solver, solver_runs in runs_by_solver.items():
        result_counts = collections.Counter(run['result'] for run in solver_runs)
        solve_times = [run['cpu_time'] for run in solver_runs if run['result'] in SOLVED_RESULTS]
        par2 = sum(run['cpu_time'] if run['result'] in SOLVED_RESULTS else 2 * TIMEOUT_SECONDS
                   for run in solver_runs)
        rows.append({
            'solver': solver,
            'sat': result_counts['sat'],
            'unsat': result_counts['unsat'],
            'solved': result_counts['sat'] + result_counts['unsat'],
            'timeout': result_counts['Timeout'],
            'out_of_memory': result_counts['OutOfMemory'],
            'unknown': result_counts['unknown'],
            'par2': par2,
            'median_solve_time': statistics.median(solve_times) if solve_times else float('nan'),
        })
    return sorted(rows, key=lambda row: (-row['solved'], row['par2']))


def solved_instances_by_solver(runs: List[dict]) -> Dict[str, Set[Instance]]:
    solved: Dict[str, Set[Instance]] = collections.defaultdict(set)
    for run in runs:
        if run['result'] in SOLVED_RESULTS:
            solved[run['solver']].add(instance_of(run))
    return solved


def per_family_breakdown(runs: List[dict], solver: str) -> Dict[str, Tuple[int, int, int]]:
    """ family -> (solved, out-of-memory, total instances the solver was run on). """
    breakdown: Dict[str, List[int]] = collections.defaultdict(lambda: [0, 0, 0])
    for run in runs:
        if run['solver'] != solver:
            continue
        family = '/'.join(run['file']['family'])
        breakdown[family][2] += 1
        if run['result'] in SOLVED_RESULTS:
            breakdown[family][0] += 1
        elif run['result'] == 'OutOfMemory':
            breakdown[family][1] += 1
    return {family: tuple(counts) for family, counts in sorted(breakdown.items())}


def report_human(runs: List[dict]) -> None:
    for division in DIVISIONS:
        division_runs = runs_of_division(runs, division)
        instances = {instance_of(run) for run in division_runs}
        print(f'== {division}: {len(instances)} instances, '
              f'{len({run["solver"] for run in division_runs})} entrants ==')

        header = f'{"solver":<28}{"sat":>5}{"unsat":>7}{"solved":>8}{"t/o":>6}{"oom":>6}{"unkn":>6}{"PAR-2":>10}{"med.":>8}'
        print(header)
        for row in summarize_division(division_runs):
            print(f'{row["solver"]:<28}{row["sat"]:>5}{row["unsat"]:>7}{row["solved"]:>8}'
                  f'{row["timeout"]:>6}{row["out_of_memory"]:>6}{row["unknown"]:>6}'
                  f'{round(row["par2"]):>10}{row["median_solve_time"]:>8.2f}')

        solved = solved_instances_by_solver(division_runs)
        ours = solved[SOLVER_UNDER_STUDY]
        others = set().union(*(instances for solver, instances in solved.items()
                               if solver != SOLVER_UNDER_STUDY))
        uniquely_solved = ours - others
        print(f'\n{SOLVER_UNDER_STUDY}: solved {len(ours)}, uniquely solved {len(uniquely_solved)}')
        if uniquely_solved:
            print('  uniquely solved by family:',
                  dict(collections.Counter('/'.join(family) for family, _ in uniquely_solved)))
        print(f'  VBS with {SOLVER_UNDER_STUDY}: {len(ours | others)}, without: {len(others)}')

        for rival in sorted(solved):
            if rival == SOLVER_UNDER_STUDY:
                continue
            print(f'  vs {rival:<28} ours-only {len(ours - solved[rival]):>4}, '
                  f'theirs-only {len(solved[rival] - ours):>4}, union {len(ours | solved[rival]):>4}')

        print(f'\n  {SOLVER_UNDER_STUDY} per family (solved / out-of-memory / total):')
        for family, (family_solved, family_oom, total) in per_family_breakdown(division_runs, SOLVER_UNDER_STUDY).items():
            print(f'    {family:<45}{family_solved:>5}{family_oom:>6}{total:>6}')
        print()


def report_latex(runs: List[dict]) -> None:
    for division in DIVISIONS:
        division_runs = runs_of_division(runs, division)
        print(f'% ---- {division} ({len({instance_of(r) for r in division_runs})} instances) ----')
        for row in summarize_division(division_runs):
            solver = row['solver'].replace('_', r'\_')
            if row['solver'] == SOLVER_UNDER_STUDY:
                solver = r'\textbf{' + solver + '}'
            print(f'{solver} & {row["sat"]} & {row["unsat"]} & {row["solved"]} & {row["timeout"]} & '
                  f'{row["out_of_memory"]} & {row["unknown"]} & {round(row["par2"]):,} & '
                  f'{row["median_solve_time"]:.2f} \\\\'.replace(',', r'\,'))
        print()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--results', default=DEFAULT_RESULTS, help='Path to results-sq-2025.json.')
    parser.add_argument('--latex', action='store_true', help='Emit the LaTeX table bodies instead of a summary.')
    args = parser.parse_args()

    runs = load_results(args.results)
    if args.latex:
        report_latex(runs)
    else:
        report_human(runs)


if __name__ == '__main__':
    main()
