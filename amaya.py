r'''
 ______     __    __     ______     __  __     ______
/\  __ \   /\ "-./  \   /\  __ \   /\ \_\ \   /\  __ \
\ \  __ \  \ \ \-./\ \  \ \  __ \  \ \____ \  \ \  __ \
 \ \_\ \_\  \ \_\ \ \_\  \ \_\ \_\  \/\_____\  \ \_\ \_\
  \/_/\/_/   \/_/  \/_/   \/_/\/_/   \/_____/   \/_/\/_/

Amaya v2.0.
Amaya is an experimental, automata based LIA SMT solver.

The solver accepts input formulae written in the SMTlib (v2) language.
Currently, there are two backends available to be used when evaluating the
given formula (controlled via the `--backend` option):
    - naive - symbols that belong to a transition are stored in a semi-
              compressed form and all the automaton operations perform
              iteration of some kind over these transitions (the backend
              is rather slow)
    - MTBDD - transition symbols are stored using MTBDDs (compact
              representation). The operations manipulating automatons are much
              faster, however the backend support is relatively fresh, so there
              might still be bugs in the evaluation).
'''
import argparse as ap
from enum import Enum
from log import logger
import os
import parse
import logging
import sys
import automatons
from typing import List, Dict, Optional
from dataclasses import dataclass
import time


class RunnerMode(Enum):
    GET_SAT = 'get-sat'
    BENCHMARK = 'benchmark'


@dataclass
class BenchmarkStat:
    name: str
    path: str
    runtimes_ns: List[int]
    failed: bool

    @property
    def avg_runtime_ns(self) -> Optional[float]:
        if not self.runtimes_ns:
            return None
        return sum(self.runtimes_ns) / len(self.runtimes_ns)

    def as_dict(self) -> Dict:
        return {
            'name': self.name,
            'path': self.path,
            'runtimes_ns': self.runtimes_ns,
            'avg_runtime_ns': self.avg_runtime_ns,
            'failed': self.failed,
        }


argparser = ap.ArgumentParser(description=__doc__, formatter_class=ap.RawTextHelpFormatter)

argparser.add_argument('--backend',
                       choices=['MTBDD', 'naive'],
                       default='naive',
                       help='Selects the backend used in the automatons to store the transition function.')

argparser.add_argument('--verbose',
                       action='store_true',
                       default=False,
                       help='Toggles the verbose output.')

argparser.add_argument('--domain',
                       choices=['integers', 'naturals'],
                       default='integers',
                       help='Selects the domain for the automatons constructed from atomic presburger formulae. NATURALS support is very questionable currently.')

subparsers = argparser.add_subparsers(help='Runner operation')
get_sat_subparser = subparsers.add_parser('get-sat')
get_sat_subparser.add_argument('input_file',
                               metavar='input_file_path',
                               help='The input .smt2 file containing the input formula.')
get_sat_subparser.add_argument('--dump-created-automatons',
                               action='store_true',
                               dest='dump_created_automatons',
                               default=False,
                               help=r'''Debug option. All automatons created during the formula evaluation will be written
                                        to separate files to the location specified by `--dump-dest`. The output format is graphviz.''')
get_sat_subparser.add_argument('--dump-dest',
                               metavar='DEST',
                               dest='dump_destination',
                               help=r'''Debug option. Specifies the location where the graphviz representations emitted during evaluation will be placed.''')
get_sat_subparser.add_argument('--print-operations-runtime',
                               action='store_true',
                               dest='should_print_operations_runtime',
                               default=False,
                               help=r'''If present, the runtime of the operations performed during the execution (e.g. determinization) will be logged.''')

benchmark_subparser = subparsers.add_parser('benchmark')
benchmark_subparser.add_argument('--add-file',
                                 metavar='FILE',
                                 action='append',
                                 default=[],
                                 dest='specified_files',
                                 help='Add a file to the performed benchmark')

benchmark_subparser.add_argument('--add-directory-recursive',
                                 default=[],
                                 metavar='DIR',
                                 action='append',
                                 dest='recursive_search_directories',
                                 help='Specify a (recursively searched) directory containing the .smt2 files that are a part of the performed benchmark.')

benchmark_subparser.add_argument('--add-directory',
                                 default=[],
                                 metavar='DIR',
                                 action='append',
                                 dest='nonrecursive_search_directories',
                                 help='Specify a directory containing the .smt2 files that are a part of the performed benchmark. Will *not* be recursively traversed.')

benchmark_subparser.add_argument('--execute-times',
                                 type=int,
                                 default=1,
                                 metavar='N',
                                 dest='benchmark_execution_count',
                                 help='Specifies the number of times to execute the whole benchmark.')

benchmark_subparser.add_argument('--output-format',
                                 choices=['json'],
                                 default='json',
                                 metavar='fmt',
                                 dest='output_format',
                                 help='Specifies the output format for the benchmark reports.')


args = argparser.parse_args()

# Determine what mode was used.
if 'specified_files' in args:
    runner_mode = RunnerMode.BENCHMARK
elif 'input_file' in args:
    runner_mode = RunnerMode.GET_SAT
logger.debug(f'Chosen runner mode: {runner_mode}')

# Verbose output?
if args.verbose:
    logger.setLevel(logging.DEBUG)
else:
    logger.setLevel(logging.WARNING)

# Evaluation config
backend_type = parse.BackendType.NAIVE
if args.backend == 'MTBDD':
    backend_type = parse.BackendType.MTBDD

solution_domain = parse.SolutionDomain.INTEGERS
if args.domain == 'naturals':
    solution_domain = parse.SolutionDomain.NATURALS

evaluation_config = parse.EvaluationConfig(solution_domain, backend_type)


def ensure_dump_destination_valid(path: str):
    '''Verifies that the given path points to a dir, or if it does not exists,
    creates a new dir.'''
    if os.path.exists(path):
        if not os.path.isdir(path):
            assert False, 'The automaton dump destination must be a folder, not a file.'
    else:
        os.mkdir(path)


def search_directory_recursive(root_path: str, filter_file_ext='.smt2') -> List[str]:
    return list(filter(
        lambda path: path.endswith(filter_file_ext),
        os.walk(root_path)
    ))


def search_directory_nonrecursive(root_path: str, filter_file_ext='.smt2') -> List[str]:
    return list(
        map(
            lambda benchmark_file: os.path.join(root_path, benchmark_file),
            filter(
                lambda path: path.endswith(filter_file_ext),
                os.listdir(root_path)
            )
        )
    )


def run_in_getsat_mode(args):
    assert os.path.exists(args.input_file), 'The SMT2 supplied file containing input formula does not exists!'
    assert os.path.isfile(args.input_file), 'The supplied file must not be a directory.'

    if args.should_print_operations_runtime:
        evaluation_config.print_operation_runtime = True

    # Wrap in a dictionary so we can modify it from nested functions
    _enclosing_ctx = {
        'automatons_written_counter': 0
    }

    def write_created_automaton_to_folder(nfa: automatons.NFA, op: parse.ParsingOperation):
        filename = os.path.join(args.dump_destination, f'{_enclosing_ctx["automatons_written_counter"]}-{op.value}.dot')
        with open(filename, 'w') as output_file:
            output_file.write(str(nfa.get_visualization_representation().compress_symbols().into_graphviz()))
        _enclosing_ctx['automatons_written_counter'] += 1

    def print_created_automaton_to_stdout(nfa: automatons.NFA, op: parse.ParsingOperation):
        print(nfa.get_visualization_representation().into_graphviz())

    def discard_created_automaton(nfa: automatons.NFA, op: parse.ParsingOperation):
        pass

    if args.dump_created_automatons:
        if args.dump_destination is None:
            handle_automaton_created_fn = print_created_automaton_to_stdout
        else:
            ensure_dump_destination_valid(args.dump_destination)
            handle_automaton_created_fn = write_created_automaton_to_folder
    else:
        handle_automaton_created_fn = discard_created_automaton

    with open(args.input_file) as input_file:
        input_text = input_file.read()
        logger.info(f'Executing evaluation procedure with configuration: {evaluation_config}')
        nfa, smt_info = parse.perform_whole_evaluation_on_source_text(input_text, evaluation_config, handle_automaton_created_fn)

        expected_sat = True
        if ':status' in smt_info:
            if smt_info[':status'] == 'unsat':
                expected_sat = False
            logger.info(f'Retrieved expected SAT value from the smt-info statements: expected_sat={expected_sat}')
        else:
            logger.warning('The given file is missing the smt-info statement specifying the expected SAT value (`:status` field), assuming expected_sat=True.')

        actual_sat, model = nfa.is_sat()
        logger.info(f'The SAT value of the result automaton: actual_sat={actual_sat}')
        sat_matches = (actual_sat == expected_sat)

        sat_value_str = 'sat' if actual_sat else 'unsat'
        expected_sat_str = 'sat' if expected_sat else 'unsat'
        if sat_matches:
            logger.info(f'The result SAT is OK (as expected) (SAT={sat_value_str}, model: {model})')
            print(sat_value_str)
        else:
            logger.critical(f'The automaton\'s SAT did not match expected: actual={sat_value_str}, given word: {model}, expected={expected_sat_str}')
            print(f'FAIL: Calculated SAT: {sat_value_str} is different from the expected value: {expected_sat_str}')


def run_in_benchmark_mode(args):  # NOQA
    benchmark_files: List[str] = []
    for benchmark_file in args.specified_files:
        assert os.path.exists(benchmark_file) and os.path.isfile(benchmark_file), f'The file in --add-file {benchmark_file} does not exists.'
        benchmark_files.append(benchmark_file)

    for nonrecursive_search_directory in args.nonrecursive_search_directories:
        benchmark_files += search_directory_nonrecursive(nonrecursive_search_directory)

    for recursive_search_directory in args.recursive_search_directories:
        benchmark_files += search_directory_recursive(nonrecursive_search_directory)

    print('Executing benchmark with the following files:')
    for f in benchmark_files:
        print(' > ', f)

    evaluation_config = parse.EvaluationConfig(solution_domain, backend_type)
    print('The evaluation configuration used during benchmarking:', evaluation_config)
    executed_benchmarks: Dict[str, BenchmarkStat] = {}
    failed = 0

    if evaluation_config.backend_type == parse.BackendType.MTBDD:
        from mtbdd_transitions import MTBDDTransitionFn

    for i in range(args.benchmark_execution_count):
        for benchmark_file in benchmark_files:
            if benchmark_file in executed_benchmarks and executed_benchmarks[benchmark_file].failed:
                # Skip benchmarks that have previously failed
                continue

            with open(benchmark_file) as benchmark_input_file:
                print('Running', benchmark_file, file=sys.stderr)
                text = benchmark_input_file.read()

                benchmark_start = time.time_ns()
                nfa, smt_info = parse.perform_whole_evaluation_on_source_text(text, evaluation_config)
                benchmark_end = time.time_ns()
                runtime_ns = benchmark_end - benchmark_start

                # Clear sylvan cache if running multiple evaluations, so that
                # the measurements do not interfere.
                if evaluation_config.backend_type == parse.BackendType.MTBDD:
                    MTBDDTransitionFn.call_clear_cachce()
                    MTBDDTransitionFn.call_sylvan_gc()

                if benchmark_file not in executed_benchmarks:
                    executed_benchmarks[benchmark_file] = BenchmarkStat(os.path.basename(benchmark_file),
                                                                        benchmark_file,
                                                                        [runtime_ns],
                                                                        False)
                else:
                    executed_benchmarks[benchmark_file].runtimes_ns.append(runtime_ns)

                expected_sat = parse.get_sat_value_from_smt_info(smt_info, None)

                if expected_sat is not None:
                    sat, _ = nfa.is_sat()
                    if sat != expected_sat:
                        failed += 1
                        executed_benchmarks[benchmark_file].failed = True

    print(f'Overall failed tests: {failed}/{len(benchmark_files)}')
    report = list(map(BenchmarkStat.as_dict, executed_benchmarks.values()))

    if args.output_format == 'json':
        import json
        print(json.dumps(report))


running_modes_procedure_table = {
    RunnerMode.BENCHMARK: run_in_benchmark_mode,
    RunnerMode.GET_SAT: run_in_getsat_mode,
}

runner_procedure = running_modes_procedure_table[runner_mode](args)
