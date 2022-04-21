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
    - native - symbols that belong to a transition are stored in a semi-
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
import os
import logging
import sys
from typing import List, Dict, Optional
from dataclasses import dataclass
import time

from amaya import automatons
from amaya import logger
from amaya import parse
from amaya.config import (
    BackendType,
    solver_config,
    SolutionDomain
)


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
                       choices=['MTBDD', 'native'],
                       default='native',
                       help='Selects the backend used in the automatons to store the transition function.')

argparser.add_argument('--verbose',
                       action='store_true',
                       default=False,
                       help='Toggles the verbose output (logging level >= INFO).')

argparser.add_argument('--debug',
                       action='store_true',
                       default=False,
                       help='Enables debug output  (logging level >= DEBUG).')

argparser.add_argument('-q', '--quiet',
                       action='store_true',
                       default=False,
                       help='Only report most critical messages.')

argparser.add_argument('--domain',
                       choices=['integers', 'naturals'],
                       default='integers',
                       help=('Selects the domain for the automatons constructed'
                             'from atomic presburger formulae. NATURALS support'
                             'is very questionable currently.'))

argparser.add_argument('-M',
                       '--minimize-eagerly',
                       action='store_true',
                       dest='minimize_eagerly',
                       default=False,
                       help=('Minimize the automatons eagerly, after automaton operation is performed.'
                             'Requires `native` backend to be used.'))

subparsers = argparser.add_subparsers(help='Runner operation')
get_sat_subparser = subparsers.add_parser('get-sat')
get_sat_subparser.add_argument('input_file',
                               metavar='input_file_path',
                               help='The input .smt2 file containing the input formula.')
get_sat_subparser.add_argument('--dump-created-automatons',
                               action='store_true',
                               dest='dump_created_automatons',
                               default=False,
                               help='All automatons constructed during the formula evaluation will be written'
                                    ' in the DOT language to separate files to the location specified by --dump-dest.')
get_sat_subparser.add_argument('--dump-dest',
                               metavar='DEST',
                               dest='dump_destination',
                               help='Specifies the location where the intermediate automata will be exported.')
get_sat_subparser.add_argument('--print-operations-runtime',
                               action='store_true',
                               dest='should_print_operations_runtime',
                               default=False,
                               help='If present, the runtime of the automata operations performed during the execution'
                                    ' will be measured and printed.')
get_sat_subparser.add_argument('-p',
                               '--print-model',
                               action='store_true',
                               dest='should_print_model',
                               default=False,
                               help='Print model after the decision procedure is finished, if any.')
get_sat_subparser.add_argument('--vis-only-free-vars',
                               action='store_true',
                               dest='vis_display_only_free_vars',
                               default=False,
                               help='Display only tracks only for free variables in the corresponding formula'
                                    ' when exporting automata.')

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

if args.quiet:
    logger.setLevel(logging.CRITICAL)
elif args.debug:
    logger.setLevel(logging.DEBUG)
elif args.verbose:
    logger.setLevel(logging.INFO)
else:
    logger.setLevel(logging.WARNING)

# Initialize the solver configuration
backend_str_to_type = {
    'native': BackendType.NATIVE,
    'MTBDD': BackendType.MTBDD,
}
solver_config.backend_type = backend_str_to_type[args.backend]

solution_domain_str_to_type = {
    'naturals': SolutionDomain.NATURALS,
    'integers': SolutionDomain.INTEGERS,
}
solver_config.solution_domain = solution_domain_str_to_type[args.domain]
solver_config.minimize_eagerly = args.minimize_eagerly
solver_config.vis_display_only_free_vars = args.vis_display_only_free_vars


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
        logger.info(f'Executing evaluation procedure with configuration: {solver_config}')
        nfa, smt_info = parse.perform_whole_evaluation_on_source_text(input_text,
                                                                      handle_automaton_created_fn)

        expected_sat = smt_info.get(':status', 'sat')
        if ':status' not in smt_info:
            logger.warning('The is missing :status in the smt-info statement, assuming sat.')

        model = nfa.find_model()
        computed_sat = 'sat' if model is not None else 'unsat'
        logger.info(f'The SAT value of the result automaton is {computed_sat}')

        if expected_sat != 'unknown':
            if computed_sat == expected_sat:
                logger.debug(f'The result SAT is matching the expected value.')
            else:
                msg = (f'The automaton\'s SAT did not match expected: actual={computed_sat}, '
                       f'expected={expected_sat}')
                logger.critical(msg)

                print('error: computed different SAT as present in the input info :status field')
                sys.exit(1)
        print(computed_sat)
        if args.should_print_model:
            print('Model:', model)


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

                expected_sat = smt_info.get(':status')

                if expected_sat is not None:
                    sat = nfa.model() is not None
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
