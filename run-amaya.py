#!/usr/bin/env python3
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
from typing import Callable, List, Dict, Optional
from dataclasses import dataclass
import time
import statistics

from amaya import automatons
from amaya import logger
from amaya import parse
from amaya.config import (
    BackendType,
    MinimizationAlgorithms,
    solver_config,
    SolutionDomain,
)
from amaya.converters import write_ast_in_lash
from amaya.preprocessing import preprocess_ast
from amaya.preprocessing.eval import convert_ast_into_evaluable_form
from amaya.relations_structures import AST_NaryNode, AST_Node, AST_Node_Names, FunctionSymbol
from amaya.tokenize import tokenize
import amaya.utils as utils


class RunnerMode(Enum):
    GET_SAT = 'get-sat'
    BENCHMARK = 'benchmark'
    CONVERT_FORMULA = 'convert'


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

argparser.add_argument('--fast',
                       action='store_true',
                       default=False,
                       help='Enable MTBDD backend and Hopcroft\'s minimization.')

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

argparser.add_argument('-m',
                       '--minimize',
                       choices=('hopcroft', 'brzozowski'),
                       dest='minimization_method',
                       default=None,
                       help='Minimize the automatons eagerly using the specified minimization algorithm.')

argparser.add_argument('-p',
                       '--preprocessing',
                       action='append',
                       dest='preprocessing_switches',
                       default=[],
                       choices=['no-var-disambiguation',
                                'assign-new-var-names',
                                'nonlinear-term-use-two-vars',
                                'no-congruences',
                                'assign-new-var-names',
                                'auto-infer',
                       ],
                       help=('Controls preprocessing transformations applied on input the formula. Options:\n'
                             '- no-congruences             : Do not use Congruence atoms when rewriting modulo terms\n'
                             '- assign-new-var-names       : Give all variables a new name, dropping identifies symbols that might be unsupported in some output format\n'
                             '- nonlinear-term-use-two-vars: Always use two variables (quotient, reminder) when rewriting a non-linear term\n'
                             '- auto-infer                 : Convert-mode specific - infer preprocessing options from output format.'))


argparser.add_argument('-O',
                       '--optimize',
                       action='append',
                       dest='optimizations',
                       default=[],
                       choices=['gcd-rewrite',
                                'var-bounds',
                                'stomp-negations',
                                'light-sat',
                                'lazy',
                                'all',
                       ],
                       help=('Controls preprocessing transformations applied on input the formula. Options:\n'
                             '- gdc-rewrite    : Rewrite existentially quantified equations using GCD rewrite\n'
                             '- var-bounds     : Simplify (hard) variable bounds if possible\n'
                             '- stomp-negations: Push negation as close to atoms as possible\n'
                             '- light-sat      : Perform light SAT reasoning on AND-OR trees\n'
                             '- lazy           : Allow lazy evaluation of conjunctions. Requires -m MTBDD.'
                             '- all            : Enable all above optimizations'))


subparsers = argparser.add_subparsers(help='Runner operation')
get_sat_subparser = subparsers.add_parser('get-sat')

get_sat_subparser.add_argument('input_file',
                               metavar='input_file_path',
                               help='The input .smt2 file containing the input formula.')

get_sat_subparser.add_argument('--output-format',
                               metavar='format',
                               choices=['dot', 'vtf', 'mata'],
                               default='dot',
                               dest='output_format',
                               help='Specify the format of the exported automata.')

get_sat_subparser.add_argument('-o'
                               '--output-created-automata',
                               metavar='destination',
                               dest='output_destination',
                               help='Causes the intermediate automata manipulated throughout the decision procedure'
                                    ' to be exported to the given location.')

get_sat_subparser.add_argument('-t',
                               '--print-operations-runtime',
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

get_sat_subparser.add_argument('--colorize-dot',
                               action='store_true',
                               dest='colorize_dot',
                               default=False,
                               help='Colorize the SCCs with more than 1 node in the exported automata if the output'
                                    ' format is dot.')

get_sat_subparser.add_argument('-s',
                               '--print-stats',
                               action='store_true',
                               dest='print_stats',
                               default=False,
                               help='Print execution statistics.')


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
                                 choices=['json', 'csv'],
                                 default='json',
                                 metavar='fmt',
                                 dest='output_format',
                                 help='Specifies the output format for the benchmark reports.')

benchmark_subparser.add_argument('--csv-fields',
                                 default='benchmark,avg_runtime,std',
                                 help=('Comma separated fields to print when outputting CSV. Available choices: '
                                       'benchmark (benchmark name), avg_time (average runtime in seconds), '
                                       'std (standard deviation)'))

formula_conversion_subparser = subparsers.add_parser('convert')
formula_conversion_subparser.add_argument('file_to_convert', help='File containing SMT2 formula to convert to other format.')
formula_conversion_subparser.add_argument('-f', '--output-format', help='Format to output the formula into.', choices=['lash'], default='lash')

args = argparser.parse_args()

# Determine what mode was used.
if 'specified_files' in args:
    runner_mode = RunnerMode.BENCHMARK
elif 'input_file' in args:
    runner_mode = RunnerMode.GET_SAT
    solver_config.print_stats = args.print_stats
elif 'file_to_convert' in args:
    runner_mode = RunnerMode.CONVERT_FORMULA
    if 'auto-infer' in args.preprocessing_switches:
       if args.output_format == 'lash':
            solver_config.preprocessing.use_congruences_when_rewriting_modulo = False
            solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms = True
            solver_config.preprocessing.assign_new_variable_names = True
else:
    print('No execution mode specified. See run-amaya.py --help for more information.', file=sys.stderr)
    sys.exit(1)
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
if args.fast:
    solver_config.backend_type = BackendType.MTBDD
    solver_config.minimization_method = MinimizationAlgorithms.HOPCROFT
else:
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

# Read supplied preprocessing switches and convert them into cfg
if 'no-var-disambiguation' in args.preprocessing_switches:
    solver_config.preprocessing.disambiguate_variables = False
if 'assign-new-var-names' in args.preprocessing_switches:
    solver_config.preprocessing.disambiguate_variables = True
    solver_config.preprocessing.assign_new_variable_names = True
if 'no-congruences' in args.preprocessing_switches:
    solver_config.preprocessing.use_congruences_when_rewriting_modulo = False
if 'nonlinear-term-use-two-vars' in args.preprocessing_switches:
    solver_config.preprocessing.use_two_vars_when_rewriting_nonlin_terms = True

if args.minimization_method == 'hopcroft':
    solver_config.minimization_method = MinimizationAlgorithms.HOPCROFT
elif args.minimization_method == 'brzozowski':
    solver_config.minimization_method = MinimizationAlgorithms.BRZOZOWSKI
    if solver_config.backend_type == BackendType.MTBDD:
        print('Brzozowski minimization is not supported with the MTBDD backend.', file=sys.stderr)
        sys.exit(1)
elif 'fast' not in args:
    solver_config.minimization_method = MinimizationAlgorithms.NONE

for opt in args.optimizations:
    if opt == 'all':
        solver_config.optimizations.simplify_variable_bounds = True
        solver_config.optimizations.rewrite_existential_equations_via_gcd = True
        solver_config.optimizations.push_negation_towards_atoms = True
        solver_config.optimizations.do_light_sat_reasoning = True
        solver_config.optimizations.do_lazy_evaluation = True
    if opt == 'gcd-rewrite':
        solver_config.optimizations.rewrite_existential_equations_via_gcd = True
    if opt == 'var-bounds':
        solver_config.optimizations.simplify_variable_bounds = True
    if opt == 'stomp-negations':
        solver_config.optimizations.push_negation_towards_atoms = True
    if opt == 'light-sat':
        solver_config.optimizations.do_light_sat_reasoning = True
    if opt == 'lazy':
        solver_config.optimizations.do_lazy_evaluation = True

def ensure_output_destination_valid(output_destination: str):
    """Ensures that the given output destination is a folder. Creates the folder if it does not exist."""
    if os.path.exists(output_destination):
        if not os.path.isdir(output_destination):
            print('Error: The automaton output destination must be a folder, not a file.', file=sys.stderr)
            sys.exit(1)
    else:
        os.mkdir(output_destination)


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


def run_in_getsat_mode(args) -> bool:
    assert os.path.exists(args.input_file), 'The SMT2 supplied file containing input formula does not exists!'
    assert os.path.isfile(args.input_file), 'The supplied file must not be a directory.'

    solver_config.track_operation_runtime = args.should_print_operations_runtime
    solver_config.vis_display_only_free_vars = args.vis_display_only_free_vars
    solver_config.current_formula_path = os.path.abspath(args.input_file)

    def write_created_automaton_to_folder(introspection_info: parse.IntrospectionData):
        filename = f'{introspection_info.operation_id}-{introspection_info.operation.value}.{args.output_format}'
        output_path = os.path.join(args.output_destination, filename)
        with open(output_path, 'w') as output_file:
            vis_representation = introspection_info.automaton.get_visualization_representation().compress_symbols()
            output_contents = ''
            if args.output_format == 'dot':
                output_contents = str(vis_representation.into_graphviz(highlight_sccs=args.colorize_dot))
            elif args.output_format == 'vtf':
                output_contents = vis_representation.into_vtf()
            elif args.output_format == 'mata':
                output_contents = vis_representation.into_mata()
            output_file.write(output_contents)

    def discard_created_automaton(info: parse.IntrospectionData):
        pass

    should_output_created_automata = bool(args.output_destination)

    if should_output_created_automata:
        ensure_output_destination_valid(args.output_destination)
        handle_automaton_created_fn = write_created_automaton_to_folder
    else:
        handle_automaton_created_fn = discard_created_automaton

    with open(args.input_file) as input_file:
        input_text = input_file.read()
        logger.info(f'Executing evaluation procedure with configuration: {solver_config}')
        nfa, smt_info, stats = parse.perform_whole_evaluation_on_source_text(input_text,
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
                return False
        print('status: ', computed_sat)
        if args.should_print_model:
            print('Model:', model)

        if solver_config.print_stats:
            print(f'############ STATISTICS ############')
            print(f'max_automaton_size: {stats.max_automaton_size}')
            for i, op in enumerate(stats.trace):
                print(f'{i}  {op.operation.value} input1={op.operand1} input2={op.operand2} output={op.output} runtime={op.runtime_ns} (ns)')

        if should_output_created_automata:
            # Dump tracefile
            trace_file = 'trace-info.dot'
            trace_path = os.path.join(args.output_destination, trace_file)
            with open(trace_path, 'w') as trace_out_file:
                trace_graph = utils.construct_dot_tree_from_trace(stats.trace)
                trace_out_file.write(trace_graph)

        return True


def print_benchmark_results_as_csv(results: Dict[str, BenchmarkStat], args, separator=';'):
    """Prints the benchmark results as a CSV with fields given by the args.csv_fields."""

    requested_csv_fields = args.csv_fields.split(',')
    supported_csv_fields = {'benchmark', 'avg_runtime', 'std'}

    csv_fields = []
    for field in requested_csv_fields:
        if field in supported_csv_fields:
            csv_fields.append(field)
        else:
            print(f'Unknown CSV field {field}, skipping it.', file=sys.stderr)

    def make_column_map(benchmark: str, result: BenchmarkStat, columns: List[str]) -> Dict[str, str]:
        column_map = {
            'avg_runtime': str(result.avg_runtime_ns / 1_000_000_000),
            'benchmark': benchmark,
        }
        if 'std' in columns:
            column_map['std'] = str(round(statistics.stdev(result.runtimes_ns) / 1_000_000_000))
        return column_map

    rows = []
    for benchmark, result in results.items():
        column_map = make_column_map(benchmark, result, csv_fields)
        row_parts = [column_map[field] for field in csv_fields]
        rows.append(separator.join(row_parts))
    print('\n'.join(rows))


def run_in_benchmark_mode(args) -> bool:  # NOQA
    benchmark_files: List[str] = []
    for benchmark_file in args.specified_files:
        assert os.path.exists(benchmark_file) and os.path.isfile(benchmark_file), f'The file in --add-file {benchmark_file} does not exists.'
        benchmark_files.append(benchmark_file)

    for nonrecursive_search_directory in args.nonrecursive_search_directories:
        benchmark_files += search_directory_nonrecursive(nonrecursive_search_directory)

    for recursive_search_directory in args.recursive_search_directories:
        benchmark_files += search_directory_recursive(recursive_search_directory)

    print('Executing benchmark with the following files:', file=sys.stderr)
    for f in benchmark_files:
        print(' > ', f, file=sys.stderr)

    executed_benchmarks: Dict[str, BenchmarkStat] = {}
    failed = 0

    if solver_config.backend_type == parse.BackendType.MTBDD:
        from amaya.mtbdd_transitions import MTBDDTransitionFn

    for i in range(args.benchmark_execution_count):
        for benchmark_file in benchmark_files:
            if benchmark_file in executed_benchmarks and executed_benchmarks[benchmark_file].failed:
                # Skip benchmarks that have previously failed
                continue

            with open(benchmark_file) as benchmark_input_file:
                # Clear sylvan cache if running multiple evaluations, so that the measurements do not interfere.
                if solver_config.backend_type == parse.BackendType.MTBDD:
                    MTBDDTransitionFn.call_clear_cachce()
                    MTBDDTransitionFn.call_sylvan_gc()

                print('Running', benchmark_file, file=sys.stderr)
                solver_config.export_counter = 0
                solver_config.current_formula_path = os.path.abspath(benchmark_file)
                text = benchmark_input_file.read()

                benchmark_start = time.time_ns()
                nfa, smt_info, stats = parse.perform_whole_evaluation_on_source_text(text)
                benchmark_end = time.time_ns()
                runtime_ns = benchmark_end - benchmark_start

                if benchmark_file not in executed_benchmarks:
                    executed_benchmarks[benchmark_file] = BenchmarkStat(os.path.basename(benchmark_file),
                                                                        benchmark_file,
                                                                        [runtime_ns],
                                                                        False)
                else:
                    executed_benchmarks[benchmark_file].runtimes_ns.append(runtime_ns)

                expected_sat_str = smt_info.get(':status', 'unknown')

                if expected_sat_str in ('sat', 'unsat'):
                    sat = nfa.find_model() is not None
                    expected_sat = (expected_sat_str == 'sat')
                    if sat != expected_sat:
                        failed += 1
                        executed_benchmarks[benchmark_file].failed = True

    print(f'Overall failed tests: {failed}/{len(benchmark_files)}', file=sys.stderr)
    print(f'Overall failed tests:', ' '.join(b for b, r in executed_benchmarks.items() if r.failed), file=sys.stderr)
    report = list(map(BenchmarkStat.as_dict, executed_benchmarks.values()))

    if args.output_format == 'json':
        import json
        print(json.dumps(report))
    elif args.output_format == 'csv':
        print_benchmark_results_as_csv(executed_benchmarks, args)

    return not failed


def convert_smt_to_other_format(args):
    if not os.path.exists(args.file_to_convert):
        sys.exit(f'The specified input file {args.file_to_convert} does not exists!')

    with open(args.file_to_convert) as input_file:
        smt2_text = input_file.read()

    tokens = tokenize(smt2_text)
    ast: List[AST_Node] = parse.build_syntax_tree(tokens)

    writer_table = {
        'lash': write_ast_in_lash,
    }

    function_symbol_table: Dict[str, FunctionSymbol] = {}
    asserted_formulae: List[AST_Node] = []
    writer: Callable[[AST_Node], str] = writer_table[args.output_format]

    for top_level_statement in ast:
        if not isinstance(top_level_statement, list):
            continue
        if top_level_statement[0] == AST_Node_Names.DECLARE_FUN.value:
            function_symbol = parse.parse_function_symbol_declaration(top_level_statement)
            function_symbol_table[function_symbol.name] = function_symbol
        elif top_level_statement[0] == AST_Node_Names.ASSERT.value:
            asserted_formulae.append(top_level_statement[1])
        elif top_level_statement[0] == AST_Node_Names.CHECK_SAT.value:
            fn_symbols = [fn_symbol for fn_symbol in function_symbol_table.values() if fn_symbol.arity == 0]
            fn_symbols = sorted(fn_symbols, key=lambda fn_symbol: fn_symbol.name)
            formula_to_emit = ['and', *asserted_formulae]
            new_fn_symbols, formula_to_emit = preprocess_ast(formula_to_emit, constant_function_symbols=fn_symbols, bool_vars=set())
            output = writer(formula_to_emit)
            print(output)

            # We are not catching any errors here, if an exception is raised it will kill the interpreter and the exit code
            # will be non-zero
            return True

running_modes_procedure_table = {
    RunnerMode.BENCHMARK: run_in_benchmark_mode,
    RunnerMode.GET_SAT: run_in_getsat_mode,
    RunnerMode.CONVERT_FORMULA: convert_smt_to_other_format,
}

run_successful = running_modes_procedure_table[runner_mode](args)
sys.exit(0 if run_successful else 1)
