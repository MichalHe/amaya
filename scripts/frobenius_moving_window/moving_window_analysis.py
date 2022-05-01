import argparse
from dataclasses import dataclass
import json
import logging
from matplotlib import pyplot as plt
import subprocess
import sys
from typing import Dict, List


FROBENIUS_FORMULA_GENERATOR_PATH = './frobenius_generator.py'

SMT_SOLVERS = {
    'z3': ['/home/codeboy/work/misc/z3-4.8.16-x64-glibc-2.31/bin/z3', '-smt2'],
    'cvc4': ['cvc4'],
    'cvc5': ['/home/codeboy/work/misc/cvc5-Linux'],
    'amaya': ['python3', '../../run-amaya.py', 'get-sat'] ,
    'amaya-mtbdd': ['python3', '../../run-amaya.py', '--backend', 'MTBDD', '-q', 'get-sat'],
}


@dataclass
class DataPoint(object):
    """
    Class holding collection of facts and statistics about one solver execution.
    """
    window_start_index: int
    primes: List[int]
    execution_status: str
    execution_time: float
    """Execution time in seconds of a solver in seconds."""

    def into_dict(self) -> Dict[str, str]:
        return {
            'window_start_index': self.window_start_index,
            'window': self.primes,
            'status': self.execution_status,
            'runtime': self.execution_time
        }

    def into_csv_row(self, separator=',') -> str:
        return separator.join((str(self.primes), str(self.execution_time)))


def read_primes_file(filename='primes.csv') -> List[int]:
    """
    Reads and returns the primes present in the given file.

    The primes are expected to be at the first line and should be separated by comma.
    """
    # All primes are present on 1 line and are separated by commas
    with open(filename, 'r') as primes_file:
        primes_line = primes_file.readline()
        primes_string = primes_line.split(',')
        primes = list(map(int, primes_string))
        return primes


def generate_frobenius_formula_for_primes(primes: List[int], formula_dst: str = '/tmp/frobenius.smt2'):
    """
    Generates formula for the frobenius coin problem in the SMT2 format.

    The resulting formula is then written to a file specified by formula_dst argument.
    """

    logging.debug(f'Spawning formula generator for: {primes}')

    generator_arg = ','.join(map(str, primes))
    subprocess_result = subprocess.run(['python3', FROBENIUS_FORMULA_GENERATOR_PATH, generator_arg], 
                                       stdout=subprocess.PIPE, text=True)

    fail_desc = 'The script generating the frobenius coin problem formula in SMT2 finished with nonzero return code.'
    assert subprocess_result.returncode == 0, fail_desc

    with open(formula_dst, 'w') as formula_file:
        formula_file.write(subprocess_result.stdout)
    logging.debug(f'The frobenius problem formula has been written to {formula_dst}.')


def generate_subformula_for_primes(primes: List[int], formula_dst: str = '/tmp/f.smt2'):
    """
    Generate the problematic subformula.
    """
    from subformula_generator import generate_formula

    print(f'Generating formula for {primes}', file=sys.stderr)

    assert 2 == len(primes), f'Too many primes given: {primes}'
    formula = generate_formula(w1=primes[0], w2=primes[1])
    with open(formula_dst, 'w') as output_file:
        output_file.write(formula)


def run_solver_on_formula(solver_with_args: List[str],
                          formula_path: str = '/tmp/frobenius.smt2',
                          timeout_secs: int = 30) -> float:
    """
    Executes the solver with its arguments on the given smt2 formula
    with the given timout and measures its runtime.

    :returns: Solver runtime in seconds with 1s/100 precision.
    """
    logging.debug(f'Timing the execution of {solver_with_args[0]}')
    result = subprocess.run(['time', '-f', r'%e', *solver_with_args, formula_path],
                            text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            timeout=timeout_secs)

    fail_desc = (f'Solver finished with nonzero exit code.\n',
                 f'>>stderr: \n{result.stderr}\n' 
                 f'>>stdout: \n{result.stdout}')
    assert result.returncode == 0, fail_desc
    
    runtime = float(result.stderr.strip())

    logging.debug(f'Done. Runtime: {runtime}s')
    return runtime


def draw_scatter(datapoints: List[DataPoint]):
    """
    Creates a matplotlib scatter chart displaying the measured runtimes and shows it on the screen.
    """
    x: List[float] = []
    y: List[float] = []
    xtick_labels: List[str] = []

    for datapoint in datapoints:
        x.append(datapoint.window_start_index)
        y.append(datapoint.execution_time)
        xtick_labels.append(str(datapoint.primes))

    plt.scatter(x, y, marker='1')
    plt.ylabel('[s]')
    plt.xlabel('primes')
    plt.xticks(ticks=x, labels=xtick_labels, rotation=70)
    plt.show()


def perform_moving_window_analysis(solver: List[str],
                                   primes: List[int],
                                   window_size: int,
                                   grace_count: int = 3,
                                   timeout=60,
                                   subformula=False):
    """
    Measure runtime of a given solven for instances of the Frobenius coin problem 
    with the `window_size` coins until the solver times out.

    Creates a windows of the given size and moves it over the given list of primes.
    The primes in the window are used to generate a frobenius coin problem formula
    that is fed to the given solver, checking where is the point in which the solver
    starts to time out.

    :param solver: The solver executable with possible args.
    :param primes: The list of primes through with will the moving window go.
    :param window_size: The size of the moving window.
    :param grace_count: How many times can the solver execution time out, before
                        terminating the analysis.
    :param timeout: Solver timeout.
    """
    datapoints: List[DataPoint] = []
    window_start_i = 0
    
    gen_formula_handle = generate_subformula_for_primes if subformula else generate_frobenius_formula_for_primes
    formula_path = '/tmp/f.smt2'

    while grace_count > 0:
        window = primes[window_start_i:window_start_i + window_size]
        gen_formula_handle(window, formula_path)
        try:
            runtime = run_solver_on_formula(solver, timeout_secs=timeout, formula_path=formula_path)
            logging.info(f'Window#{window_start_i}={window} runtime={runtime}s')
            datapoints.append(
                DataPoint(window_start_index=window_start_i,
                          primes=window,
                          execution_status='ok',
                          execution_time=runtime))
        except subprocess.TimeoutExpired:
            logging.info(f'Command timed out for window: {window}, (timeout={timeout}')
            grace_count -= 1
            datapoints.append(
                DataPoint(window_start_index=window_start_i,
                          primes=window,
                          execution_status='timeout',
                          execution_time=-1.0))
        finally:
            window_start_i += 1
    logging.info(f'Grace exhaused - last window to execute: {window}')
    return datapoints


arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('-t',
                        '--timeout',
                        type=int,
                        default=60,
                        help='Solver timeout in seconds.')
arg_parser.add_argument('-g',
                        '--grace',
                        dest='grace',
                        type=int,
                        default=1,
                        help=('How many successive windows to try until analysis termination'
                              ' when the solver starts to time out.'))
arg_parser.add_argument('-w',
                        '--window',
                        dest='window_size',
                        type=int,
                        default=3,
                        help='The size of the moving window')

arg_parser.add_argument('-d',
                        '--debug',
                        action='store_true',
                        default=False,
                        help='Debug output.')

arg_parser.add_argument('-v',
                        '--verbose',
                        action='store_true',
                        default=False,
                        help='Print what is going on.')

arg_parser.add_argument('-s',
                        '--subformula',
                        action='store_true',
                        default=False,
                        help='Generate subformula instead of the entire formula.')

arg_parser.add_argument('solver', choices=list(SMT_SOLVERS.keys()))

args = arg_parser.parse_args()
solver = SMT_SOLVERS[args.solver]

if args.debug:
    logging.getLogger().setLevel(logging.DEBUG)
elif args.verbose:
    logging.getLogger().setLevel(logging.INFO)

primes = read_primes_file()

data_points = perform_moving_window_analysis(solver, primes, args.window_size, 
                                             args.grace, timeout=args.timeout, subformula=args.subformula)

for point in data_points:
    print(point.into_csv_row())

# draw_scatter(data_points)
