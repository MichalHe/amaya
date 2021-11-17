from typing import Dict, List
import subprocess
import logging
from dataclasses import dataclass
import argparse
from matplotlib import pyplot as plt
import json


FROBENIUS_FORMULA_GENERATOR_PATH = './frobenius_generator.py'
Z3_CMD = ['z3', '-smt2']
CVC5_CMD = ['cvc5']


@dataclass
class DataPoint(object):
    window_start_index: int
    primes: int
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


def read_primes_file(filename='primes.csv') -> List[int]:
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

    generator_argument = ','.join(map(str, primes))
    logging.debug(f'Spawning formula generator for: {primes}')
    subprocess_result = subprocess.run(['python3', FROBENIUS_FORMULA_GENERATOR_PATH, generator_argument], stdout=subprocess.PIPE, text=True)
    assert subprocess_result.returncode == 0, 'The problem generator finished with nonzero return code.'

    with open(formula_dst, 'w') as formula_file:
        formula_file.write(subprocess_result.stdout)
    logging.debug(f'Formula written to {formula_dst}.')


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

    assert result.returncode == 0, 'Solver finished with nonzero return code'

    logging.debug(f'Done. Measured execution time: {result.stderr}s')
    return float(result.stderr)


def draw_scatter(datapoints: List[DataPoint]):
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
                                   timeout=60):
    """
    Creates a windows of the given size and moves it over the given list of primes
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
    while grace_count > 0:
        window = primes[window_start_i:window_start_i + window_size]
        generate_frobenius_formula_for_primes(window)
        try:
            runtime = run_solver_on_formula(solver, timeout_secs=timeout)
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
arg_parser.add_argument('solver', choices=['z3', 'cvc5'])
args = arg_parser.parse_args()

if args.solver == 'z3':
    solver = Z3_CMD
elif args.solver == 'cvc5':
    # Since we have only 2 options, we could've used else. This setup is here
    # for future extensions
    solver = CVC5_CMD

primes = read_primes_file()
data_points = perform_moving_window_analysis(solver, primes, args.window_size, args.grace, timeout=args.timeout)

data_points_dicts = list(map(DataPoint.into_dict, data_points))
print(json.dumps(data_points_dicts))

draw_scatter(data_points)
