"""
Plots the given measured runtimes of executed solvers.
"""

import argparse
import csv
from dataclasses import dataclass
import os
from typing import List

import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import numpy as np
import scipy.interpolate
import scipy.optimize


arg_parser = argparse.ArgumentParser(description=__doc__)

arg_parser.add_argument('-t', '--used-timeout',
                        help='The timeout (in seconds) used when running the benchmarks.',
                        dest='timeout',
                        type=int,
                        default=120)


arg_parser.add_argument('dataset',
                        nargs='+',
                        help='Specifies solver and dataset used. Expected form: solver,path_to_dataset')

arg_parser.add_argument('-I', '--no-interpolate',
                        action='store_false',
                        default=True,
                        help='Do not interpolate the datasets with a cubic curve.')

arg_parser.add_argument('-P', '--no-patch',
                        action='store_false',
                        default=True,
                        help='Do not create the rectangle highlighting the results of the worst solver.')

arg_parser.add_argument('-s', '--save',
                        type=str,
                        dest='save_path',
                        help='Save generated plot instead of showing it (pdf).')

args = arg_parser.parse_args()


@dataclass
class Dataset(object):
    solver: str
    coin_deniminations: List[str]
    runtimes: List[float]


def read_dataset(solver: str, path: str) -> Dataset:
    with open(os.path.abspath(path)) as dataset_file:
        # Do manual parsing of the CSV as the coin denoms have comma in them
        denoms, runtimes = [], []
        for line in dataset_file:
            coin_denoms, runtime_str = line.rstrip().rsplit(',', maxsplit=1)
            runtime = float(runtime_str)
            denoms.append(coin_denoms)
            runtimes.append(runtime)

        return Dataset(solver=solver, coin_deniminations=denoms, runtimes=runtimes)



def read_datasets_from_args(arg_datasets: List[str]) -> List[Dataset]:
    datasets = []
    for arg in arg_datasets:
        print(arg)
        solver, dataset_path = arg.split(',', maxsplit=1)
        dataset = read_dataset(solver, dataset_path)
        datasets.append(dataset)
    return datasets


def pad_datasets_with_timeout(datasets: List[Dataset], timeout: float) -> List[List[float]]:
    """
    Pads the given execution times with timeout so that they have the same length.
    """
    largest_dataset = max(datasets, key=lambda dataset: len(dataset.runtimes))

    for dataset in datasets:
        missing_padding = [timeout] * (len(largest_dataset.runtimes) - len(dataset.runtimes))
        dataset.runtimes += missing_padding

        missing_coin_denoms = largest_dataset.coin_deniminations[len(dataset.coin_deniminations):]
        dataset.coin_deniminations += missing_coin_denoms

        for i, runtime in enumerate(dataset.runtimes):
            if runtime < 0:
                dataset.runtimes[i] = timeout


def plot_datasets(datasets: List[Dataset], timeout: int = 120, interpolate: bool = True, draw_patch: bool = True):
    """
    Plots the datasets.
    """
    fig, ax = plt.subplots(figsize=(7, 7))

    dataset_representative = datasets[0]
    x_values = [i + 1 for i in range(len(dataset_representative.runtimes))]
    x_tick_labels = list(dataset_representative.coin_deniminations)

    plt.axhline(y=0, color='gray', linestyle='-', linewidth=0.5)

    plt.xticks(x_values, labels=x_tick_labels, rotation=70)

    plt.xlabel('Coin denominations', fontsize=15)
    plt.ylabel('Runtime [s]', fontsize=15)

    for dataset in datasets:
        plt.scatter(x_values, dataset.runtimes, marker='+', label=dataset.solver)

    if interpolate:
        def exponential(x, a, b, c):
            return c + a * np.exp(b*x)
        
        for dataset in datasets:
            # Select the dataset valid range (without the added padding timeouts)
            first_timeout_i = dataset.runtimes.index(timeout)
            valid_x_values = x_values[0:first_timeout_i+1]  # include the first timeout too
            valid_y_values = dataset.runtimes[0:first_timeout_i+1]

            # Place an exponential across the selected values
            fitted_params = scipy.optimize.curve_fit(exponential, valid_x_values, valid_y_values)    

            # Oversample the exponential on the valid x interval (we don't want to sample where timeouts are as that
            # would yield fn-values way beyond plot boundaries
            exp_x_sample_points = np.arange(valid_x_values[0], valid_x_values[-1] + 0.1, 0.1) 
            exp_y_points = exponential(exp_x_sample_points,
                                       a=fitted_params[0][0],
                                       b=fitted_params[0][1],
                                       c=fitted_params[0][2])
            plt.plot(exp_x_sample_points, exp_y_points, linewidth=0.6)
    
    if draw_patch:
        worst_dataset = min(datasets, key=lambda dataset: dataset.runtimes.index(timeout)) 
        rectangle_left_bottom = (dataset.runtimes.index(timeout) + 0.5, timeout - 0.5)
        height = 1.0
        width = len(dataset.runtimes) - dataset.runtimes.index(timeout)
        rectangle = Rectangle(rectangle_left_bottom, width, height, color='orange', alpha=0.2)
        ax.add_patch(rectangle)

    plt.axhline(y=timeout, color='black', linestyle='--', linewidth=0.5)
    plt.text((x_values[0] + x_values[-1])/2, timeout+2, f'Timeout={timeout}s', ha='center')

    plt.legend()
    plt.tight_layout()
    plt.subplots_adjust(left=0.09,
                        bottom=0.15, 
                        right=0.95, 
                        top=0.95, 
                        wspace=0.4, 
                        hspace=0.4)


datasets = read_datasets_from_args(args.dataset)
pad_datasets_with_timeout(datasets, args.timeout)
plot_datasets(datasets)

if args.save_path:
    plt.savefig(args.save_path, dpi=120, format='pdf')
else:
    plt.show()
