#!/usr/bin/env python3
"""
Plots the given measured runtimes of executed solvers.
"""

import argparse
import csv
from collections import defaultdict
from dataclasses import dataclass
import os
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import numpy as np


def make_arg_parser() -> argparse.ArgumentParser:
    arg_parser = argparse.ArgumentParser(description=__doc__)

    arg_parser.add_argument('-t', '--used-timeout',
                            help='The timeout (in seconds) used when running the benchmarks.',
                            dest='timeout',
                            type=float,
                            default=60.0)


    arg_parser.add_argument('results_csv',
                            help='Specifies solver and dataset used. Expected form: solver,path_to_dataset')

    arg_parser.add_argument('-i', '--interpolate',
                            action='store_true',
                            dest='interpolate',
                            default=False,
                            help='Do not place a line segments between individual scatter plots.')

    arg_parser.add_argument('-p', '--draw-patch',
                            action='store_true',
                            default=False,
                            help='Do not create the rectangle highlighting the results of the worst solver.')

    arg_parser.add_argument('-o', '--output',
                            help='Save the figure to a given path instead of showing it.')
    return arg_parser


@dataclass
class Dataset(object):
    coin_weights: List[Tuple[int,...]]
    solver_runtimes: Dict[str, List[float]]


def extract_coin_weights_from_formula_name(formula: str) -> Tuple[int, ...]:
    formula = os.path.basename(formula)
    formula = formula.lstrip('fcp_').rstrip('.smt2')
    weights = tuple(int(weight) for weight in formula.split('_'))
    return weights


def read_results_csv(path: str, timeout_secs=60, sep=';') -> Dataset:

    solver_data: Dict[Tuple[int, ...], List[Tuple[str, float]]] = defaultdict(list)
    
    with open(os.path.abspath(path)) as dataset_file:
        csv_reader = csv.reader(dataset_file, delimiter=sep)
        rows = iter(csv_reader)
        header = next(rows)
        solvers = header[1:]
        for row in rows:
            formula = row[0]
            solver_runtimes = row[1:]

            weights = extract_coin_weights_from_formula_name(formula)
            formula_data = solver_data[weights]

            for solver, solver_runtime in zip(solvers, solver_runtimes):
                solver_runtime = float(solver_runtime) if solver_runtime != 'TO' else timeout_secs
                formula_data.append((solver, solver_runtime))

    coin_weights = sorted(solver_data.keys())
    dataset = Dataset(coin_weights=coin_weights, solver_runtimes=defaultdict(list))

    for coin_weight in coin_weights:
        solver_runtime_pairs = solver_data[coin_weight]
        for solver, runtime in solver_runtime_pairs:
            dataset.solver_runtimes[solver].append(runtime)

    return dataset
               


def format_weights(weights: Tuple[int, ...]) -> str:
    weight_fmt = ','.join(str(weight) for weight in weights)
    return f'{weight_fmt}'


def plot_solver_runtimes(dataset: Dataset, interpolate: bool = True, draw_patch: bool = True, timeout_secs: float = 60.0):
    fig, ax = plt.subplots(figsize=(7, 3.5))

    x_values = [i + 1 for i in range(len(dataset.coin_weights))]
    x_tick_labels = [format_weights(weights) for weights in dataset.coin_weights]

    plt.axhline(y=0, color='gray', linestyle='-', linewidth=0.5)

    plt.xticks(x_values, labels=x_tick_labels, rotation=70)

    plt.xlabel('Coin denominations', fontsize=12)
    plt.ylabel('Runtime [s]', fontsize=12)

    marker_counter = 0
    markers = ['1', '+', 'x']
    for solver, runtimes in dataset.solver_runtimes.items():
        marker = markers[marker_counter]
        marker_counter += 1
        plt.scatter(x_values, runtimes, label=solver, s=120.0, marker=marker)

    if interpolate:
        for solver, runtimes in dataset.solver_runtimes.items():
            plt.plot(x_values, runtimes, linestyle='--', linewidth=0.7, alpha=0.5)

    if draw_patch:
        rectangle_left_bottom = (1, timeout_secs)
        height = 1.0
        width = len(x_values)
        rectangle = Rectangle(rectangle_left_bottom, width, height, color='orange', alpha=0.2)
        ax.add_patch(rectangle)

    plt.axhline(y=timeout_secs, color='black', linestyle='--', linewidth=0.5)
    plt.text((x_values[0] + x_values[-1])/2, timeout_secs+3, f'Timeout={timeout_secs} [s]', ha='center', fontsize=8)

    plt.ylim([0, timeout_secs*1.1])

    plt.legend()  # To specify legend position manually: plt.legend(bbox_to_anchor=(0.73, 0.1))
    plt.tight_layout()
    plt.subplots_adjust(left=0.08,
                        bottom=0.2,
                        right=0.92,
                        top=0.98,
                        wspace=0.4,
                        hspace=0.4)

if __name__ == '__main__':
    parser = make_arg_parser()
    args = parser.parse_args()
    data = read_results_csv(args.results_csv)
    plot_solver_runtimes(data, interpolate=args.interpolate, draw_patch=args.draw_patch, timeout_secs=args.timeout)
    print(data)

    if args.output:
        plt.savefig(args.output, dpi=100, format='pdf')
    else:
        plt.show()
