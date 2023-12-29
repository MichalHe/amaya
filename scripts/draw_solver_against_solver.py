import argparse
import csv
import itertools
import matplotlib.pyplot as plt
import numpy as np
import math
import pprint
from typing import (
    Dict,
    List,
    Tuple,
)


DATA = {
    'x': np.array([1, 2, 3, 4, 100, 13]),
    'y': np.array([1, 2, 3, 4, 12, 65]),
}

PLOT_STUFF = ('x', 'y')


def draw_single_plot(solver_pair: Tuple[str, str],
                     data: Dict[str, np.array],
                     target_axis,
                     limits=None,
                     timeout_secs=60,
                     color='red',
                     solver_names: Dict[str,  str] | None = None):

    _solver_names = solver_names if solver_names is not None else {}

    x_solver_data = data[solver_pair[0]]
    y_solver_data = data[solver_pair[1]]

    target_axis.scatter(x_solver_data, y_solver_data, marker='1', color=color, label=solver_pair[1], s=40)

    def calc_limit(bound_val, margin_growth_fun, margin_rounding_fun):
        if bound_val < 0.005:
            bound_val = 0.005
        log = math.log10(bound_val)
        rounded_log = margin_rounding_fun(log)
        if abs(log - rounded_log) < 0.05:
            rounded_log = margin_growth_fun(rounded_log)
        limit = math.pow(10, rounded_log)
        return limit

    if not limits:
        lower_limit = min(np.min(x_solver_data), np.min(y_solver_data))
        lower_limit = calc_limit(lower_limit, lambda margin_log: margin_log - 1, math.floor)
        upper_limit = max(np.max(x_solver_data), np.min(y_solver_data))
        upper_limit = calc_limit(upper_limit, lambda margin_log: margin_log + 1, math.ceil)

        limits = (lower_limit, upper_limit)

    target_axis.set_xlim(limits)
    target_axis.set_ylim(limits)

    target_axis.set_xscale('log')
    target_axis.set_yscale('log')

    lower_limit, upper_limit = limits
    current_line_pos = lower_limit * 10
    for i in range(round(math.log10(lower_limit)), round(math.log10(upper_limit))):
        target_axis.hlines(current_line_pos, limits[0], limits[1], color='gray', linewidth=0.3, linestyle='dotted')
        target_axis.vlines(current_line_pos, limits[0], limits[1], color='gray', linewidth=0.3, linestyle='dotted')
        current_line_pos *= 10
    target_axis.plot(np.array(limits), np.array(limits), color='gray', linewidth=0.5, linestyle='dashed')
    target_axis.set_aspect(1.0)

    target_axis.hlines(timeout_secs, limits[0], limits[1], linestyle='dashed', color='black', linewidth=0.7)
    target_axis.vlines(timeout_secs, limits[0], limits[1], linestyle='dashed', color='black', linewidth=0.7)

    target_axis.set_xlabel(_solver_names.get(solver_pair[0], solver_pair[0]))
    target_axis.set_ylabel(_solver_names.get(solver_pair[1], solver_pair[1]))


def make_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('results_csv')
    parser.add_argument('-t', '--title')
    parser.add_argument('-d', '--field-delimiter', default=';')
    parser.add_argument('-s', '--skip-first-column', default=False, action='store_true')
    parser.add_argument('-o', '--output', default='output.pdf')
    return parser

def load_data_from_csv(csv_path, timeout_secs=60, delimiter=';', skip_first_column=False):
    with open(csv_path) as csv_file:
        reader = csv.reader(csv_file, delimiter=delimiter)
        rows_it = iter(reader)
        header = next(rows_it)[1:]
        data = [list() for solver in header]
        for row in rows_it:
            row = row[1:]
            if 'ERR' in row:
                continue

            for i, point in enumerate(row):
                if point == 'TO':
                    point = timeout_secs
                data[i].append(float(point))

        return {header[i]: np.clip(np.array(data[i]), 0, timeout_secs) for i, _ in enumerate(header)}


if __name__ == '__main__':
    parser = make_arg_parser()
    args = parser.parse_args()
    data = load_data_from_csv(args.results_csv, delimiter=args.field_delimiter)

    solver_pairs: List[Tuple[str, str]] = [
        ('amaya-new-runtime', 'z3-runtime'),
        ('amaya-new-runtime', 'cvc5-runtime'),
        ('amaya-new-runtime', 'princess-runtime'),
    ]
    # for solver_pair in itertools.combinations(data, 2):
    #     if not any('amaya' in solver for solver in solver_pair):
    #       continue
    #     solver_pairs.append(solver_pair)

    # fig, axs = plt.subplots(nrows=len(solver_pairs), figsize=(5, len(solver_pairs)*5))
    fig, axs = plt.subplots(nrows=1, figsize=(7, 7))

    if not isinstance(axs, np.ndarray):
        axs = (axs,)

    if args.title:
        fig.suptitle(args.title)

    fig.tight_layout()
    fig.subplots_adjust(hspace=0.2, left=0.15, bottom=0.1)

    solver_rename = {
        'amaya-old-runtime': 'amaya-runtime',
        'amaya-new-runtime': 'amaya-optimized-runtime',
    }

    colors = ['red', 'blue', 'green', 'magenta']
    for solver_pair, color in zip(solver_pairs, colors):
      draw_single_plot(tuple(sorted(solver_pair)), data, axs[0], color=color)

    # for solver_pair, ax in zip(solver_pairs, axs):
    #     draw_single_plot(tuple(sorted(solver_pair)), data, ax, solver_names=solver_rename)

    # plt.savefig('output.pdf', dpi=600)
    axs[0].legend()

    y_label = '{z3/cvc5/princess}-runtime'
    axs[0].set_ylabel(y_label)

    box = axs[0].get_position()
    axs[0].set_position([box.x0, box.y0, box.width * 0.7, box.height])
    axs[0].legend(loc='center left', bbox_to_anchor=(1, 0.5))

    plt.savefig(args.output, dpi=600)


