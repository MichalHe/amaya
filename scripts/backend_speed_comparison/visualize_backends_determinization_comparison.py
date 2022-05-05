import argparse
import csv
import sys
from typing import List, Tuple

import numpy as np
import matplotlib.pyplot as plt
import scipy.optimize

arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('dataset', help='Path to the dataset CSV file.')
arg_parser.add_argument('-o', dest='output_file', help='Save to pdf file instead of showing the figure.')
arg_parser.add_argument('-i', '--interpolate',
                        dest='interpolate',
                        action='store_true',
                        default=False,
                        help='Interpolate the scatter plot with a cubic spline.')
arg_parser.add_argument('-s', '--y-scale',
                        dest='y_scale',
                        choices=('log', 'linear', 'semilog', 'logit'),
                        default='log',
                        help='Set the scale for the Y axis.')
arg_parser.add_argument('-t', '--title', dest='title', type=str, help='Plot title.')

args = arg_parser.parse_args()


def exponential(x, a, b):
    return a * np.exp(b*x)


def plot_interpolate(x_values, y_values, color: str, step: float = 0.1):
    x_samples = np.arange(x_values[0], x_values[-1] + step, step)

    xx_values = np.array([x_values[0], x_values[len(x_values)//2], x_values[-1]])
    yy_values = np.array([y_values[0], y_values[len(x_values)//2], y_values[-1]])

    print('Interpolating: {0}'.format(list(zip(x_values, y_values))), file=sys.stderr)
    print('> Using points: {0}'.format(list(zip(xx_values, yy_values))), file=sys.stderr)

    fitted_params = scipy.optimize.curve_fit(exponential, xx_values, yy_values)
    exp_y_points = exponential(x_samples,
                               a=fitted_params[0][0],
                               b=fitted_params[0][1])
    # exp_y_points += y_values[0]
    plt.plot(x_samples, exp_y_points, linewidth=0.6, c=color, linestyle='--')


def read_dataset(path: str) -> Tuple[np.array]:
    with open(path) as input_file:
        reader = csv.reader(input_file)
        rows = [[int(row[0]), float(row[1]), float(row[2])] for row in reader]

        variable_counts, native_runtimes, mtbdd_runtimes = zip(*rows)

    return (np.array(variable_counts), np.array(native_runtimes), np.array(mtbdd_runtimes))


def prepare_figure(variable_counts, native_runtimes, mtbdd_runtimes, args):
    plt.figure(figsize=(5,3))
    plt.scatter(variable_counts, native_runtimes, s=100, c='red', marker='+', label='native backend')
    plt.scatter(variable_counts, mtbdd_runtimes, s=100, c='blue', marker='+', label='MTBDD backend')
    plt.xlabel('Number of variables')
    plt.ylabel('Runtime [s]')
    plt.legend()

    if args.interpolate:
        plot_interpolate(variable_counts, native_runtimes, color='red')
        plot_interpolate(variable_counts, mtbdd_runtimes, color='blue')

    plt.yscale(args.y_scale)
    plt.tight_layout()

    if args.title:
        plt.title(args.title)

    plt.subplots_adjust(left=0.10,
                        bottom=0.15,
                        right=0.95,
                        top=0.88,
                        wspace=0.4,
                        hspace=0.4)


data = read_dataset(args.dataset)
prepare_figure(variable_counts=data[0], native_runtimes=data[1], mtbdd_runtimes=data[2], args=args)

if args.output_file:
    plt.savefig(args.output_file, dpi=300, format='pdf')
else:
    plt.show()
