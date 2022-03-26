import argparse
import csv
import sys
from typing import List

import numpy as np
import matplotlib.pyplot as plt
import scipy.interpolate

arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('dataset', help='Path to the dataset CSV file.')
arg_parser.add_argument('-o', dest='output_file', help='Save to pdf file instead of showing the figure.')
arg_parser.add_argument('-i', '--interpolate', 
                        dest='interpolate', 
                        action='store_true', 
                        default=False, 
                        help='Interpolate the scatter plot with a cubic spline.')

args = arg_parser.parse_args()


def read_dataset(path: str) -> List[np.array]:
    with open(path) as input_file:
        reader = csv.reader(input_file)
        rows = [[int(row[0]), float(row[1]), float(row[2])] for row in reader]
        
        variable_counts, native_runtimes, mtbdd_runtimes = zip(*rows)


    return (np.array(variable_counts), np.array(native_runtimes), np.array(mtbdd_runtimes))



def prepare_figure(variable_counts, native_runtimes, mtbdd_runtimes, interpolate=False):
    plt.figure(figsize=(5,3))
    plt.scatter(variable_counts, native_runtimes, s=100, marker='+', label='native backend')
    plt.scatter(variable_counts, mtbdd_runtimes, s=100, c='red', marker='+', label='MTBDD backend')
    plt.xlabel('Number of variables')
    plt.ylabel('Runtime [s]')
    plt.legend()
    
    if interpolate:
        native_curve = scipy.interpolate.CubicSpline(variable_counts, native_runtimes, extrapolate=True)
        mtbdd_curve = scipy.interpolate.CubicSpline(variable_counts, mtbdd_runtimes, extrapolate=True)
        curve_x_points = np.arange(variable_counts[0], variable_counts[-1] + 7*0.01, 0.01)
        plt.plot(curve_x_points, native_curve(curve_x_points), ls='--', linewidth=1)
        plt.plot(curve_x_points, mtbdd_curve(curve_x_points), ls='--', linewidth=1, c='red')
    
    plt.tight_layout()
    plt.subplots_adjust(left=0.12,
                        bottom=0.15, 
                        right=0.95, 
                        top=0.9, 
                        wspace=0.4, 
                        hspace=0.4)

data = read_dataset(args.dataset)
prepare_figure(*data, interpolate=args.interpolate)

if args.output_file:
    plt.savefig(args.output_file, dpi=300, format='pdf')
else:
    plt.show()
