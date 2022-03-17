import argparse
import csv
from dataclasses import dataclass
import os
from typing import List

from matplotlib import pyplot as plt
import numpy as np


@dataclass
class Datapoint(object):
    lin_size: int
    mod_size: int
    intersection_size: int
    antichains_purged: int
    dfa_size: int
    min_dfa_size: int


def read_dataset(path: str) -> List[Datapoint]:
    dataset: List[Datapoint] = []
    csv_header = ('lin_size', 'mod_size', 'intersection_size',
                  'antichains_purged', 'dfa_size', 'min_dfa_size')
    with open(path) as dataset_file:
        reader = csv.reader(dataset_file)
        for row in reader:
            dataset.append(Datapoint(**dict((field, int(row[i])) for i, field in enumerate(csv_header))))
    return dataset


def make_plot(dataset: List[Datapoint]):
    dataset = sorted(dataset, key=lambda point: point.mod_size)

    modulos = np.array([point.mod_size for point in dataset])
    intersection_sizes = np.array([point.intersection_size for point in dataset])
    dfa_sizes = np.array([point.dfa_size for point in dataset])
    min_dfa_sizes = np.array([point.min_dfa_size for point in dataset])
    antichains = np.array([point.antichains_purged for point in dataset])
    
    def plot_intersection_comparison(y, y_label, loc, title):
        axs = plt.subplot2grid((4, 2), loc, colspan=1)
        axs.set_title(title)
        axs.set_xlabel('modulo')
        axs.set_ylabel('#states')
        axs.scatter(modulos, intersection_sizes, label='Intersection size', marker='+', color='gray')
        axs.scatter(modulos, y, label=y_label, marker='+', color='orange')
        axs.legend()
        return axs

    def draw_percent_scatter(y, loc, title):
        y = 100*y
        percent_axis = plt.subplot2grid((4, 2), loc, colspan=1)
        percent_axis.set_title(title)
        percent_axis.scatter(modulos, y, label='% states', marker='+', color='orange')
        percent_axis.plot(modulos, np.repeat(np.average(y), len(modulos)), label='Mean', linestyle='--', color='gray')
        percent_axis.legend()
        return percent_axis

    intersection_vs_dfa = dfa_sizes / intersection_sizes
    antichain_percent = antichains / intersection_sizes
    min_dfa_vs_intersection = min_dfa_sizes / intersection_sizes
    
    plt.figure(figsize=(22, 12))
    plt.suptitle('Formula: ∃m(z - y ≤ 0  ∧  y ≤ 0  ∧  m - v ≤ 300007  ∧  y - m ≡ 0 (mod M))', fontsize=20)
    
    axs0 = plt.subplot2grid((4, 2), (0, 0), colspan=2)
    axs0.set_title('Intersection size')
    axs0.set_xlabel('modulo')
    axs0.set_ylabel('#states')
    axs0.scatter(modulos, intersection_sizes, label='Intersection size', marker='+')
    axs0.scatter(modulos, modulos, label='Modulo automaton size', marker='+')

    axs_antichains = plot_intersection_comparison(antichains, 'States removed', (1, 0), 'Antichains - states removed')
    axs_antichains_percent = draw_percent_scatter(antichain_percent, (1, 1), title='Antichains - % states removed')

    axs_dfa = plot_intersection_comparison(dfa_sizes, 'DFA size', (2, 0), 'DFA from intersection automaton with modulo var projected away')
    axs_dfa_percent = draw_percent_scatter(intersection_vs_dfa, (2, 1), 'DFA size / Intersection size')

    axs_min = plot_intersection_comparison(min_dfa_sizes, 'Min. DFA size', (3, 0), 'Minimized DFA size')
    axs_min_percent = draw_percent_scatter(min_dfa_vs_intersection, (3, 1), 'Minimized DFA / Intersection')

    plt.subplots_adjust(left=0.08, right=(1.0 - 0.08), top=(1.0 - 0.06), bottom=0.06, hspace=0.415, wspace=0.115)


arg_parser = argparse.ArgumentParser()
arg_parser.add_argument('dataset_path', help='Path to the CSV dataset produced by antichain_experiment.py')
arg_parser.add_argument('-s', '--save', type=str, metavar='path', 
                        dest='output_path', help='Save the figure as png instead of showing it')

args = arg_parser.parse_args()

dataset = read_dataset(args.dataset_path)
make_plot(dataset)

if args.output_path:
    plt.savefig(os.path.abspath(args.output_path), dpi=300)
else:
    plt.show()

# plt.show()
