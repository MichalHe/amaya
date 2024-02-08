#!/usr/bin/env python3
import argparse
from typing import List
import pandas as pd
import sys


def read_csv(path: str):
    return pd.read_csv(path, sep=';')


def make_argument_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('reference', help='Path to the CSV containing cvc5 and z3 results.')
    parser.add_argument('ours_results', help='Path to the CSV containing our results.')
    parser.add_argument('--reference', dest='reference_solvers', default=['z3', 'cvc5'], nargs='*')
    parser.add_argument('-ours', dest='our_solver', default='amaya')
    return parser


def check_for_different_results(df: pd.DataFrame, reference_solvers: List[str], our_solver: str):
    our_column = our_solver + '-result'
    reference_columns = [solver + '-result' for solver in reference_solvers]

    our_valid = (df[our_column] != 'TO') & (df[our_column] != 'ERR')
    any_result_differ = False
    for ref_column in reference_columns:
        ref_valid = (df[ref_column] != 'TO') & (df[ref_column] != 'ERR')
        results_differ = df[ref_column] != df[our_column]
        different_results = df[our_valid & ref_valid & results_differ]

        print(f'Results differing from {ref_column}:')
        for i, row in different_results.iterrows():
            print(f" > ours={row[our_column]} theirs={row[ref_column]} :: {row['name']}")
            any_result_differ = True

    return any_result_differ


def merge_dataset(reference, our_results, reference_solvers: List[str], our_solver: str):
    our_column = our_solver + '-result'
    if our_column in reference.columns:
        reference.drop(our_column, inplace=True)

    merged = pd.merge(reference, our_results, on=['name'], how='inner')
    cols_to_strip = [our_column] + [solver + '-result' for solver in reference_solvers]

    for col in cols_to_strip:
        merged[col] = merged[col].apply(str.strip)
    return merged


def print_timeouts(df, our_solver: str):
    our_col = our_solver + '-result'
    timeouts = (df[our_col] == 'TO')
    errors = (df[our_col] == 'ERR')

    print('Timeouts: ')
    name = 'name'
    cnt = 0
    for i, row in df[timeouts].iterrows():
        print(f' > ({cnt}) {row[name]}')
        cnt += 1

    print('Errors: ')
    for i, row in df[errors].iterrows():
        print(f' > ({cnt}) {row[name]}')
        cnt += 1


if __name__ == '__main__':
    parser = make_argument_parser()
    args = parser.parse_args()

    reference = read_csv(args.reference)
    ours = read_csv(args.ours_results)

    df = merge_dataset(reference, ours, args.reference_solvers, args.our_solver)
    any_result_differ = check_for_different_results(df, args.reference_solvers, args.our_solver)
    print_timeouts(df, args.our_solver)
    sys.exit(any_result_differ)
