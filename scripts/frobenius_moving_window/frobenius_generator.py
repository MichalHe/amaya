#!/usr/bin/python3
import argparse
from collections.abc import Sequence
import os
import sys
from typing import List


def weighted_sum(coefs, _vars):
    return '(+ {0})'.format(' '.join(f'(* {coef} {var})' for coef, var in zip(coefs, _vars)))


def conjunction(*args):
    return '(and {0})'.format(' '.join(args))


def not_eq(left, right):
    return f'(not (= {left} {right}))'


def forall(vars, formula):
    binding = ' '.join([f'({var} Int)' for var in vars])
    return f'(forall ({binding}) {formula})'


def implies(left, right):
    return f'(=> {left} {right})'


def gen_is_frobenius_candidate(var, coeficients, exist_var_prefix='x'):
    binding_vars = [f'{exist_var_prefix}{i}' for i, _ in enumerate(coeficients)]
    all_binding_vars_gte_zero = [f'(<= 0 {var})' for var in binding_vars]

    return forall(
        binding_vars,
        implies(
            conjunction(*all_binding_vars_gte_zero),
            not_eq(weighted_sum(binding_vars, coeficients), var)
        ))


def ineq(left, right):
    return f'(<= {left} {right})'


def smt_preamble(var):
    preable = [
        '(set-logic LIA)',
        f'(declare-fun {var} () Int)',
        ''
    ]
    return '\n'.join(preable)


def smt_fin():
    fin = [
        '(check-sat)',
        '(exit)',
        ''
    ]
    return '\n'.join(fin)


def _assert(formula):
    return f'(assert {formula})'


def generate_frobenius_number_formula(coefs):
    formula = conjunction(
        ineq('0', 'P'),
        gen_is_frobenius_candidate('P', coefs),
        forall(
            ['R'],
            implies(
                gen_is_frobenius_candidate('R', coefs),
                ineq('R', 'P'))))

    return smt_preamble('P') + _assert(formula) + '\n' + smt_fin()


def make_argument_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('coin_weights', metavar='W', nargs='*', type=int)
    parser.add_argument('-i', '--weights-file', help='A file with coin weights, written on a single line, separated by commas.')
    parser.add_argument('-w', '--window-size', default=2, type=int, help='How many consequent weights should be taken to produce a formula.')
    parser.add_argument('-o', '--output-dir', default='./frobenius-formulae', help='Where to create files with the resulting formulae.')
    parser.add_argument('-f', '--formula-count', default=0, type=int, help='How many formulae to create, 0 for all with available weights.')
    return parser


def read_weights_file(weights_file: str) -> Sequence[int]:
    weights: List[int] = []
    with open(weights_file) as input_file:
        for line in input_file.readlines():
            line = line.strip()
            if not line:
                continue
            return [int(weight.strip()) for weight in line.split(',')]
    return weights


def generate_formulae_to_folder(weights: Sequence[int], window_size: int, output_folder: str, formula_count: int):
    if formula_count == 0:
        formula_count = len(weights) - (window_size - 1)

    print(f'Will generate {formula_count} formulae.', file=sys.stderr)

    for formula_idx in range(formula_count):
        current_weights = weights[formula_idx:formula_idx+window_size]
        formula = generate_frobenius_number_formula(current_weights)

        weights_fmt = '_'.join(str(weight) for weight in current_weights)
        output_filename = f'fcp_{weights_fmt}.smt2'
        dest_path = os.path.join(output_folder, output_filename)

        with open(dest_path, 'w') as output_file:
            print(f'Creating {dest_path} with weights {current_weights}', file=sys.stderr)
            output_file.write(formula)


if __name__ == '__main__':
    parser = make_argument_parser()
    args = parser.parse_args()
    if args.coin_weights:
        print(f'Coin weights are present in argv, ignoring -i if present.\n', file=sys.stderr)
        coin_weights = sorted(set(args.coin_weights))
        sys.stderr.write(f'Using coin weights: {coin_weights}\n')
        formula = generate_frobenius_number_formula(coin_weights)
        print(formula)
    elif args.weights_file:
        if not os.path.exists(args.output_dir):
            print(f'The output folder {args.output_dir} (-o) does not exists', file=sys.stderr)
            parser.print_help()
            sys.exit(1)

        print(f'Using coin weights file: {args.weights_file}', file=sys.stderr)
        print(f'Using coin window size : {args.window_size}', file=sys.stderr)
        weights = read_weights_file(args.weights_file)
        generate_formulae_to_folder(weights, args.window_size, args.output_dir, args.formula_count)

    else:
        parser.print_help()
        sys.exit(1)
