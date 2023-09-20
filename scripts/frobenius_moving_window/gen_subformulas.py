"""
Generate the given number of instances of the projection onto z-axis formula into the given folder.
"""
import argparse
import os
from typing import List
import sys

from subformula_generator import generate_formula


def mk_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('formula_count', type=int, help='The number of formulae to generate')
    parser.add_argument('dest_dir', help='The folder to output the generated formulae to')
    return parser

def read_primes(primes_path: str = './primes.csv') -> List[int]:
    with open(primes_path) as input_file:
        return [int(prime) for prime in input_file.read().split(',')]

def generate_formulae(formulae_count: int, dest_path: str):
    
    dest_path = os.path.abspath(dest_path)
    
    if os.path.exists(dest_path):
        if not os.path.isdir(dest_path):
            raise ValueError('The supplied path is not a directory!')
    else:
        os.mkdir(dest_path)

    primes = read_primes()
    for i in range(formulae_count):
        window = primes[i:i+2]  # Assume window size is 2

        formula_str = generate_formula(*window)

        formula_filename = f'{i}.smt2'

        with open(os.path.join(dest_path, formula_filename), 'w') as output_file:
            print(f'Writing {formula_filename}')
            output_file.write(formula_str)

if __name__ == '__main__':
    args = mk_arg_parser().parse_args()
    generate_formulae(args.formula_count, dest_path=args.dest_dir)
