"""
Compare determinization speed using formula atomic formula with random coeficient vector with 2 vars projected away.
"""
import sys
import os
import argparse
import logging
from dataclasses import dataclass
import random
import time
from typing import (
    List,
    Tuple
)

# Modify path so we can load amaya modules
current_dir = os.getcwd()
repository_dir = os.path.join(current_dir, '../../')
sys.path.insert(0, os.path.abspath(repository_dir))

from amaya import logger
from amaya.alphabet import LSBF_Alphabet
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.mtbdd_transitions import MTBDDTransitionFn
from amaya.automatons import AutomatonType, NFA
from amaya.relations_structures import Relation
from amaya.presburger.constructions.integers import build_nfa_from_linear_inequality


@dataclass
class ExperimentResult(object):
    native: float
    mtbdd: float


arg_parser = argparse.ArgumentParser(description=__doc__)

arg_parser.add_argument('benchmarked_routine',
                        choices=['determinization', 'intersection'],
                        help='The automata operation to be benchmarked.')

arg_parser.add_argument('runs',
                        type=int,
                        help='The number of times the experiment should be rerun (with new vectors).')

arg_parser.add_argument('variable_count',
                        type=int,
                        help='The number of variables in the atomic formula used.')

arg_parser.add_argument('-O',
                        '--output-format',
                        dest='output_format',
                        choices=['csv'],
                        default='csv',
                        help='The output format.')

args = arg_parser.parse_args()

logger.setLevel(logging.CRITICAL)

var_names = [chr(ord('a') + i) for i in range(args.variable_count)]
var_id_pairs = [(var, i+1) for i, var in enumerate(var_names)]
var_ids = [var_id_pair[1] for var_id_pair in var_id_pairs]
alphabet = LSBF_Alphabet.from_variable_id_pairs(var_id_pairs)

def generate_random_inequation(min_coef: int = 1, max_coef: int = 13, abs_min: int = 10, abs_max: int = 100) -> Relation:
    """
    Generates random inequation.

    The generated inequation will have its variable coeficients in the range <min_coef, max_coef) and absolute part
    in the range <abs_min, abs_max).
    """
    ineq = Relation(variable_names=var_names,
                    variable_coeficients=[random.randint(min_coef, max_coef) for i in range(args.variable_count)],
                    modulo_terms=[], modulo_term_coeficients=[],
                    absolute_part=random.randint(abs_min, abs_max),
                    operation='<=')
    return ineq


def generate_nfas_to_intersect():
    ineq1 = generate_random_inequation()
    ineq2 = generate_random_inequation()

    native_nfa1 = build_nfa_from_linear_inequality(ineq1, var_id_pairs, alphabet, NFA)
    native_nfa2 = build_nfa_from_linear_inequality(ineq2, var_id_pairs, alphabet, NFA)
    mtbdd_nfa1 = build_nfa_from_linear_inequality(ineq1, var_id_pairs, alphabet, MTBDD_NFA)
    mtbdd_nfa2 = build_nfa_from_linear_inequality(ineq2, var_id_pairs, alphabet, MTBDD_NFA)

    return (native_nfa1, native_nfa2, mtbdd_nfa1, mtbdd_nfa2)


def generate_nfas_to_determinize() -> Tuple[NFA, MTBDD_NFA]:
    """
    Generates automaton for formula (exists (two randomly chosen vars) (vars * random_coefs)).
    """

    ineq = generate_random_inequation()

    nfa = build_nfa_from_linear_inequality(ineq, var_id_pairs, alphabet, NFA)
    mtbdd_nfa = build_nfa_from_linear_inequality(ineq, var_id_pairs, alphabet, MTBDD_NFA)

    # Pick variable tracks to project away
    available_tracks = list(var_ids)
    var_ids_projected_away: List[int] = []
    for i in range(2):
        projected_var_id = random.choice(available_tracks)
        var_ids_projected_away.append(projected_var_id)
        available_tracks.remove(projected_var_id)

    for var_id in var_ids_projected_away:
        nfa = nfa.do_projection(var_id)
        mtbdd_nfa = mtbdd_nfa.do_projection(var_id)

    return (nfa, mtbdd_nfa)


def run_determinization_experiemnt() -> ExperimentResult:
    overall_native_runtime, overall_mtbdd_runtime= 0, 0

    for i in range(args.runs):
        native_nfa, mtbdd_nfa = generate_nfas_to_determinize()
        start_ns = time.time()
        native_nfa.determinize()
        native_runtime = time.time() - start_ns

        start_ns = time.time()
        mtbdd_nfa.determinize()
        mtbdd_runtime = time.time() - start_ns

        overall_mtbdd_runtime += mtbdd_runtime
        overall_native_runtime += native_runtime

        # Clear cache so that MTBDDs do not get faster with repeated experiments
        MTBDDTransitionFn.call_clear_cachce()

    return ExperimentResult(native=overall_native_runtime/args.runs,
                            mtbdd=overall_mtbdd_runtime/args.runs)


def run_intersection_experiment() -> ExperimentResult:
    overall_native_runtime, overall_mtbdd_runtime= 0, 0

    for i in range(args.runs):
        native_nfa1, native_nfa2, mtbdd_nfa1, mtbdd_nfa2 = generate_nfas_to_intersect()
        start_ns = time.time()
        native_nfa1.intersection(native_nfa2)
        native_runtime = time.time() - start_ns

        start_ns = time.time()
        mtbdd_nfa1.intersection(mtbdd_nfa2)
        mtbdd_runtime = time.time() - start_ns

        overall_mtbdd_runtime += mtbdd_runtime
        overall_native_runtime += native_runtime

        # Clear cache so that MTBDDs do not get faster with repeated experiments
        MTBDDTransitionFn.call_clear_cachce()

    return ExperimentResult(native=overall_native_runtime/args.runs,
                            mtbdd=overall_mtbdd_runtime/args.runs)



if args.benchmarked_routine == 'determinization':
    result = run_determinization_experiemnt()
elif args.benchmarked_routine == 'intersection':
    result = run_intersection_experiment()

if args.output_format == 'csv':
    print(','.join([str(result.native), str(result.mtbdd)]))
