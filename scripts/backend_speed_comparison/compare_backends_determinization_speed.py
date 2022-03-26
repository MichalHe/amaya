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
current_dir = os.path.basename(__file__)
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

def generate_automata_for_vars(var_cnt: int) -> Tuple[NFA, MTBDD_NFA]:
    """
    Generates automaton for formula (exists (two vars projected away) (vars * random_coefs)).
    """

    var_names = [chr(ord('a') + i) for i in range(var_cnt)]
    var_id_pairs = [(var, i+1) for i, var in enumerate(var_names)]
    var_ids = [var_id_pair[1] for var_id_pair in var_id_pairs]

    alphabet = LSBF_Alphabet.from_variable_id_pairs(var_id_pairs)

    relation = Relation(variable_names=var_names,
                        variable_coeficients=[random.randint(1, 13) for i in range(var_cnt)],
                        modulo_terms=[],
                        modulo_term_coeficients=[],
                        absolute_part=random.randint(10, 100),
                        operation='<=')

    nfa = build_nfa_from_linear_inequality(relation, var_id_pairs, alphabet, NFA)
    mtbdd_nfa = build_nfa_from_linear_inequality(relation, var_id_pairs, alphabet, MTBDD_NFA)

    # Pick variable tracks to project away
    available_tracks = list(var_ids)
    projected_var_ids: List[int] = []
    for i in range(2):
        projected_var_id = random.choice(available_tracks)
        projected_var_ids.append(projected_var_id)
        available_tracks.remove(projected_var_id)

    for var_id in projected_var_ids:
        nfa = nfa.do_projection(var_id)
        mtbdd_nfa = mtbdd_nfa.do_projection(var_id)


    return (nfa, mtbdd_nfa)


def run_experiemnt(run_count: int, var_count: int) -> ExperimentResult:
    overall_native_runtime, overall_mtbdd_runtime= 0, 0

    for i in range(run_count):
        native_nfa, mtbdd_nfa = generate_automata_for_vars(var_count)
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

    return ExperimentResult(native=overall_native_runtime/run_count,
                            mtbdd=overall_mtbdd_runtime/run_count)


result = run_experiemnt(args.runs, args.variable_count)

if args.output_format == 'csv':
    print(','.join([str(result.native), str(result.mtbdd)]))
