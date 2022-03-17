import argparse
import logging
from typing import Dict, Set, Tuple, List, Iterable

from alphabet import LSBF_Alphabet
from automatons import DFA, NFA
from log import logger
from relations_structures import Relation, ModuloTerm
from presburger.constructions.naturals import (
    build_dfa_from_linear_inequality,
    build_presburger_modulo_dfa,
)

logger.setLevel(logging.CRITICAL)

CSV_SEPARATOR = ','

DESCRIPTION = ('Get information about automata produced when evaluating '
                '`z - y <= 0 /\\ y <= 0 /\\ m - v <= 300007 /\\ (y - m = 0 (mod M)) '
                'where the modulo M is configurable.\n'
                'The following information is printed (comma separated): '
                'size of the linear automaton, '
                'size of the modulo automaton, '
                'size of their intersection, '
                'number of states pruned when checking emptiness using antichains, '
                'size of the determinized intersection after projecting `m` away'
                'size of this DFA minimized')

arg_parser = argparse.ArgumentParser(description=DESCRIPTION)
arg_parser.add_argument('modulo', type=int, help='The divisor constant used in the modulo term')

args = arg_parser.parse_args()

lin1 = Relation(variable_names=['z', 'y'], variable_coeficients=[1, -1],
                modulo_terms=[], modulo_term_coeficients=[],
                absolute_part=0, operation='<=')

lin2 = Relation(variable_names=['y'], variable_coeficients=[-1],
                modulo_terms=[], modulo_term_coeficients=[],
                absolute_part=0, operation='<=')

lin3 = Relation(variable_names=['m', 'v'], variable_coeficients=[1, -1],
                modulo_terms=[], modulo_term_coeficients=[],
                absolute_part=300007, operation='<=')

mod = Relation(
    variable_names=[],
    variable_coeficients=[],
    modulo_terms=[ModuloTerm(variables=('y', 'm'), variable_coeficients=(1, -1), constant=0, modulo=args.modulo)],
    modulo_term_coeficients=[1],
    absolute_part=0,
    operation='='
)

# Variables: m v y z (alphabetically sorted)
var_id_pairs = [('m', 1), ('v', 2), ('y', 3), ('z', 4)]
alphabet = LSBF_Alphabet.from_variable_id_pairs(var_id_pairs)

a_lin1 = build_dfa_from_linear_inequality(lin1, [var_id_pairs[2], var_id_pairs[3]], alphabet, DFA)
a_lin2 = build_dfa_from_linear_inequality(lin2, [var_id_pairs[2]], alphabet, DFA)
a_lin3 = build_dfa_from_linear_inequality(lin3, [var_id_pairs[0], var_id_pairs[1]], alphabet, DFA)
a_mod = build_presburger_modulo_dfa(mod, [var_id_pairs[0], var_id_pairs[2]], alphabet, DFA)

a_lin = a_lin1.intersection(a_lin2).intersection(a_lin3)

Metastate = Tuple[Tuple[int, int]]

def compute_post(nfa: NFA, labels: Iterable[Tuple[int, int]], symbol, label_to_nfa_state) -> Tuple[Metastate, ...]:
    """Compute the post of the given metastate label."""
    post = set()
    for label in labels:
        state = label_to_nfa_state[label]
        for post_state in nfa.get_transition_target(state, symbol):
            post.add(nfa.state_labels[post_state])
    return tuple(sorted(post))


def get_number_of_states_purged_with_antichains(nfa: NFA) -> int:
    """Get number of states purged when checking language emptiness using antichains."""

    antichains: Set[Metastate] = set()
    explored_states: Set[Metastate] = set()

    # Replace the tuples marking linear components with labels for improved readability
    lin_components_to_numbers = dict((lin[0], i) for i, lin in enumerate(nfa.state_labels.values()))
    new_nfa_labels = {}
    for state, label in nfa.state_labels.items():
        lin, rem = label
        new_nfa_labels[state] = (lin_components_to_numbers[lin], rem.value)
    assert len(nfa.state_labels) == len(new_nfa_labels)
    nfa.state_labels = new_nfa_labels

    label_to_nfa_state = dict((label, state) for state, label in nfa.state_labels.items())
    assert len(label_to_nfa_state) == len(nfa.state_labels)

    metastates_to_explore: List[Metastate] = [
        tuple(nfa.state_labels[initial_state] for initial_state in nfa.initial_states)
    ]

    purged_states = set()
    while metastates_to_explore:
        metastate = metastates_to_explore.pop(-1)
        # print(f'Processing metastate: {metastate}')

        explored_states.add(metastate)

        for symbol in alphabet.symbols:
            post = compute_post(nfa, metastate, symbol, label_to_nfa_state)

            if not post:
                continue

            # Check whether we need to explore this state
            is_post_needless = False
            for antichain_metastate in antichains:
                if set(post).issuperset(antichain_metastate):
                    if set(post) != set(antichain_metastate) and set(post) not in explored_states:
                        purged_states.add(post)
                        # print(f'Explored post {post} is needless as it is a superset of {antichain_metastate}')
                    is_post_needless = True
                    break

            if not is_post_needless:
                antichains.add(post)
                if post not in metastates_to_explore and post not in explored_states:
                    metastates_to_explore.append(post)

    return len(purged_states)


results: Dict[str, int] = {
    'lin_size': len(a_lin.states),
    'mod_size': len(a_mod.states)
}
#print(f'A_lin size: {len(a_lin.states)} A_mod size: {len(a_mod.states)}')
automaton = a_lin.intersection(a_mod)

results['intersection_size'] = len(automaton.states)

automaton.do_projection(2)  # Project 'm' away

results['antichains_purged'] = get_number_of_states_purged_with_antichains(automaton)
determinized_automaton = automaton.determinize()
results['dfa_size'] = len(determinized_automaton.states)
results['min_dfa_size'] = len(determinized_automaton.hopcroft_minimization().states)

csv_header = ('lin_size', 'mod_size', 'intersection_size', 'antichains_purged', 'dfa_size', 'min_dfa_size')
print(CSV_SEPARATOR.join(str(results[field]) for field in csv_header))
