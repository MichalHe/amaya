from typing import (
    Callable,
    Type,
    TypeVar,
    Tuple
)

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    DFA,
    NFA
)
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType,
)
from amaya.test_utils import assert_dfas_isomorphic
from tests.conftest import ResolutionState

import pytest


T = TypeVar('T', NFA, MTBDD_NFA)


def make_wiki_automaton(automaton_cls: Type[T]) -> Tuple[T, NFA]:
    variable_id_pairs = (('x', 1),)
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    nfa = automaton_cls(alphabet=alphabet, automaton_type=AutomatonType.DFA,
                        state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None),
                        states={0, 1, 2, 3, 4, 5},
                        initial_states={0},
                        final_states={2, 3, 4},
                        used_variables=[1])
    state_labels = {
        0: 'a',
        1: 'b',
        2: 'c',
        3: 'd',
        4: 'e',
        5: 'f',
    }
    nfa.extra_info['state_labels'] = state_labels

    transitions = (
        ('a', (0,), 'b'),
        ('a', (1,), 'c'),
        ('b', (0,), 'a'),
        ('b', (1,), 'd'),
        ('c', (0,), 'e'),
        ('c', (1,), 'f'),
        ('d', (0,), 'e'),
        ('d', (1,), 'f'),
        ('e', (0,), 'e'),
        ('e', (1,), 'f'),
        ('f', (0,), 'f'),
        ('f', (1,), 'f'),
    )

    reverse_labels = dict((label, state) for state, label in state_labels.items())

    for source_label, symbol, dest_label in transitions:
        nfa.update_transition_fn(reverse_labels[source_label], symbol, reverse_labels[dest_label])

    expected_dfa = NFA(
        alphabet=alphabet,
        state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None),
        states={0, 1, 2},
        initial_states={0},
        final_states={1},
        used_variables=nfa.used_variables
    )
    transitions = (
        (0, (0,), 0),
        (0, (1,), 1),
        (1, (0,), 1),
        (1, (1,), 2),
        (2, (0,), 2),
        (2, (1,), 2),
    )
    for t in transitions:
        expected_dfa.update_transition_fn(*t)

    return (nfa, expected_dfa)


def make_automaton2(automaton_cls: Type[T]) -> Tuple[T, NFA]:
    variable_id_pairs = [('x', 1)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)

    dfa = automaton_cls(alphabet=alphabet,
                        automaton_type=AutomatonType.DFA,
                        states={0, 1, 2, 3, 4, 5},
                        final_states={3, 5},
                        initial_states={0},
                        used_variables=[1],
                        state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))

    transitions = (
        (0, (0,), 1),
        (0, (1,), 3),
        (1, (0,), 0),
        (1, (1,), 3),
        (2, (0,), 1),
        (2, (1,), 4),
        (3, (0,), 5),
        (3, (1,), 5),
        (4, (0,), 3),
        (4, (1,), 3),
        (5, (0,), 5),
        (5, (1,), 5),
    )

    for transition in transitions:
        dfa.update_transition_fn(*transition)

    expected_dfa = NFA(
        alphabet=alphabet,
        state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None),
        used_variables=dfa.used_variables,
        states={0, 1},
        initial_states={0},
        final_states={1},
    )
    expected_transitions = (
        (0, (0,), 0),
        (0, (1,), 1),
        (1, (0,), 1),
        (1, (1,), 1),
    )
    for t in expected_transitions:
        expected_dfa.update_transition_fn(*t)

    return (dfa, expected_dfa)


@pytest.mark.parametrize(
    ('input_output_pair', 'algorithm'),
    [
        (make_automaton2(NFA), NFA.minimize_brzozowski),
        (make_automaton2(NFA), NFA.minimize_hopcroft),
        (make_automaton2(MTBDD_NFA), MTBDD_NFA.minimize_hopcroft),
        (make_wiki_automaton(NFA), NFA.minimize_brzozowski),
        (make_wiki_automaton(NFA), NFA.minimize_hopcroft),
        (make_wiki_automaton(MTBDD_NFA), MTBDD_NFA.minimize_hopcroft),
    ])
def test_minimization(input_output_pair: Tuple[NFA, NFA], algorithm: Callable[[NFA], NFA]):
    input_dfa, expected_output_dfa = input_output_pair
    actual_output = algorithm(input_dfa)
    assert_dfas_isomorphic(actual_output, expected_output_dfa)
