from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    DFA,
    NFA
)
from tests.conftest import ResolutionState

import pytest


@pytest.fixture
def wiki_automaton() -> NFA:
    variable_id_pairs = (('x', 1),)
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    nfa = NFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)
    state_labels = {
        0: 'a',
        1: 'b',
        2: 'c',
        3: 'd',
        4: 'e',
        5: 'f',
    }
    nfa.extra_info['state_labels'] = state_labels

    nfa.states = {0, 1, 2, 3, 4, 5}
    nfa.final_states = {2, 3, 4}
    nfa.initial_states = {0,}

    nfa.used_variables = [1]

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

    return nfa


@pytest.fixture
def automaton2() -> DFA:
    variable_id_pairs = [('x', 1)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)

    dfa = DFA(alphabet=alphabet,
              automaton_type=AutomatonType.DFA,
              states={0, 1, 2, 3, 4, 5},
              final_states={3, 5},
              initial_states={0})

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
    return dfa


def test_wiki_automaton(wiki_automaton: NFA):
    """
    Checks that the hopcrofts minimization works correctly on the automaton found on Wikipedia minimiazation article.

    Link: https://en.wikipedia.org/wiki/DFA_minimization#/media/File:DFA_to_be_minimized.jpg
    Link (minimized): https://en.wikipedia.org/wiki/DFA_minimization#/media/File:Minimized_DFA.jpg
    """

    state0 = ResolutionState('0')
    state1 = ResolutionState('1')
    state2 = ResolutionState('2')

    transitions = (
        (state0, (0,), state0),
        (state0, (1,), state1),

        (state1, (0,), state1),
        (state1, (1,), state2),

        (state2, (0,), state2),
        (state2, (1,), state2),
    )

    minimized_automaton = wiki_automaton.hopcroft_minimization()

    assert len(minimized_automaton.states) == 3
    assert len(minimized_automaton.initial_states) == 1
    assert len(minimized_automaton.final_states) == 1

    state0.bind(next(iter(minimized_automaton.initial_states)))

    for origin_rs, symbol, dest_rs in transitions:
        origin = origin_rs.get()
        dest_set = minimized_automaton.get_transition_target(origin, symbol)
        assert len(dest_set) == 1, 'The resulting automaton should be deterministic'

        dest = next(iter(dest_set))
        dest_rs.bind(dest)

    assert state1.get() in minimized_automaton.final_states


def test_automaton2(automaton2: NFA):

    state0 = ResolutionState('0')
    state1 = ResolutionState('1')
    state2 = ResolutionState('2')

    expected_transitions = (
        (state0, (0,), state1),
        (state0, (1,), state2),
        (state1, (0,), state0),
        (state1, (1,), state2),
        (state2, (0,), state2),
        (state2, (1,), state2),
    )

    minimized_dfa = automaton2.hopcroft_minimization()

    assert len(minimized_dfa.states) == 3
    assert len(minimized_dfa.initial_states) == 1
    assert len(minimized_dfa.final_states) == 1

    state0.bind(next(iter(minimized_dfa.initial_states)))

    # _rs stands for resolution state
    for source_rs, symbol, dest_rs in expected_transitions:
        post = minimized_dfa.get_transition_target(source_rs.get(), symbol)
        assert len(post) == 1, 'Minimized automaton is not DFA'
        dest_rs.bind(next(iter(post)))

    assert state2.get() in minimized_dfa.final_states
