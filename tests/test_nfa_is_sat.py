import pytest
from automatons import NFA, LSBF_Alphabet, AutomatonType


@pytest.fixture()
def satisfiable_automaton() -> NFA:
    nfa = NFA(
        alphabet=LSBF_Alphabet.from_variable_ids([1, 2]),
        automaton_type=AutomatonType.NFA
    )

    nfa_states = ['s', 'f', 1, 2, 3]

    for state in nfa_states:
        nfa.add_state(state)
    nfa.add_final_state('f')
    nfa.add_initial_state('s')

    nfa_transitions = [
        # Valid path to final state
        ('s', (1, 1), 1),
        (1, (1, 1), 2),
        (2, (1, 1), 2),
        (2, (1, 1), 'f'),

        # Dead end
        ('s', ('*', '*'), 3),
        (3, (1, 1), 3),

    ]

    for transition in nfa_transitions:
        origin, symbol, destination = transition
        nfa.update_transition_fn(origin, symbol, destination)

    return nfa


@pytest.fixture()
def nonsatisfiable_automaton() -> NFA:
    nfa = NFA(
        alphabet=LSBF_Alphabet.from_variable_ids([1, 2]),
        automaton_type=AutomatonType.NFA
    )

    nfa_states = ['s', 'f', 1, 2, 3]

    for state in nfa_states:
        nfa.add_state(state)
    nfa.add_final_state('f')
    nfa.add_initial_state('s')

    nfa_transitions = [
        # Valid path to final state
        ('s', (1, 1), 1),
        (1, (1, 1), 2),
        (2, (1, 1), 2),
        (2, (1, 1), 3),

        # Dead end
        ('s', ('*', '*'), 3),
        (3, (1, 1), 3),

        ('f', (1, 1), 'f'),
    ]

    for transition in nfa_transitions:
        origin, symbol, destination = transition
        nfa.update_transition_fn(origin, symbol, destination)

    return nfa


def test_satisfiable(satisfiable_automaton: NFA, nonsatisfiable_automaton: NFA):
    is_sat, word = satisfiable_automaton.is_sat()
    assert is_sat
    expected_word = [
        (1, 1),  # s -> 1
        (1, 1),  # 1 -> 2
        (1, 1),  # 2 -> f
    ]
    assert word == expected_word

    is_sat, word = nonsatisfiable_automaton.is_sat()
    assert not is_sat
    assert word == []
