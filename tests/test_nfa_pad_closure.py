import pytest
from automatons import NFA, LSBF_Alphabet, AutomatonType


@pytest.fixture()
def simple_automaton() -> NFA:
    '''
        Automaton, which results from doing projection on NFA build from
        equation []
    '''
    alphabet = LSBF_Alphabet.from_variable_names(['u', 'v'])
    nfa = NFA(alphabet, AutomatonType.NFA)

    nfa.initial_states = set([0])
    nfa.final_states = set(['F'])
    nfa.states = set([0, 1, 'F'])

    nfa.update_transition_fn(0, (0, 0), 0)
    nfa.update_transition_fn(0, (0, 1), 0)
    nfa.update_transition_fn(0, (1, 1), 0)

    nfa.update_transition_fn(0, (0, 0), 'F')
    nfa.update_transition_fn(0, (0, 1), 'F')
    nfa.update_transition_fn(0, (1, 1), 'F')

    nfa.update_transition_fn(0, (1, 0), 1)

    nfa.update_transition_fn(1, (0, 0), 1)
    nfa.update_transition_fn(1, (1, 0), 1)
    nfa.update_transition_fn(1, (1, 1), 1)

    nfa.update_transition_fn(1, (0, 0), 'F')
    nfa.update_transition_fn(1, (1, 0), 'F')
    nfa.update_transition_fn(1, (1, 1), 'F')

    nfa.update_transition_fn(1, (0, 1), 0)

    return nfa


def test_simple_automaton(simple_automaton: NFA):
    simple_automaton.perform_pad_closure()

    expected_final_states = [0, 1, 'F']
    for efs in expected_final_states:
        assert efs in simple_automaton.final_states
