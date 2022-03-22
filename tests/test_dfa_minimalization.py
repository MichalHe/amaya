import pytest
from amaya.automatons import NFA, AutomatonType
from amaya.alphabet import LSBF_Alphabet
from tests.conftest import ResolutionState


alphabet = LSBF_Alphabet.from_variable_id_pairs((('x', 1), ))


@pytest.fixture
def nonminimal_dfa() -> NFA:
    """
    Fixture - DFA suitable for minimization.
    
    Source: https://en.wikipedia.org/wiki/DFA_minimization#/media/File:DFA_to_be_minimized.jpg
    States are mapped to ints for consistency:
        a -> 0, b -> 1, c -> 2, d -> 3, e -> 4, f -> 5
    """
    dfa = NFA(alphabet, AutomatonType.DFA)
    
    states = set(range(6))
    dfa.states = states
    dfa.add_initial_state(0)
    dfa.final_states = set((2, 3, 4))
    dfa.used_variables = [1]

    transitions = [
        (0, (0,), 1),
        (0, (1,), 2),

        (1, (0,), 0),
        (1, (1,), 3),

        (2, (0,), 4),
        (2, (1,), 5),

        (3, (0,), 4),
        (3, (1,), 5),

        (4, (0,), 4),
        (4, (1,), 5),

        (5, (0,), 5),
        (5, (1,), 5),
    ]

    for source, symbol, destination in transitions:
        dfa.update_transition_fn(source, symbol, destination)
    return dfa


@pytest.fixture
def expected_minimial_dfa() -> NFA:
    """
    Fixture - Minimal DFA eqivalent to the one returned by the dfa() fixture.
    Source: https://en.wikipedia.org/wiki/DFA_minimization#/media/File:Minimized_DFA.jpg
    States are mapped to ints for consistency:
        (a,b) -> 0
        (c, d, e) -> 1
        (f,) -> 2
    """
    dfa = NFA(alphabet, AutomatonType.DFA)
    
    dfa.states = set(range(3))
    dfa.add_initial_state(0)
    dfa.add_final_state(1)
    dfa.used_variables = [1]

    transitions = [
        (0, (0,), 0),
        (0, (1,), 1),

        (1, (0,), 1),
        (1, (1,), 2),

        (2, (0,), 2),
        (2, (1,), 2),
    ]

    for source, symbol, destination in transitions:
        dfa.update_transition_fn(source, symbol, destination)
    return dfa



def test_dfa_minimization(nonminimal_dfa: NFA, expected_minimial_dfa):
    """ 
    Verify that the given DFA is minimized as expected.
    """
    act_minimal_dfa = nonminimal_dfa.minimize() 

    assert len(act_minimal_dfa.states) == len(expected_minimial_dfa.states)
    assert len(act_minimal_dfa.initial_states) == len(expected_minimial_dfa.initial_states)

    q0 = ResolutionState()
    q1 = ResolutionState()
    q2 = ResolutionState()

    automaton_struct = [
        (q0, (0,), q0),
        (q0, (1,), q1),

        (q1, (0,), q1),
        (q1, (1,), q2),

        (q2, (0,), q2),
        (q2, (1,), q2),
    ]
    
    q0.bind(next(iter(act_minimal_dfa.initial_states)))

    for source, symbol, dest in automaton_struct:
        dest_tuple = act_minimal_dfa.get_transition_target(source.get(), symbol)
        assert len(dest_tuple) == 1, \
                'The minimal DFA should have at max only 1 dest target per symbol'

        dest_state = next(iter(dest_tuple))

        dest.bind(dest_state)
