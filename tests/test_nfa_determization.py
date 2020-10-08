import pytest
from inequations_data import Inequality
from inequations import build_nfa_from_inequality
from automatons import AutomatonType


@pytest.fixture
def simple_nfa():
    ineq = Inequality(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )

    return build_nfa_from_inequality(ineq)


def test_simple_nfa_determinization(simple_nfa):

    assert simple_nfa.automaton_type == AutomatonType.NFA

    dfa = simple_nfa.determinize()
    assert dfa
    assert len(dfa.states) == 8
    assert len(dfa.final_states) == 4
    assert len(dfa.initial_states) == 1
    assert dfa.automaton_type == AutomatonType.DFA

    expected_states = [
        (2, ), (0, ), (-1, ), (-2, ),
        (1, 'FINAL'), (0, 'FINAL'), (-1, 'FINAL'), (-2, 'FINAL')
    ]

    # @TODO @Hack: This is needed because there is no order quaranteed on the
    # name of the meta state
    permuted_expected_states = dict()

    for state in dfa.states:
        state_val = state.state

        if state_val not in expected_states:
            # Reorder state and try again
            permuted_state = (state_val[1], state_val[0])
            assert permuted_state in expected_states

            # Map the value from expected to the actual *state_val*
            permuted_expected_states[permuted_state] = state_val
        else:
            # No reordering needed in this case
            permuted_expected_states[state_val] = state_val

    # Test whether there are transitions present
    e_transitions = [
        ((2, ), (0, 0), (1, 'FINAL')),
        ((-2, ), (1, 0), (-2, 'FINAL')),

        ((0, 'FINAL'), (1, 0), (-1, 'FINAL')),
        ((0, 'FINAL'), (1, 1), (-1, 'FINAL')),

        ((0, 'FINAL'), (0, 0), (0, 'FINAL')),  # Test loop

        ((-2, ), (0, 0), (-1, )),
        ((-2, ), (0, 1), (-1, )),
        ((-2, ), (1, 0), (-2, 'FINAL')),
        ((-2, ), (1, 1), (-2, )),
    ]

    ne_transitions = [
        ((-2, ), (1, 1), (-1, 'FINAL')),
        ((-1, ), (1, 0), (0, )),  # Test existing transition with different symbol
    ]

    for transition in e_transitions:
        origin, symbol, dest = transition
        # perform state name correction
        origin = permuted_expected_states[origin]
        dest = permuted_expected_states[dest]
        assert dest in dfa.get_transition_target(origin, symbol)

    for transition in ne_transitions:
        origin, symbol, dest = transition
        # perform state name correction
        origin = permuted_expected_states[origin]
        dest = permuted_expected_states[dest]
        assert dfa.get_transition_target(origin, symbol) is None or dest not in dfa.get_transition_target(origin, symbol)

    # Test whether the automaton has some target state for every symbol in
    # alphabet

    for state in dfa.states:
        for symbol in dfa.alphabet.symbols:
            assert len(dfa.get_transition_target(state.state, symbol)) == 1
