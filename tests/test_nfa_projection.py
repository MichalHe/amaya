from tests.test_nfa_intersection import mtbdd_nfa1  # NOQA
from mtbdd_automatons import MTBDD_NFA
from automatons import AutomatonSnapshot


def complement_nth_bit(symbol, bit_pos):
    complement_sym = list(symbol)
    if (complement_sym[bit_pos] == 1):
        complement_sym[bit_pos] = 0
    else:
        complement_sym[bit_pos] = 1
    return tuple(complement_sym)


def test_mtbdd_nfa_projection(mtbdd_nfa1: MTBDD_NFA):  # NOQA

    # Copy out the states (projection might be performed in place)
    original_automaton = AutomatonSnapshot.create_snapshot(mtbdd_nfa1)

    pnfa = mtbdd_nfa1.do_projection(1)
    assert pnfa
    assert pnfa.states == original_automaton.states
    assert pnfa.final_states == original_automaton.final_states
    assert pnfa.initial_states == original_automaton.initial_states

    # expected_symbols_projection = {  # x was the first variable
    #     (0, 0): ('*', 0),
    #     (0, 1): ('*', 1),
    #     (1, 0): ('*', 0),
    #     (1, 1): ('*', 1),
    # }

    for origin, original_symbol, destination in original_automaton.transitions:
        assert destination in pnfa.get_transition_target(origin, original_symbol)
        assert destination in pnfa.get_transition_target(origin, complement_nth_bit(original_symbol, 0))
