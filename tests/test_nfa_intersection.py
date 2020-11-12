import pytest
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from typing import Any


@pytest.fixture
def nfa1():
    ineq = Relation(
        absolute_part=0,
        variable_names=['x', 'y'],
        variable_coeficients=[1, -1],
        operation="<="
    )
    return build_nfa_from_inequality(ineq)


@pytest.fixture
def nfa2():
    ineq = Relation(
        absolute_part=1,
        variable_names=['x', 'y'],
        variable_coeficients=[1, -1],
        operation="<="
    )
    return build_nfa_from_inequality(ineq)


def are_states_same(state_a, state_b):
    if not len(state_a) == len(state_b):
        return False

    for a in state_a:
        if a not in state_b:
            return False

    return True


def test_nfa_intersectoin(nfa1, nfa2):
    nfa1_translation = dict()
    nfa2_translation = dict()

    def state_name_translated(automaton_id: int, old_name: Any, new_name: int):
        if automaton_id == id(nfa1):
            nfa1_translation[old_name] = new_name
        else:
            nfa2_translation[old_name] = new_name

    nfa1._debug_state_rename = state_name_translated
    nfa2._debug_state_rename = state_name_translated

    nfa_intersection = nfa1.intersection(nfa2)
    assert nfa_intersection

    assert 'FINAL' in nfa1.final_states
    assert 'FINAL' in nfa2.final_states
    expected_final_state = (nfa1_translation['FINAL'], nfa2_translation['FINAL'])
    assert are_states_same(expected_final_state, tuple(nfa_intersection.final_states)[0])

    assert len(nfa1_translation) > 0 and len(nfa2_translation) > 0
    expected_states = [
        (0, 1),
        (0, 0),
        (-1, -1),
        (-1, 0),
        ('FINAL', 'FINAL')
    ]

    def translate_state_pair(state_pair):
        a, b = state_pair
        return (nfa1_translation[a], nfa2_translation[b])

    expected_states = list(map(translate_state_pair, expected_states))

    for e_state in expected_states:
        assert e_state in nfa_intersection.states

    es = expected_states
    expected_transitions = [
        (es[0], (0, 1), es[0]),
        (es[0], (1, 1), es[1]),
        (es[0], (0, 0), es[1]),
        (es[0], (1, 0), es[3]),
        (es[1], (0, 1), es[1]),
        (es[1], (0, 0), es[1]),
        (es[1], (1, 1), es[1]),
        (es[2], (0, 1), es[1]),

        # Test final state reachableness
        (es[2], (1, 0), expected_final_state),

        (es[0], (1, 0), expected_final_state),
        (es[0], (0, 0), expected_final_state),
        (es[0], (1, 1), expected_final_state),
    ]

    for expected_transition in expected_transitions:
        src, sym, dest = expected_transition
        assert dest in nfa_intersection.get_transition_target(src, sym)

    # Test whether states of shape ('final', int) are present

    expected_states_deadend = [
        (0, 'FINAL'),
        (-1, 'FINAL'),
        ('FINAL', 0),
        ('FINAL', -1),
    ]

    expected_states_deadend = list(map(translate_state_pair, expected_states_deadend))
    for e_state in expected_states_deadend:
        assert e_state in nfa_intersection.states
