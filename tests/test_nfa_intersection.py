import pytest
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from automatons import MTBDD_NFA, LSBF_Alphabet
from typing import Any

alphabet = LSBF_Alphabet.from_variable_names([1, 2])


@pytest.fixture
def mtbdd_nfa1() -> MTBDD_NFA:
    ineq = Relation(
        absolute_part=0,
        variable_names=['x', 'y'],
        variable_coeficients=[1, -1],
        operation="<="
    )
    return build_nfa_from_inequality(ineq, alphabet, MTBDD_NFA)


@pytest.fixture
def nfa2() -> MTBDD_NFA:
    ineq = Relation(
        absolute_part=1,
        variable_names=['x', 'y'],
        variable_coeficients=[1, -1],
        operation="<="
    )
    return build_nfa_from_inequality(ineq, alphabet, MTBDD_NFA)


def are_states_same(state_a, state_b):
    if not len(state_a) == len(state_b):
        return False

    for a in state_a:
        if a not in state_b:
            return False

    return True


def test_nfa_intersection_mtbdd(mtbdd_nfa1: MTBDD_NFA, nfa2: MTBDD_NFA):
    assert len(mtbdd_nfa1.final_states) == 1
    assert len(nfa2.final_states) == 1

    nfa1_final_state_bt = next(iter(mtbdd_nfa1.final_states))
    nfa2_final_state_bt = next(iter(nfa2.final_states))

    nfa1_translation = dict()
    nfa2_translation = dict()

    def state_name_translated(automaton_id: int, old_name: Any, new_name: int):
        if automaton_id == id(mtbdd_nfa1):
            nfa1_translation[old_name] = new_name
        else:
            nfa2_translation[old_name] = new_name

    mtbdd_nfa1._debug_state_rename = state_name_translated
    nfa2._debug_state_rename = state_name_translated

    metastate_map = {}
    metastate_inv_map = {}
    nfa_intersection = mtbdd_nfa1.intersection(nfa2, metastate_map=metastate_map)
    assert nfa_intersection

    for state, metastate in metastate_map.items():
        metastate_inv_map[metastate] = state

    expected_final_metastate = (nfa1_translation[nfa1_final_state_bt],
                                nfa2_translation[nfa2_final_state_bt])
    expected_final_state = metastate_inv_map[expected_final_metastate]

    assert len(nfa_intersection.final_states) == 1
    assert expected_final_state in nfa_intersection.final_states

    assert len(nfa1_translation) > 0 and len(nfa2_translation) > 0

    # Those are manually calculated expected intersection states
    # States overcome various transformations during intersection eval:
    # 1. state renumbering
    # 2. metastate to int translation
    # We need to apply the process onto the expected states aswell
    expected_states = [
        (0, 1),
        (0, 0),
        (-1, -1),
        (-1, 0),
        (nfa1_final_state_bt, nfa2_final_state_bt)
    ]

    translated_expected_states = []
    for left, right in expected_states:
        renumbered_metastate = (nfa1_translation[left], nfa2_translation[right])
        int_state = metastate_inv_map[renumbered_metastate]
        translated_expected_states.append(int_state)

    for ts in translated_expected_states:
        assert ts in nfa_intersection.states

    es = translated_expected_states
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

    transitions = list(nfa_intersection.transition_fn.iter())

    for et in expected_transitions:
        assert et in transitions

    # Test whether states of shape ('final', int) are present
    expected_states_deadend = [
        (0, nfa2_final_state_bt),
        (-1, nfa2_final_state_bt),
        (nfa1_final_state_bt, 0),
        (nfa1_final_state_bt, -1),
    ]

    esdt = []
    for left, right in expected_states_deadend:
        renumbered_metastate = (nfa1_translation[left], nfa2_translation[right])
        int_state = metastate_inv_map[renumbered_metastate]
        esdt.append(int_state)

    for e_state in esdt:
        assert e_state in nfa_intersection.states
