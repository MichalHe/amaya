import pytest
from automatons import NFA, AutomatonType
from inequations_data import Inequality
from inequations import build_nfa_from_inequality
from typing import (
    Any,
    Dict,
)
from utils import transition_fn_size


@pytest.fixture
def nfa() -> NFA:
    ineq = Inequality(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=3,
        operation="<="
    )
    return build_nfa_from_inequality(ineq)


def test_state_renaming(nfa):
    state_names_translat: Dict[Any, int] = dict()

    def state_renamed(automaton_id: int, old_state: Any, new_state: int):
        state_names_translat[old_state] = new_state

    assert nfa.automaton_type == AutomatonType.NFA

    nfa._debug_state_rename = state_renamed

    has_str_state = len(tuple(filter(lambda state: type(state) == str, nfa.states))) > 0
    assert has_str_state

    highest_state, new_nfa = nfa.rename_states()

    assert new_nfa
    assert nfa.automaton_type == AutomatonType.NFA
    assert len(state_names_translat) == len(new_nfa.states)

    original_transition_count = 0
    for original_origin in nfa.states:
        new_origin = state_names_translat[original_origin]
        if original_origin not in nfa.transition_fn:
            continue
        for symbol in nfa.transition_fn[original_origin]:
            for original_dest in nfa.transition_fn[original_origin][symbol]:
                new_dest = state_names_translat[original_dest]
                assert new_dest in new_nfa.transition_fn[new_origin][symbol]
                original_transition_count += 1

    assert transition_fn_size(new_nfa.transition_fn) == original_transition_count
