import pytest
from automatons import NFA
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from utils import transition_fn_size
from transitions import iter_transition_fn
from log import logger
from typing import (
    Dict,
    Any
)


@pytest.fixture
def nfa1() -> NFA:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )
    return build_nfa_from_inequality(ineq)


@pytest.fixture
def nfa2() -> NFA:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[3, -1],
        absolute_part=3, operation='<='
    )
    return build_nfa_from_inequality(ineq)


def test_automaton_union(nfa1, nfa2):
    nfa_1_state_count = len(nfa1.states)
    nfa_2_state_count = len(nfa2.states)

    nfa1_state_translation: Dict[Any, int] = dict()
    nfa2_state_translation: Dict[Any, int] = dict()
    nfa1_id = id(nfa1)
    nfa2_id = id(nfa2)

    def nfa_state_renamed(_id: int, old_state: Any, new_state: int):
        if _id == nfa1_id:
            nfa1_state_translation[old_state] = new_state
        elif _id == nfa2_id:
            nfa2_state_translation[old_state] = new_state
        else:
            logger.fatal('Error while renaming automaton states - generated translation for unknown automaton id')
            assert False

    nfa1._debug_state_rename = nfa_state_renamed
    nfa2._debug_state_rename = nfa_state_renamed

    united_automaton = nfa1.union(nfa2)
    assert len(united_automaton.states) == nfa_1_state_count + nfa_2_state_count
    assert len(united_automaton.initial_states) == len(nfa1.initial_states) + len(nfa2.initial_states)
    assert len(united_automaton.final_states) == len(nfa1.final_states) + len(nfa2.final_states)

    for final_state in united_automaton.final_states:
        assert final_state in united_automaton.final_states

    for initial_state in united_automaton.initial_states:
        assert initial_state in united_automaton.initial_states

    assert transition_fn_size(united_automaton.transition_fn.data) == transition_fn_size(nfa1.transition_fn.data) + transition_fn_size(nfa2.transition_fn.data)
    assert len(nfa1_state_translation) > 0
    assert len(nfa2_state_translation) > 0

    # Verify that both transition fns are indeed present in the united
    # automaton
    for o, s, d in iter_transition_fn(nfa1.transition_fn.data):
        translated_origin = nfa1_state_translation[o]
        translated_dest = nfa1_state_translation[d]

        assert s in united_automaton.transition_fn.data[translated_origin][translated_dest]

    for o, s, d in iter_transition_fn(nfa2.transition_fn.data):
        translated_origin = nfa2_state_translation[o]
        translated_dest = nfa2_state_translation[d]

        assert s in united_automaton.transition_fn.data[translated_origin][translated_dest]
