import pytest
from automatons import NFA, LSBF_Alphabet, MTBDD_NFA
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from utils import transition_fn_size
from transitions import iter_transition_fn
from log import logger
from collections import namedtuple
from typing import (
    Dict,
    Any
)

alphabet = LSBF_Alphabet.from_variable_names([1, 2])


@pytest.fixture
def ineq0() -> Relation:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )
    return ineq


@pytest.fixture
def ineq1() -> Relation:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[3, -1],
        absolute_part=3, operation='<='
    )
    return ineq


def do_test_automaton_union(nfa1, nfa2):
    StateSizes = namedtuple('AutomatonSizeStats',
                            ['states', 'initial_states', 'final_states'])

    nfa1_sizes = StateSizes(len(nfa1.states), len(nfa1.initial_states), len(nfa1.final_states))
    nfa2_sizes = StateSizes(len(nfa2.states), len(nfa2.initial_states), len(nfa2.final_states))

    nfa1_transitions = list(nfa1.transition_fn.iter())
    nfa2_transitions = list(nfa2.transition_fn.iter())

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
    assert len(united_automaton.states) == nfa1_sizes.states + nfa2_sizes.states
    assert len(united_automaton.initial_states) == nfa1_sizes.initial_states + nfa2_sizes.initial_states
    assert len(united_automaton.final_states) == nfa1_sizes.final_states + nfa2_sizes.final_states

    union_transitions = list(united_automaton.transition_fn.iter())
    assert len(union_transitions) == len(nfa1_transitions) + len(nfa2_transitions)

    assert len(nfa1_state_translation) > 0
    assert len(nfa2_state_translation) > 0

    # Verify that both transition fns are indeed present in the united
    # automaton
    for o, s, d in nfa1_transitions:
        to = nfa1_state_translation[o]
        td = nfa1_state_translation[d]

        assert (to, s, td) in union_transitions

    for o, s, d in nfa2_transitions:
        to = nfa2_state_translation[o]
        td = nfa2_state_translation[d]

        assert (to, s, td) in union_transitions


def test_sparse_nfa_union(ineq0, ineq1):
    nfa0 = build_nfa_from_inequality(ineq0, alphabet, NFA)
    nfa1 = build_nfa_from_inequality(ineq1, alphabet, NFA)
    do_test_automaton_union(nfa0, nfa1)


def test_mtbdd_nfa_union(ineq0, ineq1):
    mtbdd_nfa0 = build_nfa_from_inequality(ineq0, alphabet, MTBDD_NFA)
    mtbdd_nfa1 = build_nfa_from_inequality(ineq1, alphabet, MTBDD_NFA)
    do_test_automaton_union(mtbdd_nfa0, mtbdd_nfa1)
