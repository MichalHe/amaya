from collections import namedtuple
from typing import (
    Dict,
    Any
)

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.presburger.constructions.integers import build_nfa_from_linear_inequality
from amaya.relations_structures import Relation

import pytest

alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])


@pytest.fixture
def ineq0() -> Relation:
    return Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[2, -1],
                                     predicate_symbol='<=', absolute_part=2)


@pytest.fixture
def ineq1() -> Relation:
    return Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[3, -1],
                                     predicate_symbol='<=', absolute_part=3)



@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_automaton_union(automaton_cls: NFA, ineq0: Relation, ineq1: Relation):
    StateSizes = namedtuple('AutomatonSizeStats', ['states', 'initial_states', 'final_states'])

    nfa0 = build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq0, [('x', 1), ('y', 2)])
    nfa1 = build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq1, [('x', 1), ('y', 2)])

    nfa0_sizes = StateSizes(len(nfa0.states), len(nfa0.initial_states), len(nfa0.final_states))
    nfa1_sizes = StateSizes(len(nfa1.states), len(nfa1.initial_states), len(nfa1.final_states))

    nfa0_transitions = list(nfa0.transition_fn.iter())
    nfa1_transitions = list(nfa1.transition_fn.iter())

    nfa0_state_translation: Dict[Any, int] = dict()
    nfa1_state_translation: Dict[Any, int] = dict()
    nfa0_id = id(nfa0)
    nfa1_id = id(nfa1)

    def nfa_state_renamed(_id: int, old_state: Any, new_state: int):
        if _id == nfa0_id:
            nfa0_state_translation[old_state] = new_state
        elif _id == nfa1_id:
            nfa1_state_translation[old_state] = new_state
        else:
            logger.fatal('Error while renaming automaton states - generated translation for unknown automaton id')
            assert False

    nfa0._debug_state_rename = nfa_state_renamed
    nfa1._debug_state_rename = nfa_state_renamed

    united_automaton = nfa0.union(nfa1)
    assert len(united_automaton.states) == nfa0_sizes.states + nfa1_sizes.states
    assert len(united_automaton.initial_states) == nfa0_sizes.initial_states + nfa1_sizes.initial_states
    assert len(united_automaton.final_states) == nfa0_sizes.final_states + nfa1_sizes.final_states

    union_transitions = list(united_automaton.transition_fn.iter())
    assert len(union_transitions) == len(nfa0_transitions) + len(nfa1_transitions)

    # Verify that both transition fns are indeed present in the united
    # automaton
    for o, s, d in nfa0_transitions:
        to = nfa0_state_translation[o]
        td = nfa0_state_translation[d]

        assert (to, s, td) in union_transitions

    for o, s, d in nfa1_transitions:
        to = nfa1_state_translation[o]
        td = nfa1_state_translation[d]

        assert (to, s, td) in union_transitions
