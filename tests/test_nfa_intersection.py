from typing import (
    Dict,
    List,
    Tuple
)

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.presburger.constructions.integers import build_nfa_from_linear_inequality
from amaya.relations_structures import Relation
from tests.conftest import ResolutionState

import pytest

alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])


@pytest.fixture()
def relation1() -> Relation:
    """Returns relation: x - y <= 0."""
    relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, -1],
                                         absolute_part=0, predicate_symbol="<=")
    return relation


@pytest.fixture()
def relation2() -> Relation:
    relation = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[1, 1],
                                         absolute_part=1, predicate_symbol="<=")
    return relation


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_intersection(automaton_cls: NFA, relation1: Relation, relation2: Relation):
    var_id_pairs = [('x', 1), ('y', 2)]
    nfa1 = build_nfa_from_linear_inequality(automaton_cls, alphabet, relation1, var_id_pairs)
    nfa2 = build_nfa_from_linear_inequality(automaton_cls, alphabet, relation2, var_id_pairs)

    nfa = nfa1.intersection(nfa2)

    assert len(nfa.states) == 8  # We assume that nonfinishing states are removed after the automaton is constructed
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    state_names = [(0, 1), (-1, -1), (0, 0), (-1, 0), (-1, -2), (0, -1), (0, -2)]
    states: Dict[Tuple[int, int], ResolutionState] = dict((state, ResolutionState()) for state in state_names)

    initial_state = next(iter(nfa.initial_states))
    states[(0, 1)].bind(initial_state)

    expected_transitions = [
        ((0, 1), (0, 0), (0, 0)),
        ((0, 1), (0, 1), (0, 0)),
        ((0, 1), (1, 0), (-1, 0)),
        ((0, 1), (1, 1), (0, -1)),

        ((0, 0), (0, 0), (0, 0)),
        ((0, 0), (0, 1), (0, -1)),
        ((0, 0), (1, 0), (-1, -1)),
        ((0, 0), (1, 1), (0, -1)),

        ((-1, 0), (0, 0), (-1, 0)),
        ((-1, 0), (0, 1), (0, -1)),
        ((-1, 0), (1, 0), (-1, -1)),
        ((-1, 0), (1, 1), (-1, -1)),

        ((-1, -1), (0, 0), (-1, -1)),
        ((-1, -1), (0, 1), (0, -1)),
        ((-1, -1), (1, 0), (-1, -1)),
        ((-1, -1), (1, 1), (-1, -2)),

        ((-1, -2), (0, 0), (-1, -1)),
        ((-1, -2), (0, 1), (0, -2)),
        ((-1, -2), (1, 0), (-1, -2)),
        ((-1, -2), (1, 1), (-1, -2)),

        ((0, -1), (0, 0), (0, -1)),
        ((0, -1), (0, 1), (0, -1)),
        ((0, -1), (1, 0), (-1, -1)),
        ((0, -1), (1, 1), (0, -2)),

        ((0, -2), (0, 0), (0, -1)),
        ((0, -2), (0, 1), (0, -2)),
        ((0, -2), (1, 0), (-1, -2)),
        ((0, -2), (1, 1), (0, -2)),
    ]

    for origin, symbol, destination in expected_transitions:
        _origin = states[origin].get()
        dest_states = set(nfa.get_transition_target(_origin, symbol))
        dest_nonfinal_states = dest_states - nfa.final_states

        assert len(dest_nonfinal_states) == 1
        _destination = states[destination]
        _destination.bind(next(iter(dest_nonfinal_states)))

    all_symbols = {(0, 0), (0, 1), (1, 0), (1, 1)}
    expected_accepting_symbols = [
        ((0, 1), [(0, 0), (1, 0), (1, 1)]),
        ((-1, 0), [(1, 0)]),
        ((0, 0), [(0, 0), (1, 0), (1, 1)]),
        ((0, 0), [(0, 0), (1, 0), (1, 1)]),
        ((-1, -1), [(1, 0)]),
        ((-1, -2), []),
        ((0, -1), [(1, 0), (1, 1)]),
        ((0, -2), [(1, 1)]),
    ]

    for state, accepting_symbols in expected_accepting_symbols:
        _state = states[state].get()
        for accepting_symbol in accepting_symbols:
            dest_states = set(nfa.get_transition_target(_state, accepting_symbol))
            dest_final_states = nfa.final_states.intersection(dest_states)
            assert len(dest_final_states) == 1

        for nonaccepting_symbol in all_symbols.difference(set(accepting_symbols)):
            dest_states = set(nfa.get_transition_target(_state, nonaccepting_symbol))
            dest_final_states = nfa.final_states.intersection(dest_states)
            assert len(dest_final_states) == 0
