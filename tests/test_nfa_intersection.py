import pytest
from relations_structures import Relation
from presburger_algorithms import build_nfa_from_linear_inequality
from mtbdd_automatons import MTBDD_NFA
from alphabet import LSBF_Alphabet
from automatons import NFA
from typing import (
    Dict,
    List,
    Tuple
)
from tests.test_nfa_determization import ResolutionState

alphabet = LSBF_Alphabet.from_variable_ids([1, 2])
VariablesIDPairs = List[Tuple[str, int]]


@pytest.fixture()
def relation1() -> Tuple[Relation, VariablesIDPairs]:
    """
    Returns the relation encoding: x - y <= 0.
    """
    relation = Relation(
        absolute_part=0,
        variable_names=['x', 'y'],
        variable_coeficients=[1, -1],
        modulo_terms=[],
        modulo_term_coeficients=[],
        operation="<="
    )

    variable_ids_pairs: VariablesIDPairs = [('x', 1), ('y', 2)]
    return (relation, variable_ids_pairs)


@pytest.fixture()
def relation2() -> Tuple[Relation, VariablesIDPairs]:
    relation = Relation(
        absolute_part=1,
        variable_names=['x', 'y'],
        variable_coeficients=[1, 1],
        modulo_terms=[],
        modulo_term_coeficients=[],
        operation="<="
    )

    variable_ids_pairs: VariablesIDPairs = [('x', 1), ('y', 2)]
    return (relation, variable_ids_pairs)


def check_relation1_automaton(nfa: NFA):
    assert len(nfa.states) == 3
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    initial_state = next(iter(nfa.initial_states))
    final_state = next(iter(nfa.final_states))

    state_0 = ResolutionState()
    state_m1 = ResolutionState()
    state_f = ResolutionState()

    state_0.bind(initial_state)
    state_f.bind(final_state)

    expected_transitions = [
        (state_0, (0, 0), state_0),
        (state_0, (0, 1), state_0),
        (state_0, (1, 1), state_0),
        (state_0, (1, 0), state_m1),

        (state_m1, (0, 0), state_m1),
        (state_m1, (1, 0), state_m1),
        (state_m1, (1, 1), state_m1),
        (state_m1, (0, 1), state_0),
    ]

    expected_accepting_symbols = [
        (state_0, [(0, 0), (1, 0), (1, 1)]),
        (state_m1, [(1, 0)])
    ]

    for origin, symbol, destination in expected_transitions:
        dest_states = set(nfa.get_transition_target(origin.get(), symbol)) - nfa.final_states
        destination.bind(next(iter(dest_states)))

    for state, final_symbols in expected_accepting_symbols:
        for symbol in final_symbols:
            dest_states = nfa.get_transition_target(state.get(), symbol)
            final_dest_states = set(dest_states).intersection(set(nfa.final_states))
            assert len(final_dest_states) == 1
            assert {state_f.get()} == final_dest_states


def check_relation2_automaton(nfa: NFA):
    assert len(nfa.states) == 5
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    initial_state = next(iter(nfa.initial_states))

    states = dict((i, ResolutionState()) for i in [1, 0, -1, -2])

    states[1].bind(initial_state)

    expected_transitions = [
        (1, (0, 0), 0),
        (1, (0, 1), 0),
        (1, (1, 0), 0),
        (1, (1, 1), -1),

        (0, (0, 0), 0),
        (0, (0, 1), -1),
        (0, (1, 0), -1),
        (0, (1, 1), -1),

        (-1, (0, 0), -1),
        (-1, (0, 1), -1),
        (-1, (1, 0), -1),
        (-1, (1, 1), -2),

        (-2, (0, 0), -1),
        (-2, (0, 1), -2),
        (-2, (1, 0), -2),
        (-2, (1, 1), -2),
    ]

    for origin, symbol, destination in expected_transitions:
        _origin = states[origin].get()
        dest_states = set(nfa.get_transition_target(_origin, symbol))
        dest_nonfinal_states = dest_states - nfa.final_states

        assert len(dest_nonfinal_states) == 1
        _destination = states[destination]
        _destination.bind(next(iter(dest_nonfinal_states)))

    expected_accepting_symbols = [
        (1, [(0, 0), (0, 1), (1, 0), (1, 1)]),
        (0, [(0, 0), (0, 1), (1, 0), (1, 1)]),
        (-1, [(0, 1), (1, 0), (1, 1)]),
        (-2, [(1, 1)]),
    ]

    for state, accepting_symbols in expected_accepting_symbols:
        for accepting_symbol in accepting_symbols:
            dest_states = set(nfa.get_transition_target(state, accepting_symbol))
            dest_final_states = nfa.final_states.intersection(dest_states)
            assert len(dest_final_states) == 1


def check_intersection_automaton(nfa: NFA):
    """
    Verifies that the intersection automaton has the expected structure.
    """
    assert len(nfa.states) == 8  # We believe that the nonfinishing states were removed.
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


def test_mtbdd_intersection_on_atoms(relation1: Tuple[Relation, VariablesIDPairs],
                                     relation2: Tuple[Relation, VariablesIDPairs]):

    nfa1 = build_nfa_from_linear_inequality(relation1[0], relation1[1], alphabet, MTBDD_NFA)
    nfa2 = build_nfa_from_linear_inequality(relation2[0], relation2[1], alphabet, MTBDD_NFA)

    check_relation1_automaton(nfa1)
    check_relation2_automaton(nfa2)

    product_nfa = nfa1.intersection(nfa2)

    check_intersection_automaton(product_nfa)


def test_native_intersection_on_atoms(relation1: Tuple[Relation, VariablesIDPairs],
                                      relation2: Tuple[Relation, VariablesIDPairs]):

    nfa1 = build_nfa_from_linear_inequality(relation1[0], relation1[1], alphabet, NFA)
    nfa2 = build_nfa_from_linear_inequality(relation2[0], relation2[1], alphabet, NFA)

    check_relation1_automaton(nfa1)
    check_relation2_automaton(nfa2)

    product_nfa = nfa1.intersection(nfa2)
    check_intersection_automaton(product_nfa)
