import pytest
from relations_structures import Relation
from pressburger_algorithms import build_nfa_from_inequality
from typing import Union, Dict
from automatons import (
    AutomatonType,
    NFA
)


@pytest.fixture
def simple_nfa() -> NFA:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )

    return build_nfa_from_inequality(ineq)


def translate_transitions(transitions, translate):  # translate is function
    translated = []
    for transition in transitions:
        source, symbol, dest = transition
        source_translated = tuple(sorted(map(translate, source)))
        dest_translated = tuple(sorted(map(translate, dest)))

        translated.append((source_translated, symbol, dest_translated))
    return translated


def test_simple_nfa_determinization(simple_nfa: NFA[Union[int, str]]):
    assert simple_nfa.automaton_type == AutomatonType.NFA

    trans_map: Dict[Union[int, str], int] = {}

    def state_rename_occured(automaton_id: int, old_name: Union[int, str], new_name: int):
        trans_map[old_name] = new_name

    simple_nfa._debug_state_rename = state_rename_occured

    print('Translation map: ', trans_map)

    dfa = simple_nfa.determinize()
    assert dfa
    for state in dfa.states:
        print(state)
    assert len(dfa.states) == 8
    assert len(dfa.final_states) == 4
    assert len(dfa.initial_states) == 1
    assert dfa.automaton_type == AutomatonType.DFA

    def translate(state: Union[str, int]) -> int:
        return trans_map[state]

    expected_states_before_remap = [
        (2, ), (0, ), (-1, ), (-2, ),
        (1, 'FINAL'), (0, 'FINAL'), (-1, 'FINAL'), (-2, 'FINAL')
    ]

    expected_states = []
    for state in expected_states_before_remap:
        expected_states.append(tuple(map(translate, state)))

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

    e_transitions_translated = translate_transitions(e_transitions, translate)
    #  ne_transitions_translated = translate_transitions(ne_transitions, translate)

    for transition in e_transitions_translated:
        origin, symbol, dest = transition
        # perform state name correction
        assert dest in dfa.get_transition_target(origin, symbol)

    for transition in ne_transitions:
        origin, symbol, dest = transition
        assert dfa.get_transition_target(origin, symbol) is None or dest not in dfa.get_transition_target(origin, symbol)

    # Test whether the automaton has some target state for every symbol in
    # alphabet

    for state in dfa.states:
        for symbol in dfa.alphabet.symbols:
            assert len(dfa.get_transition_target(state, symbol)) == 1
