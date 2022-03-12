from typing import (
    Tuple,
    List
)

from presburger.constructions.integers import (
    build_presburger_modulo_nfa
)
from relations_structures import ModuloTerm, Relation

import pytest
from automatons import AutomatonType, LSBF_Alphabet, NFA
from tests.conftest import ResolutionState

RelationSetup = Tuple[List[Tuple[str, int]], LSBF_Alphabet, Relation]


@pytest.fixture
def ineq_with_single_mod_term() -> RelationSetup:
    '''Inequation: (x mod 3) <= 1'''
    modulo_term = ModuloTerm(variables=['x'],
                             variable_coeficients=(1,),
                             constant=0,
                             modulo=3)
    relation = Relation(variable_names=[],
                        variable_coeficients=[],
                        modulo_terms=[modulo_term],
                        modulo_term_coeficients=[1],
                        absolute_part=1,
                        operation='<=')
    variable_id_pairs = [('x', 1)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    return (variable_id_pairs, alphabet, relation)


@pytest.fixture
def eq_with_single_mod_term(ineq_with_single_mod_term: RelationSetup) -> RelationSetup:
    '''Equation (x mod 3) = 1'''

    inequation = ineq_with_single_mod_term[2]
    inequation.operation = '='
    return ineq_with_single_mod_term


def ineq_with_multiple_modulo_contraints() -> RelationSetup:
    '''Inequality setup for: (x mod 3) + (y mod 6) <= 4.'''
    x_modulo_term = ModuloTerm(variables=['x'],
                               variable_coeficients=(1,),
                               constant=0,
                               modulo=3)
    y_modulo_term = ModuloTerm(variables=['y'],
                               variable_coeficients=(1,),
                               constant=0,
                               modulo=6)
    relation = Relation(variable_names=[],
                        variable_coeficients=[],
                        modulo_terms=[x_modulo_term, y_modulo_term],
                        modulo_term_coeficients=[1, 1],
                        absolute_part=4,
                        operation='<=')
    variable_id_pairs = [('x', 1), ('y', 2)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    return (variable_id_pairs, alphabet, relation)


def assert_single_mod_term_automaton_structure(nfa: NFA,
                                               final_state_count: int) -> Tuple[ResolutionState, ResolutionState, ResolutionState]:
    '''Verifies that the automaton for relation (x mod 3) <OP> 1 has the expected structure.'''
    assert len(nfa.initial_states), 'The dfa build should have exactly 1 initial state.'
    assert len(nfa.final_states) == 1, 'The NFA should have exactly 1 final state.'
    fail_desc = 'The NFA should have a state for every possible remainder - that is 3 + one final state.'
    assert len(nfa.states) == 4, fail_desc

    # States for reminders (rem=reminder)
    rem0 = ResolutionState()
    rem1 = ResolutionState()
    rem2 = ResolutionState()

    rem1.bind(list(nfa.initial_states)[0])

    expected_transitions = [
        (rem1, (0,), rem2),
        (rem1, (1,), rem0),
        (rem0, (0,), rem0),
        (rem0, (1,), rem1),
        (rem2, (0,), rem1),
        (rem2, (1,), rem2),
    ]
    
    final_state = next(iter(nfa.final_states))
    fail_desc = 'The states should have at max 2 transitons (1 to successor, maybe 1 to final state).'

    print(nfa.extra_info['aliases'].data)
    print(rem1.get())

    for i, expected_transition in enumerate(expected_transitions):
        source, symbol, expected_destination = expected_transition
        destination = list(filter(lambda state: state != final_state, nfa.get_transition_target(source.get(), symbol)))
        assert len(destination) == 1

        print(f'Processing {i}: {source.get()} {destination}')
        expected_destination.bind(destination[0])

    expected_transitions_to_final_state = [
        (rem0, (0, )),
        (rem2, (1, ))
    ]
    for source, symbol in expected_transitions_to_final_state:
        assert final_state in nfa.get_transition_target(source.get(), symbol)
    

def test_equality_with_single_modulo_constaint(eq_with_single_mod_term: RelationSetup):
    variable_id_pairs, alphabet, equation = eq_with_single_mod_term

    nfa = build_presburger_modulo_nfa(equation, variable_id_pairs, alphabet, NFA)

    assert_single_mod_term_automaton_structure(nfa, 1)


def test_with_power_of_two_modulo():
    modulo_term = ModuloTerm(variables=['x'],
                             variable_coeficients=(1,),
                             constant=0,
                             modulo=4)
    relation = Relation(variable_names=[],
                        variable_coeficients=[],
                        modulo_terms=[modulo_term],
                        modulo_term_coeficients=[1],
                        absolute_part=0,
                        operation='=')
    variable_id_pairs = [('x', 1)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    
    nfa = build_presburger_modulo_nfa(relation, variable_id_pairs, alphabet, NFA)

    assert len(nfa.states) == 4
    assert len(nfa.final_states) == 1
    assert len(nfa.initial_states) == 1
        
    state0_0 = ResolutionState()
    state0_1 = ResolutionState()
    state0_2 = ResolutionState()
    state0_0.bind(next(iter(nfa.initial_states)))

    expected_transitions = [
        (state0_0, (0, ), state0_1),
        (state0_1, (0, ), state0_2),
        (state0_2, (0, ), state0_2),
        (state0_2, (1, ), state0_2),
    ]

    final_state = next(iter(nfa.final_states))

    for origin, symbol, dest in expected_transitions:
        destination_set = list(filter(lambda dest: dest != final_state, nfa.get_transition_target(origin.get(), symbol)))
        assert len(destination_set) == 1
        dest.bind(destination_set[0])

    assert final_state in nfa.get_transition_target(state0_0.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_1.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_2.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_2.get(), (1,))
