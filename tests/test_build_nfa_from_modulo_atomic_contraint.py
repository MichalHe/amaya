from typing import (
    Tuple,
    List
)

from alphabet import LSBF_Alphabet
from automatons import (
    AutomatonType,
    DFA,
    NFA,
)
from presburger.constructions.integers import build_presburger_modulo_nfa
from presburger.constructions.naturals import build_presburger_modulo_dfa
from relations_structures import ModuloTerm, Relation
from tests.conftest import ResolutionState

import pytest

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


def assert_state_count(nfa: NFA, state_count: int, initial_state_count: int, final_state_count: int):
    """Asserts that the automaton has correct number of states and produces a nice message if the assertion fails."""

    fail_desc = 'The automaton has wrong number of{0} states - should have {1}, but has {2}.'

    assert len(nfa.initial_states) == initial_state_count, fail_desc.format(
            ' initial', initial_state_count, len(nfa.initial_states))

    assert len(nfa.states) == state_count, fail_desc.format('', state_count, len(nfa.states))

    assert len(nfa.final_states) == final_state_count, fail_desc.format(
            ' final', final_state_count, len(nfa.final_states))


def assert_single_mod_term_automaton_structure(nfa: NFA, is_domain_naturals=False):
    '''Verifies that the automaton for relation (x mod 3) <OP> 1 has the expected structure.'''

    exp_state_count = 3 if is_domain_naturals else 4
    assert_state_count(nfa, exp_state_count, 1, 1)

    # States for reminders (rem=reminder)
    rem0 = ResolutionState()
    rem1 = ResolutionState()
    rem2 = ResolutionState()

    rem1.bind(next(iter(nfa.initial_states)))

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

    for i, expected_transition in enumerate(expected_transitions):
        source, symbol, expected_destination = expected_transition

        if is_domain_naturals:
            destination = list(nfa.get_transition_target(source.get(), symbol))
        else:
            destination = [
                state for state in nfa.get_transition_target(source.get(), symbol) if state != final_state
            ]

        assert len(destination) == 1

        expected_destination.bind(destination[0])
    
    if is_domain_naturals:
        assert rem0.get() in nfa.final_states
    else:
        expected_transitions_to_final_state = [
            (rem0, (0, )),
            (rem2, (1, ))
        ]
        for source, symbol in expected_transitions_to_final_state:
            assert final_state in nfa.get_transition_target(source.get(), symbol)
    assert nfa.used_variables == [1]
    

@pytest.mark.parametrize('domain', ('naturals', 'integers'))
def test_equality_with_single_modulo_constaint(domain, eq_with_single_mod_term: RelationSetup):
    variable_id_pairs, alphabet, equation = eq_with_single_mod_term
    is_domain_naturals = domain == 'naturals'
    if is_domain_naturals:
        nfa = build_presburger_modulo_dfa(equation, variable_id_pairs, alphabet, NFA)
    else:
        nfa = build_presburger_modulo_nfa(equation, variable_id_pairs, alphabet, DFA)

    assert_single_mod_term_automaton_structure(nfa, is_domain_naturals=is_domain_naturals)


@pytest.mark.parametrize('domain', ('naturals', 'integers'))
def test_with_power_of_two_modulo(domain):
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
    
    is_domain_naturals = domain == 'naturals'
    if is_domain_naturals:
        nfa = build_presburger_modulo_dfa(relation, variable_id_pairs, alphabet, DFA)
        exp_state_count = 3
        exp_final_state_count = 3
    else:
        nfa = build_presburger_modulo_nfa(relation, variable_id_pairs, alphabet, NFA)
        exp_state_count = 4
        exp_final_state_count = 1

    assert_state_count(nfa, exp_state_count, initial_state_count=1, final_state_count=exp_final_state_count)
        
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

    final_state = next(iter(nfa.final_states))  # Will be used only to filter out the NFA structure (integer solutions)
     
    for origin, symbol, dest in expected_transitions:
        if is_domain_naturals:
            destination_list = list(nfa.get_transition_target(origin.get(), symbol))
        else:
            destination_list = [d for d in nfa.get_transition_target(origin.get(), symbol) if d != final_state]
        assert len(destination_list) == 1
        dest.bind(destination_list[0])
    
    if is_domain_naturals:
        assert state0_0.get() in nfa.final_states
        assert state0_1.get() in nfa.final_states
        assert state0_2.get() in nfa.final_states
    else:
        assert final_state in nfa.get_transition_target(state0_0.get(), (0,))
        assert final_state in nfa.get_transition_target(state0_1.get(), (0,))
        assert final_state in nfa.get_transition_target(state0_2.get(), (0,))
        assert final_state in nfa.get_transition_target(state0_2.get(), (1,))

    assert nfa.used_variables == [1]
