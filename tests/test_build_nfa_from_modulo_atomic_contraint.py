from typing import (
    Tuple,
    List
)

from presburger_algorithms import (
    build_presburger_modulo_nfa
)
from relations_structures import ModuloTerm, Relation

import pytest
from automatons import AutomatonType, LSBF_Alphabet, NFA
from tests.test_nfa_determization import ResolutionState

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
    alphabet = LSBF_Alphabet.from_variable_names(['x'])
    variable_id_pairs = [('x', 1)]
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
    alphabet = LSBF_Alphabet.from_variable_names(['x'])
    variable_id_pairs = [('x', 1)]
    return (variable_id_pairs, alphabet, relation)


def assert_single_mod_term_automaton_structure(nfa: NFA,
                                               final_state_count: int) -> Tuple[ResolutionState, ResolutionState, ResolutionState]:
    '''Verifies that the automaton for relation (x mod 3) <OP> 1 has the expected structure.'''
    assert len(nfa.initial_states), 'The dfa build should have exactly 1 initial state.'
    assert len(nfa.final_states) == final_state_count, 'The dfa should have 2 final states - 0 and 1'
    fail_desc = 'The dfa should have a state for every possible remainder - that is 3 + one final state.'
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
    
    fail_desc = 'The states should have at max 2 transitons (1 to successor, maybe 1 to final state).'
    for expected_transition in expected_transitions:
        source, symbol, expected_destination = expected_transition
        destination = nfa.get_transition_target(source.get(), symbol)
        
        print(nfa.transition_fn.data)
        print('Destination from {0} via {1} is {2}'.format(
            source.get(), symbol, destination))

        assert len(destination) <= 2, fail_desc

        # We want to cover the automaton structure without final state, that will be checked in the future.
        destination_state = next(filter(lambda state: state not in nfa.final_states, destination))
        
        expected_destination.bind(destination_state)

    fail_desc = 'The automaton encoding a modulo contraint is expected to have only 1 final state.'
    assert len(nfa.final_states) == 1, fail_desc
    final_state = next(iter(nfa.final_states))

    expected_transitions_to_final_state = [
        (rem0, (0, )),
        (rem2, (1, ))
    ]
    for source, symbol in expected_transitions_to_final_state:
        assert final_state in nfa.get_transition_target(source.get(), symbol)
    

def test_equality_with_single_modulo_constaint(eq_with_single_mod_term: RelationSetup):
    variable_id_pairs, alphabet, equation = eq_with_single_mod_term
    nfa = NFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)

    build_presburger_modulo_nfa(equation, variable_id_pairs, alphabet, nfa)

    assert_single_mod_term_automaton_structure(nfa, 1)
