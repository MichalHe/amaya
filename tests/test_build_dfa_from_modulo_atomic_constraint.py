from typing import (
    Tuple,
    List
)

from presburger_algorithms import (
    build_presburger_modulo_dfa
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


def assert_single_mod_term_automaton_structure(nfa: NFA,
                                               final_state_count: int) -> Tuple[ResolutionState, ResolutionState, ResolutionState]:
    '''Verifies that the automaton for relation (x mod 3) <OP> 1 has the expected structure.'''
    assert len(nfa.initial_states), 'The dfa build should have exactly 1 initial state.'
    assert len(nfa.final_states) == final_state_count, 'The dfa should have 2 final states - 0 and 1'
    assert len(nfa.states) == 3, 'The dfa should have a state for every possible remainder - that is 3.'

    # States for reminders (rem=reminder)
    rem0 = ResolutionState()
    rem1 = ResolutionState()
    rem2 = ResolutionState()

    rem0.bind(list(nfa.initial_states)[0])

    expected_transitions = [
        (rem0, (0,), rem0),
        (rem0, (1,), rem1),
        (rem1, (0,), rem2),
        (rem1, (1,), rem0),
        (rem2, (0,), rem1),
        (rem2, (1,), rem2),
    ]

    for expected_transition in expected_transitions:
        source, symbol, expected_destination = expected_transition
        destination = nfa.get_transition_target(source.get(), symbol)

        assert len(destination) == 1, 'The states should have only 1 transition for every symbol.'

        expected_destination.bind(list(destination)[0])

    return (rem0, rem1, rem2)


def test_inequality_with_single_modulo_constaint(ineq_with_single_mod_term: RelationSetup):
    '''
    Tests whether the automaton built from an inequality with single modulo term works as expected.
    '''

    variable_id_pairs, alphabet, inequation = ineq_with_single_mod_term
    nfa = NFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)

    build_presburger_modulo_dfa(inequation, variable_id_pairs, alphabet, nfa)

    rem0, rem1, rem2 = assert_single_mod_term_automaton_structure(nfa, 2)

    assert rem0.get() in nfa.final_states
    assert rem1.get() in nfa.final_states


def test_equality_with_single_modulo_constaint(eq_with_single_mod_term: RelationSetup):
    variable_id_pairs, alphabet, equation = eq_with_single_mod_term
    nfa = NFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)

    build_presburger_modulo_dfa(equation, variable_id_pairs, alphabet, nfa)

    rem0, rem1, rem2 = assert_single_mod_term_automaton_structure(nfa, 1)

    assert rem1.get() in nfa.final_states
