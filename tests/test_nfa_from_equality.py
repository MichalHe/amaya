from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.presburger.constructions.integers import build_nfa_from_linear_equality, build_presburger_congruence_nfa
from amaya.relations_structures import Congruence, Relation, Var
from tests.conftest import ResolutionState

import pytest


@pytest.fixture
def simple_equation() -> Relation:
    return Relation(vars=[Var(id=1), Var(id=2)], coefs=[2, -1], rhs=2, predicate_symbol='=')


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_build_nfa_from_equality(automaton_cls: NFA, simple_equation: Relation):
    alphabet = LSBF_Alphabet.from_vars([Var(id=1), Var(id=2)])
    nfa = build_nfa_from_linear_equality(automaton_cls, alphabet, simple_equation)

    expected_states = {str(label): ResolutionState(str(label)) for label in (2, 1, 0, -1, 'qf')}

    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1
    assert len(nfa.states) == len(expected_states)

    expected_states['2'].bind(next(iter(nfa.initial_states)))
    expected_states['qf'].bind(next(iter(nfa.final_states)))

    expected_transitions = [
        (expected_states['2'], (0, 0), expected_states['1']),
        (expected_states['2'], (1, 0), expected_states['0']),

        (expected_states['1'], (0, 1), expected_states['1']),
        (expected_states['1'], (1, 1), expected_states['0']),

        (expected_states['0'], (0, 0), expected_states['0']),
        (expected_states['0'], (1, 0), expected_states['-1']),

        (expected_states['-1'], (0, 1), expected_states['0']),
        (expected_states['-1'], (1, 1), expected_states['-1']),
    ]

    fin_transitions = [
        (expected_states['1'], (0, 1)),
        (expected_states['0'], (0, 0)),
        (expected_states['-1'], (1, 1)),
    ]

    for origin, symbol, dest in expected_transitions:
        dest_set = set(nfa.get_transition_target(origin.get(), symbol)).difference(nfa.final_states)
        assert len(dest_set) == 1
        dest.bind(next(iter(dest_set)))


    for origin, symbol in fin_transitions:
        dest_set = nfa.get_transition_target(origin.get(), symbol)
        assert len(dest_set) == 2
        assert expected_states['qf'].get() in dest_set


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_build_nfa_from_equality_without_integer_solutions(automaton_cls: NFA):
    """
    `3x = 1` has no integer solution, so the automaton has no final state. Preprocessing normally
    removes such an equation, but rewrites that substitute into equations can produce one after it
    ran; building the automaton must yield an empty language rather than raise StopIteration.
    """
    equation = Relation(vars=[Var(id=1)], coefs=[3], rhs=1, predicate_symbol='=')
    alphabet = LSBF_Alphabet.from_vars([Var(id=1)])

    nfa = build_nfa_from_linear_equality(automaton_cls, alphabet, equation)

    assert not nfa.final_states
    assert nfa.state_semantics.special_state is None


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_build_nfa_from_congruence_without_integer_solutions(automaton_cls: NFA):
    """ `2x = 1 (mod 4)` has no integer solution; see the equation case above. """
    congruence = Congruence(vars=[Var(id=1)], coefs=[2], rhs=1, modulus=4)
    alphabet = LSBF_Alphabet.from_vars([Var(id=1)])

    nfa = build_presburger_congruence_nfa(automaton_cls, alphabet, congruence)

    assert not nfa.final_states
    assert nfa.state_semantics.special_state is None
