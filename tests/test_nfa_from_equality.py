from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.presburger.constructions.integers import build_nfa_from_linear_equality
from amaya.relations_structures import Relation, Var
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
