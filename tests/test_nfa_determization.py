from typing import (
    Dict,
    Union
)

from amaya.presburger.constructions.integers import (
    AutomatonConstructor,
    build_nfa_from_linear_inequality
)
from amaya.presburger.definitions import Relation
from amaya.automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.automaton_algorithms import abstract_determinize
from tests.conftest import ResolutionState

import pytest


alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])


@pytest.fixture()
def nfa_for_inequality(automaton_cls: AutomatonConstructor) -> NFA:
    ineq = Relation.new_lin_relation(variable_names=['x', 'y'], variable_coefficients=[2, -1], absolute_part=2, predicate_symbol='<=')
    return build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq, [('x', 1), ('y', 2)])


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_nfa_determinization_on_nfa_for_inequality(automaton_cls, nfa_for_inequality):
    # dfa = simple_nfa.determinize()
    dfa = nfa_for_inequality.determinize()
    assert dfa
    assert len(dfa.states) == 8
    assert len(dfa.final_states) == 4
    assert len(dfa.initial_states) == 1
    assert dfa.automaton_type == AutomatonType.DFA

    # We must perform the testing in a state-name agnostic fashion
    initial_state = ResolutionState()
    state_1 = ResolutionState()
    state_2 = ResolutionState()
    state_3 = ResolutionState()
    state_4 = ResolutionState()
    state_5 = ResolutionState()
    state_6 = ResolutionState()
    state_7 = ResolutionState()

    assert len(dfa.initial_states) == 1, 'The deterministic automaton can have only one initial state.'
    initial_state.bind(next(iter(dfa.initial_states)))

    # Test whether there are transitions present
    e_transitions = [
        (initial_state, (0, 0), state_1),
        (initial_state, (0, 1), state_1),
        (state_1, (0, 0), state_2),
        (state_1, (1, 1), state_2),
        (state_1, (0, 0), state_2),
        (state_1, (0, 0), state_3),
        (state_3, (0, 0), state_6),
        (state_3, (1, 0), state_4),
        (state_6, (0, 1), state_5),
        (state_4, (1, 1), state_7),
        (state_7, (1, 1), state_7),
    ]

    for origin, symbol, dest in e_transitions:
        dest_set = dfa.get_transition_target(origin.get(), symbol)
        assert len(dest_set) == 1, 'A DFA can have only 1 destination state for every alphabet symbol.'
        dest.bind(next(iter(dest_set)))

    for s in [state_1, state_2, state_3, state_4, state_5, state_6, state_7]:
        assert s.is_bound()

    assert len(dfa.final_states) == 4
