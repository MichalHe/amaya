from typing import (
    Tuple,
    List
)

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    DFA,
    NFA,
)
from amaya.presburger.constructions.integers import build_presburger_congruence_nfa
from amaya.relations_structures import Congruence, Var
from tests.conftest import ResolutionState

import pytest


@pytest.fixture
def congruence0() -> Tuple[LSBF_Alphabet, Congruence]:
    """Congruence (x mod 3) = 1"""

    relation = Congruence(vars=[Var(id=1)], coefs=[1], rhs=1, modulus=3)
    alphabet = LSBF_Alphabet.from_vars([Var(id=1)])
    return (alphabet, relation)


@pytest.fixture
def congruence_2pow() -> Tuple[LSBF_Alphabet, Congruence]:
    relation = Congruence(vars=[Var(id=1)], coefs=[1], rhs=0, modulus=4)
    alphabet = LSBF_Alphabet.from_vars([Var(id=1)])
    return (alphabet, relation)


def test_nfa_from_congruence_with_mod_3(congruence0: Tuple[LSBF_Alphabet, Congruence]):
    """Check that the automaton for relation (x mod 3) = 1 has the expected structure."""
    alphabet, congruence = congruence0

    nfa = build_presburger_congruence_nfa(NFA, alphabet, congruence)

    assert len(nfa.states) == 4
    assert len(nfa.final_states) == 1
    assert len(nfa.initial_states) == 1

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

        destination = [
            state for state in nfa.get_transition_target(source.get(), symbol) if state != final_state
        ]

        assert len(destination) == 1

        expected_destination.bind(destination[0])

    expected_transitions_to_final_state = [
        (rem0, (0, )),
        (rem2, (1, ))
    ]
    for source, symbol in expected_transitions_to_final_state:
        assert final_state in nfa.get_transition_target(source.get(), symbol)
    assert nfa.used_variables == [Var(id=1)]


def test_with_power_of_two_modulo(congruence_2pow: Tuple[LSBF_Alphabet, Congruence]):
    alphabet, congruence = congruence_2pow

    nfa = build_presburger_congruence_nfa(NFA, alphabet, congruence)

    assert len(nfa.states) == 4
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

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
        destination_list = [d for d in nfa.get_transition_target(origin.get(), symbol) if d != final_state]
        assert len(destination_list) == 1
        dest.bind(destination_list[0])


    assert final_state in nfa.get_transition_target(state0_0.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_1.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_2.get(), (0,))
    assert final_state in nfa.get_transition_target(state0_2.get(), (1,))

    assert nfa.used_variables == [Var(id=1)]
