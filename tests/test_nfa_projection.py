from typing import Type

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonSnapshot,
    AutomatonType,
    NFA,
)
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType
)

import pytest


def complement_nth_bit(symbol, bit_pos):
    complement_sym = list(symbol)
    if (complement_sym[bit_pos] == 1):
        complement_sym[bit_pos] = 0
    else:
        complement_sym[bit_pos] = 1
    return tuple(complement_sym)


@pytest.mark.parametrize('nfa_type', (NFA, MTBDD_NFA))
def test_mtbdd_nfa_projection(nfa_type: Type[NFA]):
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])
    nfa = nfa_type(automaton_type=AutomatonType.NFA, alphabet=alphabet,
                   state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None),
                   used_variables=[1, 2],
                   states={1, 2, 3}, final_states={3}, initial_states={1})
    
    transitions = (
        (1, (0, 0), 1),
        (1, (0, 1), 1),
        (1, (0, 0), 2),
        (2, (1, 0), 2),
        (2, (1, 1), 3),
        (2, (1, 1), 1),
        (3, (0, 1), 3),
        (3, (1, 1), 3),
    )

    for transition in transitions:
        nfa.update_transition_fn(*transition)

    # Copy out the states (projection might be performed in place)
    original_automaton = AutomatonSnapshot.create_snapshot(nfa)

    nfa_after_projection = nfa.do_projection(1)
    expected_states_after_projection = original_automaton.states.union({4})  # A state should be added in padding closure
    expected_final_states_after_projection = original_automaton.final_states.union({4})
    assert nfa_after_projection.states == expected_states_after_projection
    assert nfa_after_projection.final_states == expected_final_states_after_projection
    assert nfa_after_projection.initial_states == original_automaton.initial_states

    for origin, original_symbol, destination in original_automaton.transitions:
        assert destination in nfa_after_projection.get_transition_target(origin, original_symbol)
        assert destination in nfa_after_projection.get_transition_target(origin, complement_nth_bit(original_symbol, 0))
