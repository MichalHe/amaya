from amaya.automatons import (
    AutomatonType,
    AutomatonSnapshot,
    NFA
)
from amaya.alphabet import LSBF_Alphabet
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType,
)
from tests.conftest import ResolutionState

import pytest


@pytest.fixture()
def mtbdd_nfa1() -> MTBDD_NFA:
    variable_id_pairs = [('x', 1)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(variable_id_pairs)
    nfa = MTBDD_NFA(alphabet=alphabet, automaton_type=AutomatonType.DFA,
                    state_semantics=AH_Atom(atom_type=AH_AtomType.CUSTOM, atom=None))

    nfa.add_state(0)
    nfa.add_state(1)
    nfa.add_state(2)
    nfa.add_initial_state(0)
    nfa.add_final_state(2)

    zeta0 = (0, )
    nfa.update_transition_fn(0, zeta0, 1)
    nfa.update_transition_fn(1, zeta0, 2)
    
    nfa.add_trap_state()

    return nfa


def test_nfa_complement(mtbdd_nfa1: NFA):  # NOQA
    before_snapshot = AutomatonSnapshot.create_snapshot(mtbdd_nfa1)

    compl_nfa = mtbdd_nfa1.complement()
    assert compl_nfa

    # The NFA before completion has 3 states:
    #   0 - initial, 1, 2 - final
    # After determinization a trapstate should be added
    assert len(compl_nfa.final_states) == 3  # Final states are 0, 1, Trap
    assert len(compl_nfa.initial_states) == 1

    state0 = ResolutionState()
    state1 = ResolutionState()
    state2 = ResolutionState()
    stateTrap = ResolutionState()

    state0.bind(next(iter(compl_nfa.initial_states)))
    zeta0 = (0, )

    path = [
        (state0, zeta0, state1),
        (state1, zeta0, state2)
    ]

    for origin, symbol, dest in path:
        transition_dest_set = compl_nfa.get_transition_target(origin.get(), symbol)
        assert len(transition_dest_set) == 1
        dest.bind(next(iter(transition_dest_set)))

    assert state0.get() in compl_nfa.final_states
    assert state1.get() in compl_nfa.final_states
    assert state2.get() not in compl_nfa.final_states

    zeta1 = (1, )
    trap_paths = [
        (state0, zeta1, stateTrap),
        (state1, zeta1, stateTrap),
        (state2, zeta1, stateTrap),
    ]

    for origin, symbol, dest in trap_paths:
        transition_dest_set = compl_nfa.get_transition_target(origin.get(), symbol)
        assert len(transition_dest_set) == 1
        dest.bind(next(iter(transition_dest_set)))

    return
