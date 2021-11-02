from automatons import NFA, LSBF_Alphabet, AutomatonType, AutomatonSnapshot
from mtbdd_automatons import MTBDD_NFA
import pytest as pt
from tests.test_nfa_determization import ResolutionState


@pt.fixture()
def mtbdd_nfa1() -> MTBDD_NFA:
    '''Creates a simple synthetic nondeterministic automaton.
    Nondeterminism - not every state has a transition for every alphabet symbol.
    Otherwise it is defacto deterministic - it should be possible to project the
    structure onto the original one.'''

    alphabet = LSBF_Alphabet.from_variable_ids([1])
    nfa = MTBDD_NFA(alphabet, AutomatonType.NFA)

    nfa.add_state(0)
    nfa.add_state(1)
    nfa.add_state(2)
    nfa.add_initial_state(0)
    nfa.add_final_state(2)

    zeta0 = (0, )
    nfa.update_transition_fn(0, zeta0, 1)
    nfa.update_transition_fn(1, zeta0, 2)

    return nfa


def test_nfa_complement(mtbdd_nfa1: NFA):  # NOQA
    before_snapshot = AutomatonSnapshot.create_snapshot(mtbdd_nfa1)

    compl_nfa = mtbdd_nfa1.complement()
    assert compl_nfa

    # The NFA before completion has 3 states:
    #   0 - initial, 1, 2 - final
    # After determinization a trapstate should be added
    assert len(compl_nfa.final_states) == 2
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
        dest.bind(transition_dest_set[0])

    assert state0.get() not in compl_nfa.final_states
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
        dest.bind(transition_dest_set[0])

    return

    # assert len(tuple(iter_transition_fn(nfa1.transition_fn.data))) == len(tuple(iter_transition_fn(compl_nfa.transition_fn.data)))  # type: ignore
