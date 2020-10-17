from tests.test_nfa_intersection import nfa1 # NOQA
from automatons import NFA
from utils import iter_transition_fn


def test_nfa_complement(nfa1: NFA):  # NOQA
    non_final_states = nfa1.states - nfa1.final_states
    assert len(non_final_states) < len(nfa1.states)

    compl_nfa = nfa1.complement()
    assert compl_nfa
    assert len(compl_nfa.final_states) > len(nfa1.final_states)

    for fstate in nfa1.final_states:
        assert fstate not in compl_nfa.final_states

    assert non_final_states == compl_nfa.final_states

    assert len(tuple(iter_transition_fn(nfa1.transition_fn))) == len(tuple(iter_transition_fn(compl_nfa.transition_fn)))
