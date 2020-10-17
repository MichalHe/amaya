from tests.test_nfa_intersection import nfa1  # NOQA
from automatons import NFA

def test_nfa_projection(nfa1: NFA):  # NOQA

    pnfa = nfa1.do_projection('x')
    assert pnfa
    assert pnfa.states == nfa1.states
    assert pnfa.final_states == nfa1.final_states
    assert pnfa.initial_states == nfa1.initial_states

    assert len(pnfa.alphabet.symbols) == (len(nfa1.alphabet.symbols)/2)

    expected_symbols_projection = {  # x was the first variable
        (0, 0): (0, ),
        (0, 1): (1, ),
        (1, 0): (0, ),
        (1, 1): (1, ),
    }

    for o_src in nfa1.transition_fn:
        for o_sym in nfa1.transition_fn[o_src]:
            n_sym = expected_symbols_projection[o_sym]
            assert pnfa.transition_fn[o_src][n_sym] >= nfa1.transition_fn[o_src][o_sym]  # Each new transition fn should be superset to old one
