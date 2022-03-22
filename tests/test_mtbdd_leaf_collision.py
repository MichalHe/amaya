import pytest
import typing as _t

from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import AutomatonType
from amaya.mtbdd_automatons import MTBDD_NFA

alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2), ('z', 3)])


@pytest.fixture
def colliding_nfas() -> _t.Tuple[MTBDD_NFA, MTBDD_NFA]:
    nfa1 = MTBDD_NFA(alphabet, AutomatonType.NFA)
    nfa2 = MTBDD_NFA(alphabet, AutomatonType.NFA)

    # Both have the transition:
    # 1 ---S---> {2,3}
    nfa1.add_state(1)
    nfa1.add_state(2)
    nfa1.add_state(3)
    nfa2.add_state(1)
    nfa2.add_state(2)
    nfa2.add_state(3)

    nfa1.update_transition_fn(1, (0, 0, 0), 2)
    nfa1.update_transition_fn(1, (0, 0, 0), 3)

    nfa2.update_transition_fn(1, (0, 0, 0), 2)
    nfa2.update_transition_fn(1, (0, 0, 0), 3)
    return (nfa1, nfa2)


def test_rename_collision(colliding_nfas: _t.Tuple[MTBDD_NFA, MTBDD_NFA]):
    nfa1, nfa2 = colliding_nfas

    hightest_state, _ = nfa1.rename_states(start_from=0)
    nfa1_trans = list(nfa1.transition_fn.iter())
    print(list(nfa1.transition_fn.iter()))

    nfa2.rename_states(start_from=hightest_state)
    nfa2_trans = list(nfa2.transition_fn.iter())
    print(list(nfa2.transition_fn.iter()))

    assert len(nfa1_trans) == 2
    assert len(nfa2_trans) == 2

    assert (0, (0, 0, 0), 1) in nfa1_trans
    assert (0, (0, 0, 0), 2) in nfa1_trans

    assert (3, (0, 0, 0), 4) in nfa2_trans
    assert (3, (0, 0, 0), 5) in nfa2_trans
