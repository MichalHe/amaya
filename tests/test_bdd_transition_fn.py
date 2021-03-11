import pytest
from transitions import SparseBDDTransitionFunction
from automatons import LSBF_Alphabet
from dd import bdd

@pytest.fixture
def bddtfn() -> SparseBDDTransitionFunction:
    manager = bdd.BDD()
    manager.declare('x', 'y', 'z')
    alphabet = LSBF_Alphabet.from_variable_names(('x', 'y', 'z'))
    return SparseBDDTransitionFunction(manager, alphabet)


def test_iterator(bddtfn: SparseBDDTransitionFunction):
    bddtfn.insert_transition('q1', (0, 0, 1), 'q2')
    bddtfn.insert_transition('q1', (0, 0, 0), 'q2')

    transitions = list(bddtfn.iter())
    assert len(transitions) == 1
    assert (0, 0, '*') in transitions


def test_complete_with_trap_state(bddtfn: SparseBDDTransitionFunction):
    states = ['q0', 'q1']
    alphabet = LSBF_Alphabet.from_variable_names(('x', 'y', 'z'))
    bddtfn.insert_transition('q0', (0, 0, 1), 'q1')

    trap_state_present = bddtfn.complete_with_trap_state(alphabet, states)
    assert trap_state_present

    assert bddtfn.is_in_state_post('q0', 'TRAP')
    assert bddtfn.is_in_state_post('q1', 'TRAP')

    d = bddtfn.get_transition_target('q0', ('*', '*', 0))
    assert 'TRAP' in d
    assert len(d) == 1

    trap_state_added = bddtfn.complete_with_trap_state(alphabet, states)
    assert not trap_state_added