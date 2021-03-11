import pytest
from transitions import SparseBDDTransitionFunction, SparseSimpleTransitionFunction
from dd.bdd import BDD
from automatons import LSBF_Alphabet
from typing import Union

@pytest.fixture
def bdd_tfn():
    manager = BDD()
    manager.declare('x', 'y', 'z')
    alphabet = LSBF_Alphabet.from_variable_names(('x', 'y', 'z'))
    return SparseBDDTransitionFunction(manager, alphabet)

@pytest.fixture
def simple_tfn():
    return SparseSimpleTransitionFunction()


def _test_simple_insertion(bdd_tfn: SparseBDDTransitionFunction):
    bdd_tfn.insert_transition('q0', (0, 0, 0), 'q1')

    transition_target = bdd_tfn.get_transition_target('q0', (0,0,0))
    assert transition_target is not None
    assert 'q1' in transition_target


def _test_advanced_intersection(bdd_tfn):
    bdd_tfn.insert_transition('q0', (0, 0, 0), 'q1')
    bdd_tfn.insert_transition('q0', (0, 0, 1), 'q1')

    targets = bdd_tfn.get_transition_target('q0', (0, 0, '*'))
    assert targets is not None
    assert 'q1' in targets
    assert len(targets) == 1

    targets = bdd_tfn.get_transition_target('q1', (0, 0, '*'))
    assert targets == set()

    targets = bdd_tfn.get_transition_target('q0', ('*', 0, '*'))
    assert targets is not None
    assert len(targets) == 1
    assert 'q1' in targets

    bdd_tfn.insert_transition('q0', (0, 0, '*'), 'q2')
    targets = bdd_tfn.get_transition_target('q0', (0, 0, 0))
    assert len(targets) == 2


def _test_rename_states(bdd_tfn):
    bdd_tfn.insert_transition('q0', (0, 0, 1), 'q1')
    mapping = {'q0': 'a', 'q1': 'b'}
    bdd_tfn.rename_states(mapping)

    targets = bdd_tfn.get_transition_target('a', (0, 0, 1))
    assert 'b' in targets
    assert len(targets) == 1


def _test_union(union_fn, tfn):
    tfn_0 = tfn
    tfn_1 = tfn.copy()

    tfn_0.insert_transition('q0', (0, 0, 1), 'q1')
    targets = tfn_0.get_transition_target('q0', (0, 0, 1))

    tfn_0.insert_transition('q0', (0, 1, 1), 'q2')
    targets = tfn_0.get_transition_target('q0', (0, 0, 1))

    tfn_1.insert_transition('q0', (0, 0, 0), 'q1')
    tfn_1.insert_transition('q0', (1, 0, 0), 'q3')

    union = union_fn(tfn_0, tfn_1)

    assert union is not None
    targets = union.get_transition_target('q0', ('*', '*', '*'))
    assert targets
    assert len(targets) == 3

    expected_targets = ['q1', 'q1', 'q3']
    for target in expected_targets:
        assert target in targets

    targets = union.get_transition_target('q0', (0, 0, '*'))
    assert len(targets) == 1
    assert 'q1' in targets

def test_bdd__union(bdd_tfn: SparseBDDTransitionFunction):
    _test_union(SparseBDDTransitionFunction.union_of, bdd_tfn)

def test_simple_tfn__union(simple_tfn: SparseSimpleTransitionFunction):
    _test_union(SparseSimpleTransitionFunction.union_of, simple_tfn)

def test_bdd__rename_states(bdd_tfn: SparseBDDTransitionFunction):
    _test_rename_states(bdd_tfn)

def test_simple_tfn__rename_states(simple_tfn: SparseSimpleTransitionFunction):
    _test_rename_states(simple_tfn)

def test_bdd__advanced_intersection(bdd_tfn: SparseBDDTransitionFunction):
    _test_advanced_intersection(bdd_tfn)

def test_simple_tfn__advanced_intersection(simple_tfn: SparseBDDTransitionFunction):
    _test_advanced_intersection(simple_tfn)

def test_simple_tfn__simple_insertion(simple_tfn: SparseBDDTransitionFunction):
    _test_simple_insertion(simple_tfn)

def test_bdd__simple_insertion(bdd_tfn: SparseBDDTransitionFunction):
    _test_simple_insertion(bdd_tfn)