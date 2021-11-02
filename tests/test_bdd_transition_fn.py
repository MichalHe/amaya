import pytest
from transitions import SparseBDDTransitionFunction
from automatons import LSBF_Alphabet
from dd import bdd
from itertools import combinations
from typing import List

@pytest.fixture
def bddtfn() -> SparseBDDTransitionFunction:
    manager = bdd.BDD()
    manager.declare('1', '2', '3')
    alphabet = LSBF_Alphabet.from_variable_ids([1, 2, 3])
    return SparseBDDTransitionFunction(manager, alphabet)


def test_iterator(bddtfn: SparseBDDTransitionFunction):
    bddtfn.insert_transition('q1', (0, 0, 1), 'q2')
    bddtfn.insert_transition('q1', (0, 0, 0), 'q2')

    transitions = list(bddtfn.iter())
    assert len(transitions) == 1
    assert ('q1', (0, 0, '*'), 'q2') in transitions


def test_complete_with_trap_state(bddtfn: SparseBDDTransitionFunction):
    states = ['q0', 'q1']
    alphabet = LSBF_Alphabet.from_variable_ids([1, 2, 3])
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

def test_project_bit_away_simple(bddtfn: SparseBDDTransitionFunction):
    bddtfn.insert_transition('q0', (0, 0, 1), 'q1')
    bddtfn.project_bit_away(2)  # Remaining variables: x, y

    cube = bddtfn.get_cube_from_symbol((0, 0))
    assert 'x' in cube and cube['x'] is False
    assert 'y' in cube and cube['y'] is False
    assert len(cube) == 2

    targets = bddtfn.get_transition_target('q0', (0, 0))
    assert ['q1'] == targets
    assert not bddtfn.get_transition_target('q0', (0, 1))


def test_project_bit_away_adv(bddtfn: SparseBDDTransitionFunction):
    bddtfn.insert_transition('q0', (0, 0, 1), 'q1')
    bddtfn.insert_transition('q0', (0, 1, 1), 'q1')
    bddtfn.project_bit_away(1)  # Projects y away

    cube = bddtfn.get_cube_from_symbol((0, 1))
    assert 'x' in cube and 'z' in cube
    assert 'y' not in cube
    assert cube['x'] is False and cube['z'] is True

    symbols = list(bddtfn.iter())
    assert symbols
    assert len(symbols) == 1
    assert ('q0', (0, '*',1), 'q1') in symbols

def assert_system_part(bddtfn, system, part, expected_symbols):
    def get_symbol_from_model(model, var_names):
        symbol = list()
        for var in var_names:
            symbol.append(int(model[var]))
        return tuple(symbol)

    bdd = system[part]
    models = list(bddtfn.manager.pick_iter(bdd, care_vars=['x', 'y', 'z']))
    assert len(models) == len(expected_symbols)
    for model in models:
        symbol = get_symbol_from_model(model, ['x', 'y', 'z'])
        assert symbol in expected_symbols

def testb_bdd_minterms_simple(bddtfn: SparseBDDTransitionFunction):

    bddtfn.insert_transition('q0', (0, 0, 1), 'q1')
    bddtfn.insert_transition('q0', (0, 0, 0), 'q1')

    bddtfn.insert_transition('q2', (0, 0, 1), 'q3')
    bddtfn.insert_transition('q2', (0, 1, 0), 'q3')
    # The only symbol in the intersection is (0, 0, 1)

    sys = bddtfn.get_minterm_system_from_states(['q0', 'q2'])
    assert sys
    assert len(sys)
    assert ('q1',) in sys
    assert ('q3',) in sys
    assert ('q1', 'q3') in sys


    assert_system_part(bddtfn, sys, ('q1', ), [(0, 0, 0)])
    assert_system_part(bddtfn, sys, ('q3', ), [(0, 1, 0)])
    assert_system_part(bddtfn, sys, ('q1', 'q3'), [(0, 0, 1)])


def test_minterms_advanced(bddtfn: SparseBDDTransitionFunction):# Alpha
    # Alpha     ~ q1
    bddtfn.insert_transition('q0', (0, 0, 0), 'q1')
    bddtfn.insert_transition('q0', (0, 0, 1), 'q1')
    bddtfn.insert_transition('q0', (1, 0, 0), 'q1')

    # Beta      ~ q3
    bddtfn.insert_transition('q2', (1, 0, 0), 'q3')
    bddtfn.insert_transition('q2', (0, 0, 1), 'q3')

    # Gama      ~ q5
    bddtfn.insert_transition('q4', (0, 1, 0), 'q5')
    bddtfn.insert_transition('q4', (0, 0, 0), 'q5')
    bddtfn.insert_transition('q4', (0, 0, 1), 'q5')

    sys = bddtfn.get_minterm_system_from_states(['q0', 'q2', 'q4'])
    assert len(sys) == 7

    assert_system_part(bddtfn, sys, ('q1', 'q3', 'q5'), [(0, 0, 1)])

    assert_system_part(bddtfn, sys, ('q1', 'q3'), [(1, 0, 0)])
    assert_system_part(bddtfn, sys, ('q1', 'q5'), [(0, 0, 0)])
    assert_system_part(bddtfn, sys, ('q3', 'q5'), [])

    assert_system_part(bddtfn, sys, ('q1', ), [])
    assert_system_part(bddtfn, sys, ('q3', ), [])
    assert_system_part(bddtfn, sys, ('q5', ), [(0, 1, 0)])


def test_determinize_syntetic_simple(bddtfn: SparseBDDTransitionFunction):
    from automaton_algorithms import determinize_bdd
    bddtfn.insert_transition('qA', (0, 0, 0), 'q1')
    bddtfn.insert_transition('qA', (0, 0, 1), 'q2')
    bddtfn.insert_transition('qB', (0, 0, 0), 'q3')
    # Expected determinization result:
    # {qA, qB} ---- (0, 0, 0) ----> {q1, q3}
    # {qA, qB} ---- (0, 0, 1) ----> {q2}
    result = determinize_bdd(initial_states=['qA', 'qB'],
                             final_states=[],
                             tfn=bddtfn)
    assert result
    assert result['initial_states'] == {('qA', 'qB'), }
    assert result['final_states'] == set()
    assert len(result['states'])

    expected_states = [('qA', 'qB'), ('q1', 'q3'), ('q2', )]
    for es in expected_states:
        assert es in result['states']

    expected_transitions = [
        (('qA', 'qB'), (0, 0, 0), ('q1', 'q3')),
        (('qA', 'qB'), (0, 0, 1), ('q2', )),
    ]

    actual_transitions = list(result['transition_fn'].iter())
    for et in expected_transitions:
        assert et in actual_transitions
        
        
def test_determinize_real_nfa():
    from automaton_algorithms import determinize_bdd
    manager = bdd.BDD()
    manager.declare('1', '2')
    alphabet = LSBF_Alphabet.from_variable_ids([1, 2])
    tfn: SparseBDDTransitionFunction = SparseBDDTransitionFunction(manager, alphabet)

    # Real automaton for the intequation: x - y \le 3
    # states = {3, 2, 0, -1, 'F'}
    final_states = {'F',}
    initial_states = {3}

    # Transitions
    tfn.insert_transition(3, (0, 0), 1)
    tfn.insert_transition(3, (1, 0), 1)
    tfn.insert_transition(3, (1, 1), 1)
    tfn.insert_transition(3, (0, 1), 2)
    tfn.insert_transition(3, ('*', '*'), 'F')

    tfn.insert_transition(2, (0, 0), 1)
    tfn.insert_transition(2, (1, 1), 1)
    tfn.insert_transition(2, (0, 1), 1)
    tfn.insert_transition(2, (1, 0), 0)
    tfn.insert_transition(2, ('*', '*'), 'F')

    tfn.insert_transition(1, (0, 0), 0)
    tfn.insert_transition(1, (1, 1), 0)
    tfn.insert_transition(1, (1, 0), 0)
    tfn.insert_transition(1, (0, 1), 1)
    tfn.insert_transition(1, ('*', '*'), 'F')

    tfn.insert_transition(0, (0, 0), 0)
    tfn.insert_transition(0, (1, 1), 0)
    tfn.insert_transition(0, (0, 1), 0)
    tfn.insert_transition(0, (1, 0), -1)
    tfn.insert_transition(0, (0, 0), 'F')
    tfn.insert_transition(0, (1, 1), 'F')
    tfn.insert_transition(0, (1, 0), 'F')

    tfn.insert_transition(-1, (0, 0), -1)
    tfn.insert_transition(-1, (1, 1), -1)
    tfn.insert_transition(-1, (1, 0), -1)
    tfn.insert_transition(-1, (0, 1), 0)

    tfn.insert_transition(-1, (1, 0), 'F')

    det_res = determinize_bdd(initial_states=list(initial_states), final_states=list(final_states), tfn=tfn)
    assert det_res

    act_states = det_res['states']
    exp_states = [(3,), (1, 'F'), (2, 'F'), (0, 'F'), (-1, 'F'), (-1, ), (0, )]
    assert len(act_states) == 7
    for es in exp_states:
        assert es in act_states
    
    act_fin_states = det_res['final_states'] 
    exp_fin_states = [(1, 'F'), (2, 'F'), (0, 'F'), (-1, 'F')]
    for efs in exp_fin_states:
        assert efs in act_fin_states

    resulting_tfn = det_res['transition_fn']

    # Check some transitions(not all):
    expected_transitions = [
        ((3, ), (0, 0), (1, 'F')),
        ((0, ), (0, 1), (0, )),
        ((0, 'F'), (0, 0), (0, 'F')),
        ((-1, 'F'), (0, 1), (0, )),
    ]

    act_t = list(resulting_tfn.iter())
    for et in expected_transitions:
        assert et in act_t