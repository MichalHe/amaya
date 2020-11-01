from transitions import (
    get_indices_of_missing_variables,
    unite_alphabets,
    extend_symbol_with_missing_indices,
    extend_transitions_to_new_alphabet_symbols,
    iter_transition_fn
)
from typing import List, Union
from inequations_data import Inequality
from inequations import build_nfa_from_inequality
from automatons import NFA
import pytest


@pytest.fixture
def xy_nfa_from_ineq() -> NFA[Union[int, str]]:
    ineq1 = Inequality(['x', 'y'], [1, 1], -1, '<=')
    nfa1 = build_nfa_from_inequality(ineq1)
    return nfa1


@pytest.fixture
def xz_nfa_from_ineq() -> NFA[Union[int, str]]:
    ineq2 = Inequality(['x', 'z'], [1, 1], 0, '<=')
    nfa2 = build_nfa_from_inequality(ineq2)
    return nfa2


@pytest.fixture
def y_nfa_from_ineq() -> NFA[Union[int, str]]:
    ineq1 = Inequality(['y'], [1], -1, '<=')
    nfa1 = build_nfa_from_inequality(ineq1)
    return nfa1


@pytest.fixture
def x_nfa_from_ineq() -> NFA[Union[int, str]]:
    ineq2 = Inequality(['x'], [1], 0, '<=')
    nfa2 = build_nfa_from_inequality(ineq2)
    return nfa2


def test_get_indices_of_missing_variables():
    indices: List[int] = get_indices_of_missing_variables("a b c".split(), "x a y b c z w".split())
    expected_indices = [0, 2, 5, 6]
    assert expected_indices == indices

    indices = get_indices_of_missing_variables("a".split(), "a b c x y z".split())
    expected_indices = [1, 2, 3, 4, 5]
    assert expected_indices == indices

    indices = get_indices_of_missing_variables("a x y z".split(), "b c a x y z u".split())
    expected_indices = [0, 1, 6]
    assert expected_indices == indices


def test_unite_alphabets():
    alphabet1 = 'a c d'.split()
    alphabet2 = 'b x'.split()

    u = unite_alphabets(alphabet1, alphabet2)
    assert 'a b c d x' == ' '.join(u)

    indices_1 = get_indices_of_missing_variables(alphabet1, u)
    expected_indices = [1, 4]
    assert indices_1 == expected_indices

    indices_2 = get_indices_of_missing_variables(alphabet2, u)
    expected_indices = [0, 2, 3]
    assert indices_2 == expected_indices


def test_extend_symbol_on_indices():
    old_al = 'b x'.split()
    new_al = 'a b c x z'.split()

    indices = get_indices_of_missing_variables(old_al, new_al)
    assert indices == [0, 2, 4]

    symbol = (1, 0)
    assert ('*', 1, '*', 0, '*') == extend_symbol_with_missing_indices(symbol, indices)


def test_extend_transitions_to_new_alphabet():
    old_al = 'b x'.split()
    new_al = 'a b c x z'.split()

    transitions = {
        1: {
            2: set([(0, 1), (1, 0)]),
            3: set([(1, '*')]),
        },
        2: {
            1: set([('*', 1)])
        }
    }

    extended_transitions = extend_transitions_to_new_alphabet_symbols(old_al, new_al, transitions)

    assert('*', 0, '*', 1, '*') in extended_transitions[1][2]
    assert('*', 1, '*', 0, '*') in extended_transitions[1][2]

    assert('*', 1, '*', '*', '*') in extended_transitions[1][3]
    assert('*', '*', '*', 1, '*') in extended_transitions[2][1]


def test_unite_nfas_with_different_alphabets(xy_nfa_from_ineq, xz_nfa_from_ineq):
    nfa1 = xy_nfa_from_ineq
    nfa2 = xz_nfa_from_ineq

    union = nfa1.union(nfa2)
    assert union
    assert len(union.alphabet.variable_names) == 3

    cnt = 0
    for o, s, d in iter_transition_fn(union.transition_fn):
        assert len(s) == 3
        cnt += 1

    assert cnt == len(list(iter_transition_fn(nfa1.transition_fn))) + len(list(iter_transition_fn(nfa2.transition_fn)))


def test_intersect_nfas_with_different_alphabets(y_nfa_from_ineq, x_nfa_from_ineq):

    state_names_x = {}
    state_names_y = {}

    def state_renamed(aid, old, new):
        if aid == id(y_nfa_from_ineq):
            state_names_y[old] = new
        else:
            state_names_x[old] = new

    y_nfa_from_ineq._debug_state_rename = state_renamed
    x_nfa_from_ineq._debug_state_rename = state_renamed

    intersection = y_nfa_from_ineq.intersection(x_nfa_from_ineq)
    print(state_names_x)
    print(state_names_y)
    assert len(y_nfa_from_ineq.states) == 2
    assert len(x_nfa_from_ineq.states) == 3
    assert intersection
    assert len(intersection.final_states) == 1

    _e_states = [
        (0, -1),
        (-1, -1),
        ('FINAL', 'FINAL')
    ]

    expected_states = []
    for state in _e_states:
        b, a = state
        expected_states.append((state_names_y[a], state_names_x[b]))

    for expected_state in expected_states:
        assert expected_state in intersection.states
