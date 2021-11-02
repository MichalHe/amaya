import pytest
from automatons import NFA, LSBF_Alphabet, AutomatonType
from export_transformations import convert_automaton_to_vtf, iter_alphabet_symbol


@pytest.fixture()
def simple_automaton() -> NFA:
    return NFA(
        alphabet=LSBF_Alphabet.from_variable_ids([1, 2]),
        automaton_type=AutomatonType.NFA,
        initial_states=set([0]),
        final_states=set([1]),
        states=set([0, 1]),
        transition_fn={
            0: {
                1: set([('*', 0)])
            }
        }
    )


@pytest.fixture()
def automaton_for_ground_formula() -> NFA:
    return NFA(
        alphabet=LSBF_Alphabet.from_variable_ids([1, 2]),
        automaton_type=AutomatonType.NFA,
        initial_states=set([0]),
        final_states=set([0]),
        states=set([0]),
        transition_fn={
            0: {
                0: set([('*', '*')])
            }
        }
    )


def test_simple_nfa(simple_automaton: NFA):
    assert simple_automaton
    vtf = convert_automaton_to_vtf(simple_automaton)
    assert vtf

    lines = vtf.split('\n')
    assert len(lines) == 9

    assert lines[0] == '@NFA'
    assert lines[1] == '%States 0 1'
    assert lines[2] == '%Initial 0'
    assert lines[3] == '%Final 1'

    assert lines[6] == '0 00 1'
    assert lines[7] == '0 10 1'


def test_automaton_for_ground_formula(automaton_for_ground_formula: NFA):
    g_nfa = automaton_for_ground_formula
    assert g_nfa
    vtf = convert_automaton_to_vtf(g_nfa)
    assert vtf

    lines = vtf.split('\n')
    assert len(lines) == 11

    assert lines[0] == '@NFA'
    assert lines[1] == '%States 0'
    assert lines[2] == '%Initial 0'
    assert lines[3] == '%Final 0'

    assert lines[6] == '0 00 0'
    assert lines[7] == '0 01 0'
    assert lines[8] == '0 10 0'
    assert lines[9] == '0 11 0'


def test_transition_symbols_expansion():
    sym = ('*', '*')
    g_syms = list(iter_alphabet_symbol(sym))
    expected_syms = [
        (0, 0),
        (0, 1),
        (1, 0),
        (1, 1),
    ]
    assert len(g_syms) == 4
    for sym in expected_syms:
        assert sym in expected_syms

    sym = ('*')
    g_syms = list(iter_alphabet_symbol(sym))
    expected_syms = [
        (0, ),
        (1, ),
    ]
    assert len(g_syms) == 2
    for sym in expected_syms:
        assert sym in expected_syms

    sym = (1, 0)
    g_syms = list(iter_alphabet_symbol(sym))
    expected_syms = [
        (1, 0),
    ]
    assert len(g_syms) == 1
    for sym in expected_syms:
        assert sym in expected_syms

    sym = tuple()
    g_syms = list(iter_alphabet_symbol(sym))
    assert len(g_syms) == 0
