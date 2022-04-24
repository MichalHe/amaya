from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import (
    AutomatonType,
    AutomatonVisRepresentation,
    NFA, 
)

import pytest


alphabet = LSBF_Alphabet.from_variable_id_pairs((('x', 1), ('y', 2)))

@pytest.fixture()
def simple_automaton() -> NFA:
    nfa = NFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.NFA,
        initial_states={0}, final_states={1}, states={0, 1},
        used_variables=[1, 2],
    )
    nfa.update_transition_fn(0, ('*', 0), 1)
    return nfa


def test_convert_simple_nfa_into_vtf(simple_automaton: NFA):
    vtf = simple_automaton.get_visualization_representation().into_vtf(uncompress_symbols=True)
    assert vtf

    lines = vtf.split('\n')
    assert len(lines) == 9

    assert lines[0] == '@NFA'
    assert lines[1] == '%States 0 1'
    assert lines[2] == '%Initial 0'
    assert lines[3] == '%Final 1'
    assert lines[6] == '0 00 1'
    assert lines[7] == '0 10 1'

    vtf = simple_automaton.get_visualization_representation().into_vtf(uncompress_symbols=False)

    lines = vtf.split('\n')
    assert len(lines) == 8
    assert lines[0] == '@NFA'
    assert lines[1] == '%States 0 1'
    assert lines[2] == '%Initial 0'
    assert lines[3] == '%Final 1'
    assert lines[6] == '0 x0 1'


@pytest.mark.parametrize(
    ('compressed_symbol', 'expected_symbols'),
    (
        (('*', '*'), ((0, 0), (0, 1), (1, 0), (1, 1))),
        (('*',), ((0,), (1,))),
        ((1, 0), ((1, 0), )),
        (tuple(), ()),
        ((1, '*'), ((1, 0), (1, 1))),
        ((1, '*', 0), ((1, 0, 0), (1, 1, 0))),
    )
)
def test_uncompress_transition_symbols(compressed_symbol, expected_symbols):
    actual = sorted(AutomatonVisRepresentation._uncompress_symbol(compressed_symbol))
    assert actual == sorted(expected_symbols)
