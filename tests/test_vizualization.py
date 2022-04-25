import re

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


def test_colorize_dot():
    nfa = NFA(automaton_type=AutomatonType.NFA, alphabet=alphabet,
              states={0, 1, 2}, initial_states={0}, final_states={1}, used_variables=[1, 2]) 

    # SCCs: {0, 1}, {2}
    nfa.update_transition_fn(0, (0, 0), 1)
    nfa.update_transition_fn(1, (0, 0), 0)
    nfa.update_transition_fn(1, (0, 0), 2)

    dot = str(nfa.get_visualization_representation().into_graphviz(highlight_sccs=True))
    assert dot
    colorized_lines = [line.strip()[:1] for line in dot.split('\n') if 'fillcolor' in line]
    assert colorized_lines == ['0', '1']

    # SCCs: {0, 1}, {2, 3}
    nfa = NFA(automaton_type=AutomatonType.NFA, alphabet=alphabet,
              states={0, 1, 2, 3}, initial_states={0}, final_states={1}, used_variables=[1, 2]) 

    nfa.update_transition_fn(0, (0, 0), 1)
    nfa.update_transition_fn(1, (0, 0), 0)
    nfa.update_transition_fn(1, (0, 0), 2)
    nfa.update_transition_fn(2, (0, 0), 3)
    nfa.update_transition_fn(3, (0, 0), 2)

    dot = str(nfa.get_visualization_representation().into_graphviz(highlight_sccs=True))

    node_to_fill_color = {}
    for line in dot.split('\n'):
        line = line.strip()
        if not len(line) > 2 or not line[2] == '[':
            continue
        node, attrs_label = line.split(' ', 1)
        attrs = attrs_label.strip('[]').split(' ')
        fill_color = next(filter(lambda attr: 'fillcolor' in attr, attrs))
        node_to_fill_color[node] = fill_color

    assert node_to_fill_color['0'] == node_to_fill_color['1']
    assert node_to_fill_color['2'] == node_to_fill_color['3']


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
