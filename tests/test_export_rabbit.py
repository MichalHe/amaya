import pytest

from export_transformations import convert_automaton_to_rabbit
from automatons import (
    NFA,
    LSBF_Alphabet,
    AutomatonType
)


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


def test_simple_automaton(simple_automaton: NFA):
    rabbit = convert_automaton_to_rabbit(simple_automaton)
    assert rabbit

    lines = rabbit.split('\n')
    assert len(lines) == 4

    assert lines[0] == '[0]'
    assert lines[1] == '00,[0]->[1]'
    assert lines[2] == '10,[0]->[1]'
    assert lines[3] == '[1]'
