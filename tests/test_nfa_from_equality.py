from relations_structures import Relation
import pytest
from presburger_algorithms import build_nfa_from_linear_equality
from transitions import iter_transition_fn
from alphabet import LSBF_Alphabet
from automatons import NFA


@pytest.fixture
def simple_equation() -> Relation:
    return Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        modulo_terms=[],
        modulo_term_coeficients=[],
        absolute_part=2,
        operation='='
    )


def test_build_nfa_from_equality(simple_equation: Relation):
    alphabet = LSBF_Alphabet.from_variable_ids([1, 2])
    nfa = build_nfa_from_linear_equality(simple_equation, [1, 2], alphabet, NFA)

    expected_states = [2, 1, 0, -1, 'FINAL']
    for e_state in expected_states:
        assert e_state in nfa.states

    assert len(nfa.final_states) == 1
    assert len(nfa.states) == len(expected_states)

    expected_transitions = [
        (2, (0, 0), 1),
        (2, (1, 0), 0),

        (1, (0, 1), 1),
        (1, (1, 1), 0),
        (1, (0, 1), 'FINAL'),

        (0, (0, 0), 0),
        (0, (1, 0), -1),
        (0, (0, 0), 'FINAL'),

        (-1, (0, 1), 0),
        (-1, (1, 1), -1),
        (-1, (1, 1), 'FINAL'),
    ]

    actual_transitions = list(iter_transition_fn(nfa.transition_fn.data))

    assert len(actual_transitions) == len(expected_transitions)
    for actual_t in actual_transitions:
        assert actual_t in expected_transitions
