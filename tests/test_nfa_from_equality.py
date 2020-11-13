from relations_structures import Relation
import pytest
from pressburger_algorithms import build_nfa_from_equality
from transitions import iter_transition_fn


@pytest.fixture
def simple_equation() -> Relation:
    return Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='='
    )


def test_build_nfa_from_equality(simple_equation: Relation):
    nfa = build_nfa_from_equality(simple_equation)

    assert len(nfa.final_states) == 1
    assert len(nfa.states) == 6

    expected_states = [2, 1, 0, -1, 'FINAL', 'TRAP']
    for e_state in expected_states:
        assert e_state in nfa.states

    expected_transitions = [
        (2, (0, 0), 1),
        (2, (1, 0), 0),
        (2, (0, 1), 'TRAP'),
        (2, (1, 1), 'TRAP'),

        (1, (0, 0), 'TRAP'),
        (1, (0, 1), 1),
        (1, (1, 0), 'TRAP'),
        (1, (1, 1), 0),
        (1, (0, 1), 'FINAL'),

        (0, (0, 0), 0),
        (0, (0, 1), 'TRAP'),
        (0, (1, 0), -1),
        (0, (1, 1), 'TRAP'),
        (0, (0, 0), 'FINAL'),

        (-1, (0, 0), 'TRAP'),
        (-1, (0, 1), 0),
        (-1, (1, 0), 'TRAP'),
        (-1, (1, 1), -1),
        (-1, (1, 1), 'FINAL'),

        ('TRAP', (0, 0), 'TRAP'),
        ('TRAP', (0, 1), 'TRAP'),
        ('TRAP', (1, 0), 'TRAP'),
        ('TRAP', (1, 1), 'TRAP'),
    ]

    actual_transitions = list(iter_transition_fn(nfa.transition_fn))

    assert len(actual_transitions) == len(expected_transitions)
    for actual_t in actual_transitions:
        assert actual_t in expected_transitions
