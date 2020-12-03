import pytest
from pressburger_algorithms import build_dfa_from_sharp_inequality
from relations_structures import Relation


@pytest.fixture()
def simple_sharp_ineq() -> Relation:
    return Relation(
        ['x', 'y'],
        [1, 1],
        4,
        '<'
    )


def test_dfa_from_sharp_indeq_simple(simple_sharp_ineq: Relation):
    dfa = build_dfa_from_sharp_inequality(simple_sharp_ineq)

    expected_structure = [
        (4, (0, 0), 2),
        (4, (0, 1), 1),
        (4, (1, 0), 1),
        (4, (1, 1), 1),

        (2, (0, 0), 1),
        (2, (0, 1), 0),
        (2, (1, 0), 0),
        (2, (1, 1), 0),

        (1, (0, 0), 0),
        (1, (0, 1), 0),
        (1, (1, 0), 0),
        (1, (1, 1), -1),

        (0, (0, 0), 0),
        (0, (0, 1), -1),
        (0, (1, 0), -1),
        (0, (1, 1), -1),

        (-1, (0, 0), -1),
        (-1, (0, 1), -1),
        (-1, (1, 0), -1),
        (-1, (1, 1), -2),

        (-2, (0, 0), -1),
        (-2, (0, 1), -2),
        (-2, (1, 0), -2),
        (-2, (1, 1), -2),
    ]

    assert dfa

    for expected_transition in expected_structure:
        o, s, d = expected_transition
        print(o, s, d)
        dests = dfa.get_transition_target(o, s)
        assert len(dests) == 1
        assert d in dests

    expected_final_states = [4, 2, 1]
    for efs in expected_final_states:
        assert efs in dfa.final_states
    assert len(dfa.final_states) == 3
