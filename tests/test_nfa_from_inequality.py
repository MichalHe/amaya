import pytest

from inequations import (
    Inequality,
    build_nfa_from_inequality
)


@pytest.fixture
def ineq() -> Inequality:
    return Inequality(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )


@pytest.fixture
def ineq2() -> Inequality:
    return Inequality(
        variable_names=['x', 'y'],
        variable_coeficients=[-3, 2],
        absolute_part=7,
        operation='<='
    )


def test_nfa_buildup_simple(ineq):
    nfa = build_nfa_from_inequality(ineq)
    assert nfa

    expected_states = [2, 1, 0, -1, -2, 'FINAL']
    assert len(nfa.states) == len(expected_states)
    for e_state in expected_states:
        assert nfa.has_state_with_value(e_state)
    assert len(nfa.final_states) == 1
    assert len(nfa.initial_states) == 1
    assert len(nfa.alphabet.symbols) == 4

    expected_transitions = [
        (2, (0, 0), 1),
        (1, (1, 0), -1),
        (-1, (1, 1), -1),
        (-1, (1, 0), -2),
        (-2, (1, 0), -2),
        (-2, (1, 0), 'FINAL'),
        (0, (0, 0), 0),
        (0, (0, 0), 'FINAL'),
    ]

    for expected_transition in expected_transitions:
        origin, symbol, dest = expected_transition
        transition_targets = nfa.get_transition_target(origin, symbol)
        assert transition_targets
        assert dest in transition_targets

    for symbol in nfa.alphabet.symbols:
        # FINAL should be reachable via all symbols from initial_state 2
        assert 'FINAL' in nfa.get_transition_target(2, symbol)


def test_nfa_buildup(ineq2):
    nfa = build_nfa_from_inequality(ineq2)
    assert nfa

    expected_states = [7, 5, 4, 3, 2, 1, 0, -1, -2, 'FINAL']
    assert len(nfa.states) == len(expected_states)
    for e_state in expected_states:
        assert nfa.has_state_with_value(e_state)

    expected_transitions = [
        (-1, (1, 0), 1),
        (-1, (0, 0), -1),
        (-1, (0, 1), -2),
        (-1, (1, 1), 0),

        (-2, (0, 0), -1),
        (-2, (1, 0), 0),
        (-2, (0, 1), -2),
        (-2, (1, 1), -1),

        (0, (0, 0), 0),
        (0, (1, 1), 0),
    ]

    for expected_transition in expected_transitions:
        origin, symbol, dest = expected_transition
        transition_targets = nfa.get_transition_target(origin, symbol)
        assert transition_targets
        assert dest in transition_targets

    unexpected_transitions = [
        (-2, (1, 1), 0),
        (7, (1, 1), 2),
        (4, (1, 1), 5),
    ]

    for unexpected_transition in unexpected_transitions:
        origin, symbol, dest = unexpected_transition
        transition_targets = nfa.get_transition_target(origin, symbol)
        if transition_targets:
            assert dest not in transition_targets
        else:
            assert not transition_targets

    # FINAL should be reachable from any state except FINAL, via 0,1

    for origin in expected_states:
        symbol = (0, 1)
        if origin == 'FINAL':
            continue
        assert 'FINAL' in nfa.get_transition_target(origin, symbol)
