from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.mtbdd_automatons import MTBDD_NFA
from amaya.relations_structures import Relation, Var
from amaya.presburger.constructions.integers import build_nfa_from_linear_inequality
from tests.conftest import ResolutionState

import pytest


alphabet = LSBF_Alphabet.from_vars([Var(id=1), Var(id=2)])

@pytest.fixture
def ineq() -> Relation:
    return Relation(vars=[Var(id=1), Var(id=2)], coefs=[2, -1], predicate_symbol='<=', rhs=2)


@pytest.fixture()
def ineq1() -> Relation:
    """Returns relation: x - y <= 0."""
    return Relation(vars=[Var(id=1), Var(id=2)], coefs=[1, -1], rhs=0, predicate_symbol="<=")


@pytest.fixture()
def ineq2() -> Relation:
    return Relation(vars=[Var(id=1), Var(id=2)], coefs=[1, 1], rhs=1, predicate_symbol="<=")


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_ineq0(automaton_cls: NFA, ineq: Relation):
    nfa = build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq)
    assert nfa

    expected_states = {
        '2': ResolutionState('2'),
        '1': ResolutionState('1'),
        '0': ResolutionState('0'),
        '-1': ResolutionState('-1'),
        '-2': ResolutionState('-2'),
        'qf': ResolutionState('qf'),
    }

    assert len(nfa.final_states) == 1
    assert len(nfa.initial_states) == 1
    assert len(nfa.states) == len(expected_states)

    expected_transitions = [
        (expected_states['2'], (0, 0), expected_states['1']),
        (expected_states['2'], (0, 1), expected_states['1']),
        (expected_states['2'], (1, 0), expected_states['0']),
        (expected_states['2'], (1, 1), expected_states['0']),

        (expected_states['1'], (0, 0), expected_states['0']),
        (expected_states['1'], (0, 1), expected_states['1']),
        (expected_states['1'], (1, 0), expected_states['-1']),
        (expected_states['1'], (1, 1), expected_states['0']),

        (expected_states['0'], (0, 0), expected_states['0']),
        (expected_states['0'], (0, 1), expected_states['0']),
        (expected_states['0'], (1, 0), expected_states['-1']),
        (expected_states['0'], (1, 1), expected_states['-1']),

        (expected_states['-1'], (0, 0), expected_states['-1']),
        (expected_states['-1'], (0, 1), expected_states['0']),
        (expected_states['-1'], (1, 0), expected_states['-2']),
        (expected_states['-1'], (1, 1), expected_states['-1']),

        (expected_states['-2'], (0, 0), expected_states['-1']),
        (expected_states['-2'], (0, 1), expected_states['-1']),
        (expected_states['-2'], (1, 0), expected_states['-2']),
        (expected_states['-2'], (1, 1), expected_states['-2']),
    ]

    expected_fin_transitions = [
        (expected_states['2'], (0, 0)),
        (expected_states['2'], (0, 1)),
        (expected_states['2'], (1, 0)),
        (expected_states['2'], (1, 1)),

        (expected_states['1'], (0, 0)),
        (expected_states['1'], (0, 1)),
        (expected_states['1'], (1, 0)),
        (expected_states['1'], (1, 1)),

        (expected_states['0'], (0, 0)),
        (expected_states['0'], (1, 0)),
        (expected_states['0'], (1, 1)),

        (expected_states['-1'], (1, 0)),
        (expected_states['-1'], (1, 1)),

        (expected_states['-2'], (1, 0)),
    ]

    expected_states['2'].bind(next(iter(nfa.initial_states)))
    expected_states['qf'].bind(next(iter(nfa.final_states)))

    for origin, symbol, dest in expected_transitions:
        transition_targets = set(nfa.get_transition_target(origin.get(), symbol)).difference(nfa.final_states)
        assert len(transition_targets) == 1
        dest.bind(next(iter(transition_targets)))


    for origin, symbol in expected_fin_transitions:
        transition_targets = set(nfa.get_transition_target(origin.get(), symbol))
        assert expected_states['qf'].get() in transition_targets


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_ineq1(automaton_cls: NFA, ineq1: Relation):
    nfa = build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq1)

    assert len(nfa.states) == 3
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    initial_state = next(iter(nfa.initial_states))
    final_state = next(iter(nfa.final_states))

    state_0 = ResolutionState()
    state_m1 = ResolutionState()
    state_f = ResolutionState()

    state_0.bind(initial_state)
    state_f.bind(final_state)

    expected_transitions = [
        (state_0, (0, 0), state_0),
        (state_0, (0, 1), state_0),
        (state_0, (1, 1), state_0),
        (state_0, (1, 0), state_m1),

        (state_m1, (0, 0), state_m1),
        (state_m1, (1, 0), state_m1),
        (state_m1, (1, 1), state_m1),
        (state_m1, (0, 1), state_0),
    ]

    expected_accepting_symbols = [
        (state_0, [(0, 0), (1, 0), (1, 1)]),
        (state_m1, [(1, 0)])
    ]

    for origin, symbol, destination in expected_transitions:
        dest_states = set(nfa.get_transition_target(origin.get(), symbol)) - nfa.final_states
        destination.bind(next(iter(dest_states)))

    for state, final_symbols in expected_accepting_symbols:
        for symbol in final_symbols:
            dest_states = nfa.get_transition_target(state.get(), symbol)
            final_dest_states = set(dest_states).intersection(set(nfa.final_states))
            assert len(final_dest_states) == 1


            assert {state_f.get()} == final_dest_states


@pytest.mark.parametrize('automaton_cls', (NFA, MTBDD_NFA))
def test_ineq2(automaton_cls: NFA, ineq2: Relation):
    nfa = build_nfa_from_linear_inequality(automaton_cls, alphabet, ineq2)

    assert len(nfa.states) == 5
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    initial_state = next(iter(nfa.initial_states))

    states = dict((i, ResolutionState()) for i in [1, 0, -1, -2])

    states[1].bind(initial_state)

    expected_transitions = [
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

    for origin, symbol, destination in expected_transitions:
        _origin = states[origin].get()
        dest_states = set(nfa.get_transition_target(_origin, symbol))
        dest_nonfinal_states = dest_states - nfa.final_states

        assert len(dest_nonfinal_states) == 1
        _destination = states[destination]
        _destination.bind(next(iter(dest_nonfinal_states)))

    expected_accepting_symbols = [
        (1, [(0, 0), (0, 1), (1, 0), (1, 1)]),
        (0, [(0, 0), (0, 1), (1, 0), (1, 1)]),
        (-1, [(0, 1), (1, 0), (1, 1)]),
        (-2, [(1, 1)]),
    ]

    for state, accepting_symbols in expected_accepting_symbols:
        for accepting_symbol in accepting_symbols:
            dest_states = set(nfa.get_transition_target(state, accepting_symbol))
            dest_final_states = nfa.final_states.intersection(dest_states)
            assert len(dest_final_states) == 1

