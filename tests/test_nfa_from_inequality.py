from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.relations_structures import Relation
from amaya.presburger.constructions.integers import build_nfa_from_linear_inequality
from tests.conftest import ResolutionState

import pytest


@pytest.fixture
def ineq() -> Relation:
    return Relation.new_lin_relation(variable_names=['x', 'y'], variable_coeficients=[2, -1],
                                     operation='<=', absolute_part=2)


def test_nfa_buildup_simple(ineq: Relation):
    alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1), ('y', 2)])
    nfa = build_nfa_from_linear_inequality(ineq, [('x', 1), ('y', 2)], alphabet, NFA)
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
