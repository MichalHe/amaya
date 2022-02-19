from alphabet import LSBF_Alphabet
from automatons import DFA
from presburger_algorithms import build_dfa_from_linear_inequality
from relations_structures import Relation
from tests.conftest import ResolutionState

import pytest

@pytest.fixture()
def ineq() -> Relation:
    return Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[1, 1],
        modulo_terms=[],
        modulo_term_coeficients=[],
        absolute_part=2,
        operation='<='
    )


def test_dfa_from_sharp_indeq_simple(ineq: Relation):
    var_id_pairs = [(var, i + 1) for i, var in enumerate(ineq.variable_names)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(var_id_pairs)
    dfa = build_dfa_from_linear_inequality(ineq, var_id_pairs, alphabet, DFA)
    
    s2 = ResolutionState('2')
    s1 = ResolutionState('1')
    s0 = ResolutionState('0')
    sm1 = ResolutionState('-1')
    sm2 = ResolutionState('-2')

    expected_structure = [
        (s2, (0, 0), s1),
        (s2, (0, 1), s0),
        (s2, (1, 0), s0),
        (s2, (1, 1), s0),

        (s1, (0, 0), s0),
        (s1, (0, 1), s0),
        (s1, (1, 0), s0),
        (s1, (1, 1), sm1),

        (s0, (0, 0), s0),
        (s0, (0, 1), sm1),
        (s0, (1, 0), sm1),
        (s0, (1, 1), sm1),

        (sm1, (0, 0), sm1),
        (sm1, (0, 1), sm1),
        (sm1, (1, 0), sm1),
        (sm1, (1, 1), sm2),

        (sm2, (0, 0), sm1),
        (sm2, (0, 1), sm2),
        (sm2, (1, 0), sm2),
        (sm2, (1, 1), sm2),
    ]

    assert len(dfa.initial_states) == 1
    s2.bind(next(iter(dfa.initial_states)))

    for source, symbol, dest in expected_structure:
        post = dfa.get_transition_target(source.get(), symbol)
        assert len(post) == 1, 'The resulting automaton should be deterministic'
        dest.bind(next(iter(post)))

    assert len(dfa.final_states) == 3
    assert {s2.get(), s1.get(), s0.get()} == dfa.final_states
