from collections import defaultdict
from typing import Dict, Set

from alphabet import LSBF_Alphabet
from automatons import DFA
from tests.conftest import ResolutionState
from presburger.constructions.naturals import build_dfa_from_linear_equality
from relations_structures import Relation

import pytest


@pytest.fixture()
def equation() -> Relation:
    return Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[1, 1],
        modulo_term_coeficients=[],
        modulo_terms=[],
        absolute_part=4,
        operation='='
    )


def test_eq_to_dfa_simple(equation: Relation):
    """
    Asserts that the automaton construction EqToDFA gives expected results for a simple equation.
    """
    
    var_id_pairs = [(var, i+1) for i, var in enumerate(equation.variable_names)]
    alphabet = LSBF_Alphabet.from_variable_id_pairs(var_id_pairs)
    alphabet_symbols = set(alphabet.symbols)
    dfa = build_dfa_from_linear_equality(equation, var_id_pairs, alphabet, DFA)
    
    s4 = ResolutionState('4')
    s2 = ResolutionState('2')
    s1 = ResolutionState('1')
    s0 = ResolutionState('0')
    sm1 = ResolutionState('-1')
    s_trap = ResolutionState('trap')

    expected_transitions = [
        (s4, (0, 0), s2),
        (s4, (1, 1), s1),
        (s2, (0, 0), s1),
        (s2, (1, 1), s0),
        (s0, (0, 0), s0),
        (s0, (1, 1), sm1),
        (sm1, (0, 1), sm1),
        (sm1, (1, 0), sm1),
    ]
    
    assert len(dfa.initial_states) == 1
    s4.bind(next(iter(dfa.initial_states)))

    # Collect all symbols for which there is no meaningful transition - assert that they lead to trap state.
    out_symbols_per_state: Dict[str, Set[Tuple[int, ...]]] = defaultdict(set)

    for source, symbol, dest in expected_transitions:
        out_symbols_per_state[source].add(symbol)
        
        post = dfa.get_transition_target(source.get(), symbol)
        assert len(post) == 1, 'The created automaton should be deterministic.'
        dest.bind(next(iter(post)))

    for state, symbols in out_symbols_per_state.items():
        for missing_symbol in alphabet_symbols.difference(symbols):
            post = dfa.get_transition_target(state.get(), missing_symbol)
            assert len(post) == 1
            print(f'{state=}')
            dest = next(iter(post))
            s_trap.bind(dest)

    assert len(dfa.final_states) == 1
    assert s0.get() in dfa.final_states

    assert len(dfa.states) == 6  # 5 normal plus trap
