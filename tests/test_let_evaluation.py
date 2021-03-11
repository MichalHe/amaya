import pytest
from typing import List
from parse import eval_smt_tree, EvaluationContext, SolutionDomain, VariableType
from log import logger
import logging
from automatons import AutomatonType
from transitions import iter_transition_fn

logger.setLevel(logging.DEBUG)


@pytest.fixture
def simple_term() -> List:
    return ['let', [['T', ['=', 'x', '0']]], 'T']


@pytest.fixture
def nested_let_term() -> List:
    term = [
        'let',
        [['B0', ['<=', 'x', '0']]],
        [
            'let',
            [['B1', ['=', 'x', '0']]],
            ['and', 'B0', 'B1']
        ]]
    return term


@pytest.fixture
def simple_let_term_with_ite() -> List:
    term = [
        'let',
        [
            ['T0', ['<=',
                    ['ite', 'b0', 'x', ['*', '2', 'x']],
                    1]]
        ],
        ['and', 'T0', ['<=', 'x', '2']]
    ]

    return term


def test_simple_let_term(simple_term: List):
    ctx = EvaluationContext(SolutionDomain.INTEGERS)
    nfa = eval_smt_tree(simple_term, ctx, {})
    assert nfa.is_sat()
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1
    assert len(nfa.states) == 2
    assert nfa.automaton_type == AutomatonType.NFA

    expected_transitions = [
        (0, (0, ), 'FINAL'),
        (0, (0, ), 0)
    ]
    assert len(list(iter_transition_fn(nfa.transition_fn.data))) == len(expected_transitions)


def test_nested_let_tree(nested_let_term: List):
    ctx = EvaluationContext(SolutionDomain.INTEGERS)
    nfa = eval_smt_tree(nested_let_term, ctx, {})

    # Basically intersection of two automatons
    assert len(nfa.states) == 4
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1

    assert len(list(iter_transition_fn(nfa.transition_fn.data))) == 4


def test_simple_let_term_with_ite(simple_let_term_with_ite: List):
    assert simple_let_term_with_ite
    ctx = EvaluationContext(SolutionDomain.INTEGERS)
    eval_smt_tree(simple_let_term_with_ite, ctx, variable_types={'b0': VariableType.Bool})
    # The intersection (AND) of a True boolean with a relation is tested in
    # different test
