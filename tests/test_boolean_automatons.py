import pytest
from parse import eval_smt_tree, EvaluationContext, SolutionDomain, VariableType
from automatons import NFA


@pytest.fixture
def conj_bool_relation_term():
    term = [
        'and',
        'b0',
        ['<=', ['*', '2', 'x'], 1]
    ]

    return term


def test_conj_bool_with_relation(conj_bool_relation_term):
    ctx = EvaluationContext(SolutionDomain.INTEGERS)
    nfa = eval_smt_tree(conj_bool_relation_term, ctx, variable_types={'b0': VariableType.Bool})

    assert nfa
    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1
    assert len(nfa.states) == 5

    init_state = list(nfa.initial_states)[0]
    final_state = list(nfa.final_states)[0]

    assert len(nfa.get_transition_target(init_state, (1, 0))) == 2
    assert final_state in nfa.get_transition_target(init_state, (1, 0))

    assert len(nfa.get_transition_target(init_state, (1, 1))) == 2
    assert final_state in nfa.get_transition_target(init_state, (1, 1))

    q1 = list(set(nfa.get_transition_target(init_state, (1, 1))) - nfa.final_states)[0]

    assert len(nfa.get_transition_target(q1, (1, 1))) == 2
    assert len(nfa.get_transition_target(q1, (0, 1))) == 2
    assert final_state in nfa.get_transition_target(q1, (1, 1))
    assert final_state in nfa.get_transition_target(q1, (0, 1))

    q2 = list(set(nfa.get_transition_target(q1, (1, 1))) - nfa.final_states)[0]
    assert len(nfa.get_transition_target(q2, (1, 1))) == 2

    assert q2 in nfa.get_transition_target(q2, (1, 1))
    assert final_state in nfa.get_transition_target(q2, (1, 1))


def test_bool_automaton_complement():
    nfa_0 = NFA.for_bool_variable('b0', True)
    nfa = nfa_0.determinize().complement()

    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1
    assert len(nfa.states) == 3

    init_state = list(nfa.initial_states)[0]
    final_state = list(nfa.final_states)[0]

    assert final_state in nfa.get_transition_target(init_state, (0, ))
    assert len(nfa.get_transition_target(init_state, (0, ))) == 1

    assert final_state not in nfa.get_transition_target(init_state, (1, ))
    assert len(nfa.get_transition_target(init_state, (1, ))) == 1

    assert len(nfa.get_transition_target(final_state, ('*', ))) == 1

    nonfinal_state_set = nfa.states - nfa.initial_states - nfa.final_states
    nonfinal_state = list(nonfinal_state_set)[0]
    assert nonfinal_state

    assert len(set(nfa.get_transition_target(final_state, ('*', )))) == 1
    assert len(set(nfa.get_transition_target(nonfinal_state, ('*', )))) == 1
