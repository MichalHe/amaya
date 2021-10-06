import pytest
from parse import (
    run_evaluation_procedure,
    EvaluationContext,
    EvaluationConfig,
    BackendType,
    SolutionDomain,
    VariableType,
)
from automatons import (
    NFA,
    LSBF_Alphabet
)


@pytest.fixture
def conj_bool_relation_term():
    term = [
        'and',
        'b0',
        ['<=', ['*', '2', 'x'], 1]
    ]

    return term


@pytest.mark.parametrize(('backend_type',), [(BackendType.NAIVE,), (BackendType.MTBDD,)])
def test_conj_bool_with_relation(conj_bool_relation_term, backend_type):
    eval_cfg = EvaluationConfig(
        solution_domain=SolutionDomain.INTEGERS,
        backend_type=backend_type
    )

    alphabet = LSBF_Alphabet.from_variable_ids([1, 2])
    ctx = EvaluationContext(eval_cfg, alphabet=alphabet)
    ctx.add_global_variable('b0', VariableType.BOOL)
    ctx.add_global_variable('x', VariableType.INT)

    nfa = run_evaluation_procedure(
        conj_bool_relation_term,
        ctx)

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
    alphabet = LSBF_Alphabet.from_variable_ids([1])
    nfa_0 = NFA.for_bool_variable(alphabet, var_id=1, var_value=True)
    nfa = nfa_0.determinize().complement()

    assert len(nfa.initial_states) == 1
    assert len(nfa.final_states) == 1
    assert len(nfa.states) == 3

    # The bool automaton should have three states after determinization:
    # initial, final and TRAP
    init_state = list(nfa.initial_states)[0]
    final_state = list(nfa.final_states)[0]  # TRAP is final, since it is a complement automaton

    assert final_state in nfa.get_transition_target(init_state, (0, ))
    assert len(nfa.get_transition_target(init_state, (0, ))) == 1

    assert final_state not in nfa.get_transition_target(init_state, (1, ))
    assert len(nfa.get_transition_target(init_state, (1, ))) == 1

    assert len(nfa.get_transition_target(final_state, ('*', ))) == 1

    nonfinal_state_set = nfa.states - nfa.initial_states - nfa.final_states
    nonfinal_state = list(nonfinal_state_set)[0]
    assert nonfinal_state

    print(nfa.get_visualization_representation())

    assert len(set(nfa.get_transition_target(final_state, ('*', )))) == 1

    # The previous accepting state should have one selfloop the true/false
    # symbol and one leading to the trap state
    assert len(set(nfa.get_transition_target(nonfinal_state, ('*', )))) == 2
