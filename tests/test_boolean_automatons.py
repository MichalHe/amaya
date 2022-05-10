from amaya.alphabet import LSBF_Alphabet
from amaya.automatons import NFA
from amaya.config import BackendType
from amaya.mtbdd_automatons import MTBDD_NFA

import pytest


alphabet = LSBF_Alphabet.from_variable_id_pairs([('x', 1)])


@pytest.mark.parametrize(('automaton_cls',), [(NFA,), (MTBDD_NFA,)])
def test_x_and_not_x(automaton_cls: NFA):
    x_nfa = automaton_cls.for_bool_variable(overall_alphabet=alphabet, var_id=1, var_value=True)
    not_x_nfa = automaton_cls.for_bool_variable(overall_alphabet=alphabet, var_id=1, var_value=True).complement()
    
    result = x_nfa.intersection(not_x_nfa)

    assert len(result.final_states) == 0  # The language of the resulting automaton should be empty


@pytest.mark.parametrize(('automaton_cls',), [(NFA,), (MTBDD_NFA,)])
def test_x_or_not_x(automaton_cls: NFA):
    x_nfa = automaton_cls.for_bool_variable(overall_alphabet=alphabet, var_id=1, var_value=True)
    not_x_nfa = automaton_cls.for_bool_variable(overall_alphabet=alphabet, var_id=1, var_value=True).determinize().complement()

    result: NFA = x_nfa.union(not_x_nfa).determinize().complement()
    assert not result.final_states


@pytest.mark.parametrize(('automaton_cls',), [(NFA,), (MTBDD_NFA,)])
def test_not_x(automaton_cls: NFA):
    nfa: NFA = automaton_cls.for_bool_variable(alphabet, var_id=1, var_value=False)

    assert len(nfa.states) == 2  # States (except intiial) have universal/empty language - the empty might be removed
    assert len(nfa.final_states) == 1
    assert len(nfa.initial_states) == 1

    init_state = next(iter(nfa.initial_states))
    final_state = next(iter(nfa.final_states))
    dest = nfa.get_transition_target(init_state, (0, )) 
    assert final_state in dest
