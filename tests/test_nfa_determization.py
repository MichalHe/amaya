import pytest
from relations_structures import Relation
from presburger_algorithms import build_nfa_from_linear_inequality
from presburger_algorithms import AutomatonConstructor
from typing import Union, Dict
from automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from mtbdd_automatons import MTBDD_NFA

alphabet = LSBF_Alphabet.from_variable_names([1, 2])


def mk_simple_presburger(constr: AutomatonConstructor) -> NFA:
    ineq = Relation(
        variable_names=['x', 'y'],
        variable_coeficients=[2, -1],
        absolute_part=2,
        operation='<='
    )

    return build_nfa_from_linear_inequality(ineq, alphabet, constr)


@pytest.fixture
def simple_nfa() -> NFA:
    return mk_simple_presburger(NFA)


@pytest.fixture
def simple_mtbdd_nfa() -> NFA:
    return mk_simple_presburger(MTBDD_NFA)


def translate_transitions(transitions, translate):  # translate is function
    translated = []
    for transition in transitions:
        source, symbol, dest = transition
        source_translated = tuple(sorted(map(translate, source)))
        dest_translated = tuple(sorted(map(translate, dest)))

        translated.append((source_translated, symbol, dest_translated))
    return translated


class ResolutionState:
    def __init__(self):
        self.automaton_state = None

    def bind(self, real_automaton_state):
        if self.automaton_state is not None:
            if self.automaton_state != real_automaton_state:
                raise ValueError('Attempting to rebind automaton state value! Current: {0} New {1}'.format(
                    self.automaton_state, real_automaton_state
                ))
        else:
            self.automaton_state = real_automaton_state

    def is_bound(self):
        return self.automaton_state is not None

    def get(self):
        if self.automaton_state is None:
            raise ValueError('Attempting to read from resolvent state without assigning the value first.')
        return self.automaton_state


def do_simple_nfa_determinization_tests(simple_nfa: NFA[Union[int, str]]):
    assert simple_nfa.automaton_type == AutomatonType.NFA
    assert len(simple_nfa.final_states) == 1, \
        'The simple NFA resulting from the presburger formula should contain 1 final state.'

    trans_map: Dict[Union[int, str], int] = {}

    def state_rename_occured(automaton_id: int, old_name: Union[int, str], new_name: int):
        trans_map[old_name] = new_name

    simple_nfa._debug_state_rename = state_rename_occured

    dfa = simple_nfa.determinize()
    assert dfa
    assert len(dfa.states) == 8
    assert len(dfa.final_states) == 4
    assert len(dfa.initial_states) == 1
    assert dfa.automaton_type == AutomatonType.DFA

    # We must perform the testing in a state-name agnostic fashion
    initial_state = ResolutionState()
    state_1 = ResolutionState()
    state_2 = ResolutionState()
    state_3 = ResolutionState()
    state_4 = ResolutionState()
    state_5 = ResolutionState()
    state_6 = ResolutionState()
    state_7 = ResolutionState()

    assert len(dfa.initial_states) == 1, 'The deterministic automaton can have only one initial state.'
    initial_state.bind(next(iter(dfa.initial_states)))

    # Test whether there are transitions present
    e_transitions = [
        (initial_state, (0, 0), state_1),
        (initial_state, (0, 1), state_1),
        (state_1, (0, 0), state_2),
        (state_1, (1, 1), state_2),
        (state_1, (0, 0), state_2),
        (state_1, (0, 0), state_3),
        (state_3, (0, 0), state_6),
        (state_3, (1, 0), state_4),
        (state_6, (0, 1), state_5),
        (state_4, (1, 1), state_7),
        (state_7, (1, 1), state_7),
    ]

    for origin, symbol, dest in e_transitions:
        dest_set = dfa.get_transition_target(origin.get(), symbol)
        assert len(dest_set) == 1, 'A DFA can have only 1 destination state for every alphabet symbol.'
        dest.bind(dest_set[0])

    for s in [state_1, state_2, state_3, state_4, state_5, state_6, state_7]:
        assert s.is_bound()

    assert len(dfa.final_states) == 4


def test_simple_nfa_determinization(simple_nfa: NFA):
    do_simple_nfa_determinization_tests(simple_nfa)


def test_simple_mtbdd_nfa_determinization(simple_mtbdd_nfa: NFA):
    do_simple_nfa_determinization_tests(simple_mtbdd_nfa)
