from __future__ import annotations
from typing import Set, Dict, Tuple, List, Union
from dataclasses import dataclass

AutomatonStateLabel = Union[int, str]
NFA_AutomatonState = Union[int, str]  # The automaton state can be also special non int value such as Qf='FINAL'
DFA_AutomatonState = Union[AutomatonStateLabel, Tuple[AutomatonStateLabel, ...]]
AlphabetLetter = Tuple[int, ...]

NFA_Transitions = Dict[
    NFA_AutomatonState,
    Dict[
        AlphabetLetter,
        Set[NFA_AutomatonState]
    ]]

DFA_Transitions = Dict[
    DFA_AutomatonState,
    Dict[
        AlphabetLetter,
        DFA_AutomatonState
    ]]


@dataclass
class DFA:
    alphabet: Tuple[AlphabetLetter, ...]
    initial_state: DFA_AutomatonState
    final_states: Tuple[DFA_AutomatonState, ...]
    states: Tuple[DFA_AutomatonState, ...]
    transitions: DFA_Transitions


@dataclass
class NFA:
    alphabet: Tuple[AlphabetLetter, ...]
    initial_states: Tuple[NFA_AutomatonState, ...]
    final_states: Set[NFA_AutomatonState]
    states: Set[NFA_AutomatonState]
    transitions: NFA_Transitions


def unite_transition_functions(alphabet: Tuple[AlphabetLetter, ...],
                               t1: Union[NFA_Transitions, DFA_Transitions],
                               t2: Union[NFA_Transitions, DFA_Transitions],
                               ) -> NFA_Transitions:
    # @TODO: Refactor types - namely a DFA should be also an NFA

    transitions: NFA_Transitions = {}
    for state in t1:
        transitions[state] = {}
        for transition_symbol in t1[state]:
            if type(t1) == NFA_Transitions:
                # Copy the tuple
                transitions[state][transition_symbol] = tuple(t1[state][transition_symbol])
            else:
                transitions[state][transition_symbol] = (t1[state][transition_symbol], )
        transitions

    for state in t2:
        if state not in transitions:
            transitions[state] = {}
        for transition_symbol in t2[state]:
            if type(t2) == NFA_Transitions:
                # Copy the tuple
                transitions[state][transition_symbol] += tuple(t2[state][transition_symbol])
            else:
                transitions[state][transition_symbol] += (t2[state][transition_symbol], )
    return transitions


def unite_states(a1_states: Tuple[NFA_AutomatonState, ...],
                 a2_states: Tuple[NFA_AutomatonState, ...],
                 ) -> Tuple[NFA_AutomatonState]:
    return tuple(set(a1_states + a2_states))


def NFAtoDFA(nfa: NFA) -> DFA:
    '''Performs NFA -> DFA using the powerset construction'''
    # @TODO: This is actually broken (in terms of types)
    working_queue: List[Tuple[AutomatonStateLabel, ...]] = [nfa.initial_states]

    dfa_states = set()
    dfa_final_states: Set[DFA_AutomatonState] = set()
    dfa_transitions: DFA_Transitions = {}

    while working_queue:
        unexplored_dfa_state = working_queue.pop(0)

        dfa_states.add(unexplored_dfa_state)

        intersect = set(unexplored_dfa_state).intersection(nfa.final_states)
        if intersect:
            dfa_final_states.add(unexplored_dfa_state)

        for letter in nfa.alphabet:
            reachable_states: List[NFA_AutomatonState] = list()
            for state in unexplored_dfa_state:
                if state not in nfa.transitions:
                    continue
                state_transitions = nfa.transitions[state]
                if letter in state_transitions:
                    reachable_states += state_transitions[letter]

            dfa_state = tuple(set(reachable_states))

            if dfa_state and dfa_state not in dfa_states:
                working_queue.append(dfa_state)

            if unexplored_dfa_state not in dfa_transitions:
                dfa_transitions[unexplored_dfa_state] = {}
            dfa_transitions[unexplored_dfa_state][letter] = dfa_state

    return DFA(
        initial_state=nfa.initial_states,
        final_states=tuple(dfa_final_states),
        states=tuple(dfa_states),
        transitions=dfa_transitions,
        alphabet=nfa.alphabet
               )


def automaton_union(a1: Union[DFA, NFA], a2: Union[DFA, NFA]) -> NFA:
    assert type(a1) == NFA and type(a2) == NFA
    states = set(a1.states).union(a2.states)
    transitions = unite_transition_functions(a1, a2)
    initial_states = unite_states(a1.initial_states, a2.initial_states)
    final_states = unite_states(a1.final_states, a2.final_states)

    return NFA(
        a1.alphabet,
        initial_states,
        final_states,
        states,
        transitions
    )
