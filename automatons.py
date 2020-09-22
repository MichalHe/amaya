from __future__ import annotations
from typing import Set, Dict, Tuple, List, Union
from dataclasses import dataclass

NFA_AutomatonState = int
DFA_AutomatonState = Union[int, Tuple[int, ...]]
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
    alphabet: Tuple[AlphabetLetter]
    initial_states: Tuple[NFA_AutomatonState]
    final_states: Set[NFA_AutomatonState]
    states: Set[NFA_AutomatonState]
    transitions: NFA_Transitions


def NFAtoDFA(nfa: NFA) -> DFA:
    '''Performs NFA -> DFA using the powerset construction'''
    # @TODO: This is actually broken (in terms of types)
    working_queue: List[Tuple[int, ...]] = [nfa.initial_states]

    dfa_states = set()
    dfa_final_states: Set[Tuple[int, ...]] = set()
    dfa_transitions: DFA_Transitions = {}

    while working_queue:
        unexplored_dfa_state = working_queue.pop(0)

        dfa_states.add(unexplored_dfa_state)

        intersect = set(unexplored_dfa_state).intersection(nfa.final_states)
        if intersect:
            dfa_final_states.add(unexplored_dfa_state)

        for letter in nfa.alphabet:
            reachable_states: List[int] = list()
            for state in unexplored_dfa_state:
                if state not in nfa.transitions:
                    continue
                state_transitions = nfa.transitions[state]
                if letter in state_transitions:
                    reachable_states += state_transitions[letter]

            dfa_state: Tuple[int, ...] = tuple(set(reachable_states))

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
