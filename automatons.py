from __future__ import annotations
from typing import Set, Dict, Tuple
from dataclasses import dataclass

AutomatonState = int
AlphabetLetter = Tuple[int]
NFA_Transitions = Dict[AutomatonState, Dict[AlphabetLetter, Set[AutomatonState]]]
DFA_Transitions = Dict[AutomatonState, Dict[AlphabetLetter, AutomatonState]]


@dataclass
class DFA:
    alphabet: Tuple[AlphabetLetter]
    initial_state: AutomatonState
    final_states: Set[AutomatonState]
    states: Set[AutomatonState]
    transitions: DFA_Transitions


@dataclass
class NFA:
    alphabet: Tuple[AlphabetLetter]
    initial_state: AutomatonState
    final_states: Set[AutomatonState]
    states: Set[AutomatonState]
    transitions: NFA_Transitions


def NFAtoDFA(nfa: NFA) -> DFA:
    '''Performs NFA -> DFA using the powerset construction'''
    working_queue = [(nfa.initial_state,)]

    dfa_states = set()
    dfa_final_states = set()
    dfa_transitions: DFA_Transitions = {}

    while working_queue:
        unexplored_dfa_state = working_queue.pop(0)

        dfa_states.add(unexplored_dfa_state)

        intersect = set(unexplored_dfa_state).intersection(nfa.final_states)
        if intersect:
            dfa_final_states.add(unexplored_dfa_state)

        for letter in nfa.alphabet:
            reachable_states = list()
            for state in unexplored_dfa_state:
                if state not in nfa.transitions:
                    continue
                state_transitions = nfa.transitions[state]
                if letter in state_transitions:
                    reachable_states += state_transitions[letter]

            reachable_states = tuple(set(reachable_states))

            if reachable_states and reachable_states not in dfa_states:
                working_queue.append(reachable_states)

            if unexplored_dfa_state not in dfa_transitions:
                dfa_transitions[unexplored_dfa_state] = {}
            dfa_transitions[unexplored_dfa_state][letter] = reachable_states

    return DFA(
        initial_state=set([nfa.initial_state]),
        final_states=dfa_final_states,
        states=dfa_states,
        transitions=dfa_transitions,
        alphabet=nfa.alphabet
               )
