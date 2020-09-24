from __future__ import annotations
from typing import (
    Set,
    Dict,
    Tuple,
    List,
    TypeVar,
    Generic
)
from dataclasses import dataclass

AutomatonState = TypeVar('AutomatonState')
AlphabetSymbol = TypeVar('AlphabetSymbol')


class TransitionFn(Generic[AutomatonState, AlphabetSymbol]):
    data: Dict[AutomatonState,
               Dict[
                  AlphabetSymbol,
                  Tuple[AutomatonState, ...]
               ]]

    def __init__(self):
        self.data = {}

    def __getitem__(self, item: AutomatonState) -> Dict[AlphabetSymbol, Tuple[AutomatonState, ...]]:
        return self.data[item]

    def __setitem__(self, item: AutomatonState, val: Dict[AlphabetSymbol, Tuple[AutomatonState, ...]]):
        self.data[item] = val

    def __iter__(self):
        return self.data


@dataclass
class NFA(Generic[AutomatonState, AlphabetSymbol]):
    alphabet:       Tuple[AlphabetSymbol, ...]
    initial_states: Set[AutomatonState]
    final_states:   Set[AutomatonState]
    states:         Set[AutomatonState]
    transition_fn:  TransitionFn[AutomatonState, AlphabetSymbol]

    def union(self,
              other: NFA[AutomatonState, AlphabetSymbol]
              ) -> NFA[AutomatonState, AlphabetSymbol]:
        if self.alphabet != other.alphabet:
            raise NotImplementedError('Union of automatons with different alphabets is not implemented')

        states = set(self.states).union(other.states)
        transitions = NFA.__unite_transition_functions(self.transition_fn, other.transition_fn)
        initial_states = self.__unite_states(self.initial_states, other.initial_states)
        final_states = self.__unite_states(self.final_states, other.final_states)

        return NFA(
            self.alphabet,
            initial_states,
            final_states,
            states,
            transitions
        )

    @staticmethod
    def __unite_transition_functions(f1: TransitionFn[AutomatonState, AlphabetSymbol],
                                     f2: TransitionFn[AutomatonState, AlphabetSymbol]):

        transitions = TransitionFn[AutomatonState, AlphabetSymbol]()
        for state in f1:
            transitions[state] = {}
            for transition_symbol in f1[state]:
                # Copy the tuple
                transitions[state][transition_symbol] = tuple(f1[state][transition_symbol])
        for state in f2:
            if state not in transitions:
                transitions[state] = {}
            for transition_symbol in f2[state]:
                transitions[state][transition_symbol] += tuple(f2[state][transition_symbol])
        return transitions

    @staticmethod
    def __unite_states(s1: Set[AutomatonState], s2: Set[AutomatonState]):
        return s1.union(s2)

    def determinize(self):
        '''Performs NFA -> DFA using the powerset construction'''
        working_queue: List[Tuple[AutomatonState, ...]] = [self.initial_states]

        DFA_AutomatonState = Tuple[AutomatonState, ...]  # Alias type
        dfa_states: Set[DFA_AutomatonState] = set()
        dfa_final_states: Set[DFA_AutomatonState] = set()
        dfa_transitions: TransitionFn[DFA_AutomatonState, AlphabetSymbol] = {}

        while working_queue:
            unexplored_dfa_state: DFA_AutomatonState = working_queue.pop(0)

            dfa_states.add(unexplored_dfa_state)

            intersect = set(unexplored_dfa_state).intersection(self.final_states)
            if intersect:
                dfa_final_states.add(unexplored_dfa_state)

            for symbol in self.alphabet:
                reachable_states: List[AutomatonState] = list()
                for state in unexplored_dfa_state:
                    if state not in self.transition_fn:
                        continue

                    state_transitions = self.transition_fn[state]
                    if symbol in state_transitions:
                        reachable_states += list(state_transitions[symbol])  # transitions are a tuple

                dfa_state: DFA_AutomatonState = tuple(set(reachable_states))

                if dfa_state and dfa_state not in dfa_states:
                    working_queue.append(dfa_state)

                if unexplored_dfa_state not in dfa_transitions:
                    dfa_transitions[unexplored_dfa_state] = {}
                dfa_transitions[unexplored_dfa_state][symbol] = dfa_state

        return DFA[DFA_AutomatonState, AlphabetSymbol](
            initial_state=self.initial_states,
            final_states=dfa_final_states,
            states=dfa_states,
            transitions=dfa_transitions,
            alphabet=self.alphabet
                )


class DFA(NFA):
    def __init__(self, initial_state, *args, **kwargs):
        # @TODO: Check whether this works
        super(
            initial_states=(initial_state, ),
            *args,
            **kwargs,
        )
