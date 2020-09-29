from __future__ import annotations
from enum import Enum
from typing import (
    Set,
    Dict,
    Tuple,
    List,
    TypeVar,
    Generic,
    Optional
)

from inequations import Inequality
from utils import number_to_bit_tuple

from dataclasses import (
    dataclass,
    field
)

AutomatonState = TypeVar('AutomatonState')
LSBF_AlphabetSymbol = Tuple[int, ...]


class TransitionFn_(Generic[AutomatonState]):
    data: Dict[AutomatonState,
               Dict[
                  LSBF_AlphabetSymbol,
                  Tuple[AutomatonState, ...]
               ]]

    def __init__(self):
        self.data = {}

    def __getitem__(self, item: AutomatonState) -> Dict[LSBF_AlphabetSymbol, Tuple[AutomatonState, ...]]:
        return self.data[item]

    def __setitem__(self, item: AutomatonState, val: Dict[LSBF_AlphabetSymbol, Tuple[AutomatonState, ...]]):
        self.data[item] = val

    def __iter__(self):
        return self.data


TransitionFn = Dict[AutomatonState,
                    Dict[
                        LSBF_AlphabetSymbol,
                        Tuple[AutomatonState, ...]
                    ]]


AutomatonType = Enum('AutomatonType', 'DFA NFA')


@dataclass
class LSBF_Alphabet():
    symbols: Tuple[LSBF_AlphabetSymbol, ...]
    variable_names: Tuple[str, ...]

    @staticmethod
    def from_inequation(ineq: Inequality) -> LSBF_Alphabet:
        letter_size = len(ineq.variable_names)
        symbols = tuple(map(
            lambda i: number_to_bit_tuple(i, tuple_size=letter_size, pad=0),
            range(2**letter_size)
        ))

        return LSBF_Alphabet(
            symbols=symbols,
            variable_names=tuple(ineq.variable_names)
        )


@dataclass
class NFA(Generic[AutomatonState]):
    alphabet:       LSBF_Alphabet
    automaton_type: AutomatonType = AutomatonType.NFA
    initial_states: Set[AutomatonState] = field(default_factory=set)
    final_states:   Set[AutomatonState] = field(default_factory=set)
    states:         Set[AutomatonState] = field(default_factory=set)
    transition_fn:  TransitionFn[AutomatonState] = field(default_factory=dict)

    def union(self,
              other: NFA[AutomatonState]
              ) -> NFA[AutomatonState]:
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
    def __unite_transition_functions(f1: TransitionFn[AutomatonState],
                                     f2: TransitionFn[AutomatonState]):

        transitions = TransitionFn[AutomatonState]()
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
        working_queue: List[Tuple[AutomatonState, ...]] = [tuple(self.initial_states)]

        DFA_AutomatonState = Tuple[AutomatonState, ...]  # Alias type
        dfa_states: Set[DFA_AutomatonState] = set()
        dfa_final_states: Set[DFA_AutomatonState] = set()
        dfa_transitions: TransitionFn[DFA_AutomatonState, LSBF_AlphabetSymbol] = {}

        while working_queue:
            unexplored_dfa_state: DFA_AutomatonState = working_queue.pop(0)

            dfa_states.add(unexplored_dfa_state)

            intersect = set(unexplored_dfa_state).intersection(self.final_states)
            if intersect:
                dfa_final_states.add(unexplored_dfa_state)

            for symbol in self.alphabet.symbols:
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

        return DFA[DFA_AutomatonState](
            initial_states=tuple(self.initial_states),
            final_states=dfa_final_states,
            states=dfa_states,
            transition_fn=dfa_transitions,
            alphabet=self.alphabet
                )

    def update_transition_fn(self,
                             from_state: AutomatonState,
                             via_symbol: LSBF_AlphabetSymbol,
                             to_state: AutomatonState
                             ):
        if from_state not in self.transition_fn:
            self.transition_fn[from_state] = {}

        if via_symbol not in self.transition_fn[from_state]:
            self.transition_fn[from_state][via_symbol] = (to_state, )
        else:
            if to_state not in self.transition_fn[from_state][via_symbol]:
                self.transition_fn[from_state][via_symbol] += (to_state, )

    def add_state(self, state: AutomatonState):
        self.states.add(state)

    def add_final_state(self, state: AutomatonState):
        self.final_states.add(state)

    def __var_bit_position_in_alphabet_symbol(self, variable_name) -> Optional[int]:
        for pos, alphabet_var_name in enumerate(self.alphabet.variable_names):
            if alphabet_var_name == variable_name:
                return pos
        return None

    def __create_projection_symbol_map(self, variable_name) -> Dict[LSBF_AlphabetSymbol, LSBF_AlphabetSymbol]:
        projection_map: Dict[LSBF_AlphabetSymbol, LSBF_AlphabetSymbol] = {}
        variable_position = self.__var_bit_position_in_alphabet_symbol(variable_name)
        if not variable_position:
            raise ValueError(f'Given variable name is not in alphabet: {variable_name}, available names: {self.alphabet.variable_names}')

        for symbol in self.alphabet.symbols:
            if variable_position == 0:
                new_symbol = symbol[1:]
            elif variable_position == len(symbol) - 1:
                new_symbol = symbol[:-1]
            else:
                new_symbol = symbol[0:variable_position] + symbol[variable_position + 1:]

            projection_map[symbol] = new_symbol

        return projection_map

    def do_projection(self, variable_name: str):
        work_queue = list(self.states)
        projection_map = self.__create_projection_symbol_map(variable_name)
        while work_queue:
            current_state = work_queue.pop(0)
            out_transitions = self.transition_fn[current_state]  # Outwards transitions
            for alphabet_symbol in out_transitions:
                # Remap alphabet_symbol to its projected counterpart
                out_states = out_transitions[alphabet_symbol]
                new_symbol = projection_map[alphabet_symbol]
                out_transitions[new_symbol] = out_states

                # Delete old mapping
                out_transitions.pop(alphabet_symbol)


DFA = NFA
