from __future__ import annotations
from enum import Enum
from typing import (
    Set,
    Dict,
    Tuple,
    List,
    TypeVar,
    Generic,
    Optional,
    Callable,
)

from utils import (
    number_to_bit_tuple,
    carthesian_product,
)

from dataclasses import (
    dataclass,
    field
)

from inequations_data import (
    Inequality
)

AutomatonState = TypeVar('AutomatonState')
S = TypeVar('S')

LSBF_AlphabetSymbol = Tuple[int, ...]

TransitionFn = Dict[AutomatonState,
                    Dict[
                        LSBF_AlphabetSymbol,
                        Set[AutomatonState]
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

    # Debug handle to listen to any state renaming happening during
    # intersecion/union; takes (automaton_id, old_state(int, str),
    # new_state(int))
    _debug_state_rename: Optional[Callable[[int, AutomatonState, int], None]] = None

    @staticmethod
    def __unite_transition_functions(f1: TransitionFn[AutomatonState], f2: TransitionFn[AutomatonState]):

        # States are unique
        transitions: TransitionFn[AutomatonState] = dict()
        for state in f1:
            transitions[state] = {}
            for transition_symbol in f1[state]:
                # Copy the tuple
                transitions[state][transition_symbol] = set(f1[state][transition_symbol])
        for state in f2:
            if state not in transitions:
                transitions[state] = {}
            for transition_symbol in f2[state]:
                transitions[state][transition_symbol] = set(f2[state][transition_symbol])
        return transitions

    def update_transition_fn(self,
                             from_state: AutomatonState,
                             via_symbol: LSBF_AlphabetSymbol,
                             to_state: AutomatonState
                             ):

        if from_state not in self.transition_fn:
            self.transition_fn[from_state] = {}

        if via_symbol not in self.transition_fn[from_state]:
            self.transition_fn[from_state][via_symbol] = set((to_state, ))
        else:
            self.transition_fn[from_state][via_symbol].add(to_state)

    def add_state(self, state: AutomatonState):
        self.states.add(state)

    def add_final_state(self, state: AutomatonState):
        self.final_states.add(state)

    def add_initial_state(self, state: AutomatonState):
        self.initial_states.add(state)

    def has_state_with_value(self, state: AutomatonState) -> bool:
        return state in self.states

    def has_final_state_with_value(self, value: AutomatonState) -> bool:
        return value in self.final_states

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

    def get_transition_target(self,
                              origin: AutomatonState,
                              via_symbol: LSBF_AlphabetSymbol
                              ) -> Optional[Tuple[AutomatonState, ...]]:

        if origin not in self.transition_fn:
            return None
        if via_symbol not in self.transition_fn[origin]:
            return None

        return tuple(self.transition_fn[origin][via_symbol])

    def intersection(self, other: NFA[S]):
        resulting_nfa: NFA[Tuple[AutomatonState, S]] = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA
        )

        # @TODO: First perform state renaming, and then execute the
        # intersection on other automatons

        # @Maybe: Pull the implementations of ops into functions that take NFA
        # and return NFA without performing all kinds of renaming under the
        # hood

        # Add all the initial states to the to-be-processed queue
        work_queue = carthesian_product(self.initial_states, other.initial_states)
        for initial_state in work_queue:
            resulting_nfa.add_initial_state(initial_state)

        while work_queue:
            current_state: Tuple[AutomatonState, S] = work_queue.pop(0)
            resulting_nfa.add_state(current_state)

            # States in work_queue are boxed
            self_state, others_state = current_state

            # Check whether intersecti n state should be made final
            if (self_state in self.final_states and others_state in other.final_states):
                resulting_nfa.add_final_state((self_state, others_state))

            for symbol in self.alphabet.symbols:
                self_targets = self.get_transition_target(self_state, symbol)
                other_targets = other.get_transition_target(others_state, symbol)

                if self_targets is None or other_targets is None:
                    continue

                for new_intersect_state in carthesian_product(self_targets, other_targets):
                    if new_intersect_state not in resulting_nfa.states:
                        if new_intersect_state not in work_queue:
                            work_queue.append(new_intersect_state)

                    resulting_nfa.update_transition_fn(current_state, symbol, new_intersect_state)

        return resulting_nfa

    def union(self, other: NFA[S]) -> NFA[int]:
        if self.alphabet != other.alphabet:
            raise NotImplementedError('Union of automatons with different alphabets is not implemented')

        latest_state_value, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=latest_state_value)

        states = self_renamed.states.union(other_renamed.states)
        transitions = NFA.__unite_transition_functions(self_renamed.transition_fn, other_renamed.transition_fn)
        initial_states = self_renamed.initial_states.union(other_renamed.initial_states)
        final_states = self_renamed.final_states.union(other_renamed.final_states)

        return NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA,
            initial_states=initial_states,
            final_states=final_states,
            states=states,
            transition_fn=transitions
        )

    def determinize(self):
        '''Performs NFA -> DFA using the powerset construction'''
        working_queue: List[Tuple[AutomatonState, ...]] = [tuple(self.initial_states)]
        _final_states_raw = self.final_states

        DFA_AutomatonState = Tuple[AutomatonState, ...]  # Alias type
        determinized_automaton: DFA[DFA_AutomatonState] = DFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.DFA)
        determinized_automaton.add_initial_state(working_queue[0])

        while working_queue:
            unexplored_dfa_state: DFA_AutomatonState = working_queue.pop(0)

            determinized_automaton.add_state(unexplored_dfa_state)

            intersect = set(unexplored_dfa_state).intersection(_final_states_raw)
            if intersect:
                determinized_automaton.add_final_state(unexplored_dfa_state)

            for symbol in self.alphabet.symbols:
                reachable_states: List[AutomatonState] = list()
                for state in unexplored_dfa_state:
                    # Get all states reacheble from current state via symbol
                    out_states = self.get_transition_target(state, symbol)
                    if out_states:
                        reachable_states += list(out_states)

                dfa_state: DFA_AutomatonState = tuple(set(reachable_states))

                if dfa_state and not determinized_automaton.has_state_with_value(dfa_state):
                    if dfa_state not in working_queue:
                        working_queue.append(dfa_state)

                determinized_automaton.update_transition_fn(unexplored_dfa_state, symbol, dfa_state)

        return determinized_automaton

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

    def rename_states(self, start_from: int = 0) -> Tuple[int, NFA[int]]:
        # import pdb
        # pdb.set_trace()
        state_cnt = start_from
        nfa: NFA[int] = NFA(alphabet=self.alphabet, automaton_type=self.automaton_type)
        self_id = id(self)

        state_name_translation: Dict[AutomatonState, int] = dict()

        for state in self.states:
            new_state_name = state_cnt
            if (self._debug_state_rename is not None):
                self._debug_state_rename(self_id, state, new_state_name)

            state_name_translation[state] = new_state_name
            state_cnt += 1

            nfa.add_state(new_state_name)

        def translate(old_state_name: AutomatonState) -> int:
            return state_name_translation[old_state_name]

        for initial_state in self.initial_states:
            nfa.add_initial_state(translate(initial_state))

        for final_state in self.final_states:
            nfa.add_final_state(translate(final_state))

        # Perform translation of transition function
        for origin in self.transition_fn:
            state_exits = self.transition_fn[origin]
            renamed_origin = translate(origin)
            for symbol, destinations in state_exits.items():
                if renamed_origin not in nfa.transition_fn:
                    nfa.transition_fn[renamed_origin] = dict()
                nfa.transition_fn[renamed_origin][symbol] = set(map(translate, destinations))

        return (state_cnt, nfa)


DFA = NFA
