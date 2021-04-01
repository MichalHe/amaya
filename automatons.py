from __future__ import annotations
from enum import IntFlag
from log import logger
from typing import (
    Set,
    Dict,
    Tuple,
    List,
    TypeVar,
    Generic,
    Optional,
    Callable,
    Union, Any
)

from utils import (
    number_to_bit_tuple,
    carthesian_product,
    create_enumeration_state_translation_map,
    get_default_if_none,
)

from dataclasses import (
    dataclass,
    field
)

import automaton_algorithms

from relations_structures import Relation

from transitions import (
    calculate_variable_bit_position,
    unite_alphabets,
    iterate_over_active_variables,
    construct_transition_fn_to_bddtfn,
    SparseSimpleTransitionFunction
)

import functools
import dd  # type: ignore


AutomatonState = TypeVar('AutomatonState')
S = TypeVar('S')

LSBF_AlphabetSymbol = Tuple[Union[int, str], ...]

TransitionFn = Dict[AutomatonState,
                    Dict[
                        LSBF_AlphabetSymbol,
                        Set[AutomatonState]
                    ]]


class AutomatonType(IntFlag):
    DFA = 0x01
    NFA = 0x02
    TRIVIAL = 0x04
    BOOL = 0x08


@dataclass
class LSBF_Alphabet():
    symbols: Tuple[LSBF_AlphabetSymbol, ...]
    variable_names: Tuple[str, ...]
    active_variables: Set[str]
    active_symbols: Optional[Tuple[LSBF_AlphabetSymbol, ...]] = None

    @staticmethod
    def from_inequation(ineq: Relation) -> LSBF_Alphabet:
        '''Generates a compressed alphabet from given relation.'''
        act_symbols, symbols = LSBF_Alphabet.generate_compressed_symbols(ineq.variable_coeficients)
        for symbol in symbols:
            print(symbol)

        active_variables = [var for i, var in enumerate(ineq.variable_names) if ineq.variable_coeficients[i] != 0]
        return LSBF_Alphabet(tuple(symbols), sorted(ineq.variable_names), set(active_variables), active_symbols=act_symbols)

    @staticmethod
    def generate_compressed_symbols(coefs):
        nonzero_coefs_pos = [i for i, coef in enumerate(coefs) if coef != 0]
        nonzero_coefs_cnt = len(nonzero_coefs_pos)

        total_coefs_cnt = len(coefs)
        if nonzero_coefs_cnt == 0:
            symbols = [tuple(['*'] * total_coefs_cnt)]
            return [], symbols  # Active symbols are empty

        act_symbols = []
        symbols = []
        for i in range(2**nonzero_coefs_cnt):
            bits = number_to_bit_tuple(i, tuple_size=nonzero_coefs_cnt)

            ni = 0  # Index to the next nonused nonzero coef index
            symbol = [None] * total_coefs_cnt
            for i in range(total_coefs_cnt):
                if i == nonzero_coefs_pos[ni]:
                    symbol[i] = bits[ni]
                    ni += 1
                    # All nonzero coefs have been used, do the rest.
                    if ni == nonzero_coefs_cnt:
                        for j in range(i+1, total_coefs_cnt):
                            symbol[j] = '*'
                        break
                else:
                    symbol[i] = '*'

            act_symbols.append(bits)
            symbols.append(tuple(symbol))
        return act_symbols, symbols

    @staticmethod
    def from_variable_names(variable_names: Tuple[str, ...]) -> LSBF_Alphabet:
        letter_size = len(variable_names)
        symbols = tuple(map(
            lambda i: number_to_bit_tuple(i, tuple_size=letter_size, pad=0),
            range(2**letter_size)
        ))

        return LSBF_Alphabet(
            active_variables=set(variable_names),
            symbols=symbols,
            variable_names=variable_names
        )

    def new_with_variable_removed(self,
                                  removed_var: str) -> Optional[LSBF_Alphabet]:

        new_variable_names = tuple(
            filter(lambda variable_name: removed_var != variable_name,
                   self.variable_names))

        if len(new_variable_names) == len(self.variable_names):
            return None  # The variable name to be removed was not present in the current variable list

        active_variables = set(self.active_variables)
        if removed_var in active_variables:
            active_variables.remove(removed_var)

        new_symbols = tuple(
            map(number_to_bit_tuple, range(2**len(new_variable_names))))

        return LSBF_Alphabet(symbols=new_symbols,
                             variable_names=new_variable_names,
                             active_variables=active_variables)


@dataclass
class NFA(Generic[AutomatonState]):
    alphabet:       LSBF_Alphabet
    transition_fn:  SparseSimpleTransitionFunction
    automaton_type: AutomatonType = AutomatonType.NFA
    initial_states: Set[Any] = field(default_factory=set)
    final_states:   Set[Any] = field(default_factory=set)
    states:         Set[Any] = field(default_factory=set)

    # Debug handle to listen to any state renaming happening during
    # intersecion/union; takes (automaton_id, old_state(int, str),
    # new_state(int))
    _debug_state_rename: Optional[Callable[[int, AutomatonState, int], None]] = None

    def __init__(self,
                 alphabet: LSBF_Alphabet,
                 automaton_type=AutomatonType.NFA,
                 initial_states: Optional[Set] = None,
                 final_states: Optional[Set] = None,
                 states: Optional[Set] = None,
                 transition_fn: Optional[SparseSimpleTransitionFunction] = None):

        self.alphabet = alphabet
        self.automaton_type = automaton_type
        self.final_states   = get_default_if_none(final_states, set)
        self.states         = get_default_if_none(states, set)
        self.initial_states = get_default_if_none(initial_states, set)
        self.transition_fn  = get_default_if_none(transition_fn, SparseSimpleTransitionFunction)

    def update_transition_fn(self,
                             from_state: AutomatonState,
                             via_symbol: LSBF_AlphabetSymbol,
                             to_state: AutomatonState
                             ):
        self.transition_fn.insert_transition(from_state, via_symbol, to_state)

    def add_state(self, state: Any):
        self.states.add(state)

    def add_final_state(self, state: Any):
        self.final_states.add(state)

    def add_initial_state(self, state: Any):
        self.initial_states.add(state)

    def has_state_with_value(self, state: Any) -> bool:
        return state in self.states

    def has_final_state_with_value(self, value: Any) -> bool:
        return value in self.final_states

    def get_transition_target(self,
                              origin: Any,
                              via_symbol: LSBF_AlphabetSymbol
                              ) -> Tuple[Any, ...]:
        # FIXME: Remove this cast.
        return tuple(self.transition_fn.get_transition_target(origin, via_symbol))

    def intersection(self, other: NFA[S]):
        if self.alphabet != other.alphabet:
            self.extend_to_common_alphabet(other)

        logger.debug(f'Calculating intercestion with alphabet size: {len(self.alphabet.variable_names)}')

        self_renamed_highest_state, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=self_renamed_highest_state)

        resulting_nfa: NFA[Tuple[int, int]] = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA
        )

        # Add all the initial states to the to-be-processed queue
        work_queue = carthesian_product(self_renamed.initial_states,
                                        other_renamed.initial_states)
        for initial_state in work_queue:
            resulting_nfa.add_initial_state(initial_state)

        bdd_manager = dd.autoref.BDD()

        _var_names = []
        for i, _ in enumerate(self_renamed.alphabet.variable_names):
            _var_names .append(chr(ord('A') + i))

        bdd_manager.declare(*_var_names)

        logger.info('Converting transition FNs to BDDs.')
        self_tfn = construct_transition_fn_to_bddtfn(self_renamed.transition_fn.data, _var_names, bdd_manager)
        other_tfn = construct_transition_fn_to_bddtfn(other_renamed.transition_fn.data, _var_names, bdd_manager)
        logger.info('Done.')

        while work_queue:
            current_state: Tuple[int, int] = work_queue.pop(0)
            resulting_nfa.add_state(current_state)

            logger.debug(f'Processed state {current_state}, remaining in queue {len(work_queue)}')

            # States in work_queue are boxed
            self_state, others_state = current_state

            # Check whether intersectin state should be made final
            if (self_state in self_renamed.final_states and others_state in other_renamed.final_states):
                resulting_nfa.add_final_state((self_state, others_state))

            used_symbols = 0

            # optimized_intersection: Set[Tuple[LSBF_AlphabetSymbol, Tuple[int, int]]] = set()
            if self_state in self_tfn and others_state in other_tfn:
                for self_dest_state in self_tfn[self_state]:
                    for other_dest_state in other_tfn[others_state]:
                        transition_self_bdd = self_tfn[self_state][self_dest_state]
                        transition_other_bdd = other_tfn[others_state][other_dest_state]

                        for transition_model in bdd_manager.pick_iter(transition_self_bdd & transition_other_bdd, care_vars=_var_names):
                            symbol = tuple(map(lambda var_name: transition_model[var_name], _var_names))
                            dest_state = (self_dest_state, other_dest_state)
                            if dest_state not in resulting_nfa.states:
                                if dest_state not in work_queue:
                                    work_queue.append(dest_state)

                            resulting_nfa.update_transition_fn(current_state, symbol, (self_dest_state, other_dest_state))
                            used_symbols += 1

            logger.info('Intersection: Used symbols minimized to: {0}/{1}'.format(used_symbols, len(self.alphabet.symbols)))

            # for symbol in self_renamed.alphabet.symbols:
            # generated_intersection: Set[Tuple[LSBF_AlphabetSymbol, Tuple[int, int]]] = set()
            # for symbol in intersect_symbols:
            #     self_targets = self_renamed.get_transition_target(self_state, symbol)
            #     other_targets = other_renamed.get_transition_target(others_state, symbol)

            #     if self_targets is None or other_targets is None:
            #         continue

            #     for new_intersect_state in carthesian_product(self_targets, other_targets):
            #         if new_intersect_state not in resulting_nfa.states:
            #             if new_intersect_state not in work_queue:
            #                 work_queue.append(new_intersect_state)

            #         generated_intersection.add((symbol, new_intersect_state))
            #         resulting_nfa.update_transition_fn(current_state, symbol, new_intersect_state)

            # logger.info(f'Standard intersection produced: {len(generated_intersection)}')
            # logger.info(f'Optimized intersection produced: {len(optimized_intersection)}')
            # msg: str = 'OK' if len(generated_intersection) == len(optimized_intersection) else 'FAIL'
            # logger.info(f'Size {msg}.')

        return resulting_nfa

    def union(self, other: NFA[S]) -> NFA[int]:
        if self.alphabet != other.alphabet:
            self.extend_to_common_alphabet(other)

        latest_state_value, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=latest_state_value)

        states = self_renamed.states.union(other_renamed.states)
        transitions = SparseSimpleTransitionFunction.union_of(self_renamed.transition_fn, other_renamed.transition_fn)
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

    def extend_to_common_alphabet(self, other: NFA[S]):
        unified_variable_names = unite_alphabets(self.alphabet.variable_names, other.alphabet.variable_names)
        self.transition_fn.extend_to_new_alphabet_symbols(unified_variable_names, self.alphabet.variable_names)
        other.transition_fn.extend_to_new_alphabet_symbols(unified_variable_names, other.alphabet.variable_names)

        self.alphabet = LSBF_Alphabet.from_variable_names(unified_variable_names)
        other.alphabet = self.alphabet

    def determinize(self):
        '''Performs NFA -> DFA using the powerset construction'''
        self._rename_own_states()

        working_queue: List[Tuple[AutomatonState, ...]] = [tuple(self.initial_states)]
        _final_states_raw = self.final_states

        determinized_automaton: DFA[Tuple[AutomatonState, ...]] = DFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.DFA)
        determinized_automaton.add_initial_state(working_queue[0])

        while working_queue:
            unexplored_dfa_state: Tuple[AutomatonState, ...] = working_queue.pop(0)
            logger.debug(f'Determinization for {unexplored_dfa_state}, remaining in work queue: {len(working_queue)}')

            determinized_automaton.add_state(unexplored_dfa_state)

            intersect = set(unexplored_dfa_state).intersection(_final_states_raw)
            if intersect:
                determinized_automaton.add_final_state(unexplored_dfa_state)

            for symbol in iterate_over_active_variables(self.alphabet.variable_names, self.alphabet.active_variables):
                reachable_states: List[AutomatonState] = list()
                for state in unexplored_dfa_state:
                    # Get all states reacheble from current state via symbol
                    out_states = self.get_transition_target(state, symbol)
                    if out_states:
                        reachable_states += list(out_states)

                # FIXME: Some form of a restriction to AutomatonState type is needed in order to support SupportsLessThan type
                dfa_state: Tuple[AutomatonState, ...] = tuple(set(sorted(reachable_states)))  # type: ignore

                if dfa_state and not determinized_automaton.has_state_with_value(dfa_state):
                    if dfa_state not in working_queue:
                        working_queue.append(dfa_state)

                if dfa_state:
                    determinized_automaton.update_transition_fn(unexplored_dfa_state, symbol, dfa_state)

        determinized_automaton.add_trap_state()
        return determinized_automaton

    def add_trap_state(self):
        '''Adds trap (sink) state with transitions to it as needed.
        The Given automaton should be determinized first.
        '''
        trap_state = 'TRAP'
        states = list(self.states)
        added_trap_state = self.transition_fn.complete_with_trap_state(self.alphabet, states, trap_state=trap_state)
        if added_trap_state:
            self.states.add(trap_state)

    def _rename_own_states(self):
        debug_fn: Optional[functools.partial[None]]
        if self._debug_state_rename is not None:
            debug_fn = functools.partial(self._debug_state_rename, id(self))
        else:
            debug_fn = None

        _, state_name_translation = create_enumeration_state_translation_map(self.states, debug_fn, start_from=0)

        def translate(state: AutomatonState) -> int:
            return state_name_translation[state]

        self.states         = set(map(translate, self.states))
        self.initial_states = set(map(translate, self.initial_states))
        self.final_states   = set(map(translate, self.final_states))

        self.transition_fn.rename_states(state_name_translation)

    def do_projection(self, variable_name: str) -> Optional[NFA]:
        resulting_alphabet_var_count = len(self.alphabet.active_variables) - 1

        if resulting_alphabet_var_count == 0:
            is_sat, _ = self.is_sat()  # Check whether the language is nonempty
            if is_sat:
                return NFA.trivial_accepting(self.alphabet)
            else:
                return NFA.trivial_nonaccepting(self.alphabet)

        else:
            # Cross out the projected variable
            new_nfa: NFA[AutomatonState] = NFA(
                alphabet=self.alphabet,
                automaton_type=AutomatonType.NFA,
            )

            new_nfa.states = set(self.states)
            new_nfa.initial_states = set(self.initial_states)
            new_nfa.final_states = set(self.final_states)

            bit_pos = calculate_variable_bit_position(self.alphabet.variable_names, variable_name)
            if bit_pos is None:
                raise ValueError(f'Could not find variable_name "{variable_name}" in current alphabet {self.alphabet}')

            new_nfa.transition_fn = self.transition_fn.copy()
            new_nfa.transition_fn.project_bit_away(bit_pos)

            new_nfa.alphabet.active_variables -= set((variable_name, ))

            new_nfa.perform_pad_closure()
            return new_nfa

    def perform_pad_closure(self):
        '''Performs inplace padding closure. See file automaton_algorithms.py:padding_closure'''
        automaton_algorithms.pad_closure(self)

    def get_symbols_leading_from_state_to_state(self,
                                                from_state: AutomatonState,
                                                to_state: AutomatonState) -> Set[LSBF_AlphabetSymbol]:
        return self.transition_fn.get_symbols_between_states(from_state, to_state)

    def rename_states(self, start_from: int = 0) -> Tuple[int, NFA[int]]:
        nfa: NFA[int] = NFA(alphabet=self.alphabet, automaton_type=self.automaton_type)

        debug_fn: Optional[functools.partial[None]]
        if self._debug_state_rename is not None:
            debug_fn = functools.partial(self._debug_state_rename, id(self))
        else:
            debug_fn = None

        hightest_state, state_name_translation = create_enumeration_state_translation_map(self.states, debug_fn, start_from=start_from)

        def translate(state: AutomatonState) -> int:
            return state_name_translation[state]

        nfa.states.update(map(translate, self.states))
        nfa.initial_states.update(map(translate, self.initial_states))
        nfa.final_states.update(map(translate, self.final_states))
        nfa.transition_fn = self.transition_fn.copy()
        nfa.transition_fn.rename_states(state_name_translation)

        return (hightest_state, nfa)

    def complement(self) -> NFA:
        ''' The complement is done with respect to \\Sigma^{+},
            since empty word encodes nothing.
        '''
        result: NFA[AutomatonState] = NFA(
            alphabet=self.alphabet,
            automaton_type=self.automaton_type
        )

        result.initial_states = set(self.initial_states)
        result.states = set(self.states)
        if self.automaton_type & AutomatonType.TRIVIAL:
            # In trivial automaton we only need to do alternation.
            result.final_states = result.initial_states - self.final_states
        else:
            result.final_states = self.states - self.initial_states - self.final_states

        result.transition_fn = self.transition_fn.copy()

        return result

    def is_sat(self) -> Tuple[bool, List[LSBF_AlphabetSymbol]]:
        if not self.alphabet.active_variables:
            if self.final_states:
                return (True, [])
            else:
                return (False, [])

        # Implementation of DFS
        # Implementation for determinized automaton
        state_stack: List[AutomatonState] = list(self.initial_states)
        traversal_history: Dict[AutomatonState, AutomatonState] = dict()

        explored_states: Set[AutomatonState] = set()
        used_word: List[LSBF_AlphabetSymbol] = list()

        while state_stack:
            current_state = state_stack.pop(-1)

            explored_states.add(current_state)

            if current_state in self.final_states:
                used_word = self.transition_fn.calculate_path_from_dfs_traversal_history(
                    traversal_history, current_state, self.initial_states)

                # The NFA cannot accept empty words - that happens when after
                # determinization and complement some of the initial states
                # becomes accepting -- THIS SHOUL NOT HAPPEN anymore
                if used_word:
                    return (True, used_word)

            if current_state not in self.transition_fn.data:
                if used_word:
                    used_word.pop(-1)
            else:
                transitions = self.transition_fn.data[current_state]
                for destination, _ in transitions.items():
                    if destination not in explored_states:
                        traversal_history[destination] = current_state
                        state_stack.append(destination)
        return (False, [])

    def remove_nonfinishing_states(self):
        '''BFS on rotated transitions'''
        reachable_states = self.transition_fn.remove_nonfinishing_states(self.states, self.final_states)
        self.states = reachable_states

    @staticmethod
    def trivial_accepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa: NFA[str] = NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)

        final_state = 'FINAL'
        nfa.add_state(final_state)
        nfa.add_initial_state(final_state)
        nfa.add_final_state(final_state)

        self_loop_symbol = tuple(['*'] * len(alphabet.variable_names))
        nfa.update_transition_fn(final_state, self_loop_symbol, final_state)
        nfa.alphabet.active_variables = set()

        return nfa

    @staticmethod
    def trivial_nonaccepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa: NFA[str] = NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)

        initial_state = 'INITIAL'
        nfa.add_state(initial_state)
        nfa.add_initial_state(initial_state)

        self_loop_symbol = tuple(['*'] * len(alphabet.variable_names))
        nfa.update_transition_fn(initial_state, self_loop_symbol, initial_state)
        nfa.alphabet.active_variables = set()

        return nfa

    @staticmethod
    def for_bool_variable(variable_name: str, var_value: bool):
        '''Builds an equivalent automaton encoding the provided bool variable.

        The resulting autmaton is not complete (must be completed before complement).
        '''
        if var_value is True:
            states = set(['q0', 'qT'])
            final_states = set(['qT'])
        else:
            states = set(['q0', 'qF'])
            final_states = set(['qF'])
        initial_states = set(['q0'])
        alphabet = LSBF_Alphabet(((0, ), (1, ),), (variable_name, ), set([variable_name]))

        a_type = AutomatonType.DFA | AutomatonType.BOOL

        nfa: NFA = NFA(alphabet, a_type, initial_states, final_states, states)

        if var_value is True:
            nfa.update_transition_fn('q0', (1, ), 'qT')  # Var = True --> accepting state
            nfa.update_transition_fn('qT', ('*', ), 'qT')
        else:
            nfa.update_transition_fn('q0', (0, ), 'qF')  # Var = False --> accepting state
            nfa.update_transition_fn('qF', ('*', ), 'qF')

        return nfa


DFA = NFA
