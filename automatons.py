from __future__ import annotations
from enum import IntFlag
from log import logger
from collections import defaultdict
from typing import (
    Set,
    Generator,
    Dict,
    Tuple,
    List,
    TypeVar,
    Iterable,
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
    SparseSimpleTransitionFunction
)

from visualization import AutomatonVisRepresentation

from mtbdd_transitions import MTBDDTransitionFn, mtbdd_false

import functools


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
    variable_names: Dict[int, str]
    variable_numbers: List[int]
    active_variables: Set[str]
    active_symbols: Optional[Tuple[LSBF_AlphabetSymbol, ...]] = None

    @staticmethod
    def from_inequation(ineq: Relation) -> LSBF_Alphabet:
        '''Generates a compressed alphabet from given relation.'''
        act_symbols, _ = LSBF_Alphabet.generate_compressed_symbols(ineq.variable_coeficients)

        active_variables = [var for i, var in enumerate(ineq.variable_names) if ineq.variable_coeficients[i] != 0]
        variable_ids = list(range(1, len(active_variables) + 1))
        return LSBF_Alphabet(variable_names={},
                             variable_numbers=variable_ids,
                             active_variables=set(active_variables),
                             active_symbols=act_symbols)

    def gen_projection_symbols_onto_variables(self, variables_subset: List[int]) -> Generator[Tuple[int, ...], Any, Any]:
        '''Generates all symbols that would be contained in an alphabet that
        would result from projecting onto the given subset of alphabet
        variables.'''
        # We actually do not care about the subset passed in, we just generate
        # bit vectors of given length
        symbol_size = len(variables_subset)
        for i in range(2**len(variables_subset)):
            bit_vector = number_to_bit_tuple(i, tuple_size=symbol_size)
            yield bit_vector

    def cylindrify_symbol_of_projected_alphabet(self,
                                                variables: List[int],
                                                symbol: Tuple[int, ...]) -> Tuple[Union[str, int], ...]:
        '''Performs cylindrification on the given symbol that belongs to
        some smaller alphabet that resulted from projecting some variables from
        this one away.'''
        alphabet_size = len(self.variable_numbers)

        # Create a list of indices where we should put the values from the
        # provided symbol (rest will be '*')
        vi = 0  # Index of the next variable name in provided variables to be checked
        used_variables_cooficients = []
        for i, var_id in enumerate(self.variable_numbers):
            if var_id == variables[vi]:
                used_variables_cooficients.append(i)
                vi += 1

            if vi == len(variables):
                break

        ni = 0  # Index to the next bit in the given symbol that should be used.
        cylindrified_symbol: List = [None] * alphabet_size
        for i in range(alphabet_size):
            if i == used_variables_cooficients[ni]:
                cylindrified_symbol[i] = symbol[ni]
                ni += 1
                # All bits from the given symbol have been used, fill the rest
                # with *.
                if ni == len(symbol):
                    for j in range(i+1, alphabet_size):
                        cylindrified_symbol[j] = '*'
                    break
            else:
                cylindrified_symbol[i] = '*'
        return tuple(cylindrified_symbol)

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
            symbol: List = [None] * total_coefs_cnt
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

        variable_numbers = list(map(
            lambda index: index + 1,
            range(len(variable_names))))

        return LSBF_Alphabet(
            active_variables=set(variable_names),
            variable_names={},
            variable_numbers=variable_numbers
        )

    @staticmethod
    def from_variable_ids(variable_ids: List[int]) -> LSBF_Alphabet:
        '''Creates a new alphabet from the given variable_name, id pairs.
        The variables list should be sorted by the ID.
        '''
        variable_names: Dict[int, str] = dict()
        variable_ids = sorted(variable_ids)

        return LSBF_Alphabet(
            active_variables=set(),
            variable_names=variable_names,
            variable_numbers=variable_ids
        )

    @property
    def symbols(self):
        letter_size = len(self.variable_numbers)
        for i in range(2**letter_size):
            yield number_to_bit_tuple(i, tuple_size=letter_size, pad=0)

    def bind_variable_name_to_id(self, variable_name: str, variable_id: int):
        self.variable_names[variable_id] = variable_name


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
                 transition_fn: Optional[SparseSimpleTransitionFunction] = None,
                 used_variables: List[int] = []):

        self.alphabet = alphabet
        self.automaton_type = automaton_type
        self.final_states = get_default_if_none(final_states, set)
        self.states = get_default_if_none(states, set)
        self.initial_states = get_default_if_none(initial_states, set)
        self.transition_fn = get_default_if_none(transition_fn, SparseSimpleTransitionFunction)

        self.extra_info: Dict[str, Any] = dict()
        self.used_variables = used_variables

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
            assert False

        self_renamed_highest_state, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=self_renamed_highest_state)

        resulting_nfa: NFA[Tuple[int, int]] = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA
        )

        used_variable_ids = sorted(set(self.used_variables + other.used_variables))
        projected_alphabet = list(self.alphabet.gen_projection_symbols_onto_variables(used_variable_ids))

        logger.debug('Calculating intersection with used_variables: self={0} other={1} result={2}'.format(
            self.used_variables,
            other.used_variables,
            used_variable_ids
        ))

        # Add all the initial states to the to-be-processed queue
        work_queue = carthesian_product(self_renamed.initial_states,
                                        other_renamed.initial_states)

        for initial_state in work_queue:
            resulting_nfa.add_initial_state(initial_state)

        while work_queue:
            current_state: Tuple[int, int] = work_queue.pop(-1)
            resulting_nfa.add_state(current_state)

            logger.debug(f'Processed state {current_state}, remaining in queue {len(work_queue)}')

            # States in work_queue are boxed
            self_state, others_state = current_state

            # Check whether intersectin state should be made final
            if (self_state in self_renamed.final_states and others_state in other_renamed.final_states):
                resulting_nfa.add_final_state((self_state, others_state))

            # optimized_intersection: Set[Tuple[LSBF_AlphabetSymbol, Tuple[int, int]]] = set()
            has_self_state_out_transitions = bool(self_renamed.transition_fn.get_state_post(self_state))
            has_other_state_out_transitions = bool(other_renamed.transition_fn.get_state_post(others_state))

            if has_self_state_out_transitions and has_other_state_out_transitions:
                for projected_symbol in projected_alphabet:
                    cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(used_variable_ids,
                                                                                                projected_symbol)
                    self_destination_set = self_renamed.get_transition_target(self_state, cylindrified_symbol)
                    other_destination_set = other_renamed.get_transition_target(others_state, cylindrified_symbol)

                    for produced_intersection_metastate in carthesian_product(self_destination_set,
                                                                              other_destination_set):

                        resulting_nfa.update_transition_fn(current_state,
                                                           cylindrified_symbol,
                                                           produced_intersection_metastate)

                        if not resulting_nfa.has_state_with_value(produced_intersection_metastate) and produced_intersection_metastate not in work_queue:
                            work_queue.append(produced_intersection_metastate)

        resulting_nfa.used_variables = used_variable_ids

        resulting_nfa.remove_nonfinishing_states()

        assert resulting_nfa.used_variables

        return resulting_nfa

    def union(self, other: NFA[S]) -> NFA[int]:
        if self.alphabet != other.alphabet:
            assert False

        latest_state_value, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=latest_state_value)

        states = self_renamed.states.union(other_renamed.states)
        transitions = SparseSimpleTransitionFunction.union_of(self_renamed.transition_fn, other_renamed.transition_fn)
        initial_states = self_renamed.initial_states.union(other_renamed.initial_states)
        final_states = self_renamed.final_states.union(other_renamed.final_states)

        union_nfa: NFA[int] = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA,
            initial_states=initial_states,
            final_states=final_states,
            states=states,
            transition_fn=transitions
        )
        union_nfa.used_variables = sorted(set(self.used_variables + other.used_variables))

        return union_nfa

    def determinize(self):
        '''Performs NFA -> DFA using the powerset construction'''
        self._rename_own_states()

        working_queue: List[Tuple[AutomatonState, ...]] = [tuple(self.initial_states)]
        _final_states_raw = self.final_states

        determinized_automaton: DFA[Tuple[AutomatonState, ...]] = DFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.DFA)
        determinized_automaton.add_initial_state(working_queue[0])

        projected_alphabet_symbols = list(self.alphabet.gen_projection_symbols_onto_variables(self.used_variables))

        while working_queue:
            unexplored_dfa_state: Tuple[AutomatonState, ...] = working_queue.pop(-1)
            logger.debug(f'Determinization for {unexplored_dfa_state}, remaining in work queue: {len(working_queue)}')

            determinized_automaton.add_state(unexplored_dfa_state)

            intersect = set(unexplored_dfa_state).intersection(_final_states_raw)
            if intersect:
                determinized_automaton.add_final_state(unexplored_dfa_state)

            for symbol in projected_alphabet_symbols:
                reachable_states: List[AutomatonState] = list()

                cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(self.used_variables,
                                                                                            symbol)
                for state in unexplored_dfa_state:
                    # Get all states reacheble from current state via symbol
                    out_states = self.get_transition_target(state, cylindrified_symbol)
                    if out_states:
                        reachable_states += list(out_states)

                # FIXME: Some form of a restriction to AutomatonState type is needed in order to support SupportsLessThan type
                dfa_state: Tuple[AutomatonState, ...] = tuple(set(sorted(reachable_states)))  # type: ignore

                if dfa_state and not determinized_automaton.has_state_with_value(dfa_state):
                    if dfa_state not in working_queue:
                        working_queue.append(dfa_state)

                if dfa_state:
                    determinized_automaton.update_transition_fn(unexplored_dfa_state, cylindrified_symbol, dfa_state)

        determinized_automaton.used_variables = self.used_variables
        determinized_automaton.add_trap_state()
        return determinized_automaton

    def add_trap_state(self):
        '''Adds trap (sink) state with transitions to it as needed.
        The Given automaton should be determinized first.
        '''
        trap_state = 'TRAP'
        states = list(self.states)
        added_trap_state = self.transition_fn.complete_with_trap_state(self.alphabet, self.used_variables, states, trap_state=trap_state)
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

        self.states = set(map(translate, self.states))
        self.initial_states = set(map(translate, self.initial_states))
        self.final_states = set(map(translate, self.final_states))

        self.transition_fn.rename_states(state_name_translation)

    def do_projection(self, variable_id: int, skip_pad_closure: bool = False) -> Optional[NFA]:
        resulting_alphabet_var_count = len(self.used_variables) - 1

        if resulting_alphabet_var_count == 0:
            logger.info('Projecting away the last variable for automaton - performing DFS search for a model.')
            is_sat, _ = self.is_sat()  # Check whether the language is nonempty
            logger.info(f'Was model found? {is_sat}')
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

            bit_pos = calculate_variable_bit_position(self.alphabet.variable_numbers, variable_id)
            if bit_pos is None:
                raise ValueError(f'Could not find variable_name "{variable_id}" in current alphabet {self.alphabet}')

            new_nfa.transition_fn = self.transition_fn
            new_nfa.transition_fn.project_bit_away(bit_pos)

            new_nfa.perform_pad_closure()
            new_used_vars = list(self.used_variables)
            new_used_vars.remove(variable_id)
            new_nfa.used_variables = new_used_vars
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

        result.used_variables = list(self.used_variables)
        return result

    def is_sat(self) -> Tuple[bool, List[LSBF_AlphabetSymbol]]:
        if not self.used_variables:
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

    def get_state_post(self, state: int) -> List[int]:
        assert state in self.states, \
            f'Cannot retrieve post of non automaton state: {state}'
        return self.transition_fn.get_state_post(state)

    @staticmethod
    def trivial_accepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa = NFA.trivial_nonaccepting(alphabet)
        nfa.add_final_state(0)
        return nfa

    @staticmethod
    def trivial_nonaccepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa: NFA[str] = NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)

        state = 0
        nfa.add_state(state)
        nfa.add_initial_state(state)

        self_loop_symbol = tuple(['*'] * len(alphabet.variable_numbers))
        nfa.update_transition_fn(state, self_loop_symbol, state)
        nfa.alphabet.active_variables = set()

        return nfa

    @classmethod
    def for_bool_variable(cls, overall_alphabet: LSBF_Alphabet, var_id: int, var_value: bool):
        '''Builds an equivalent automaton encoding the provided bool variable.

        The resulting autmaton is not complete (must be completed before complement).
        '''

        automaton_type = AutomatonType.DFA | AutomatonType.BOOL

        nfa = cls(overall_alphabet, automaton_type, used_variables=[var_id])
        nfa.states = {0, 1}
        nfa.initial_states = {0}
        nfa.final_states = {1}

        transition_symbol = (1, ) if var_value else (0, )
        cylindrified_symbol = overall_alphabet.cylindrify_symbol_of_projected_alphabet([var_id], transition_symbol)

        nfa.update_transition_fn(0, cylindrified_symbol, 1)  # Var = True --> accepting state
        nfa.update_transition_fn(1, cylindrified_symbol, 1)

        nfa.extra_info = {}
        nfa.extra_info['bool_var_value'] = var_value

        return nfa

    def get_visualization_representation(self) -> AutomatonVisRepresentation:
        '''Retrieves the information necessary to visualize this automaton.'''

        # The transition information needed is already stored in the correct form
        # inside the transition function, however it might change in the future
        # - so we use iter() and reconstruct the information.
        _transitions = defaultdict(list)
        for origin_state, symbol, destination_state in self.transition_fn.iter():
            _transitions[(origin_state, destination_state)].append(symbol)

        transitions = []
        for state_pair, symbols in _transitions.items():
            transitions.append((state_pair[0], symbols, state_pair[1]))

        # TODO(temporary hack)
        var_names = list(map(lambda id: 'v' + str(id), self.alphabet.variable_numbers))

        return AutomatonVisRepresentation(
            states=set(self.states),
            final_states=set(self.final_states),
            initial_states=set(self.initial_states),
            variable_names=var_names,
            transitions=transitions
        )


class MTBDD_NFA(NFA):
    automaton_id_counter = 0  # ^^^ Used to mark mtbdd leaves in order to avoid sharing them between multiple mtbdds
    fast_prunining_enabled = False

    def __init__(self,
                 alphabet: LSBF_Alphabet,
                 automaton_type: AutomatonType,
                 used_variables: List[int] = []):
        logger.debug('Initializing an MTBDD NFA Automaton.')
        self.alphabet = alphabet
        self.automaton_type = automaton_type
        self.states: Set[int] = set()
        self.final_states: Set[int] = set()
        self.initial_states: Set[int] = set()
        self.transition_fn = MTBDDTransitionFn(self.alphabet.variable_numbers, MTBDD_NFA.automaton_id_counter)
        self.trapstate = None
        self.applied_operations_info = []
        self.used_variables = used_variables
        MTBDD_NFA.automaton_id_counter += 1

    def add_state(self, state: int):
        self.states.add(state)

    def add_final_state(self, state: int):
        self.final_states.add(state)

    def add_initial_state(self, state: int):
        self.initial_states.add(state)

    def update_transition_fn(self,
                             source: int,
                             symbol: LSBF_AlphabetSymbol,
                             dest: int):
        self.transition_fn.insert_transition(source, symbol, dest)

    def rename_states(self, start_from: int = 0) -> Tuple[int, MTBDD_NFA]:
        return self.renumber_states(start_from), self

    def renumber_states(self, start_from: int = 0) -> int:
        rename_map = {}

        new_states = set()
        new_final_states = set()
        new_initial_states = set()

        cnt = start_from
        for old_s in self.states:
            rename_map[old_s] = cnt
            new_states.add(cnt)

            if self._debug_state_rename is not None:
                self._debug_state_rename(id(self), old_s, cnt)

            if old_s in self.final_states:
                new_final_states.add(cnt)

            if old_s in self.initial_states:
                new_initial_states.add(cnt)

            cnt += 1

        self.transition_fn.rename_states(rename_map)

        self.states = new_states
        self.final_states = new_final_states
        self.initial_states = new_initial_states
        return cnt

    def get_state_post(self, state: int) -> List[int]:
        assert state in self.states, 'Cannot retrieve post of a non automaton state'
        return self.transition_fn.get_state_post(state)

    def union(self, other: MTBDD_NFA) -> MTBDD_NFA:
        logger.debug('Entering MTBDD NFA union procedure.')
        first_unreached_state = self.renumber_states(start_from=0)

        other.renumber_states(start_from=first_unreached_state)

        self.transition_fn = MTBDDTransitionFn.union_of(self.transition_fn,
                                                        other.transition_fn,
                                                        MTBDD_NFA.get_next_automaton_id())

        self.states = self.states.union(other.states)
        self.final_states.update(other.final_states)
        self.initial_states.update(other.initial_states)

        self.applied_operations_info += ['union']
        self.used_variables = sorted(set(self.used_variables + other.used_variables))

        self.automaton_type = AutomatonType.NFA

        logger.debug('Exiting MTBDD NFA union procedure.')
        return self

    def is_safe_to_quick_prune_intersection_states(self) -> bool:
        no_determinization = 'determinization' not in self.applied_operations_info
        return no_determinization

    def intersection(self, other: MTBDD_NFA, metastate_map: Optional[Dict[int, Tuple[int, int]]] = None):  # NOQA
        logger.debug('Entering MTBDD NFA intersection procedure.')
        if metastate_map is None:
            metastate_map = dict()

        logger.debug(f'Beginning to renumber states. Self state count: {len(self.states)} {len(other.states)}')
        logger.debug('Is pruning enabled? {0}'.format(self.fast_prunining_enabled))
        if self.fast_prunining_enabled:
            logger.debug('Is early safe pruning possible? self={0} other={1}'.format(self.is_safe_to_quick_prune_intersection_states(), other.is_safe_to_quick_prune_intersection_states()))
        hightest_state = self.renumber_states(start_from=0)
        other.renumber_states(start_from=hightest_state)
        logger.debug('Intersection state renumbering done.')

        prune_configuration = (False, [])
        if MTBDD_NFA.fast_prunining_enabled:
            if self.is_safe_to_quick_prune_intersection_states() and other.is_safe_to_quick_prune_intersection_states():
                prune_configuration = (True, list(self.final_states.union(other.final_states)))

        MTBDDTransitionFn.begin_intersection(prune_configuration)

        def set_cross(s1: Iterable[int], s2: Iterable[int]):
            for left_state in s1:
                for right_state in s2:
                    yield (left_state, right_state)

        # Origin states
        intersect_initial_states = list(set_cross(self.initial_states, other.initial_states))
        work_queue = []
        for i, init_metastate in enumerate(intersect_initial_states):
            metastate_map[i] = init_metastate
            work_queue.append(i)

        MTBDDTransitionFn.update_intersection_state(metastate_map)

        int_nfa = MTBDD_NFA(self.alphabet, AutomatonType.NFA)
        # Make sure that we use the single-integer state numbers not pairs
        logger.info(f'Setting initial states to: {metastate_map.keys()} {metastate_map}')
        int_nfa.initial_states = set(metastate_map.keys())

        # The new automaton should have unique ID
        assert int_nfa.transition_fn.automaton_id not in \
            [self.transition_fn.automaton_id, other.transition_fn.automaton_id]

        work_set = set(work_queue)
        while work_queue:
            cur_state = work_queue.pop(-1)
            work_set.remove(cur_state)
            cur_metastate = metastate_map[cur_state]
            logger.debug(f'MTBDD NFA Intersection: Processing metastate: {cur_metastate}, remaining in work queue: {len(work_queue)}')

            if cur_state in int_nfa.states:
                continue  # Each state can be processed only once

            int_nfa.add_state(cur_state)

            left_state, right_state = cur_metastate
            if left_state in self.final_states and right_state in other.final_states:
                int_nfa.add_final_state(cur_state)

            l_mtbdd = self.transition_fn.mtbdds.get(left_state, None)
            r_mtbdd = other.transition_fn.mtbdds.get(right_state, None)

            if l_mtbdd is None or r_mtbdd is None:
                # The current metastate is dead end.
                continue

            generated_metastates = {}
            cur_int_mtbdd = self.transition_fn.compute_mtbdd_intersect(
                l_mtbdd,
                r_mtbdd,
                int_nfa.transition_fn.automaton_id,
                generated_metastates=generated_metastates  # Get generated metastates
            )

            # Prevent the created MTBDD from getting GCd
            MTBDDTransitionFn.inc_mtbdd_ref(cur_int_mtbdd)

            for gm in generated_metastates.items():
                gen_state, gen_metastate = gm
                metastate_map[gen_state] = gen_metastate

                if gen_state not in work_set:
                    work_queue.append(gen_state)
                    work_set.add(gen_state)

            int_nfa.transition_fn.mtbdds[cur_state] = cur_int_mtbdd

        MTBDDTransitionFn.end_intersection()
        int_nfa.applied_operations_info = self.applied_operations_info + ['intersection']

        int_nfa.used_variables = sorted(set(self.used_variables + other.used_variables))

        int_nfa.remove_nonfinishing_states()

        logger.debug('Exiting MTBDD NFA intersection procedure.')
        return int_nfa

    def perform_pad_closure(self):
        self.transition_fn.do_pad_closure(self.initial_states, self.final_states)

    def determinize(self):
        '''Performs in-place determinization of the automaton. No
        determinization is performed if the automaton is already marked as a
        DFA.

        The determinized automaton has a transition for every alphabet symbol
        in every state - after determinization a completion with a trapstate is
        performed.  '''

        if self.automaton_type & AutomatonType.DFA:
            return self
        logger.debug('Performing MTBDD NFA determinization.')

        work_queue = [tuple(self.initial_states)]
        work_set = set(work_queue)
        dfa = MTBDD_NFA(self.alphabet, AutomatonType.DFA)

        states = set()
        initial_states = set(work_queue)
        final_states = set()

        # Stores the actual structure of the automaton.
        mtbdds = {}

        while work_queue:
            logger.debug(f'Determinization: The number of states remaining in the work queue: {len(work_queue)}')
            c_metastate = work_queue.pop(-1)
            work_set.remove(c_metastate)

            # @Optimize: This is true only for the initial states
            #            Other states are reachable from other and are remapped
            #            when the transition is added.
            states.add(c_metastate)
            if set(c_metastate).intersection(self.final_states):
                final_states.add(c_metastate)

            c_metastate_union_mtbdd = self.transition_fn.get_union_mtbdd_for_states(c_metastate, self.transition_fn.automaton_id)

            # The mtbdd has already ref count increased, do not increase it

            if c_metastate_union_mtbdd is None:
                continue
            mtbdds[c_metastate] = c_metastate_union_mtbdd

            reachable_metastates = MTBDDTransitionFn.call_get_mtbdd_leaves(c_metastate_union_mtbdd)
            for r_metastate in reachable_metastates:
                r_metastate = tuple(r_metastate)

                if r_metastate not in states and r_metastate not in work_set:
                    work_queue.append(r_metastate)
                    work_set.add(r_metastate)

        # We have explored the entire structure - time to mangle the generated
        # metastates into integers, so that the automaton has the correct form.
        automaton_id = dfa.transition_fn.automaton_id
        metastates, _mtbdds = zip(*mtbdds.items())
        patched_mtbdds, metastate2int_map = MTBDDTransitionFn.rename_metastates_after_determinization(_mtbdds, automaton_id)

        # The patched mtbdds have already ref count incremented, no need to
        # increment the ref counter. The old mtbdds will be decremented when
        # MTBDDTransitionFn will be GC'd by python garbage collection.

        max_state = max(metastate2int_map.values())
        for state in states:
            # Initial states might never get discovered - we need to remap them
            # manually, because they will not be present in any of the mtbdd
            # leaves
            if state in metastate2int_map:
                dfa.add_state(metastate2int_map[state])
            else:
                max_state += 1
                metastate2int_map[state] = max_state
                dfa.add_state(max_state)
        for f_state in final_states:
            dfa.add_final_state(metastate2int_map[f_state])
        for i_state in initial_states:
            dfa.add_initial_state(metastate2int_map[i_state])

        for metastate, patched_mtbdd in zip(metastates, patched_mtbdds):
            state = metastate2int_map[metastate]
            dfa.transition_fn.mtbdds[state] = patched_mtbdd

        dfa.add_trap_state()

        dfa.applied_operations_info = self.applied_operations_info + ['determinization']
        dfa.used_variables = list(self.used_variables)
        logger.debug('Exiting MTBDD NFA determinization procedure.')
        return dfa

    def complement(self) -> MTBDD_NFA:
        '''Creates the automaton complement. Determinization (and
        completion with a trapstate) is performed only if the current automaton
        is not DFA (.automaton_type).

        Note that the complement is peformed to \\sigma^* - \\eps, as the empty
        word cannot never be contained in a language encoding presburger
        formula over \\mathcal{Z}.  '''

        dfa = self.determinize()

        new_final_states = dfa.states - dfa.final_states

        # The initial states can never become final - the language cannot
        # contain empty word.
        if not self.automaton_type & AutomatonType.TRIVIAL:
            new_final_states -= dfa.initial_states
        dfa.final_states = new_final_states

        dfa.applied_operations_info += ['complement']
        # Do not need to set used_variables here as the determinized automaton
        # already has them set
        return dfa

    def add_trap_state(self):
        '''Creates a new state - the trapstate and for every state that
        does not have an outgoing transition for some alphabet symbol A creates
        a new transition from the this state via A to this trapstate.'''

        # Some states might not be present in the transition fn - have no
        # outgoing entries - fix it, so the they will have the transition to
        # trapstate afterwards
        logger.debug('MTBDD NFA Adding trapstate...')

        logger.debug('Populating transition function with empty mtbdd where an origin state is missing.')
        for state in self.states:
            if state not in self.transition_fn.mtbdds:
                self.transition_fn.mtbdds[state] = mtbdd_false
        logger.debug('Done.')

        trapstate = max(self.states) + 1
        was_trapstate_added = self.transition_fn.complete_transitions_with_trapstate(trapstate)
        logger.debug(f'Was a trapstate needed? {was_trapstate_added}.')

        if was_trapstate_added:
            logger.debug(f'The trapstate value is: {trapstate}.')
            self.trapstate = trapstate
            self.states.add(self.trapstate)

            all_symbols = tuple(['*'] * len(self.alphabet.variable_numbers))

            self.transition_fn.insert_transition(self.trapstate,
                                                 all_symbols,
                                                 self.trapstate
                                                 )

    @staticmethod
    def get_next_automaton_id() -> int:
        c = MTBDD_NFA.automaton_id_counter
        MTBDD_NFA.automaton_id_counter += 1
        return c

    def do_projection(self, var: int, skip_pad_closure: bool = False):
        logger.info(f'Performing MTBDD NFA projection on variable: {var}. Currently employed variables: {self.used_variables}')
        self.transition_fn.project_variable_away(var)

        logger.debug(f'Variable projected away, proceeding to padding closure. Should skip pad closure?: {skip_pad_closure}')
        if not skip_pad_closure:
            self.transition_fn.do_pad_closure(self.initial_states,
                                              list(self.final_states))
            logger.debug('Padding closure done.')
        else:
            logger.debug('Skipping padding closure.')

        self.used_variables.remove(var)

        if not self.used_variables:
            logger.info('After the projection there are no more variables used by the MTBDD NFA - performing reduction to a trivial automaton.')
            model = self.find_some_model()
            logger.info(f'Does the automaton have a model? model={model}')

            if model is None:
                logger.info('Returning trivial rejecting automaton.')
                return MTBDD_NFA.trivial_nonaccepting(self.alphabet)
            else:
                logger.info('Returning trivial accepting automaton.')
                return MTBDD_NFA.trivial_accepting(self.alphabet)

        self.applied_operations_info.append('projection')
        return self

    @staticmethod
    def trivial_nonaccepting(alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        '''Creates a new NFA backed by MTBDDs that contains only one state (that is initial
        and not final) and has loop to self over all alphabet symbols.

        Params:
            alphabet - The lsbf alphabet for the created automaton.
        Returns:
            The created (trivial) mtbdd automaton.
        @TODO: Can we somehow get merge the trivial automatons of plain NFA with ours?
        '''
        nfa = MTBDD_NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)
        nfa.add_state(0)
        nfa.add_initial_state(0)
        universal_symbol = tuple(['*'] * len(alphabet.variable_numbers))
        nfa.update_transition_fn(0, universal_symbol, 0)
        nfa.used_variables = []
        return nfa

    @staticmethod
    def trivial_accepting(alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        '''Creates a new NFA backed by MTBDDs that contains only one state (that is initial
        and and **final**) and has loop to self over all alphabet symbols.

        Params:
            alphabet - The lsbf alphabet for the created automaton.
        Returns:
            The created (trivial) mtbdd automaton.
        '''
        nfa = MTBDD_NFA.trivial_nonaccepting(alphabet)
        nfa.add_final_state(0)  # Just toggle the finality of the rejecting state
        return nfa

    def find_some_model(self) -> Optional[Tuple[List[LSBF_AlphabetSymbol], List[int]]]:
        '''Runs DFS on this automaton searching for a model.

        Returns:
             //- A tuple containing the model (word over alphabet) and a list of states that would be traversed or
            -
             \\- None, if the automaton has no model (DFS search failed).
        '''
        stack: List[Tuple[int, List[Tuple[Union[int, str]]]]] = list(map(lambda state: (state, []), self.initial_states))
        states_already_visited: Set[int] = set()
        state_predecesors: Dict[int, int] = {}
        while stack:
            current_state, path = stack.pop(-1)
            if current_state in self.final_states:
                # We have found the a model, reconstruct the visited states
                states_remaining = len(path)
                visited_states_along_path = [current_state]
                rev_traversal_state = current_state
                for _ in range(states_remaining):
                    predecesor = state_predecesors[rev_traversal_state]
                    visited_states_along_path.append(predecesor)
                    rev_traversal_state = predecesor
                return (path, list(reversed(visited_states_along_path)))

            states_already_visited.add(current_state)
            reachable_state_symbol_pairs = self.transition_fn.get_state_post_with_some_symbol(current_state)
            for reachable_state, transition_symbol in reachable_state_symbol_pairs:
                if reachable_state in states_already_visited:
                    continue  # Skip the state we did already visit

                new_path = path + [transition_symbol]
                stack.append((reachable_state, new_path))
                state_predecesors[reachable_state] = current_state
        return None

    def is_sat(self) -> Tuple[bool, List[LSBF_AlphabetSymbol]]:
        model = self.find_some_model()
        if model:
            return (True, model[0])
        return (False, [])

    def get_visualization_representation(self) -> AutomatonVisRepresentation:

        '''Returns a structure carrying all necessary information to visualize this automaton.'''
        # Most of the information is already present, the only thing remaining
        # is to collect the transition function stored within the mtbdds.
        def replace_dont_care_bits_with_star(symbol):
            new_symbol = list(symbol)
            for i, bit in enumerate(symbol):
                if bit == 2:
                    new_symbol[i] = '*'
            return tuple(new_symbol)

        transitions: Dict[Tuple[int, int], List] = defaultdict(list)
        for compressed_transition in self.transition_fn.iter_compressed():
            origin, compressed_symbol, dest = compressed_transition
            compressed_vis_symbol = replace_dont_care_bits_with_star(compressed_symbol)
            transitions[(origin, dest)].append(compressed_vis_symbol)

        vis_transitions = []  # Visualization transitions
        for state_pair, transition_symbols in transitions.items():
            vis_transitions.append((state_pair[0], transition_symbols, state_pair[1]))
        return AutomatonVisRepresentation(
            initial_states=set(self.initial_states),
            final_states=set(self.final_states),
            states=set(self.states),
            transitions=vis_transitions,
            variable_names=self.alphabet.variable_numbers
        )

    def remove_nonfinishing_states(self):
        '''Removes states from which is not reachable any acceptable state.'''
        logger.debug('Removing automaton nonfinishing states.')
        mtbdd_transition_fn: MTBDDTransitionFn = self.transition_fn  # type: ignore
        adjacency_matrix = mtbdd_transition_fn.build_automaton_adjacency_matrix(self.initial_states)

        logger.debug('Adjacency matrix built from the MTBDD transition FN, reversing.')

        reversed_adjacency_matrix: Dict[int, Set[int]] = defaultdict(set)
        for origin_state in adjacency_matrix:
            for destination_state in adjacency_matrix[origin_state]:
                reversed_adjacency_matrix[destination_state].add(origin_state)

        logger.debug('Reversed adjacency matrix built, identifying states that do not lead to an accepting state.')

        work_queue = list(self.final_states)  # The final states themselves can always reach themselves
        work_set = set(work_queue)
        states_reaching_accepting_state: Set[int] = set()
        while work_queue:
            current_state = work_queue.pop(-1)
            logger.debug(f'Nonfinishing states removal: The number of states in the work queue: {len(work_queue)}')
            work_set.remove(current_state)
            states_reaching_accepting_state.add(current_state)

            # Take the PRE of current state and add it to the work queue
            for pre_state in reversed_adjacency_matrix[current_state]:
                # Note that if there is a self loop on current state it will
                # not be added as it already is in the processed states set
                if pre_state not in states_reaching_accepting_state and pre_state not in work_set:
                    work_queue.append(pre_state)
                    work_set.add(pre_state)

        states_removed = self.states - states_reaching_accepting_state

        logger.debug('Removing nonfinishing states from the MTBDD transitions.')
        logger.debug(f'Removed {len(states_removed)} out of {len(self.states)}.')

        self.transition_fn.remove_states(states_removed)
        self.states = states_reaching_accepting_state


@dataclass
class AutomatonSnapshot:
    states:         Set[int]
    final_states:   Set[int]
    initial_states: Set[int]
    transitions:    List[Tuple[Any, Any, Any]]

    @staticmethod
    def create_snapshot(nfa: NFA) -> AutomatonSnapshot:
        initial_states = set(nfa.initial_states)
        final_states = set(nfa.final_states)
        states = set(nfa.states)
        transitions = list(nfa.transition_fn.iter())
        return AutomatonSnapshot(states, final_states, initial_states, transitions)


DFA = NFA
