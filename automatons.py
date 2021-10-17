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
    Generic,
    Optional,
    Callable,
    Union,
    Any
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

        logger.info('Performing automaton intesection. Input automaton sizes: {0} states other {1} states'.format(
            len(self.states), len(other.states)))

        self_renamed_highest_state, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=self_renamed_highest_state)

        resulting_nfa: NFA[Tuple[int, int]] = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA
        )

        used_variable_ids = sorted(set(self.used_variables + other.used_variables))
        projected_alphabet = list(self.alphabet.gen_projection_symbols_onto_variables(used_variable_ids))

        logger.debug('Automata use the following vvariables: self={0} other={1} result={2}'.format(
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
        logger.info(f'Intersection done. Result has {len(resulting_nfa.states)} states.')
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
