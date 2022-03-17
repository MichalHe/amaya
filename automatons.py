from __future__ import annotations
from collections import defaultdict
from dataclasses import (
    dataclass,
    field
)
import functools
from enum import IntFlag
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
)

from alphabet import (
    LSBF_Alphabet,
    LSBF_AlphabetSymbol
)
import automaton_algorithms
from log import logger
from transitions import (
    calculate_variable_bit_position,
    SparseSimpleTransitionFunction
)
from utils import (
    carthesian_product,
    create_enumeration_state_translation_map,
)
from visualization import AutomatonVisRepresentation


class AutomatonType(IntFlag):
    DFA = 0x01
    NFA = 0x02
    TRIVIAL = 0x04
    BOOL = 0x08


@dataclass
class NFA(object):
    alphabet:       LSBF_Alphabet
    automaton_type: AutomatonType = AutomatonType.NFA
    transition_fn:  SparseSimpleTransitionFunction = field(default_factory=SparseSimpleTransitionFunction)
    initial_states: Set[int] = field(default_factory=set)
    final_states:   Set[int] = field(default_factory=set)
    states:         Set[int] = field(default_factory=set)
    state_labels:   Dict[int, Any] = field(default_factory=dict)
    extra_info:     Dict[Any, Any] = field(default_factory=dict)

    # Debug handle to listen to any state renaming happening during
    # intersecion/union; takes (automaton_id: int, old_state: int, new_state: int)
    _debug_state_rename: Optional[Callable[[int, int, int], None]] = None

    used_variables: List[int] = field(default_factory=list)
    """Variable IDs that are free in the formula represented by this automaton."""

    def update_transition_fn(self, from_state: int, via_symbol: LSBF_AlphabetSymbol, to_state: int):
        self.transition_fn.insert_transition(from_state, via_symbol, to_state)

    def add_state(self, state: int):
        self.states.add(state)

    def add_final_state(self, state: int):
        self.final_states.add(state)

    def add_initial_state(self, state: int):
        self.initial_states.add(state)

    def has_state_with_value(self, state: int) -> bool:
        return state in self.states

    def has_final_state_with_value(self, value: int) -> bool:
        return value in self.final_states

    def get_transition_target(self, origin: int, via_symbol: LSBF_AlphabetSymbol) -> Tuple[int, ...]:
        # FIXME: Remove this cast.
        # TODO: Rename this function to be get post or similar
        return tuple(self.transition_fn.get_transition_target(origin, via_symbol))

    def intersection(self, other: NFA, remove_nonfinishing_states: bool = True):
        """
        Construct automaton accepting the intersection of the languages of this and the other automaton.
        """
        assert self.alphabet == other.alphabet

        logger.info('Performing automaton intesection. Input automaton sizes: {0} states other {1} states'.format(
            len(self.states), len(other.states)))

        resulting_nfa: NFA = NFA(alphabet=self.alphabet, automaton_type=AutomatonType.NFA)

        used_variable_ids = sorted(set(self.used_variables + other.used_variables))
        projected_alphabet = list(self.alphabet.gen_projection_symbols_onto_variables(used_variable_ids))

        logger.debug('Automata use the following variables: self={0} other={1} result={2}'.format(
            self.used_variables,
            other.used_variables,
            used_variable_ids
        ))

        # Add all the initial states to the to-be-processed queue
        work_queue: List[Tuple[int, int]] = carthesian_product(self.initial_states, other.initial_states)
        labels_to_state_number: Dict[Tuple[int, int], int] = dict(
            (state, i) for i, state in enumerate(work_queue)
        )

        for initial_state in work_queue:
            state_number = labels_to_state_number[initial_state]
            resulting_nfa.add_initial_state(state_number)

        states_processed_cnt = 0
        while work_queue:
            current_state_label: Tuple[int, int] = work_queue.pop(-1)
            # Product states have their numbers assigned as their are discovered during the intersection procedure
            current_state: int = labels_to_state_number[current_state_label]

            resulting_nfa.add_state(current_state)

            logger.debug(f'Processed state {current_state_label}, remaining in queue {len(work_queue)}')

            self_state, others_state = current_state_label

            # Check whether the product state is final (both components are final in corresponding automata)
            if (self_state in self.final_states and others_state in other.final_states):
                resulting_nfa.add_final_state(current_state)

            has_self_state_out_transitions = bool(self.transition_fn.get_state_post(self_state))
            has_other_state_out_transitions = bool(other.transition_fn.get_state_post(others_state))

            if has_self_state_out_transitions and has_other_state_out_transitions:
                for projected_symbol in projected_alphabet:
                    cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(used_variable_ids,
                                                                                                projected_symbol)
                    self_destination_set = self.get_transition_target(self_state, cylindrified_symbol)
                    other_destination_set = other.get_transition_target(others_state, cylindrified_symbol)

                    for next_state_label in carthesian_product(self_destination_set, other_destination_set):
                        if next_state_label in labels_to_state_number:
                            next_state = labels_to_state_number[next_state_label]
                        else:
                            next_state = len(labels_to_state_number) + 1
                            labels_to_state_number[next_state_label] = next_state

                        resulting_nfa.update_transition_fn(current_state, cylindrified_symbol, next_state)

                        if not resulting_nfa.has_state_with_value(next_state) and next_state_label not in work_queue:
                            work_queue.append(next_state_label)

            states_processed_cnt += 1

        resulting_nfa.used_variables = used_variable_ids
        for label, state in labels_to_state_number.items():
            self_state, other_state = label
            self_state_label = self.state_labels.get(self_state, self_state)
            other_state_label = other.state_labels.get(other_state, other_state)
            resulting_nfa.state_labels[state] = (self_state_label, other_state_label)

        if remove_nonfinishing_states:
            resulting_nfa.remove_nonfinishing_states()

        assert resulting_nfa.used_variables
        logger.info('Intersection done. States processed: %d. Result has %d states.',
                    states_processed_cnt,
                    len(resulting_nfa.states))
        return resulting_nfa

    def union(self, other: NFA) -> NFA:
        if self.alphabet != other.alphabet:
            assert False

        latest_state_value, self_renamed = self.rename_states()
        _, other_renamed = other.rename_states(start_from=latest_state_value)

        states = self_renamed.states.union(other_renamed.states)
        transitions = SparseSimpleTransitionFunction.union_of(self_renamed.transition_fn, other_renamed.transition_fn)
        initial_states = self_renamed.initial_states.union(other_renamed.initial_states)
        final_states = self_renamed.final_states.union(other_renamed.final_states)

        union_nfa = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA,
            initial_states=initial_states,
            final_states=final_states,
            states=states,
            transition_fn=transitions
        )
        union_nfa.used_variables = sorted(set(self.used_variables + other.used_variables))

        return union_nfa

    def determinize(self) -> DFA:
        """
        Constructs a DFA having the same language as this automaton (standard subset construction).
        """

        # FIXME: This should map the states to int right away so that all automata have the same state type
        work_list: List[Tuple[int, ...]] = [tuple(sorted(self.initial_states))]

        determinized_automaton: DFA = DFA(alphabet=self.alphabet, automaton_type=AutomatonType.DFA)
        label_to_state_number: Dict[Tuple[int, ...], int] = {work_list[0]: 0}
        determinized_automaton.add_initial_state(0)  # As there is only one initial state we know its label

        projected_alphabet_symbols = list(self.alphabet.gen_projection_symbols_onto_variables(self.used_variables))

        while work_list:
            current_metastate_label: Tuple[int, ...] = work_list.pop(-1)
            current_metastate = label_to_state_number[current_metastate_label]

            logger.debug(f'Determinization for {current_metastate}, remaining in work queue: {len(work_list)}')

            determinized_automaton.add_state(current_metastate)

            if not self.final_states.isdisjoint(current_metastate_label):
                determinized_automaton.add_final_state(current_metastate)

            for symbol in projected_alphabet_symbols:
                reachable_states: List[int] = []

                cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(self.used_variables,
                                                                                            symbol)
                for state in current_metastate_label:
                    # Get all states reacheble from current state via symbol
                    out_states = self.get_transition_target(state, cylindrified_symbol)
                    reachable_states.extend(out_states)

                if not reachable_states:
                    continue

                next_metastate_label: Tuple[int, ...] = tuple(sorted(set(reachable_states)))

                if next_metastate_label in label_to_state_number:
                    next_metastate_num = label_to_state_number[next_metastate_label]
                else:
                    next_metastate_num = len(label_to_state_number)
                    label_to_state_number[next_metastate_label] = next_metastate_num

                if not determinized_automaton.has_state_with_value(next_metastate_num):
                    if next_metastate_label not in work_list:
                        work_list.append(next_metastate_label)

                determinized_automaton.update_transition_fn(current_metastate, cylindrified_symbol, next_metastate_num)

        determinized_automaton.used_variables = sorted(self.used_variables)

        for label, state in label_to_state_number.items():
            rich_label = tuple(self.state_labels.get(component, component) for component in label)
            determinized_automaton.state_labels[state] = rich_label

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

        def translate(state: int) -> int:
            return state_name_translation[state]

        self.states = set(map(translate, self.states))
        self.initial_states = set(map(translate, self.initial_states))
        self.final_states = set(map(translate, self.final_states))

        self.transition_fn.rename_states(state_name_translation)

    def do_projection(self, variable_id: int, skip_pad_closure: bool = False) -> Optional[NFA]:
        # FIXME: This cannot return None, fix the type
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
            new_nfa = NFA(alphabet=self.alphabet, automaton_type=AutomatonType.NFA)

            new_nfa.states = set(self.states)
            new_nfa.initial_states = set(self.initial_states)
            new_nfa.final_states = set(self.final_states)

            bit_pos = calculate_variable_bit_position(self.alphabet.variable_numbers, variable_id)
            if bit_pos is None:
                raise ValueError(f'Could not find variable_name "{variable_id}" in current alphabet {self.alphabet}')

            new_nfa.transition_fn = self.transition_fn
            new_nfa.transition_fn.project_bit_away(bit_pos)

            if not skip_pad_closure:
                new_nfa.perform_pad_closure()

            new_used_vars = list(self.used_variables)
            new_used_vars.remove(variable_id)
            new_nfa.used_variables = new_used_vars
            return new_nfa

    def perform_pad_closure(self):
        '''Performs inplace padding closure. See file automaton_algorithms.py:padding_closure'''
        automaton_algorithms.pad_closure2(self)

    def get_symbols_leading_from_state_to_state(self, from_state: int, to_state: int) -> Set[LSBF_AlphabetSymbol]:
        return self.transition_fn.get_symbols_between_states(from_state, to_state)

    def rename_states(self, start_from: int = 0) -> Tuple[int, NFA]:
        nfa = NFA(alphabet=self.alphabet, automaton_type=self.automaton_type)

        debug_fn: Optional[functools.partial[None]]
        if self._debug_state_rename is not None:
            debug_fn = functools.partial(self._debug_state_rename, id(self))
        else:
            debug_fn = None

        hightest_state, state_name_translation = create_enumeration_state_translation_map(self.states,
                                                                                          debug_fn,
                                                                                          start_from=start_from)

        def translate(state: int) -> int:
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
        result = NFA(alphabet=self.alphabet, automaton_type=self.automaton_type)

        result.initial_states = set(self.initial_states)
        result.states = set(self.states)

        # FIXME: The trivial automata are handled the same way as normal, remove this
        if self.automaton_type & AutomatonType.TRIVIAL:
            result.final_states = result.initial_states - self.final_states
        else:
            result.final_states = self.states - self.final_states

        result.transition_fn = self.transition_fn.copy()

        result.used_variables = sorted(self.used_variables)
        return result

    def is_sat(self) -> Tuple[bool, List[LSBF_AlphabetSymbol]]:
        if not self.used_variables:
            if self.final_states:
                return (True, [])
            else:
                return (False, [])

        # Implementation of DFS for a determinized automaton
        state_stack: List[int] = list(self.initial_states)
        traversal_history: Dict[int, int] = dict()

        explored_states: Set[int] = set()
        used_word: List[LSBF_AlphabetSymbol] = list()

        while state_stack:
            current_state = state_stack.pop(-1)

            explored_states.add(current_state)

            if current_state in self.final_states:
                used_word = self.transition_fn.calculate_path_from_dfs_traversal_history(
                    traversal_history, current_state, self.initial_states)

                # The NFA cannot accept empty words - that happens when after
                # determinization and complement some of the initial states
                # becomes accepting
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
        assert state in self.states, f'Cannot retrieve post of non automaton state: {state}'
        return self.transition_fn.get_state_post(state)

    @staticmethod
    def trivial_accepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa = NFA.trivial_nonaccepting(alphabet)
        nfa.add_final_state(0)
        return nfa

    @staticmethod
    def trivial_nonaccepting(alphabet: LSBF_Alphabet) -> NFA:
        nfa = NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)

        state = 0
        nfa.add_state(state)
        nfa.add_initial_state(state)

        self_loop_symbol = tuple('*' for i in len(alphabet.variable_numbers))
        nfa.update_transition_fn(state, self_loop_symbol, state)

        return nfa

    @classmethod
    def for_bool_variable(cls, overall_alphabet: LSBF_Alphabet, var_id: int, var_value: bool):
        """
        Builds an automaton accepting words representing the given bool variable having given value.

        The accepted words for a variable being True have only 1s (at least one), and similarly, all 0s for
        the variable being False.
        The resulting autmaton is not complete (must be completed before complement).
        """

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
        """Retrieves the information necessary to visualize this automaton."""

        # The transition information needed is already stored in the correct form
        # inside the transition function, however it might change in the future
        # - so we use iter() and reconstruct the information.
        _transitions = defaultdict(list)
        for origin_state, symbol, destination_state in self.transition_fn.iter():
            _transitions[(origin_state, destination_state)].append(symbol)

        transitions = []
        for state_pair, symbols in _transitions.items():
            transitions.append((state_pair[0], symbols, state_pair[1]))

        var_ids: List[int] = tuple(self.alphabet.variable_numbers)
        var_names: Tuple[str] = tuple(self.alphabet.variable_names[var_id] for var_id in var_ids)

        return AutomatonVisRepresentation(
            states=set(self.states),
            final_states=set(self.final_states),
            initial_states=set(self.initial_states),
            variable_names=var_names,
            variable_ids=var_ids,
            transitions=transitions,
            state_labels=self.state_labels
        )

    def minimize(self) -> NFA:
        """Minimize using the Brzozowski NFA minimization procedure."""

        def reverse_automaton(nfa: NFA) -> NFA:
            """Reverse the automaton. Resulting NFA accepts the reverse language."""
            reverse_nfa: NFA = NFA(nfa.alphabet, AutomatonType.NFA)
            reverse_nfa.states = set(nfa.states)
            reverse_nfa.initial_states = set(nfa.final_states)
            reverse_nfa.final_states = set(nfa.initial_states)
            reverse_nfa.used_variables = sorted(nfa.used_variables)

            for source, symbol, destination in nfa.transition_fn.iter():
                reverse_nfa.update_transition_fn(destination, symbol, source)
            return reverse_nfa

        logger.info(
            'Performing Brzozowski minimalization, input size: {0}. Reversing the automaton.'.format(
                len(self.states)))

        reverse_nfa = reverse_automaton(self)

        logger.info('Determinizing the reversed automaton.')
        determinized_reverse_nfa = reverse_nfa.determinize()
        logger.info(f'Determinized reversed automaton size: {len(determinized_reverse_nfa.states)}.')

        logger.info('Reversing the resulting DFA.')

        nfa = reverse_automaton(determinized_reverse_nfa)
        logger.info(f'Automaton size: {len(nfa.states)}.')

        logger.info('Determinizing the automaton.')
        minimal_dfa = nfa.determinize()
        logger.info(f'Automaton size: {len(minimal_dfa.states)}')

        return minimal_dfa

    def hopcroft_minimization(self) -> NFA:
        """
        Minimizes the automaton using the Hopcroft minimization.

        Requires the automaton to be deterministic.
        """
        assert self.automaton_type == AutomatonType.DFA

        partitions = {tuple(sorted(self.final_states)), tuple(sorted(self.states - self.final_states))}
        work_list = list(partitions)

        alphabet_symbols = tuple(self.alphabet.gen_projection_symbols_onto_variables(sorted(self.used_variables)))

        while work_list:
            current_partition = work_list.pop(-1)
            for symbol in alphabet_symbols:
                X = set()  # Set of all states that can reach current partition via symbol
                for state in current_partition:
                    state_pre = self.transition_fn.get_state_pre_with_symbol(state, symbol)
                    X.update(state_pre)

                for partition in tuple(partitions):
                    Y = set(partition)
                    intersect = X.intersection(Y)
                    difference = Y - X
                    if not intersect or not difference:
                        # The partition split results in one empty set - no refinement can be gained
                        continue

                    intersect_partition = tuple(sorted(intersect))
                    difference_partition = tuple(sorted(difference))

                    # Refine the current partition into intersect and difference as we know that these sets
                    # of states are not equivalent
                    partitions.remove(partition)
                    partitions.add(intersect_partition)
                    partitions.add(difference_partition)

                    # Check whether the partition we've just refined is a yet-to-be processed distinguisher
                    if partition in work_list:
                        # partition has just became obsole - replace it by the two new distinguishers
                        work_list.remove(partition)
                        work_list.append(intersect_partition)
                        work_list.append(difference_partition)
                    else:
                        # It is sufficient to use only the smaller of the new distinguishers
                        work_list.append(
                            intersect_partition if len(intersect) < len(difference) else difference_partition
                        )

        minimized_nfa = NFA(automaton_type=AutomatonType.DFA,
                            alphabet=self.alphabet,
                            used_variables=self.used_variables)
        partition_enumeration: Dict[Tuple[int, ...], int] = dict((part, i) for i, part in enumerate(partitions))
        minimized_nfa.states = set(partition_enumeration.values())

        original_state_to_partition: Dict[int, Tuple[int, ...]] = {}
        for partition in partitions:
            for state in partition:
                original_state_to_partition[state] = partition

        for partition in partitions:
            min_state = partition_enumeration[partition]
            partition_state = next(iter(partition))

            for symbol, dest_state in self.transition_fn.get_out_transitions_for_state(partition_state):
                dest_partition = original_state_to_partition[dest_state]
                dest_min_state = partition_enumeration[dest_partition]

                minimized_nfa.update_transition_fn(min_state, symbol, dest_min_state)

            if partition_state in self.final_states:
                minimized_nfa.add_final_state(min_state)

            for state in partition:
                if state in self.initial_states:
                    minimized_nfa.add_initial_state(min_state)
                    break

        return minimized_nfa


@dataclass
class AutomatonSnapshot:
    """
    Debug class representing the automaton in an explicit manner.

    Designed to allow for snapshoting the structure before and after some operation and inspecting the changes.
    """
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

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, AutomatonSnapshot):
            return False

        return all((
            self.states == other.states,
            self.final_states == other.final_states,
            self.initial_states == self.initial_states,
            sorted(self.transitions) == sorted(other.transitions),
        ))

DFA = NFA
