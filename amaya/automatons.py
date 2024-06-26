from __future__ import annotations
from collections import defaultdict
from dataclasses import (
    dataclass,
    field
)
import functools
from enum import IntFlag, IntEnum
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from amaya import logger
from amaya.alphabet import (
    LSBF_Alphabet,
    LSBF_AlphabetSymbol,
    uncompress_transition_symbol
)
from amaya.config import (
    solver_config,
    SolutionDomain,
)
from amaya.relations_structures import Var
from amaya.transitions import (
    calculate_variable_bit_position,
    SparseSimpleTransitionFunction
)
from amaya.utils import (
    carthesian_product,
)
from amaya.visualization import (
    AutomatonVisRepresentation,
)
import amaya.semantics_tracking as state_semantics_lib
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType,
    AH_Determinization,
    AH_Intersection,
    AH_Minimization,
    AH_Negation,
    AH_Node,
    AH_Projection,
    AH_Union,
)


class AutomatonType(IntFlag):
    DFA = 0x01
    NFA = 0x02
    TRIVIAL = 0x04
    BOOL = 0x08


@dataclass
class NFA:
    alphabet:        LSBF_Alphabet
    state_semantics: AH_Node

    automaton_type: AutomatonType = AutomatonType.NFA
    transition_fn:  SparseSimpleTransitionFunction = field(default_factory=SparseSimpleTransitionFunction)
    initial_states: Set[int] = field(default_factory=set)
    final_states:   Set[int] = field(default_factory=set)
    states:         Set[int] = field(default_factory=set)
    extra_info:     Dict[Any, Any] = field(default_factory=dict)

    operation_id:   int = -1

    # Debug handle to listen to any state renaming happening during
    # intersecion/union; takes (automaton_id: int, old_state: int, new_state: int)
    _debug_state_rename: Optional[Callable[[int, int, int], None]] = None

    used_variables: List[Var] = field(default_factory=list)
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
        # TODO: Rename this function to be get post or similar
        return self.transition_fn.get_transition_target(origin, via_symbol)

    def intersection(self, other: NFA, remove_nonfinishing_states: bool = True) -> NFA:
        """
        Construct automaton accepting the intersection of the languages of this and the other automaton.
        """
        assert self.alphabet == other.alphabet

        if not self.final_states or not other.final_states:
            return self.trivial_nonaccepting(self.alphabet)

        logger.info('Performing automaton intesection. Input automaton sizes: {0} states other {1} states'.format(
            len(self.states), len(other.states)))

        resulting_nfa: NFA = NFA(alphabet=self.alphabet, automaton_type=AutomatonType.NFA, state_semantics=AH_Intersection(children=()))

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

            logger.debug('Processed state %s, remaining in queue %s', current_state_label, len(work_queue))

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

        if remove_nonfinishing_states:
            resulting_nfa.remove_nonfinishing_states()

        if solver_config.track_state_semantics:
            state_id_to_label = {state_id: label for label, state_id in labels_to_state_number.items()}
            resulting_nfa.state_semantics = state_semantics_lib.construct_flattened_intersection_semantics(state_id_to_label,
                                                                                                           self.state_semantics,
                                                                                                           other.state_semantics)
        assert resulting_nfa.used_variables
        logger.info('Intersection done. States processed: %d. Result has %d states (initial=%d, final=%d).',
                    states_processed_cnt, len(resulting_nfa.states), len(resulting_nfa.initial_states), len(resulting_nfa.final_states))
        return resulting_nfa

    def union(self, other: NFA) -> NFA:
        """Construct an automaton accepting the union languages of this automaton and the other."""
        assert self.alphabet == other.alphabet

        logger.info('Performing NFA union: operand1 has %d states, operand2 has %d states.', len(self.states), len(other.states))

        # Rename states to avoid aliasing as the automata can have equally named states
        # NOTE: Renaming does not modify state semantics - it break state labeling maps, however it does not matter as the renaming
        #       information will be folded in into the AH_Union node of the resulting automaton
        old_self_state_to_new_state_map, self_renamed = self.rename_states()
        old_other_state_to_new_state_map, other_renamed = other.rename_states(start_from=len(old_self_state_to_new_state_map))

        states = self_renamed.states.union(other_renamed.states)
        transitions = SparseSimpleTransitionFunction.union_of(self_renamed.transition_fn, other_renamed.transition_fn)
        initial_states = self_renamed.initial_states.union(other_renamed.initial_states)
        final_states = self_renamed.final_states.union(other_renamed.final_states)

        # Create state semantics for the union automaton based on the inputs
        labels = {}
        if solver_config.track_state_semantics:
            labels = {new_state: (0, original_state) for original_state, new_state in old_self_state_to_new_state_map.items()}
            labels.update((new_state, (1, original_state)) for original_state, new_state in old_other_state_to_new_state_map.items())
        state_semantics = AH_Union(state_labels=labels, children=(self.state_semantics, other.state_semantics))

        union_nfa = NFA(
            alphabet=self.alphabet,
            automaton_type=AutomatonType.NFA,
            initial_states=initial_states,
            final_states=final_states,
            states=states,
            transition_fn=transitions,
            state_semantics=state_semantics
        )
        union_nfa.used_variables = sorted(set(self.used_variables + other.used_variables))

        return union_nfa

    def determinize(self) -> DFA:
        """
        Constructs a DFA having the same language as this automaton (standard subset construction).
        """

        work_list: List[Tuple[int, ...]] = [tuple(sorted(self.initial_states))]

        determinized_automaton: DFA = DFA(alphabet=self.alphabet, automaton_type=AutomatonType.DFA, state_semantics=AH_Determinization(child=self.state_semantics))
        macrostate_to_id_map: Dict[Tuple[int, ...], int] = {work_list[0]: 0}
        determinized_automaton.add_initial_state(0)  # As there is only one initial state we know its label

        projected_alphabet_symbols = list(self.alphabet.gen_projection_symbols_onto_variables(self.used_variables))

        while work_list:
            current_macrostate: Tuple[int, ...] = work_list.pop(-1)
            current_macrostate_id = macrostate_to_id_map[current_macrostate]

            logger.debug('Determinization for %s, remaining in work queue: %s', current_macrostate_id, len(work_list))

            determinized_automaton.add_state(current_macrostate_id)

            if not self.final_states.isdisjoint(current_macrostate):
                determinized_automaton.add_final_state(current_macrostate_id)

            for symbol in projected_alphabet_symbols:
                reachable_states: List[int] = []

                cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(self.used_variables,
                                                                                            symbol)
                for state in current_macrostate:
                    # Get all states reacheble from current state via symbol
                    out_states = self.get_transition_target(state, cylindrified_symbol)
                    reachable_states.extend(out_states)

                if not reachable_states:
                    continue

                next_macrostate_label: Tuple[int, ...] = tuple(sorted(set(reachable_states)))

                if next_macrostate_label in macrostate_to_id_map:
                    next_macrostate_num = macrostate_to_id_map[next_macrostate_label]
                else:
                    next_macrostate_num = len(macrostate_to_id_map)
                    macrostate_to_id_map[next_macrostate_label] = next_macrostate_num

                if not determinized_automaton.has_state_with_value(next_macrostate_num):
                    if next_macrostate_label not in work_list:
                        work_list.append(next_macrostate_label)

                determinized_automaton.update_transition_fn(current_macrostate_id, cylindrified_symbol, next_macrostate_num)

        determinized_automaton.used_variables = sorted(self.used_variables)

        if solver_config.track_state_semantics:
            macrostate_id_to_macrostate = {macrostate_id: macrostate for macrostate, macrostate_id in macrostate_to_id_map.items()}
            determinized_automaton.state_semantics.state_labels = macrostate_id_to_macrostate

        determinized_automaton.add_trap_state()
        return determinized_automaton

    def add_trap_state(self):
        """
        Augments the automaton structure with a trapstate, making this DFA a complete one.

        A complete DFA has a run for every given word. If there is no run for a given word in the orignal
        DFA, this function adds it so that it leads to a trapstate that has an universal self loop.

        The automaton should be deterministic.
        """
        assert self.automaton_type & AutomatonType.DFA, 'Cannot add a trap state to a nondeterministic automaton.'

        trap_state = max(self.states) + 1
        trap_state_added = self.transition_fn.complete_with_trap_state(self.alphabet, self.used_variables,
                                                                       self.states, trap_state)
        if trap_state_added:
            self.states.add(trap_state)

    def do_projection(self, var: Var, skip_pad_closure: bool = False) -> NFA:
        """
        Project away the given variable track.

        :param variable_id: ID of variable of which should the corresponding tape track be projected away.
        :param skip_pad_closure: Skip pad_closure after the projection has been performed.
        :returns: NFA with the given variable track projected away.
        """
        resulting_alphabet_var_count = len(self.used_variables) - 1

        if resulting_alphabet_var_count == 0:
            logger.info('Projecting away the last variable for automaton - performing DFS search for a model.')
            is_sat = self.find_model() is not None  # Check whether the language is nonempty
            logger.info(f'Was model found? {is_sat}')
            return NFA.trivial_accepting(self.alphabet) if is_sat else NFA.trivial_nonaccepting(self.alphabet)
        else:
            # Cross out the projected variable
            new_nfa = NFA(alphabet=self.alphabet, automaton_type=AutomatonType.NFA,
                          state_semantics=AH_Projection(child=self.state_semantics, states_added_in_pad_closure=set()))

            new_nfa.states = set(self.states)
            new_nfa.initial_states = set(self.initial_states)
            new_nfa.final_states = set(self.final_states)

            # Assumes that the variables are kept sorted - does not perform sorting again
            new_used_vars = [used_var for used_var in self.used_variables if used_var != var]
            new_nfa.used_variables = new_used_vars

            bit_pos = calculate_variable_bit_position(self.alphabet.all_vars, var)
            if bit_pos is None:
                raise ValueError(f'Could not find variable_name "{var}" in current alphabet {self.alphabet}')

            new_nfa.transition_fn = self.transition_fn
            new_nfa.transition_fn.project_bit_away(bit_pos)

            states_added_in_pad_closure = set()
            if not skip_pad_closure:
                maybe_state_added_in_pad_closure = new_nfa.perform_pad_closure()
                if maybe_state_added_in_pad_closure:
                    states_added_in_pad_closure.add(maybe_state_added_in_pad_closure)

            labels = {state: state for state in self.states}
            new_nfa.state_semantics = AH_Projection(child=self.state_semantics, states_added_in_pad_closure=states_added_in_pad_closure)
            return new_nfa

    def perform_pad_closure(self) -> Optional[int]:
        """Performs inplace padding closure. See file automaton_algorithms.py:padding_closure"""
        logger.info('Performing padding closure.')
        if solver_config.solution_domain == SolutionDomain.INTEGERS:
            added_final_state = automaton_algorithms.pad_closure2(self)
        else:
            added_final_state = automaton_algorithms.pad_closure2_naturals(self)
        logger.info('Pad closure done.')
        return added_final_state

    def get_symbols_leading_from_state_to_state(self, from_state: int, to_state: int) -> Set[LSBF_AlphabetSymbol]:
        return self.transition_fn.get_symbols_between_states(from_state, to_state)

    def rename_states(self, start_from: int = 0) -> Tuple[Dict[int, int], NFA]:
        """
        Rename the state of this automaton to integers starting from `start_from` assigning states a new unique number.

        :param start_from: The integer value given to the first renamed state.
        """

        # Create a dictionary mapping the old states to new numbers
        next_state_name = start_from
        state_to_new_name: Dict[int, int] = {}
        for state in self.states:
            if self._debug_state_rename:
                self._debug_state_rename(id(self), state, next_state_name)  # Emit debug info about state new name

            state_to_new_name[state] = next_state_name
            next_state_name += 1

        nfa = NFA(alphabet=self.alphabet,
                  automaton_type=self.automaton_type,
                  states=set(state_to_new_name[state] for state in self.states),
                  initial_states=set(state_to_new_name[state] for state in self.initial_states),
                  final_states=set(state_to_new_name[state] for state in self.final_states),
                  state_semantics=self.state_semantics)

        nfa.transition_fn = self.transition_fn.copy()
        nfa.transition_fn.rename_states(state_to_new_name)

        return (state_to_new_name, nfa)

    def complement(self) -> NFA:
        """
        Construct automaton accepting the complement of the language.

        The underlying automaton must be deterministic and complete in order for the complement to be correct.
        """
        assert self.automaton_type & AutomatonType.DFA, 'Cannot complement nondeterministic automaton'

        result = NFA(alphabet=self.alphabet,
                     automaton_type=self.automaton_type,
                     states=set(self.states),
                     initial_states=set(self.initial_states),
                     final_states=self.states - self.final_states,  # Swap accepting and nonaccepting states
                     used_variables=sorted(self.used_variables),
                     state_semantics=AH_Negation(child=self.state_semantics))

        result.transition_fn = self.transition_fn.copy()

        return result

    def find_model(self) -> Optional[Tuple[LSBF_AlphabetSymbol, ...]]:
        """
        Check whether the language of the automaton is empty using depth first search and return the model if found.
        """
        Word = Tuple[LSBF_AlphabetSymbol, ...]

        states_with_words_to_explore: List[Tuple[int, Word]] = list((q0, tuple()) for q0 in self.initial_states)
        states_to_explore = set(self.initial_states)
        explored_states: Set[int] = set()

        # Use DFS to find an accepting state reachable by a suitable model
        while states_with_words_to_explore:
            current_state, word = states_with_words_to_explore.pop(-1)

            states_to_explore.remove(current_state)
            if word or solver_config.solution_domain == SolutionDomain.NATURALS:
                # Make sure that we consider the initial state as unexplored until it is reached by a non-empty word
                # if solving over integers
                explored_states.add(current_state)

            for destination in self.transition_fn.data.get(current_state, tuple()):
                if destination in explored_states or destination in states_to_explore:
                    # If it was already explored it is needless to explore it again,
                    # if it already is in states to explore, nothing can be gained by creating
                    # a dest_word and adding it again to be explored twice
                    continue

                # Pick arbitrary transition symbol to use
                dest_word = word + (next(iter(self.transition_fn.data[current_state][destination])),)

                if destination in self.final_states:
                    # Automaton language does not contain empty word if solving over integers
                    if solver_config.solution_domain != SolutionDomain.INTEGERS or dest_word:
                        return dest_word

                states_with_words_to_explore.append((destination, dest_word))
                states_to_explore.add(destination)

        return None

    def remove_nonfinishing_states(self):
        """BFS on rotated transitions"""
        reachable_states = self.transition_fn.remove_nonfinishing_states(self.states, self.final_states)
        self.states = reachable_states

    def get_state_post(self, state: int) -> List[int]:
        assert state in self.states, f'Cannot retrieve post of non automaton state: {state}'
        return self.transition_fn.get_state_post(state)

    @classmethod
    def trivial_accepting(cls, alphabet: LSBF_Alphabet) -> NFA:
        nfa = cls(alphabet=alphabet, automaton_type=(AutomatonType.DFA | AutomatonType.TRIVIAL),
                  state_semantics=AH_Atom(atom_type=AH_AtomType.TRIVIAL, atom=None))

        nfa.states = {0, 1}  # There must be two states to not accepts the empty word
        nfa.initial_states = {0}
        nfa.final_states = {1}

        self_loop_symbol = tuple('*' for vn in alphabet.all_vars)
        nfa.update_transition_fn(0, self_loop_symbol, 1)
        nfa.update_transition_fn(1, self_loop_symbol, 1)

        return nfa

    @classmethod
    def trivial_nonaccepting(cls, alphabet: LSBF_Alphabet) -> NFA:
        nfa = cls(alphabet=alphabet, automaton_type=(AutomatonType.DFA | AutomatonType.TRIVIAL),
                  state_semantics=AH_Atom(atom_type=AH_AtomType.TRIVIAL, atom=None))

        nfa.states = {0}
        nfa.initial_states = {0}

        self_loop_symbol = tuple('*' for vn in alphabet.all_vars)
        nfa.update_transition_fn(0, self_loop_symbol, 0)

        return nfa

    @classmethod
    def for_bool_variable(cls, overall_alphabet: LSBF_Alphabet, var: Var, var_value: bool):
        """
        Builds an automaton accepting words representing the given bool variable having given value.

        The accepted words for a variable being True have only 1s (at least one), and similarly, all 0s for
        the variable being False.
        The resulting autmaton is not complete (must be completed before complement).
        """
        automaton_type = AutomatonType.NFA | AutomatonType.BOOL

        nfa = cls(alphabet=overall_alphabet,
                  automaton_type=automaton_type,
                  used_variables=[var],
                  state_semantics=AH_Atom(atom_type=AH_AtomType.BOOL, atom=[]))
        nfa.states = {0, 1}
        nfa.initial_states = {0}
        nfa.final_states = {1}

        transition_symbol = (1, ) if var_value else (0, )
        cylindrified_symbol = overall_alphabet.cylindrify_symbol_of_projected_alphabet([var], transition_symbol)

        nfa.update_transition_fn(0, cylindrified_symbol, 1)
        universal_symbol = tuple('*' for i in range(len(overall_alphabet.all_vars)))
        nfa.update_transition_fn(1, universal_symbol, 1)

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
            if solver_config.vis_display_only_free_vars:
                symbol = tuple(b for i, b in enumerate(symbol) if (i+1) in self.used_variables)
            else:
                symbol = tuple(symbol)
            _transitions[(origin_state, destination_state)].append(symbol)

        transitions = []
        for state_pair, symbols in _transitions.items():
            transitions.append((state_pair[0], symbols, state_pair[1]))

        var_ids = self.used_variables if solver_config.vis_display_only_free_vars else self.alphabet.all_vars
        var_names: Tuple[str, ...] = tuple(str(var.id) for var in var_ids)
        return AutomatonVisRepresentation(
            states=set(self.states),
            final_states=set(self.final_states),
            initial_states=set(self.initial_states),
            variable_names=var_names,
            variable_ids=var_ids,
            transitions=transitions,
            state_semantics=self.state_semantics
        )

    def minimize_brzozowski(self) -> NFA:
        """Minimize using the Brzozowski NFA minimization procedure."""

        def reverse_automaton(nfa: NFA) -> NFA:
            """Reverse the automaton. Resulting NFA accepts the reverse language."""
            reverse_nfa: NFA = NFA(nfa.alphabet, AutomatonType.NFA)
            reverse_nfa.states = set(nfa.states)
            reverse_nfa.initial_states = set(nfa.final_states)
            reverse_nfa.final_states = set(nfa.initial_states)
            reverse_nfa.used_variables = sorted(nfa.used_variables)
            # NOTE: Reversing the automaton breaks the state semantics, however, since we reverse it twice it is OK
            reverse_nfa.state_semantics = nfa.state_semantics

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

    def minimize_hopcroft(self) -> NFA:
        """
        Minimizes the automaton using the Hopcroft minimization.

        Requires the automaton to be deterministic.
        """
        assert self.automaton_type == AutomatonType.DFA

        partitions = {tuple(sorted(self.final_states)), tuple(sorted(self.states - self.final_states))}
        work_list = list(partitions)

        alphabet_symbols = tuple(self.alphabet.gen_projection_symbols_onto_variables(sorted(self.used_variables)))

        def get_transitions_with_sym(sym):
            transitions = []
            for transition in self.transition_fn.iter():
                if transition[1] == sym:
                    transitions.append(transition)
            return transitions


        while work_list:
            current_partition = work_list.pop(-1)
            for symbol in alphabet_symbols:
                X = set()  # Set of all states that can reach the current partition via symbol
                cylindrified_symbol = self.alphabet.cylindrify_symbol_of_projected_alphabet(self.used_variables, symbol)
                for state in current_partition:
                    state_pre = self.transition_fn.get_state_pre_with_symbol(state, cylindrified_symbol)
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

        minimized_dfa = NFA(automaton_type=AutomatonType.DFA,
                            alphabet=self.alphabet,
                            used_variables=self.used_variables,
                            state_semantics=AH_Minimization(child=self.state_semantics))

        state_to_its_partition_map: Dict[int, Tuple[int, ...]] = {}
        for partition in partitions:
            for state in partition:
                state_to_its_partition_map[state] = partition

        initial_state = next(iter(self.initial_states))  # There is only 1 initial state
        partition_containing_initial_state = state_to_its_partition_map[initial_state]
        partitions_to_explore = {partition_containing_initial_state}

        partition_to_state_number_map: Dict[Tuple[int, ...], int] = {partition_containing_initial_state: 0}

        # Partition with the initial state has number 0
        minimized_dfa.states.add(0)
        minimized_dfa.initial_states.add(0)
        next_avaiable_partition_number = 1  # State=0 was already assigned to partition containing the initial state

        explored_partition_labels: Set[int] = set()

        while partitions_to_explore:
            partition = next(iter(partitions_to_explore))
            partitions_to_explore.remove(partition)
            partition_state_number = partition_to_state_number_map[partition]

            minimized_dfa.states.add(partition_state_number)
            explored_partition_labels.add(partition_state_number)

            # All the states in the partition are considered equivalent, therefore it is sufficient to use only one
            # to discovered transitions to other partitions
            some_partiton_state = next(iter(partition))

            for symbol, dest_state in self.transition_fn.get_out_transitions_for_state(some_partiton_state):
                dest_partition = state_to_its_partition_map[dest_state]

                # The destination partition might not be explored yet, so it might not have a state number assigned
                if dest_partition in partition_to_state_number_map:
                    dest_partition_state_number = partition_to_state_number_map[dest_partition]
                else:
                    dest_partition_state_number = next_avaiable_partition_number
                    partition_to_state_number_map[dest_partition] = next_avaiable_partition_number
                    next_avaiable_partition_number += 1;

                minimized_dfa.update_transition_fn(partition_state_number, symbol, dest_partition_state_number)

                if dest_partition_state_number not in explored_partition_labels:
                    partitions_to_explore.add(dest_partition)

            # Again, states in a partitions are equivalent, therefore there cannot be an accepting and a non-accepting
            # state in the same partition (all are either accepting or non-accepting)
            if some_partiton_state in self.final_states:
                minimized_dfa.add_final_state(partition_state_number)

        if solver_config.track_state_semantics:
            partition_id_to_partition = {partition_id: partition for partition, partition_id in partition_to_state_number_map.items()}
            minimized_dfa.state_semantics.state_labels = partition_id_to_partition

        return minimized_dfa

    def check_nondeterminism(self) -> bool:
        dest_per_symbol_table: Dict[int, Dict[LSBF_AlphabetSymbol, int]] = defaultdict(lambda: defaultdict(int))
        for source, compressed_symbol, dest in self.transition_fn.iter():
            for symbol in uncompress_transition_symbol(compressed_symbol):
                dest_per_symbol_table[source][symbol] += 1
                if dest_per_symbol_table[source][symbol] > 1:
                    return True
        return False


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

from amaya import automaton_algorithms
