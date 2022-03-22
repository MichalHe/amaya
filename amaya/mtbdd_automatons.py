from __future__ import annotations
from collections import defaultdict
from typing import (
    Any,
    Dict,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from amaya.alphabet import (
    LSBF_Alphabet,
    LSBF_AlphabetSymbol,
)
from amaya.automatons import (
    AutomatonType,
    NFA,
)
from amaya.mtbdd_transitions import (
    MTBDDTransitionFn,
    mtbdd_false
)
from amaya.visualization import AutomatonVisRepresentation
from amaya import logger


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
        self.extra_info: Dict[str, Any] = {}
        self.state_labels: Dict[int, Any] = {}
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

        # @Note(codeboy): This is a debug call, remove it.
        # MTBDDTransitionFn.transition_fn.get_states_in_mtbdd_leaves()

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
        processed_states_cnt = 0
        while work_queue:
            cur_state = work_queue.pop(-1)
            work_set.remove(cur_state)
            cur_metastate = metastate_map[cur_state]
            logger.debug('MTBDD NFA Intersection: Processing metastate: %s, remaining in work queue: %d',
                         cur_state,
                         len(work_queue))

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

                if gen_state not in work_set and gen_state not in work_queue:
                    work_queue.append(gen_state)
                    work_set.add(gen_state)

            int_nfa.transition_fn.mtbdds[cur_state] = cur_int_mtbdd
            processed_states_cnt += 1

        MTBDDTransitionFn.end_intersection()
        int_nfa.applied_operations_info = self.applied_operations_info + ['intersection']

        int_nfa.used_variables = sorted(set(self.used_variables + other.used_variables))

        int_nfa.remove_nonfinishing_states()

        logger.info('MTBDD NFA Intersection done. Processed states %d. Result has %d states.',
                    processed_states_cnt,
                    len(int_nfa.states))
        return int_nfa

    def perform_pad_closure(self):
        saturation_prop_repaired = self.transition_fn.do_pad_closure(self.initial_states, self.final_states)
        if saturation_prop_repaired:
            self.final_states.add(100)

    def determinize(self):
        """
        Performs in-place determinization of the automaton.

        No determinization is performed if the automaton is already marked as a
        DFA.

        The resulting automaton is complete - a transition to trapstate is
        added where needed.
        """

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

        # dfa = self.determinize()
        assert self.automaton_type == AutomatonType.DFA

        new_final_states = self.states - self.final_states
        self.final_states = new_final_states

        self.applied_operations_info += ['complement']
        # Do not need to set used_variables here as the determinized automaton
        # already has them set
        return self

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
        self.automaton_type = AutomatonType.NFA
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
        """
        Remove states from which there is no reachable accepting state.
        """
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
