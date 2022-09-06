from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass, field
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

from amaya import logger
from amaya.alphabet import (
    LSBF_Alphabet,
    LSBF_AlphabetSymbol,
)
from amaya.automatons import (
    AutomatonType,
    NFA,
)
from amaya.config import (
    solver_config,
    SolutionDomain
)
from amaya.mtbdd_transitions import (
    MTBDDTransitionFn,
    mtbdd_false
)
from amaya.visualization import AutomatonVisRepresentation


@dataclass
class MTBDD_NFA(NFA):
    automaton_id_counter = 0  # ^^^ Used to mark mtbdd leaves in order to avoid sharing them between multiple mtbdds
    fast_prunining_enabled = False

    alphabet:       LSBF_Alphabet
    automaton_type: AutomatonType = AutomatonType.NFA
    transition_fn:  MTBDDTransitionFn = field(init=False)

    states:         Set[int] = field(default_factory=set)
    initial_states: Set[int] = field(default_factory=set)
    final_states:   Set[int] = field(default_factory=set)
    used_variables: List[int] = field(default_factory=list)
    applied_operations_info: List[str] = field(default_factory=list)
    state_labels:   Dict[int, Any] = field(default_factory=dict)
    extra_info:     Dict[Any, Any] = field(default_factory=dict)

    trapstate: Optional[int] = None

    def __post_init__(self):
        self.transition_fn = MTBDDTransitionFn(self.alphabet.variable_numbers, MTBDD_NFA.automaton_id_counter)
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
        new_final_state = max(self.states) + 1
        saturation_prop_repaired = self.transition_fn.do_pad_closure(self.initial_states,
                                                                     self.final_states,
                                                                     new_final_state)
        if saturation_prop_repaired:
            self.states.add(new_final_state)
            self.final_states.add(new_final_state)

    def determinize(self):
        """
        Performs in-place determinization of the automaton.

        No determinization is performed if the automaton is already marked as a
        DFA.

        The resulting automaton is complete - a transition to trapstate is
        added where needed.
        """
        logger.debug('Performing MTBDD NFA determinization.')

        work_queue = [tuple(self.initial_states)]
        work_set = set(work_queue)
        dfa = MTBDD_NFA(self.alphabet, automaton_type=AutomatonType.DFA, state_semantics=None)

        # import pdb; pdb.set_trace()

        states = set()
        initial_states = set(work_queue)
        final_states = set()

        # Stores the actual structure of the automaton.
        mtbdds = {}

        while work_queue:
            logger.debug(f'Determinization: The number of states remaining in the work queue: {len(work_queue)}')
            c_macrostate = work_queue.pop(-1)
            work_set.remove(c_macrostate)

            # @Optimize: This is true only for the initial state. Other states are reachable from other and are remapped when the transition is added.
            states.add(c_macrostate)
            if set(c_macrostate).intersection(self.final_states):
                final_states.add(c_macrostate)

            c_macrostate_union_mtbdd = self.transition_fn.get_union_mtbdd_for_states(c_macrostate, self.transition_fn.automaton_id)

            # The mtbdd has already ref count increased, do not increase it

            if c_macrostate_union_mtbdd is None:
                continue
            mtbdds[c_macrostate] = c_macrostate_union_mtbdd

            reachable_macrostates = MTBDDTransitionFn.call_get_mtbdd_leaves(c_macrostate_union_mtbdd)
            for r_macrostate in reachable_macrostates:
                r_macrostate = tuple(r_macrostate)

                if r_macrostate not in states and r_macrostate not in work_set:
                    work_queue.append(r_macrostate)
                    work_set.add(r_macrostate)

        # Check an edge case when there were no transitions in the automaton - only the initial state is present in the DFA.
        if not mtbdds:
            assert len(states) == 1
            # There is only one macrostates, so there is no need to do some advanced mapping of the macrostates to ints.
            dfa.states.add(0)
            dfa.initial_states.add(0)
            if final_states:
                dfa.final_states.add(0)
            dfa.transition_fn.mtbdds[0] = mtbdd_false
            dfa.used_variables = list(self.used_variables)
            return dfa

        # We have explored the entire structure - time to mangle the generated
        # macrostates into integers, so that the automaton has the correct form.
        automaton_id = dfa.transition_fn.automaton_id
        macrostates, _mtbdds = zip(*mtbdds.items())
        patched_mtbdds, macrostate2int_map = MTBDDTransitionFn.rename_macrostates_after_determinization(_mtbdds, automaton_id)

        # The patched mtbdds have already ref count incremented, no need to
        # increment the ref counter. The old mtbdds will be decremented when
        # MTBDDTransitionFn will be GC'd by Python garbage collection.

        max_state = max(macrostate2int_map.values())
        for state in states:
            # Initial states might never get discovered - we need to remap them manually,
            # because they will not be present in any of the mtbdd leaves
            if state in macrostate2int_map:
                dfa.add_state(macrostate2int_map[state])
            else:
                max_state += 1
                macrostate2int_map[state] = max_state
                dfa.add_state(max_state)
        for f_state in final_states:
            dfa.add_final_state(macrostate2int_map[f_state])
        for i_state in initial_states:
            dfa.add_initial_state(macrostate2int_map[i_state])

        for macrostate, patched_mtbdd in zip(macrostates, patched_mtbdds):
            state = macrostate2int_map[macrostate]
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
        assert self.automaton_type & AutomatonType.DFA

        new_final_states = self.states - self.final_states
        self.final_states = new_final_states

        self.applied_operations_info += ['complement']
        # Do not need to set used_variables here as the determinized automaton already has them set
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
            self.perform_pad_closure()
            logger.debug('Padding closure done.')
        else:
            logger.debug('Skipping padding closure.')

        self.used_variables.remove(var)

        if not self.used_variables:
            logger.info('After the projection there are no more variables used by the MTBDD NFA - performing reduction to a trivial automaton.')
            model = self.find_model()
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

    def find_model(self) -> Optional[Tuple[List[LSBF_AlphabetSymbol], List[int]]]:
        """
        Check whether the language of this automaton is empty and return the found model if not.

        Returns:
            A tuple containing the model (word over alphabet) and a list of states that would be traversed or
            None, if the automaton has empty language.
        """
        Word = Tuple[LSBF_AlphabetSymbol, ...]
        states_with_word_to_explore: List[Tuple[int, Word]] = [(q0, tuple()) for q0 in self.initial_states]
        states_to_explore = set(self.initial_states)  # To prevent having the same state waiting to be explored multiple times
        visited_states: Set[int] = set()

        while states_with_word_to_explore:
            state, word = states_with_word_to_explore.pop(-1)

            states_to_explore.remove(state)
            if word or solver_config.solution_domain == SolutionDomain.NATURALS:
                visited_states.add(state)

            dest_state_symbol_pairs = self.transition_fn.get_state_post_with_some_symbol(state)

            for dest_state, transition_symbol in dest_state_symbol_pairs:
                # We can skip the state if it already is explored, or if it is waiting to be explored,
                # since it would not be waiting if it was accepting
                if dest_state in visited_states or dest_state in states_to_explore:
                    continue

                dest_word = word + (transition_symbol,)

                if dest_state in self.final_states:
                    if solver_config.solution_domain != SolutionDomain.INTEGERS or dest_word:
                        return dest_word

                states_with_word_to_explore.append((dest_state, dest_word))
                states_to_explore.add(dest_state)
        return None

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
            variable_names=self.alphabet.variable_numbers,
            variable_ids=self.used_variables,
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

        logger.debug(f'Removed {len(states_removed)} out of {len(self.states)}.')
        self.transition_fn.remove_states(states_removed)
        self.states = states_reaching_accepting_state

        if not states_reaching_accepting_state:
            # In case the language of the automaton is empty keep at least 1 nonaccepting state so that functions
            # generating unique states by taking max(self.states) will not crash
            self.states.add(0)

    def minimize_hopcroft(self) -> MTBDD_NFA:
        """Minimize the underlying automaton using hopcroft's minimization algorithm."""
        dfa = self.determinize()
        return MTBDDTransitionFn.minimize_hopcroft(dfa)
