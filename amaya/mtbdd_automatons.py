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
        self.transition_fn = MTBDDTransitionFn(self.alphabet.variable_numbers)

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

        self.transition_fn = MTBDDTransitionFn.union_of(self.transition_fn, other.transition_fn)

        self.states = self.states.union(other.states)
        self.final_states.update(other.final_states)
        self.initial_states.update(other.initial_states)

        self.applied_operations_info += ['union']
        self.used_variables = sorted(set(self.used_variables + other.used_variables))

        self.automaton_type = AutomatonType.NFA

        logger.debug('Exiting MTBDD NFA union procedure.')
        return self

    def intersection(self, other: MTBDD_NFA, metastate_map: Optional[Dict[int, Tuple[int, int]]] = None):
        logger.info('Performing intersection of two automata of size %d and %d', len(self.states), len(other.states))
        result = MTBDDTransitionFn.compute_nfa_intersection(self, other)
        logger.info('Intersection done: result size=%d, left operand size: %d , right operand size: %d', len(result.states), len(self.states), len(other.states))
        return result

    def perform_pad_closure(self):
        result = MTBDDTransitionFn.do_pad_closure(self)
        if len(result.states) > len(self.states):
            self.states = result.states
            self.final_states = result.final_states

            # Swap transition function so that the currently held mtbdds will be GC'd with `result`
            self.transition_fn.mtbdds, result.transition_fn.mtbdds = result.transition_fn.mtbdds, self.transition_fn.mtbdds


    def determinize(self) -> MTBDD_NFA:
        # @Todo: Before simplification, this method previously called: mtbdd union, mtbdd rename, get leaves.
        #        Check whether any of these API calls can be removed.
        logger.debug('Performing MTBDD NFA determinization. Automaton size: #states=%d', len(self.states))
        dfa = MTBDDTransitionFn.determinize(self)
        logger.debug('MTBDD NFA determinization done. Results size: #states=%d', len(dfa.states))
        return dfa

    def complement(self) -> MTBDD_NFA:
        """
        Modifies the automaton instance to accept the complement of the language.

        Returns reference to self, no new automaton is created.
        """

        # dfa = self.determinize()
        assert self.automaton_type & AutomatonType.DFA

        new_final_states = self.states - self.final_states
        self.final_states = new_final_states

        self.applied_operations_info += ['complement']
        # Do not need to set used_variables here as the determinized automaton already has them set
        return self

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
        """
        Creates an MTBDD NFA with an empty language.

        Params:
            alphabet - The LSBF alphabet for the created automaton.
        Returns:
            The created automaton.
        """
        nfa = MTBDD_NFA(alphabet, AutomatonType.DFA | AutomatonType.TRIVIAL)
        nfa.add_state(0)
        nfa.add_initial_state(0)
        universal_symbol = tuple(['*'] * len(alphabet.variable_numbers))
        nfa.update_transition_fn(0, universal_symbol, 0)
        nfa.used_variables = []
        return nfa

    @staticmethod
    def trivial_accepting(alphabet: LSBF_Alphabet) -> MTBDD_NFA:
        """
        Create a new MTBDD NFA with universal lanugage.

        Params:
            alphabet - The LSBF alphabet for the created automaton.
        Returns:
            The created automaton.
        """
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
        """Returns a structure carrying all necessary information to visualize this automaton."""
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
            state_semantics=None,
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
        assert bool(self.automaton_type & AutomatonType.DFA)
        return MTBDDTransitionFn.minimize_hopcroft(self)
