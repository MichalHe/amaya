from __future__ import annotations
from typing import (
    List,
    Dict,
    Tuple,
    Union,
    Set,
    Callable,
    Optional
)
from log import logger
from utils import vector_dot
from automatons import (
    DFA,
    NFA,
    LSBF_Alphabet,
    AutomatonType,
)
from dataclasses import dataclass
from relations_structures import Relation
import math


DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int
NFA_AutomatonStateType = Union[int, str]
NFA_AlphabetSymbolType = Tuple[int, ...]


def add_trap_state_to_automaton(automaton: NFA, trap_state_name='TRAP'):
    automaton.add_state(trap_state_name)
    universal_symbol = tuple(['*' for v in automaton.alphabet.variable_names])
    automaton.update_transition_fn(trap_state_name, universal_symbol, trap_state_name)


def build_dfa_from_inequality(ineq: Relation) -> DFA:
    '''Builds DFA with Lang same as solutions to the inequation over N'''
    logger.debug(f'Building DFA (over N) to inequation: {ineq}')

    alphabet = LSBF_Alphabet.from_inequation(ineq)
    dfa: DFA[DFA_AutomatonStateType] = DFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.DFA
    )
    dfa.add_initial_state(ineq.absolute_part)

    work_queue: List[DFA_AutomatonStateType] = [ineq.absolute_part]

    logger.info(f'Generated alphabet for automaton: {alphabet}')

    while work_queue:
        currently_processed_state = work_queue.pop()
        dfa.add_state(currently_processed_state)

        # Check whether current state satisfies property that it accepts an
        # empty word
        if currently_processed_state >= 0:
            dfa.add_final_state(currently_processed_state)

        # @Optimize: iterate over act symbols projection
        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, ineq.variable_coeficients)
            next_state = math.floor(0.5 * (currently_processed_state - dot))

            # Add newly discovered transition
            dfa.update_transition_fn(currently_processed_state, alphabet_symbol, next_state)

            if not dfa.has_state_with_value(next_state):
                if next_state not in work_queue:
                    work_queue.append(next_state)

    logger.debug(f'Extracted dfa: {dfa}')

    return dfa


def build_dfa_from_equality(eq: Relation) -> DFA:
    alphabet = LSBF_Alphabet.from_inequation(eq)
    dfa: DFA[DFA_AutomatonStateType] = DFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.DFA
    )
    dfa.add_initial_state(eq.absolute_part)
    work_queue: List[DFA_AutomatonStateType] = [eq.absolute_part]

    while work_queue:
        currently_processed_state = work_queue.pop()
        dfa.add_state(currently_processed_state)

        # Check whether current state satisfies property that it accepts an
        # empty word
        if currently_processed_state == 0:
            dfa.add_final_state(currently_processed_state)

        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, eq.variable_coeficients)
            next_value = currently_processed_state - dot

            if next_value % 2 == 0:
                next_state = int(next_value/2)

                # Add newly discovered transition
                dfa.update_transition_fn(currently_processed_state, alphabet_symbol, next_state)

                if not dfa.has_state_with_value(next_state):
                    if next_state not in work_queue:
                        work_queue.append(next_state)
            else:
                trap_state = 'TRAP'
                if not dfa.has_state_with_value(trap_state):
                    add_trap_state_to_automaton(dfa, trap_state_name=trap_state)
                dfa.update_transition_fn(currently_processed_state, alphabet_symbol, trap_state)

    return dfa


def build_dfa_from_sharp_inequality(ineq: Relation) -> DFA:
    alphabet = LSBF_Alphabet.from_inequation(ineq)
    dfa: DFA[NFA_AutomatonStateType] = DFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.DFA,
    )
    dfa.add_initial_state(ineq.absolute_part)

    work_queue: List[int] = [ineq.absolute_part]

    while work_queue:
        current_state = work_queue.pop()
        dfa.add_state(current_state)

        if current_state > 0:
            dfa.add_final_state(current_state)

        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, ineq.variable_coeficients)
            next_value = current_state - dot

            destination_state = math.floor(0.5 * next_value)

            if not dfa.has_state_with_value(destination_state):
                work_queue.append(destination_state)

            dfa.update_transition_fn(current_state, alphabet_symbol, destination_state)

    return dfa


AutomatonConstructor = Callable[[LSBF_Alphabet, AutomatonType], NFA]


def project_symbol_onto_tracks(symbol: Tuple[int, ...], track_indices: List[int]) -> Tuple[int, ...]:
    return tuple(symbol[i] for i in track_indices)


def identify_tracks_used_by_ineq_components(relation_variables: List[str], relation: Relation) -> List[List[int]]:
    '''
    Identifies tracks used by the individual components of the relation.

    The relation has exactly one nonmodular compoment and zero or more modular components.
    The returned list has always the first entry indices used by the nonmodular component and the rest by the modular ones
    in the same order as stored in the relation.

    :param relation_variables: The variables used in the whole relation, *sorted*.
    :param relation: The relation itself.
    :returns: Collection of lists containing indices used by the components.
    '''

    component_tracks: List[List[int]] = []

    nonmodular_track_indices = []
    for track_index, variable_id_pair in enumerate(relation_variables):
        variable, _ = variable_id_pair
        if variable in relation.variable_names:
            nonmodular_track_indices.append(track_index)
    component_tracks.append(nonmodular_track_indices)

    # For every modulo term, identify the tracks that should be used from the  symbols of the projected alphabet
    for modulo_term in relation.modulo_terms:
        tracks_used = []
        for track_index, variable_id_pair in enumerate(relation_variables):
            variable, _ = variable_id_pair
            if variable in modulo_term.variables:
                tracks_used.append(track_index)
        component_tracks.append(tracks_used)
    return component_tracks


@dataclass(frozen=True)
class LinearStateComponent(object):
    value: int
    variable_coeficients: Tuple[int, ...]

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        raise NotImplementedError('The LinearStateComponent should not be instantiated directly, use its subclasses')


class IneqLinearStateComponent(LinearStateComponent):
    def __init__(self, value: int, variable_coeficients: Tuple[int, ...]):
        super().__init__(value, variable_coeficients)

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        dot = vector_dot(alphabet_symbol, self.variable_coeficients)
        destination_state = math.floor(0.5 * (self.value - dot))
        return IneqLinearStateComponent(value=destination_state,
                                        variable_coeficients=self.variable_coeficients)


class EqLinearStateComponent(LinearStateComponent):
    def __init__(self, value: int, variable_coeficients: Tuple[int, ...]):
        super().__init__(value, variable_coeficients)

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        dot = vector_dot(alphabet_symbol, self.variable_coeficients)
        diff = self.value - dot

        if diff % 2 == 1:
            return None

        return IneqLinearStateComponent(value=diff // 2,
                                        variable_coeficients=self.variable_coeficients)


@dataclass(frozen=True)
class ModuloTermStateComponent(object):
    value: int
    modulo: int
    variable_coeficients: Tuple[int, ...]

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[ModuloTermStateComponent]:
        dot = vector_dot(self.variable_coeficients, alphabet_symbol)

        if self.modulo % 2 == 0:
            if dot % 2 == 0:
                return ModuloTermStateComponent(
                    value=dot//2,
                    modulo=self.modulo//2,
                    variable_coeficients=self.variable_coeficients
                )
            else:
                return None

        difference = self.value - dot
        next_value = difference//2 if difference % 2 == 0 else (difference + self.modulo) // 2
        return ModuloTermStateComponent(
            value=next_value,
            modulo=self.modulo,
            variable_coeficients=self.variable_coeficients
        )


# This is used in the formula->NFA procedure. The created NFA has int automaton
# states
InterimModuloAutomatonState = Tuple[ModuloTermStateComponent, ...]
InterimAutomatonState = Tuple[Union[LinearStateComponent, ModuloTermStateComponent], ...]
TransitionPredicate = Callable[[InterimAutomatonState, Tuple[int, ...], InterimAutomatonState, Relation], bool]


class AliasStore(object):
    def __init__(self):
        self.data: Dict[InterimAutomatonState, int] = {}
        self.counter = 0

    def get_alias_for_state(self, state: InterimAutomatonState):
        if state in self.data:
            return self.data[state]
        else:
            alias = self.counter
            self.data[state] = alias
            self.counter += 1
            return alias


def create_multicomponent_initial_state_from_relation(relation: Relation) -> InterimAutomatonState:
    '''Creates initial state for NFA that has multiple components (linear + modular).'''
    # Setup the initial state
    modulo_term_state_components = [ModuloTermStateComponent(value=modulo_term.constant,
                                                             modulo=modulo_term.modulo,
                                                             variable_coeficients=modulo_term.variable_coeficients)
                                    for modulo_term in relation.modulo_terms]
    linear_component = LinearStateComponent(value=relation.absolute_part, variable_coeficients=tuple(relation.variable_coeficients))
    initial_state = tuple([linear_component] + modulo_term_state_components)
    return initial_state


def build_presburger_linear_nfa_from_initial_state(initial_state: LinearStateComponent,
                                                   is_transition_final: TransitionPredicate,
                                                   relation_variable_with_ids: List[Tuple[str, int]],
                                                   alphabet: LSBF_Alphabet,
                                                   nfa: NFA) -> NFA:
    '''
    Abstract algorithm to build automaton from the given atomic presburger formula.

    The logic that decides what states are direct successors of the currently processed
    state is contained in the state components.

    :param initial_state: The state that will be initial for the nfa. As a LinearStateComponent contains logic
                          how to generate successors.
    :param is_transition_final: Predicate to determine which generated transition should also lead to the final state.
    :param relation_variable_with_ids: Variables of the overall alphabet that are used in the relation.
    :param alphabet: The overall alphabet of the current solver run.
    :param nfa: The empty nfa to give structure to.
    :returns: The passed nfa with structure encoding solution space of the relation.
    '''

    # We have to postpone the addition of final state, since it has to have
    # unique number and that we cannot tell until the end
    f_transitions = []

    work_list: List[LinearStateComponent] = [initial_state]
    work_set: Set[LinearStateComponent] = set(work_list)  # Seed up checking whether a state is already present in the work_list

    relation_variable_ids = list(map(lambda pair: pair[1], relation_variable_with_ids))
    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(relation_variable_ids))

    while work_list:
        current_state = work_list.pop()
        work_set.remove(current_state)

        logger.debug(f'Processing state {current_state}, remaining in work queue: {len(work_list)}')

        nfa.add_state(current_state.value)

        for alphabet_symbol in projected_alphabet:
            destination_state = current_state.generate_next(alphabet_symbol)

            if destination_state is None:
                continue

            if not nfa.has_state_with_value(destination_state.value) and destination_state not in work_set:
                work_list.append(destination_state)
                work_set.add(destination_state)

            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(relation_variable_ids, alphabet_symbol)
            nfa.update_transition_fn(current_state.value,
                                     cylindrified_symbol,
                                     current_state.value)

            if is_transition_final(current_state, alphabet_symbol, destination_state):
                f_transitions.append((current_state, cylindrified_symbol))

    # All states have been added, now determine the final state value
    if f_transitions:
        max_state = max(nfa.states)
        final_state = max_state + 1
        nfa.add_state(final_state)
        nfa.add_final_state(final_state)
        for origin, symbol in f_transitions:
            nfa.update_transition_fn(origin, symbol, final_state)

    nfa.used_variables = relation_variable_with_ids
    return nfa


def build_nfa_from_linear_inequality(ineq: Relation,
                                     ineq_variables_ordered: List[Tuple[str, int]],
                                     alphabet: LSBF_Alphabet,
                                     automaton_constr: AutomatonConstructor) -> NFA[NFA_AutomatonStateType]:

    initial_state = IneqLinearStateComponent(value=ineq.absolute_part, variable_coeficients=tuple(ineq.variable_coeficients))

    def is_transition_final(source: LinearStateComponent,
                            symbol: Tuple[int, ...],
                            target: LinearStateComponent) -> bool:
        dot = vector_dot(symbol, source.variable_coeficients)
        if source.value + dot >= 0:
            return True
        return False

    nfa = automaton_constr(alphabet=alphabet, automaton_type=AutomatonType.NFA)

    nfa = build_presburger_linear_nfa_from_initial_state(initial_state,
                                                         is_transition_final,
                                                         ineq_variables_ordered,
                                                         alphabet,
                                                         nfa)

    return nfa


def build_nfa_from_linear_equality(eq: Relation,
                                   eq_variables_ordered: List[int],
                                   alphabet: LSBF_Alphabet,
                                   automaton_constr: AutomatonConstructor) -> NFA:
    '''
    Builds NFA representing the solution space of given equality.
    '''

    nfa = automaton_constr(
        alphabet=alphabet,
        automaton_type=AutomatonType.NFA
    )

    initial_state = EqLinearStateComponent(value=eq.absolute_part,
                                           variable_coeficients=tuple(eq.variable_coeficients))

    def is_transition_final(source: LinearStateComponent,
                            symbol: Tuple[int, ...],
                            target: LinearStateComponent) -> bool:
        dot = vector_dot(symbol, source.variable_coeficients)
        if source.value + dot == 0:
            return True
        return False

    nfa = build_presburger_linear_nfa_from_initial_state(initial_state,
                                                         is_transition_final,
                                                         eq_variables_ordered,
                                                         alphabet,
                                                         nfa)
    return nfa


def build_nfa_from_linear_sharp_inequality(ineq: Relation, emit_handle=None):
    assert ineq.operation == '<'

    # Since we are dealing with a discrete domain:
    ineq.absolute_part -= 1
    ineq.operation = '<='

    nfa_ineq = build_nfa_from_linear_inequality(ineq)

    return nfa_ineq


def build_presburger_modulo_nfa(relation: Relation,  # NOQA
                                relation_variables_with_ids: List[Tuple[str, int]],
                                alphabet: LSBF_Alphabet,
                                nfa: NFA) -> NFA:
    '''
    Builds the NFA that encodes the given relation of the form is_congruent_with(vector_dot(a.x, K))

    :param relation: Relation of the form described abouve that should be encoded with the automaton.
    :param relation_variables_with_ids: The sorted (by ID) list of variable names with their IDs.
                                        Required so we know which tracks of the overall alphabet are used.
    :param alphabet: The overall alphabet.
    :param nfa: An empty NFA that will have its structure formed to encode the modulo relation.
    '''

    logger.info('Building modulo-DFA for provided relation: {0}'.format(relation))

    assert not relation.variable_names, 'Trying to build modulo automaton from relation with some linear terms.'
    assert len(relation.modulo_terms) == 1, 'Currently we don\'t know how to build automaton for more than 1 mod term.'
    assert relation.operation == '=', 'Don\'t know how to build NFA for different relation than equality.'

    variable_name_to_id: Dict[str, int] = dict(relation_variables_with_ids)
    variable_ids = sorted(variable_name_to_id.values())
    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(variable_ids))

    variable_name_to_track_index: Dict[str, int] = {}
    for i, variable_id_pair in enumerate(relation_variables_with_ids):
        variable_name_to_track_index[variable_id_pair[0]] = i

    modulo_term = relation.modulo_terms[0]
    initial_state = ModuloTermStateComponent(value=relation.absolute_part,
                                             modulo=modulo_term.modulo,
                                             variable_coeficients=modulo_term.variable_coeficients)

    work_list: List[ModuloTermStateComponent] = [initial_state]
    work_set: Set[ModuloTermStateComponent] = set(work_list)

    nfa.add_initial_state(initial_state.value)

    # List of transitions to final state that will be added after the main
    # automaton structure is build (because final state will be calculated as
    # max of all the states + 1)
    transitions_to_final_state: List[Tuple[int, Tuple[int, ...]]] = []

    while work_list:
        current_state = work_list.pop(-1)
        work_set.remove(current_state)

        logger.debug('Processing metastate {0}, remaining in work list: {1}'.format(
            current_state, len(work_list)
        ))

        nfa.add_state(current_state.value)

        for symbol in projected_alphabet:
            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(variable_ids, symbol)
            destination_state = current_state.generate_next(symbol)

            if destination_state is None:
                continue

            nfa.update_transition_fn(current_state.value, cylindrified_symbol, destination_state.value)

            # Make nondeterministic guess that the current symbol is the last on the input tape.
            value_with_symbol_interp_as_sign = current_state.value + vector_dot(symbol, modulo_term.variable_coeficients)
            if (value_with_symbol_interp_as_sign % modulo_term.modulo) == 0:
                partial_transition_to_final_state = (current_state.value, cylindrified_symbol)
                transitions_to_final_state.append(partial_transition_to_final_state)

            if not nfa.has_state_with_value(destination_state.value) and destination_state not in work_set:
                work_list.append(destination_state)
                work_set.add(destination_state)

    if transitions_to_final_state:
        final_state = max(nfa.states) + 1
        nfa.add_final_state(final_state)
        nfa.add_state(final_state)
        for source, symbol in transitions_to_final_state:
            nfa.update_transition_fn(source, symbol, final_state)

    logger.info('Done. Built DFA with {0} states, out of which {1} are final.'.format(
        len(nfa.states), len(nfa.final_states)))
    return nfa
