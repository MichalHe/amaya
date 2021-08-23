from __future__ import annotations
from typing import (
    List,
    Dict,
    Iterable,
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

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> LinearStateComponent:
        dot = vector_dot(alphabet_symbol, self.variable_coeficients)
        destination_state = math.floor(0.5 * (self.value - dot))
        return LinearStateComponent(value=destination_state,
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
InterimAutomatonState = Tuple[Union[LinearStateComponent, ModuloTermStateComponent], ...]


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


def build_nfa_from_inequality(ineq: Relation,
                              ineq_variables_ordered: List[Tuple[str, int]],
                              alphabet: LSBF_Alphabet,
                              automaton_constr: AutomatonConstructor,
                              embed_metadata: bool = False) -> NFA[NFA_AutomatonStateType]:
    '''Constructs a non-deterministic automaton for the inequality `ineq` (<=) over whole (Z) numbers.

    We need to pass the variables with the corresponding IDs so that we know at which tract we need to
    cylindrify the symbols used when building the automaton. We cannot ask the alphabet, since the variable
    names are ambiguous (two AST can have the same variable name, but the variables are bound by separate
    quantifiers).

    :param ineq: The inequality. The variables should be pre-sorted according to their IDs.
    :param ineq_variables_ordered: An ordered list of the variables used in this inequality with their ID.
    :param alphabet: - Alphabet containing *all* the variables present in the SMT tree.
    :param automaton_constr: - A factory function for constructing the automaton itself.
    :returns: The NFA encoding the inequality.
    '''
    nfa = automaton_constr(alphabet, AutomatonType.NFA)

    nfa.add_initial_state(ineq.absolute_part)

    # NOTE:
    # The relation we receive is no longer a simple straight forward a.x <= C.
    # Currently we are dealing with something that has multiple individual
    # components (1 linear and 0+ modular)

    # Not every variable in the overall alphabet might be present in the
    # inequality - we need to iterate over an alphabet projection to the used
    # variables (the bitvectors used in automaton creation) and use the
    # cylindrified version of those bitvectors to insert actual transitions.
    used_variables = ineq.get_used_variables()
    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(used_variables))

    component_tracks = identify_tracks_used_by_ineq_components(
        ineq_variables_ordered,
        ineq)

    # We have to postpone the addition of final state, since it has to have
    # unique number and that we cannot tell until the end
    f_transitions = []

    def is_current_transition_final(origin: InterimAutomatonState,
                                    destination: InterimAutomatonState,
                                    relation: Relation,
                                    component_symbols: Iterable[Iterable[int]]) -> bool:
        '''
        Looks at the calculated transition and checks whether the
        transition would lead to a final state if the inpu symbol was the last one.
        '''

        linear_component = origin[0]
        linear_component_symbol = component_symbols[0]
        dot = vector_dot(linear_component.variable_coeficients, linear_component_symbol)

        # Interpret the read symbol as the last one.
        linear_component_with_sign = linear_component.value + dot

        modulo_terms_value = 0
        for modulo_term_coeficient, modulo_term_value in zip(relation.modulo_term_coeficients, destination[1:]):
            modulo_terms_value += modulo_term_coeficient * modulo_term_value.value

        relation_value = linear_component_with_sign - modulo_terms_value
        return relation_value >= 0

    initial_state = create_multicomponent_initial_state_from_relation(ineq)

    work_list: List[InterimAutomatonState] = [initial_state]
    work_set: Set[InterimAutomatonState] = set(work_list)  # Seed up checking whether a statee is already present in the work_list
    alias_store = AliasStore()

    ineq_variable_numbers = list(map(lambda pair: pair[1], ineq_variables_ordered))

    while work_list:
        current_state = work_list.pop()
        work_set.remove(current_state)

        logger.debug(f'Processing state {current_state}, remaining in work queue: {len(work_list)}')

        current_state_alias = alias_store.get_alias_for_state(current_state)

        nfa.add_state(current_state_alias)

        for alphabet_symbol in projected_alphabet:
            component_symbols = [project_symbol_onto_tracks(alphabet_symbol, track_indices)
                                 for track_indices in component_tracks]
            destination_state = tuple(
                component_state.generate_next(component_symbol)
                for component_state, component_symbol in zip(current_state, component_symbols))

            if None in destination_state:
                continue

            destination_state_alias = alias_store.get_alias_for_state(destination_state)

            if not nfa.has_state_with_value(destination_state_alias) and destination_state not in work_set:
                work_list.append(destination_state)
                work_set.add(destination_state)

            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(ineq_variable_numbers, alphabet_symbol)
            nfa.update_transition_fn(current_state_alias,
                                     cylindrified_symbol,
                                     destination_state_alias)

            if is_current_transition_final(current_state, destination_state, ineq, component_symbols):
                f_transitions.append((current_state_alias, cylindrified_symbol))

    # All states have been added, now determine the final state value
    if f_transitions:
        max_state = max(nfa.states)
        final_state = max_state + 1
        nfa.add_state(final_state)
        nfa.add_final_state(final_state)
        for origin, symbol in f_transitions:
            nfa.update_transition_fn(origin, symbol, final_state)

    nfa.used_variables = ineq_variables_ordered
    if embed_metadata:
        nfa.extra_info['metadata'] = alias_store
    return nfa


def build_nfa_from_equality(eq: Relation,
                            eq_variables_ordered: List[int],
                            alphabet: LSBF_Alphabet,
                            automaton_constr: AutomatonConstructor):
    '''TODO'''

    nfa = automaton_constr(
        alphabet=alphabet,
        automaton_type=AutomatonType.NFA
    )

    nfa.add_initial_state(eq.absolute_part)

    states_to_explore: List[int] = [eq.absolute_part]

    # We keep only the information about the origin state and transition symbol
    # as the final state is only one
    transitions_to_final_state: Set[Tuple[int, Tuple[int, ...]]] = set()

    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(eq_variables_ordered))

    work_set = set(states_to_explore)
    while states_to_explore:
        logger.debug(f'Build NFA from equality: Remaining states in the work queue: {len(states_to_explore)}')
        e_state = states_to_explore.pop()  # e_state = (currently) explored state
        work_set.remove(e_state)

        nfa.add_state(e_state)

        for symbol in projected_alphabet:
            dot = vector_dot(symbol, eq.variable_coeficients)
            d_state = e_state - dot  # Discovered state

            # Process only even states
            if d_state % 2 == 0:
                d_state = int(d_state / 2)
                nfa.update_transition_fn(e_state,
                                         alphabet.cylindrify_symbol_of_projected_alphabet(eq_variables_ordered, symbol),
                                         d_state)

                # Check whether we already did process this state
                if not nfa.has_state_with_value(d_state):
                    # State might be reachable from multiple locations, this
                    # discovery does not have to be the first one
                    if d_state not in work_set:
                        states_to_explore.append(d_state)
                        work_set.add(d_state)

                # Check whether current state should have transition to final
                if e_state + dot == 0:
                    # Postpone the addition of the transition to final state
                    # (we do not know the integer value of the state yet)
                    transitions_to_final_state.add((e_state, alphabet.cylindrify_symbol_of_projected_alphabet(eq_variables_ordered, symbol)))

    if transitions_to_final_state:
        final_state = max(nfa.states) + 1
        nfa.add_state(final_state)
        nfa.add_final_state(final_state)
        for origin, symbol in transitions_to_final_state:
            nfa.update_transition_fn(origin, symbol, final_state)

    nfa.used_variables = eq_variables_ordered

    return nfa


def create_and_link_prefinal_state(automaton: NFA,
                                   current_state: int,
                                   self_loop_set: Set[Tuple[int, ...]],
                                   final_set: Set[Tuple[int, ...]],
                                   final_state: str):

    prefinal_state = f'{current_state}\'prefinal'
    automaton.add_state(prefinal_state)

    # Link current_state and prefinal
    for symbol in (self_loop_set - final_set):
        automaton.update_transition_fn(current_state, symbol, prefinal_state)

    # Create selfloop
    for self_loop_symbol in self_loop_set:
        automaton.update_transition_fn(prefinal_state, self_loop_symbol, prefinal_state)

    # Link prefinal and final
    for fin_symbol in final_set:
        automaton.update_transition_fn(prefinal_state, fin_symbol, final_state)


def build_nfa_from_sharp_inequality(ineq: Relation, emit_handle=None):
    nfa_eq = build_nfa_from_equality(ineq)
    nfa_neq = nfa_eq.complement()
    nfa_ineq = build_nfa_from_inequality(ineq)

    result = nfa_neq.intersection(nfa_ineq)
    result.remove_nonfinishing_states()
    return result


def build_nfa_from_sharp_inequality2(s_ineq: Relation):
    alphabet = LSBF_Alphabet.from_inequation(s_ineq)
    nfa: NFA[NFA_AutomatonStateType] = NFA(
        alphabet=alphabet,
        automaton_type=AutomatonType.NFA,
    )
    nfa.add_initial_state(s_ineq.absolute_part)

    work_queue: List[int] = [s_ineq.absolute_part]

    while work_queue:
        current_state = work_queue.pop()
        nfa.add_state(current_state)

        final_symbols = []
        self_loop_symbols = []

        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, s_ineq.variable_coeficients)
            destination_state = math.floor(0.5 * (current_state - dot))

            if not nfa.has_state_with_value(destination_state):
                work_queue.append(destination_state)

            nfa.update_transition_fn(current_state, alphabet_symbol, destination_state)
            if current_state == destination_state:
                self_loop_symbols.append(alphabet_symbol)

            if current_state + dot >= 0:
                # We need to wait till every alphabet symbol has beed explored
                final_symbols.append(alphabet_symbol)

        if final_symbols:
            # We know that a symbol which is leads to final state and also is
            # self loop, would be present also in equation with exact same
            # structure
            final_set = set(final_symbols)
            self_loop_set = set(self_loop_symbols)
            eq_set = final_set.intersection(self_loop_set)
            final_state = None

            if self_loop_set - final_set:
                final_state = 'FINAL'
                nfa.add_state(final_state)
                nfa.add_final_state(final_state)

            # All symbols did lead to final, without selfloop
            # So there is no such symbol which would be accepted by =
            if not eq_set:
                final_state = 'FINAL'
                for symbol in final_set:
                    nfa.update_transition_fn(current_state, symbol, final_state)
            else:
                # Otherwise we wanna take only symbols different from those
                # accepted by =

                # There needs to be at least one such symbol (because all
                # might have been =
                if final_state is not None:
                    create_and_link_prefinal_state(nfa,
                                                   current_state,
                                                   self_loop_set,
                                                   final_set,
                                                   final_state)
    return nfa
