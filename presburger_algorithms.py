from __future__ import annotations
from typing import (
    List,
    Dict,
    Generator,
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


def add_trap_state_to_automaton(automaton: NFA, trap_state: Optional[int] = None) -> int:
    """
    Add a nonaccepting state with selfloop over all alphabet symbols to the given automaton.

    :param automaton: Automaton to which a trap state will be added
    :param trap_state: The value of the trapstate
    :returns: The value of the added trap state
    """
    if trap_state is None:
        trap_state = max(automaton.states) + 1

    automaton.add_state(trap_state)
    universal_symbol = tuple('*' for v in automaton.alphabet.variable_numbers)
    automaton.update_transition_fn(trap_state, universal_symbol, trap_state)
    return trap_state


def build_dfa_from_linear_equality(eq: Relation,
                                   eq_var_id_pairs: List[Tuple[str, int]],
                                   alphabet: LSBF_Alphabet,
                                   constr: AutomatonConstructor) -> DFA:
    """
    Construct a DFA with language that is the solution space of the given equation 
    encoded in 2's complement.  
    """
    dfa: DFA[DFA_AutomatonStateType] = DFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)
    dfa.add_initial_state(eq.absolute_part)

    work_queue: List[DFA_AutomatonStateType] = [eq.absolute_part]

    trap_state: Optional[int] = None
    while work_queue:
        current_state = work_queue.pop()
        dfa.add_state(current_state)

        # Check whether current state satisfies property that it accepts an empty word -> state is final
        if current_state == 0:
            dfa.add_final_state(current_state)

        # TODO: Iterate over the alphabet projected onto the variables that are actually present in the equality
        for alphabet_symbol in alphabet.symbols:
            dot = vector_dot(alphabet_symbol, eq.variable_coeficients)
            next_value = current_state - dot

            if next_value % 2 == 0:
                next_state = int(next_value/2)

                # Add the newly discovered transition
                dfa.update_transition_fn(current_state, alphabet_symbol, next_state)

                if not dfa.has_state_with_value(next_state):
                    if next_state not in work_queue:
                        work_queue.append(next_state)
            else:
                # This means the the input tape and the absolute part differ in the currently read bit,
                # therefore, they cannot be equal -> no transition along the current symbol. However,
                # we would like the automaton to be complete, therefore add a trap state for such transitions
                if has_trap_state is None:
                    trap_state = add_trap_state_to_automaton(dfa)
                dfa.update_transition_fn(current_state, alphabet_symbol, trap_state)

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

        return EqLinearStateComponent(value=diff // 2,
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
        next_value = difference // 2 if difference % 2 == 0 else (difference + self.modulo) // 2
        next_value = next_value % self.modulo
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
                                     destination_state.value)

            if is_transition_final(current_state, alphabet_symbol, destination_state):
                f_transitions.append((current_state, cylindrified_symbol))

    # All states have been added, now determine the final state value
    if f_transitions:
        max_state = max(nfa.states)
        final_state = max_state + 1
        nfa.add_state(final_state)
        nfa.add_final_state(final_state)
        for origin, symbol in f_transitions:
            nfa.update_transition_fn(origin.value, symbol, final_state)

    nfa.used_variables = relation_variable_ids
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

    nfa.add_initial_state(initial_state.value)

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

    nfa.add_initial_state(initial_state.value)

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
                                automaton_constr: AutomatonConstructor) -> NFA:
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

    nfa = automaton_constr(alphabet=alphabet, automaton_type=AutomatonType.NFA)

    variable_name_to_id: Dict[str, int] = dict(relation_variables_with_ids)
    variable_ids = sorted(variable_name_to_id.values())
    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(variable_ids))

    variable_name_to_track_index: Dict[str, int] = {}
    for i, variable_id_pair in enumerate(relation_variables_with_ids):
        variable_name_to_track_index[variable_id_pair[0]] = i

    modulo_term = relation.modulo_terms[0]
    initial_state = ModuloTermStateComponent(value=relation.absolute_part,
                                             modulo=modulo_term.modulo,
                                             variable_coeficients=tuple(modulo_term.variable_coeficients))

    alias_store = AliasStore()
    work_list: List[ModuloTermStateComponent] = [initial_state]
    work_set: Set[ModuloTermStateComponent] = set(work_list)

    nfa.add_initial_state(alias_store.get_alias_for_state(initial_state))

    # List of transitions to final state that will be added after the main
    # automaton structure is build (because final state will be calculated as
    # max of all the states + 1)
    transitions_to_final_state: List[Tuple[int, Tuple[int, ...]]] = []

    while work_list:
        current_state = work_list.pop(-1)
        current_state_alias = alias_store.get_alias_for_state(current_state)
        work_set.remove(current_state)

        logger.debug('Processing metastate {0} (aka {1}), remaining in work list: {2}'.format(
            current_state, current_state_alias, len(work_list)
        ))

        nfa.add_state(current_state_alias)

        for symbol in projected_alphabet:
            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(variable_ids, symbol)
            destination_state = current_state.generate_next(symbol)

            if destination_state is None:
                continue

            destination_state_alias = alias_store.get_alias_for_state(destination_state)

            nfa.update_transition_fn(current_state_alias, cylindrified_symbol, destination_state_alias)

            # Make nondeterministic guess that the current symbol is the last on the input tape.
            value_with_symbol_interp_as_sign = current_state.value + vector_dot(symbol, modulo_term.variable_coeficients)
            if (value_with_symbol_interp_as_sign % current_state.modulo) == 0:
                partial_transition_to_final_state = (current_state_alias, cylindrified_symbol)
                transitions_to_final_state.append(partial_transition_to_final_state)

            if not nfa.has_state_with_value(destination_state_alias) and destination_state not in work_set:
                work_list.append(destination_state)
                work_set.add(destination_state)

    if transitions_to_final_state:
        final_state = max(nfa.states) + 1
        nfa.add_final_state(final_state)
        nfa.add_state(final_state)
        for source, symbol in transitions_to_final_state:
            nfa.update_transition_fn(source, symbol, final_state)

    logger.info('Done. Built NFA with {0} states, out of which {1} are final.'.format(
        len(nfa.states), len(nfa.final_states)))

    nfa.used_variables = list(map(lambda pair: pair[1], relation_variables_with_ids))
    nfa.extra_info['aliases'] = alias_store
    return nfa


def on_the_fly_intersection(lin_automaton: NFA, modulo_relation_variables: List[int], modulo_relation: Relation):
    """
    Performs on-the-fly intersection.

    Performs on-the-fly intersection on the given automaton from linear constraints
    with the automaton that would result from the modulo term.
    """
    modulo_term = modulo_relation.modulo_terms[0]

    lin_automaton_initial_state = next(iter(lin_automaton.initial_states))
    mod_automaton_initial_state = ModuloTermStateComponent(
        value=modulo_relation.absolute_part,
        modulo=modulo_term.modulo,
        variable_coeficients=tuple(modulo_term.variable_coeficients))

    initial_state: Tuple[int, ModuloTermStateComponent] = (lin_automaton_initial_state, mod_automaton_initial_state)
    work_list: List[Tuple[int, ModuloTermStateComponent]] = [initial_state]
    work_set = set(work_list)

    # To support MTBDDs we need to keep states as ints. Therefore, we have
    # to map the product states to ints as we are creating them.
    alias_store = AliasStore()

    result = NFA(alphabet=lin_automaton.alphabet, automaton_type=AutomatonType.NFA)
    result.initial_states = {alias_store.get_alias_for_state(initial_state)}

    def flat_post(state) -> Generator[Tuple[int, int], None, None]:
        for post_state in lin_automaton.get_state_post(state):
            for symbol in lin_automaton.get_symbols_leading_from_state_to_state(state, post_state):
                yield (post_state, symbol)

    def mod_accepts_with_symbol(mod_state: ModuloTermStateComponent, symbol: LSBF_Alphabet) -> bool:
        value_with_symbol_interp_as_sign = mod_state.value + vector_dot(symbol, mod_state.variable_coeficients)
        return value_with_symbol_interp_as_sign % mod_state.modulo == 0

    # Problems with alphabets - we are iterating over some (a, b, c, x) and the modulo automaton can have (x, y, z)
    # we need a function to convert (a, b, c, x) into {(x, 0, 0), ..., (x, 1, 1)}
    # To do so in an easier manner we identify the intersection of variables used project the symbol (a, b, c, x) onto
    # those and then generate (x, y, z) from the projected symbols.

    assert sorted(lin_automaton.used_variables) == lin_automaton.used_variables
    common_variables = sorted(set(lin_automaton.used_variables).intersection(modulo_relation_variables))
    alphabet = lin_automaton.alphabet
    modulo_alphabet_helper = LSBF_Alphabet.from_variable_ids(modulo_relation_variables)

    processed_states_counter = 0
    while work_list:
        current_product_state = work_list.pop(-1)
        work_set.remove(current_product_state)

        current_product_state_alias = alias_store.get_alias_for_state(current_product_state)
        current_lin_component, current_mod_component = current_product_state

        result.add_state(current_product_state_alias)

        for post_state, symbol in flat_post(current_lin_component):
            mod_symbols = modulo_alphabet_helper.cylindrify_projected_symbol_iter_all(
                alphabet.project_symbol_onto_variables(symbol, common_variables),
                common_variables
                )
            for mod_symbol in mod_symbols:
                mod_accepts = mod_accepts_with_symbol(current_mod_component, mod_symbol)
                lin_is_final = post_state in lin_automaton.final_states

                if mod_accepts and lin_is_final:
                    print('>>> Result', (current_mod_component, current_lin_component))
                    print('Overall processed states:', processed_states_counter)
                    return (current_mod_component, current_lin_component)

                mod_post_state = current_mod_component.generate_next(mod_symbol)
                dest_product_state = (post_state, mod_post_state)
                dest_product_state_alias = alias_store.get_alias_for_state(dest_product_state)

                # Check whether we should process this state again.
                in_result = dest_product_state_alias in result.states
                in_worklist = dest_product_state in work_set  # Use workset to speed up lookups

                if not in_result and not in_worklist:
                    work_list.append(dest_product_state)
                    work_set.add(dest_product_state)

                result.update_transition_fn(current_product_state_alias, symbol, dest_product_state_alias)
        processed_states_counter += 1
