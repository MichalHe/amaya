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


# TODO: Make automata not be generic anymore (hardcode ints)
DFA_AlphabetSymbolType = Tuple[int, ...]
DFA_AutomatonStateType = int



NFA_AlphabetSymbolType = Tuple[int, ...]
NFA_AutomatonStateType = int
AutomatonConstructor = Callable[[LSBF_Alphabet, AutomatonType], NFA]


def project_symbol_onto_tracks(symbol: Tuple[int, ...], track_indices: List[int]) -> Tuple[int, ...]:
    return tuple(symbol[i] for i in track_indices)


def identify_tracks_used_by_ineq_components(relation_variables: List[str], relation: Relation) -> List[List[int]]:
    '''
    Identifies tracks used by the individual components of the relation.

    The relation has exactly one nonmodular compoment and zero or more modular components.
    The returned list has always the first entry indices used by the nonmodular component and the rest by the modular 
    ones in the same order as stored in the relation.

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
