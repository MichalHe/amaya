from __future__ import annotations
from dataclasses import dataclass
import math
from typing import (
    Callable,
    Dict,
    List,
    Optional,
    Set,
    Tuple,
    Union,
)

from automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from log import logger
from presburger.definitions import(
    AutomatonConstructor,
    NFA_AutomatonStateType,
)
from relations_structures import Relation
from utils import vector_dot


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
    work_set: Set[LinearStateComponent] = set(work_list)  # Seed up checking the presence in the work_list

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

            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(relation_variable_ids,
                                                                                   alphabet_symbol)
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
    """
    Construct an NFA accepting the solutions of given inequation encoded using 2's complement.
    """

    initial_state = IneqLinearStateComponent(value=ineq.absolute_part,
                                             variable_coeficients=tuple(ineq.variable_coeficients))

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
    """
    Construct an NFA accepting the solutions of given equation encoded using 2's complement.
    """

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
