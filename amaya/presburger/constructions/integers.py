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
    Type,
    Union,
)

from amaya.automatons import (
    AutomatonType,
    LSBF_Alphabet,
    NFA,
)
from amaya import logger
from amaya.presburger.definitions import(
    AliasStore,
    AutomatonConstructor,
    NFA_AutomatonStateType,
    ModuloTermStateComponent,
)
from amaya.relations_structures import Congruence, Relation, Var
from amaya.utils import vector_dot
from amaya.semantics_tracking import (
    AH_Atom,
    AH_AtomType
)


@dataclass(frozen=True)
class LinearStateComponent(object):
    value: int
    variable_coefficients: Tuple[int, ...]

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        raise NotImplementedError('The LinearStateComponent should not be instantiated directly, use its subclasses')


class IneqLinearStateComponent(LinearStateComponent):
    def __init__(self, value: int, variable_coefficients: Tuple[int, ...]):
        super().__init__(value, variable_coefficients)

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        dot = vector_dot(alphabet_symbol, self.variable_coefficients)
        destination_state = math.floor(0.5 * (self.value - dot))
        return IneqLinearStateComponent(value=destination_state,
                                        variable_coefficients=self.variable_coefficients)


class EqLinearStateComponent(LinearStateComponent):
    def __init__(self, value: int, variable_coefficients: Tuple[int, ...]):
        super().__init__(value, variable_coefficients)

    def generate_next(self, alphabet_symbol: Tuple[int, ...]) -> Optional[LinearStateComponent]:
        dot = vector_dot(alphabet_symbol, self.variable_coefficients)
        diff = self.value - dot

        if diff % 2 == 1:
            return None

        return EqLinearStateComponent(value=diff // 2,
                                      variable_coefficients=self.variable_coefficients)


# This is used in the formula->NFA procedure. The created NFA has int automaton states
InterimAutomatonState = Tuple[Union[LinearStateComponent, ModuloTermStateComponent], ...]
TransitionPredicate = Callable[[InterimAutomatonState, Tuple[int, ...], InterimAutomatonState], bool]


def build_presburger_linear_nfa_from_initial_state(initial_state: LinearStateComponent,
                                                   is_transition_final: TransitionPredicate,
                                                   vars: List[Var],
                                                   nfa: NFA) -> NFA:
    """
    Abstract algorithm to build automaton from the given atomic presburger formula.

    The logic that decides what states are direct successors of the currently processed
    state is contained in the state components.

    :param initial_state: The state that will be initial for the nfa. As a LinearStateComponent contains logic
                          how to generate successors.
    :param is_transition_final: Predicate to determine which generated transition should also lead to the final state.
    :param relation_variable_with_ids: Variables of the overall alphabet that are used in the relation.
    :param nfa: The empty nfa to give structure to.
    :returns: The passed nfa with structure encoding solution space of the relation.
    """

    # We have to postpone the addition of final state, since it has to have
    # unique number and that we cannot tell until the end
    f_transitions = []

    work_list: List[LinearStateComponent] = [initial_state]
    work_set: Set[LinearStateComponent] = set(work_list)  # Seed up checking the presence in the work_list

    projected_alphabet = tuple(nfa.alphabet.gen_projection_symbols_onto_variables(vars))

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

            cylindrified_symbol = nfa.alphabet.cylindrify_symbol_of_projected_alphabet(vars, alphabet_symbol)
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

    nfa.used_variables = list(vars)
    return nfa


def build_nfa_from_linear_inequality(nfa_type: Type[NFA], alphabet: LSBF_Alphabet, ineq: Relation) -> NFA:

    initial_state = IneqLinearStateComponent(value=ineq.rhs, variable_coefficients=tuple(ineq.coefs))

    def is_transition_final(source: LinearStateComponent,
                            symbol: Tuple[int, ...],
                            target: LinearStateComponent) -> bool:
        dot = vector_dot(symbol, source.variable_coefficients)
        if source.value + dot >= 0:
            return True
        return False

    nfa = nfa_type(automaton_type=AutomatonType.NFA,
                   alphabet=alphabet,
                   state_semantics=AH_Atom(atom_type=AH_AtomType.PRESBURGER_LE, atom=ineq))

    nfa.add_initial_state(initial_state.value)

    nfa = build_presburger_linear_nfa_from_initial_state(initial_state, is_transition_final, ineq.vars, nfa)
    nfa.state_semantics.special_state = next(iter(nfa.final_states))
    return nfa


def build_nfa_from_linear_equality(nfa_type: Type[NFA], alphabet: LSBF_Alphabet, eq: Relation) -> NFA:
    initial_state = EqLinearStateComponent(value=eq.rhs, variable_coefficients=tuple(eq.coefs))

    nfa = nfa_type(automaton_type=AutomatonType.NFA,
                   alphabet=alphabet,
                   state_semantics=AH_Atom(atom_type=AH_AtomType.PRESBURGER_EQ, atom=eq))

    nfa.add_initial_state(initial_state.value)

    def is_transition_final(source: LinearStateComponent,
                            symbol: Tuple[int, ...],
                            target: LinearStateComponent) -> bool:
        dot = vector_dot(symbol, source.variable_coefficients)
        if source.value + dot == 0:
            return True
        return False

    nfa = build_presburger_linear_nfa_from_initial_state(initial_state, is_transition_final, list(eq.vars), nfa)
    nfa.state_semantics.special_state = next(iter(nfa.final_states))
    return nfa


def build_presburger_congruence_nfa(nfa_type: Type[NFA],
                                    alphabet: LSBF_Alphabet,
                                    congruence: Congruence) -> NFA:
    """
    Builds an NFA encoding the solutions to given congurence relation.

    :param nfa: An empty NFA that will have its structure formed to encode the modulo relation.
    :param relation: Relation of the form described abouve that should be encoded with the automaton.
    :param relation_variables_with_ids: The sorted (by ID) list of variable names with their IDs.
                                        Required so we know which tracks of the overall alphabet are used.
    """

    logger.info('Building NFA for provided congruence: %s', congruence)

    nfa = nfa_type(automaton_type=AutomatonType.NFA,
                   alphabet=alphabet,
                   state_semantics=AH_Atom(atom_type=AH_AtomType.PRESBURGER_CONGRUENCE, atom=congruence))

    projected_alphabet = tuple(nfa.alphabet.gen_projection_symbols_onto_variables(congruence.vars))

    initial_state = ModuloTermStateComponent(value=congruence.rhs,
                                             modulo=congruence.modulus,
                                             variable_coefficients=tuple(congruence.coefs))

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
            cylindrified_symbol = nfa.alphabet.cylindrify_symbol_of_projected_alphabet(congruence.vars, symbol)
            destination_state = current_state.generate_next(symbol)

            if destination_state is None:
                continue

            destination_state_alias = alias_store.get_alias_for_state(destination_state)

            nfa.update_transition_fn(current_state_alias, cylindrified_symbol, destination_state_alias)

            # Make nondeterministic guess that the current symbol is the last on the input tape.
            value_with_symbol_interp_as_sign = current_state.value + vector_dot(symbol, congruence.coefs)
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

    logger.info('Done. Built NFA with %d states (%d %s final).',
                len(nfa.states), len(nfa.final_states), 'is' if len(nfa.final_states) == 1 else 'are')

    nfa.used_variables = list(congruence.vars)
    # nfa.state_labels = StateLabelUnaryNode(labels=dict((state, label) for label, state in alias_store.data.items()), child=None)
    nfa.extra_info['aliases'] = alias_store
    nfa.state_semantics.special_state = next(iter(nfa.final_states))
    return nfa
