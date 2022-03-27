from __future__ import annotations
import math
from typing import (
    List,
    Tuple,
    Optional
)

from amaya.automatons import (
    DFA,
    LSBF_Alphabet,
    AutomatonType,
)
from amaya import logger
from amaya.presburger.definitions import (
    AliasStore,
    AutomatonConstructor,
    can_build_modulo_automaton,
    DFA_AutomatonStateType,
    ModuloTermStateComponent,
)
from amaya.relations_structures import Relation
from amaya.utils import vector_dot


def sort_relation_var_vector_to_match_track_order(rel: Relation, var_id_pairs: List[Tuple[str, int]]):
    """
    Changes the order of variables and correspoding coeficients to match the order of tracks that belong to the them.
    """
    var_name_to_track_index: Dict[str, int] = dict(var_id_pairs)
    sorted_var_coef_pairs = sorted(zip(rel.variable_names, rel.variable_coeficients),
                                   key=lambda var_coef_pair: var_name_to_track_index[var_coef_pair[0]])
    rel.variable_names, rel.variable_coeficients = zip(*sorted_var_coef_pairs)


def build_dfa_from_linear_inequality(ineq: Relation,
                                     ineq_var_id_pairs: List[Tuple[str, int]],
                                     alphabet: LSBF_Alphabet,
                                     automaton_constr: AutomatonConstructor) -> DFA:
    """
    Construct an automaton accepting ineq solutions encoded in 2's complement binary encoding.

    :param ineq: Inequation that will have its solutions accepted by the created automaton.
    :param ineq_var_id_pairs: Variables present in the given inequation with their unique IDs. These pairs should be
                              ordered according to the variable ID (ascending).
    :param alphabet: Alphabet for the created automaton.
    :param automaton_constr: Constructor for the automaton.
    """
    logger.debug(f'Building DFA encoding the solutions of the inequation: {ineq}')

    dfa: DFA[DFA_AutomatonStateType] = DFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)
    dfa.add_initial_state(ineq.absolute_part)

    work_queue: List[DFA_AutomatonStateType] = [ineq.absolute_part]

    # We need to work only with alphabet symbols differing in the tracks of variables present in the relation
    active_alphabet = list(alphabet.gen_projection_symbols_onto_variables(ineq_var_id_pairs))

    sort_relation_var_vector_to_match_track_order(ineq, ineq_var_id_pairs)

    var_ids = [var_id_pair[1] for var_id_pair in ineq_var_id_pairs]

    while work_queue:
        currently_processed_state = work_queue.pop()
        dfa.add_state(currently_processed_state)

        # Check whether current state is final
        if currently_processed_state >= 0:
            dfa.add_final_state(currently_processed_state)

        for symbol in active_alphabet:
            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(var_ids, symbol)

            dot = vector_dot(symbol, ineq.variable_coeficients)
            next_state = math.floor(0.5 * (currently_processed_state - dot))

            # Add newly discovered transition
            dfa.update_transition_fn(currently_processed_state, cylindrified_symbol, next_state)

            if not (dfa.has_state_with_value(next_state) or next_state in work_queue):
                work_queue.append(next_state)

    dfa.used_variables = sorted(var_id_pair[1] for var_id_pair in ineq_var_id_pairs)

    logger.debug(f'The constructed DFA: {dfa}')

    return dfa


def build_dfa_from_sharp_linear_inequality(ineq: Relation,
                                           ineq_var_id_pairs: List[Tuple[str, int]],
                                           alphabet: LSBF_Alphabet,
                                           automaton_constr: AutomatonConstructor) -> DFA:
    """
    Construct an automaton accepting the solutions (over N) of given ineq encoded in binary.

    :param ineq: Inequation that will have its solutions accepted by the created automaton.
    :param ineq_var_id_pairs: Variables present in the given inequation with their unique IDs. These pairs should be
                              ordered according to the variable ID (ascending).
    :param alphabet: Alphabet for the created automaton.
    :param automaton_constr: Constructor for the automaton.
    """
    assert ineq.operation == '<'

    # Since we are dealing with a discrete domain:
    ineq.absolute_part -= 1
    ineq.operation = '<='

    ineq_dfa = build_dfa_from_linear_inequality(ineq)

    return ineq_dfa


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
    Construct a DFA with language that is the solution space (over N) of the given equation using binary encoding.
    """
    dfa: DFA[DFA_AutomatonStateType] = DFA(alphabet=alphabet, automaton_type=AutomatonType.DFA)
    dfa.add_initial_state(eq.absolute_part)

    work_queue: List[DFA_AutomatonStateType] = [eq.absolute_part]

    sort_relation_var_vector_to_match_track_order(eq, eq_var_id_pairs)
    var_ids = [var_id_pair[1] for var_id_pair in eq_var_id_pairs]

    # We need to work only with alphabet symbols differing in the tracks of variables present in the relation
    active_alphabet = list(alphabet.gen_projection_symbols_onto_variables(eq_var_id_pairs))

    trap_state: Optional[int] = None
    while work_queue:
        current_state = work_queue.pop()
        dfa.add_state(current_state)

        # Check whether the current state is accepting (condition: accepts an empty word)
        if current_state == 0:
            dfa.add_final_state(current_state)

        for alphabet_symbol in active_alphabet:
            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(var_ids, alphabet_symbol)

            dot = vector_dot(alphabet_symbol, eq.variable_coeficients)
            next_value = current_state - dot

            if next_value % 2 == 0:
                next_state = int(next_value / 2)

                # Add the newly discovered transition
                dfa.update_transition_fn(current_state, cylindrified_symbol, next_state)

                if not (dfa.has_state_with_value(next_state) or next_state in work_queue):
                    work_queue.append(next_state)
            else:
                # This means the the input tape and the absolute part differ in the currently read bit,
                # therefore, they cannot be equal -> no transition along the current symbol. However,
                # we would like the automaton to be complete, therefore add a trap state for such transitions.
                if trap_state is None:
                    trap_state = add_trap_state_to_automaton(dfa)
                dfa.update_transition_fn(current_state, cylindrified_symbol, trap_state)

    dfa.used_variables = sorted(var_id_pair[1] for var_id_pair in eq_var_id_pairs)

    return dfa


def build_presburger_modulo_dfa(equality: Relation,
                                eq_var_id_pairs: List[Tuple[str, int]],
                                alphabet: LSBF_Alphabet,
                                constr: AutomatonConstructor) -> DFA:
    """
    Construct a DFA acception the solutions (natural numbers) of the given equality of the form `(a.x mod C) = K`.

    The equality must contain only 1 modulo term and no other freestanding variable terms.
    """

    logger.info('Building modulo-DFA for provided relation: {0}'.format(equality))

    can_construct_automaton = can_build_modulo_automaton(equality)
    assert can_construct_automaton is True, f'Cannot construct automaton for {equality}: {can_construct_automaton}'

    dfa = constr(alphabet=alphabet, automaton_type=AutomatonType.DFA)

    variable_name_to_id: Dict[str, int] = dict(eq_var_id_pairs)
    variable_ids = sorted(variable_name_to_id.values())
    projected_alphabet = list(alphabet.gen_projection_symbols_onto_variables(variable_ids))

    variable_name_to_track_index: Dict[str, int] = dict(
        (var_id_pair[0], i) for i, var_id_pair in enumerate(eq_var_id_pairs)
    )

    modulo_term = equality.modulo_terms[0]

    vars_with_coefs = zip(modulo_term.variables, modulo_term.variable_coeficients)
    variable_coefs_ord_by_track = sorted(vars_with_coefs, key=lambda vc: variable_name_to_track_index[vc[0]])

    initial_state = ModuloTermStateComponent(value=equality.absolute_part,
                                             modulo=modulo_term.modulo,
                                             variable_coeficients=tuple(vc[1] for vc in variable_coefs_ord_by_track))

    print(f'{initial_state.variable_coeficients=}')

    alias_store = AliasStore()
    work_list: List[ModuloTermStateComponent] = [initial_state]
    work_set: Set[ModuloTermStateComponent] = set(work_list)

    dfa.add_initial_state(alias_store.get_alias_for_state(initial_state))

    while work_list:
        current_state = work_list.pop(-1)
        current_state_alias = alias_store.get_alias_for_state(current_state)
        work_set.remove(current_state)

        logger.debug('Processing metastate {0} (aka {1}), remaining in work list: {2}'.format(
            current_state, current_state_alias, len(work_list)
        ))

        dfa.add_state(current_state_alias)

        if current_state.value == 0:
            dfa.add_final_state(current_state_alias)

        for symbol in projected_alphabet:
            cylindrified_symbol = alphabet.cylindrify_symbol_of_projected_alphabet(variable_ids, symbol)
            destination_state = current_state.generate_next(symbol)

            if destination_state is None:
                continue

            destination_state_alias = alias_store.get_alias_for_state(destination_state)

            dfa.update_transition_fn(current_state_alias, cylindrified_symbol, destination_state_alias)

            if not dfa.has_state_with_value(destination_state_alias) and destination_state not in work_set:
                work_list.append(destination_state)
                work_set.add(destination_state)

    logger.info('Done. Built DFA with {0} states ({1} {2} final).'.format(
        len(dfa.states), len(dfa.final_states), 'is' if len(dfa.final_states) == 1 else 'are'
    ))

    dfa.used_variables = sorted(var_id_pair[1] for var_id_pair in eq_var_id_pairs)
    # Alias store maps the rich information about modulo states to ints, create reverse mapping for debugging purposes
    dfa.state_labels = dict((state, label) for label, state in alias_store.data.items())
    return dfa
