from __future__ import annotations
from typing import (
    List,
    Tuple,
    Optional
)
from log import logger
from utils import vector_dot
from automatons import (
    DFA,
    LSBF_Alphabet,
    AutomatonType,
)
from relations_structures import Relation
import math


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

    while work_queue:
        currently_processed_state = work_queue.pop()
        dfa.add_state(currently_processed_state)

        # Check whether current state is final
        if currently_processed_state >= 0:
            dfa.add_final_state(currently_processed_state)

        for symbol in active_alphabet:
            dot = vector_dot(symbol, ineq.variable_coeficients)
            next_state = math.floor(0.5 * (currently_processed_state - dot))

            # Add newly discovered transition
            dfa.update_transition_fn(currently_processed_state, symbol, next_state)

            if not (dfa.has_state_with_value(next_state) or next_state in work_queue):
                work_queue.append(next_state)

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
            dot = vector_dot(alphabet_symbol, eq.variable_coeficients)
            next_value = current_state - dot

            if next_value % 2 == 0:
                next_state = int(next_value / 2)

                # Add the newly discovered transition
                dfa.update_transition_fn(current_state, alphabet_symbol, next_state)

                if not (dfa.has_state_with_value(next_state) or next_state in work_queue):
                    work_queue.append(next_state)
            else:
                # This means the the input tape and the absolute part differ in the currently read bit,
                # therefore, they cannot be equal -> no transition along the current symbol. However,
                # we would like the automaton to be complete, therefore add a trap state for such transitions.
                if trap_state is None:
                    trap_state = add_trap_state_to_automaton(dfa)
                dfa.update_transition_fn(current_state, alphabet_symbol, trap_state)

    return dfa


