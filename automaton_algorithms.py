from typing import (
    Set,
    List,
)


def pad_closure(nfa):
    '''Performs inplace padding closure.

    Why is in a standalone function and not withing a NFA? - Because it utilizes the internal structure of
    transition function too much, therefore it makes it inconvenient when switching transition function implementations.  
    '''
    finishing_set: Set = set()
    for final_state in nfa.final_states:
        finishing_states = nfa.transition_fn.get_states_with_post_containing(final_state)
        finishing_set.update(finishing_states)

    work_queue: List = list(finishing_set)
    while work_queue:
        # Current state has transition to final for sure
        current_state = work_queue.pop()

        potential_states = nfa.transition_fn.get_states_with_post_containing(current_state)
        for potential_state in potential_states:
            symbols_from_potential_to_current = nfa.transition_fn.get_symbols_between_states(potential_state, current_state)
            symbols_from_current_to_final = nfa.transition_fn.get_symbols_between_states(current_state, final_state)

            # Mark(BDD) - This needs to be calculated via BDD
            intersect = symbols_from_potential_to_current.intersection(symbols_from_current_to_final)

            # Lookup symbols leading from potential state to final to see whether something changed
            symbols_from_potential_to_final = nfa.transition_fn.get_symbols_between_states(potential_state, final_state)

            # (intersect - symbols_from_potential_to_final)  ===> check whether intersect brings any new symbols to transitions P->F
            if intersect and (intersect - symbols_from_potential_to_final):
                # Propagate the finishing ability
                if nfa.transition_fn.is_in_state_post(potential_state, final_state):
                    # Some transition from potential to final was already made - just update it

                    # Mark(BDD): This manipulates internal structure.
                    nfa.transition_fn.data[potential_state][final_state].update(intersect)
                else:
                    # Mark(BDD): This manipulates internal structure.
                    # There is no transition from potential to final
                    nfa.transition_fn.data[potential_state][final_state] = intersect

                # We need to check all states that could reach 'potential' -- they can now become finishing
                if potential_state not in work_queue and potential_state != current_state:
                    work_queue.append(potential_state)


from transitions import SparseBDDTransitionFunction
from typing import Dict


def determinize_bdd(initial_states: List, final_states: List,
                    tfn: SparseBDDTransitionFunction) -> Dict:
    '''Given a NFA description with transition function based on BDDs, 
    produces DFA using the set construction.
    '''
    initial_state = tuple(initial_states)
    work_queue: List = [initial_state]

    final_set: Set = set(final_states)

    result_states: Set = set()
    result_final_states: Set = set()
    resulting_transition_fn: SparseBDDTransitionFunction = SparseBDDTransitionFunction(tfn.manager, tfn.alphabet)

    while work_queue:
        cs = work_queue.pop()  # Current State
        result_states.add(cs)

        for composite_state_part in cs:
            if composite_state_part in final_set:
                result_final_states.add(cs)

        minterms = tfn.get_minterm_system_from_states(list(cs))

        for destination, minterm in minterms.items():
            if tfn.manager.to_expr(minterm) == 'FALSE':
                continue

            resulting_transition_fn.insert_transition_bdd(cs, minterm, destination)

            # If this is a new state - add to queue
            if destination not in result_states:
                if destination not in work_queue:
                    work_queue.append(destination)

    # TODO: This will be probably changed to return a DFA when the implementation is using BDDs
    return {
        'states': result_states,
        'initial_states': {initial_state, },
        'transition_fn': resulting_transition_fn,
        'final_states': result_final_states
    }