from typing import (
    Set,
    List,
    Optional,
)


def pad_closure(nfa):
    """
    Performs inplace padding closure.

    Why is in a standalone function and not withing a NFA?:
        Because it utilizes the internal structure of transition function too much,
        therefore it makes it inconvenient when switching transition function implementations.  
    """
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



def pad_closure2(nfa):
    """
    Ensure that the automaton satisfies the saturation property.

    Saturation property:
        Given a word `w_1 \\dots w_n p` with the last symbol `p`, every word 
        created by repeating the padding symbol `p` should be accepted.
    """

    # Add a new final state so that the modifications to the automaton structure will not cause overapproximations
    new_final_state: Optional[int] = None

    for symbol in nfa.alphabet.symbols:
        states = set()
        work_list = []
        # Start by collecting all states that have a transition to a final state
        for final_state in nfa.final_states:
            for pre_state in nfa.transition_fn.get_state_pre_with_symbol(final_state, symbol):
                if pre_state not in states:
                    states.add(pre_state)
                    work_list.append(pre_state)

        # Collect all final states reaching a final state via words consisiting of repeated `symbol`
        while work_list:
            state = work_list.pop(-1)
            for pre_state in nfa.transition_fn.get_state_pre_with_symbol(state, symbol):
                if pre_state not in states:
                    states.add(pre_state)
                    work_list.append(pre_state)
        
        for state in states:
            has_transition_to_final = False
            # Check whether there exists a transition to the final state via the symbol
            for post_state in nfa.transition_fn.get_state_post_with_symbol(state, symbol):
                if post_state in nfa.final_states:
                    has_transition_to_final = True
                    break
            if not has_transition_to_final:
                # Maybe no new final states has been generated yet, generate it
                if new_final_state is None:
                    new_final_state = max(nfa.states) + 1
                    nfa.add_state(new_final_state)
                    nfa.add_final_state(new_final_state)

                nfa.update_transition_fn(state, symbol, new_final_state)


def pad_closure2_naturals(nfa):
    """
    Ensures the saturation property holds when solving over naturals.
    """
    # Add a new final state so that the modifications to the automaton structure will not cause overapproximations
    new_final_state: Optional[int] = None

    # When solving over naturals there is only one padding symbol - zero tuple
    padding_symbol = tuple(0 for i in range(len(nfa.alphabet.variable_numbers)))

    states = set()
    work_list = list(nfa.final_states)

    # Collect all states reaching a final state via words consisiting of repeated `symbol`
    while work_list:
        state = work_list.pop(-1)
        for pre_state in nfa.transition_fn.get_state_pre_with_symbol(state, padding_symbol):
            if pre_state not in states:
                states.add(pre_state)
                work_list.append(pre_state)

    # All the collected states should be accepting since we are solving over naturals, however
    # we cannot just make them accepting. Instead, add a new final state and link every predecesor
    # of these states via the accepting symbol

    # Collect all predecesors of the states reaching final with padding
    for state in states:
        for pre_state in nfa.transition_fn.get_state_pre(state):
            if state == pre_state:
                continue
            for symbol in nfa.transition_fn.get_symbols_between_states(pre_state, state):
                # Maybe no new final states has been generated yet, generate it
                if new_final_state is None:
                    new_final_state = max(nfa.states) + 1
                    nfa.add_state(new_final_state)
                    nfa.add_final_state(new_final_state)

                nfa.update_transition_fn(pre_state, symbol, new_final_state)


from amaya.transitions import SparseBDDTransitionFunction
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
