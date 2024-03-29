from collections import defaultdict
from functools import reduce
from typing import (
    Callable,
    List,
    Optional,
    Set,
    Tuple,
)

from amaya.automatons import (
    AutomatonType,
    DFA,
    LSBF_Alphabet,
    NFA
)
from amaya.presburger.definitions import AliasStore
from amaya import logger
from amaya.transitions import symbols_intersect
from amaya.alphabet import uncompress_transition_symbol
from amaya.semantics_tracking import (
    AH_AtomType,
    AH_Determinization,
    AH_Intersection,
)


def pad_closure(nfa: NFA):
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



def pad_closure2(nfa: NFA) -> Optional[int]:
    """
    Ensure that the automaton satisfies the saturation property.

    Saturation property:
        Given a word `w_1 \\dots w_n p` with the last symbol `p`, every word
        created by repeating the padding symbol `p` should be accepted.
    """

    # Add a new final state so that the modifications to the automaton structure will not cause overapproximations
    new_final_state: Optional[int] = None
    local_alphabet = nfa.alphabet.gen_projection_symbols_onto_variables(nfa.used_variables)
    for symbol in local_alphabet:
        symbol = nfa.alphabet.cylindrify_symbol_of_projected_alphabet(nfa.used_variables, symbol)
        states = set()
        work_list = []

        # Start by collecting all states that can reach a final state by 1 transition
        for final_state in nfa.final_states:
            for pre_state in nfa.transition_fn.get_state_pre_with_symbol(final_state, symbol):
                if pre_state not in states:
                    states.add(pre_state)
                    work_list.append(pre_state)

        # Collect all states that can reach a final state with 1+ transitions with current symbol
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
    return new_final_state


def pad_closure2_naturals(nfa) -> Optional[int]:
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
    return new_final_state


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


Macrostate = Tuple[int, ...]

def abstract_determinize(nfa: NFA, compress_macrostate: Callable[[NFA, Macrostate], Macrostate], track_semantics: bool = False) -> DFA:
    """Determinize given NFA using a macrostate compression function."""
    alias_store = AliasStore()

    initial_state = compress_macrostate(nfa, tuple(sorted(nfa.initial_states)))
    initial_state_alias = alias_store.get_alias_for_state(initial_state)

    dfa = DFA(alphabet=nfa.alphabet, automaton_type=AutomatonType.DFA, initial_states={initial_state_alias},
              state_semantics=AH_Determinization(child=nfa.state_semantics), used_variables=nfa.used_variables)

    work_set = {initial_state}

    while work_set:
        macrostate = work_set.pop()
        macrostate_id = alias_store.get_alias_for_state(macrostate)

        dfa.add_state(macrostate_id)
        if not set(macrostate).isdisjoint(nfa.final_states):
            dfa.add_final_state(macrostate_id)

        for symbol in nfa.alphabet.gen_symbols_for_relevant_variables(nfa.used_variables):
            macrostate_member_posts = (set(nfa.get_transition_target(sc, symbol)) for sc in macrostate)
            post_macrostate = compress_macrostate(nfa, tuple(sorted(reduce(set.union, macrostate_member_posts))))
            post_macrostate_id = alias_store.get_alias_for_state(post_macrostate)

            dfa.update_transition_fn(macrostate_id, symbol, post_macrostate_id)

            if not (post_macrostate_id in dfa.states or post_macrostate in work_set):
                work_set.add(post_macrostate)

    if track_semantics:
        state_labels = {macrostate_id: macrostate_label for macrostate_label, macrostate_i in alias_store.data.items()}
        dfa.state_semantics.state_labels = state_labels
        
    return dfa


def create_compression_function_for_intersection_of_atoms(nfa: NFA, state_semantics: AH_Intersection) -> Callable[[Macrostate], Macrostate]:
    mod_atom_indices = tuple(
        atom_index for atom_index, atom in enumerate(state_semantics.children) if atom.atom_type == AH_AtomType.PRESBURGER_CONGRUENCE
    )
    # @Optimize: This is not the most efficient way to do it, however, it is not called offen
    lin_atom_indices = tuple(i for i in range(len(state_semantics.children)) if i not in mod_atom_indices)
    final_state_semantics = tuple(child.final_state for child in state_semantics.children)

    def is_state_covered_by_state(state: Tuple[int, ...], covering_state: Tuple[int, ...]) -> bool:
        if state == covering_state:
            # Every state simulates itself. Return False, so we won't remove every state based on this self simulation.
            return False
        return all(state[i] <= covering_state[i] for i in lin_atom_indices)

    def compression_function(nfa: NFA, macrostate: Macrostate) -> Macrostate:
        # Split the members of the macrostate into buckets based on the values of modulo atoms
        mod_buckets: Dict[Tuple[int, ...], Tuple[int, Set[Tuple[int, ...]]]] = defaultdict(set)
        compressed_macrostate: List[int] = []

        for member in macrostate:
            member_semantics = state_semantics.state_labels.get(member)
            if not member_semantics:
                # We are dealing with effective semantics, thus there might be some unary nodes above in the semantics
                # tree adding states without semantics, e.g., padding closure after projection adds a state.
                compressed_macrostate.append(member)
                continue

            if member in nfa.final_states:
                # A final state is not simulated by anything when dealing with an intersection of atoms. This is not
                # necessary as we could still rely on state semantics, since the values in the semantics tuple belonging
                # to modulo components would be unique to the final state.
                compressed_macrostate.append(member)
                continue

            mod_atom_values = tuple(member_semantics[i] for i in mod_atom_indices)
            mod_buckets[mod_atom_values].add((member, member_semantics))
        
        for mod_bucket, bucket_values in mod_buckets.items():
            bucket_values_not_covered = set(bucket_values)
            for bucket_value in bucket_values:
                bucket_value_state_id, bucket_value_semantics = bucket_value
                if any((is_state_covered_by_state(bucket_value_semantics, other_bucket_value[1]) for other_bucket_value in bucket_values)):
                    bucket_values_not_covered.remove(bucket_value)
            
            compressed_macrostate.extend(bucket_value_not_covered[0] for bucket_value_not_covered in bucket_values_not_covered)
        
        result = tuple(sorted(compressed_macrostate))
        logger.info('[Macrostate compression] Compressed %s into %s', macrostate, result)
        return result
    return compression_function
