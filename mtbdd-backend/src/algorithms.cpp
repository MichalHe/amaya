#include <chrono>

#include <sylvan.h>
#include <sylvan_mtbdd.h>
#include "../include/base.hpp"
#include "../include/bit_set.hpp"
#include "../include/custom_leaf.hpp"
#include "../include/operations.hpp"

void sanity_check_state_numbers(NFA* nfa) {
    bool is_continuous_seq = true;
    bool seen_state = false;
    State last_state;

    for (State state : nfa->states) {
        if (!seen_state) {
            last_state = state;
            continue;
        }

        assert ((state - last_state) == 1);
        last_state = state;
    }
}


NFA do_pad_closure_using_bit_sets(NFA* nfa, Bit_Set::Block_Arena_Allocator* allocator) {
    if (nfa->states.empty()) return *nfa;

    sanity_check_state_numbers(nfa);

    LACE_ME;
    using namespace sylvan;

    Pad_Closure_Info2 pad_closure_info = {};
    g_pad_closure_info = &pad_closure_info;

    allocator->start_new_generation(nfa->states.size());

    Bit_Set::Bit_Set* initial_frontier = allocator->alloc();
    for (s64 state : nfa->final_states) {
        initial_frontier->add_state(state);
    }

    sylvan::MTBDD frontier = Bit_Set_Leaf::make_bit_set_leaf(initial_frontier);

    sylvan::mtbdd_ref(frontier);

    g_pad_closure_info->final_states_bits = initial_frontier;

    bool was_frontier_modified = true;
    while (was_frontier_modified) {

        MTBDD this_iter_start_frontier = frontier;  // Frontier created at the end of this iteration
        MTBDD this_iter_end_frontier   = frontier;  // Frontier after we propagate everything in this iteration

        sylvan::mtbdd_ref(this_iter_start_frontier);
        sylvan::mtbdd_ref(this_iter_end_frontier);

        for (auto& [origin, state_mtbdd]: nfa->transitions) {
            MTBDD tmp_frontier = mtbdd_applyp(state_mtbdd,
                                              this_iter_end_frontier,
                                              origin,
                                              TASK(build_pad_closure_bit_set_fronier_op),
                                              AMAYA_EXTEND_FRONTIER_OP_ID);

            sylvan::mtbdd_ref(tmp_frontier);
            sylvan::mtbdd_deref(this_iter_end_frontier);

            this_iter_end_frontier = tmp_frontier;
        }

        was_frontier_modified = (this_iter_end_frontier != this_iter_start_frontier);

        // frontier, start_frontier, end_frontier are all referenced
        sylvan::mtbdd_deref(frontier);
        frontier = this_iter_end_frontier;
        sylvan::mtbdd_deref(this_iter_start_frontier);
        // Only end_frontier is now referenced, and it is assigned above to fronier --->
        // only frontier is referenced
    }

    State new_final_state = *nfa->states.rbegin() + 1;
    g_pad_closure_info->new_final_state = new_final_state;

    NFA new_nfa = *nfa;

    const u64 current_pad_closure_id = get_next_operation_id();

    bool was_any_transition_added = false;
    for (auto& [state, state_transition_mtbdd]: nfa->transitions) {
        MTBDD new_transitions_mtbdd = mtbdd_applyp(state_transition_mtbdd,
                                                   frontier,
                                                   static_cast<u64>(state),
                                                   TASK(add_pad_transitions_bit_set_op),
                                                   current_pad_closure_id);

        // Increase the ref counter regardless of whether the automaton has been modified
        // to maintain the invariant that any automaton resulting from an operation should
        // have all of its mtbdds referenced. Therefore, an input automaton from Python
        // will have all its MTBDDs ref'd, the output automaton will have its MTBDD's ref'd
        // separetely, and thus python GC will correctly decrement ref counts for both automatons.
        sylvan::mtbdd_ref(new_transitions_mtbdd);
        new_nfa.transitions[state] = new_transitions_mtbdd;

        if (new_transitions_mtbdd != state_transition_mtbdd) {
            was_any_transition_added = true;
        }
    }

    if (was_any_transition_added) {
        new_nfa.states.insert(new_final_state);
        new_nfa.final_states.insert(new_final_state);
        PRINT_DEBUG("Added a new final state " << new_final_state << " during pad closue.");
    }


    allocator->dealloc(initial_frontier);

    sylvan::mtbdd_deref(frontier); // -frontier
    return new_nfa;
}
