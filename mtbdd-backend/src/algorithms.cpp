#include <chrono>

#include <sylvan.h>
#include <sylvan_mtbdd.h>
#include "../include/base.hpp"
#include "../include/bit_set.hpp"
#include "../include/custom_leaf.hpp"
#include "../include/operations.hpp"

/*
The bit sets used as the pad-closure frontier are indexed by the state *number* (`Bit_Set::add_state`
does `data[state / 64] |= ...`), so a generation has to be sized by the largest state number present,
not by how many states there are. The two coincide only when the states are numbered 0..n-1; amaya
numbers them from 1, which made the old `states.size()` sizing one bit short and let the frontier
write a u64 past its allocation whenever the state count was a multiple of 64.
*/
u64 count_bits_needed_to_index_states(NFA* nfa) {
    if (nfa->states.empty()) return 0;
    return static_cast<u64>(*nfa->states.rbegin()) + 1;
}


NFA do_pad_closure_using_bit_sets(NFA* nfa, Bit_Set::Block_Arena_Allocator* allocator) {
    if (nfa->states.empty()) return *nfa;

    g_pad_closure_stats.calls += 1;
    g_pad_closure_stats.states_seen += nfa->states.size();
    auto pad_stats_frontier_start = std::chrono::steady_clock::now();

    LACE_ME;
    using namespace sylvan;

    Pad_Closure_Info2 pad_closure_info = {};
    g_pad_closure_info = &pad_closure_info;

    allocator->start_new_generation(count_bits_needed_to_index_states(nfa));

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

        g_pad_closure_stats.frontier_passes += 1;

        for (auto& [origin, state_mtbdd]: nfa->transitions) {
            g_pad_closure_stats.frontier_applies += 1;
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

    g_pad_closure_stats.frontier_seconds +=
        std::chrono::duration<double>(std::chrono::steady_clock::now() - pad_stats_frontier_start).count();
    auto pad_stats_augment_start = std::chrono::steady_clock::now();

    State new_final_state = *nfa->states.rbegin() + 1;
    g_pad_closure_info->new_final_state = new_final_state;

    NFA new_nfa = *nfa;

    const u64 current_pad_closure_id = get_next_operation_id();

    bool was_any_transition_added = false;
    for (auto& [state, state_transition_mtbdd]: nfa->transitions) {
        g_pad_closure_stats.augment_applies += 1;
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


    g_pad_closure_stats.augment_seconds +=
        std::chrono::duration<double>(std::chrono::steady_clock::now() - pad_stats_augment_start).count();

    allocator->dealloc(initial_frontier);

    sylvan::mtbdd_deref(frontier); // -frontier
    return new_nfa;
}
