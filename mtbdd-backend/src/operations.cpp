#include "../include/operations.hpp"
#include "../include/custom_leaf.hpp"
#include "../include/base.hpp"
#include "../include/bit_set.hpp"

#include <sylvan.h>
#include <sylvan_common.h>
#include <sylvan_mtbdd.h>
#include <sylvan_bdd.h>
#include <sylvan_mt.h>
#include <sylvan_int.h>
#include <sylvan_mtbdd_int.h>
#include <sylvan_stats.h>
#include <lace.h>

#include <unistd.h>
#include <assert.h>
#include <stdio.h>

#include <algorithm>
#include <unordered_set>
#include <utility>
#include <iostream>
#include <vector>
#include <map>
#include <string>
#include <sstream>

using std::set;
using std::stringstream;
using std::string;
using std::pair;

using sylvan::MTBDD;
using sylvan::mtbdd_makeleaf;
using sylvan::mtbdd_false;
using sylvan::mtbdd_isleaf;
using sylvan::mtbdd_getvalue;
using sylvan::mtbdd_invalid;
using sylvan::mtbdd_applyp_CALL;

/**
 * Global variables:
 */
void*       REMOVE_STATES_OP_PARAM = NULL;
uint64_t    REMOVE_STATES_OP_COUNTER = 0;
void*       ADD_TRAPSTATE_OP_PARAM = NULL;

State_Rename_Op_Info *STATE_RENAME_OP_PARAM = NULL;

uint64_t  ADD_TRAPSTATE_OP_COUNTER = (1LL << 32);
uint64_t  STATE_RENAME_OP_COUNTER = (1LL << 33);

/**
 * Dynamic operation ID management.
 */
u64 g_operation_id = AMAYA_DYNAMIC_OP_ID_START;
u64 get_next_operation_id() {
    u64 operation_id = g_operation_id;
    g_operation_id += AMAYA_DYNAMIC_OP_ID_START;
    return operation_id;
}

/**
* Data necessary for applying pad closure to a single automaton.
*/
Pad_Closure_Info2* g_pad_closure_info = nullptr;

/**
 * Unites the two transition MTBDDs.
 */
u64 union_applied_cnt = 0;

TASK_IMPL_3(MTBDD, transitions_union_op, MTBDD *, left_op_ptr, MTBDD *, right_op_ptr, uint64_t, param)
{
    MTBDD left_mtbdd = *left_op_ptr, right_mtbdd = *right_op_ptr;

    if (left_mtbdd == mtbdd_false)  return right_mtbdd;
    if (right_mtbdd == mtbdd_false) return left_mtbdd;

    if (mtbdd_isleaf(left_mtbdd) && mtbdd_isleaf(right_mtbdd)) {

        auto left_contents  = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(left_mtbdd));
        auto right_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(right_mtbdd));

        Transition_Destination_Set leaf_contents;

        std::set_union(left_contents->destination_set.begin(), left_contents->destination_set.end(),
                       right_contents->destination_set.begin(), right_contents->destination_set.end(),
                       std::inserter(leaf_contents.destination_set, leaf_contents.destination_set.begin()));

        union_applied_cnt += 1;

        MTBDD union_leaf = make_set_leaf(&leaf_contents);
        return union_leaf;
    }

    return sylvan::mtbdd_invalid;
}

/**
 * 'Abstraction' operation defines what happens to MTBDD subtrees when a variable is projected away.
 * We perform an union of the subtrees trees.
 */
TASK_IMPL_3(MTBDD, project_variable_away_abstract_op, MTBDD, left_mtbdd, MTBDD, right_mtbdd, int, k)
{
    MTBDD u = mtbdd_applyp(left_mtbdd, right_mtbdd, (uint64_t)-1, TASK(transitions_union_op), AMAYA_EXISTS_OPERATION_ID);
    return u;
}

/**
 * NOTES:
 * The param is actually not used, since the (const) param would cause the sylvan cache to return
 * a result from some previous remove-states-op application.
 */
TASK_IMPL_2(MTBDD, remove_states_op, MTBDD, dd, uint64_t, param) {
    if (dd == mtbdd_false) return mtbdd_false;

    if (mtbdd_isleaf(dd)) {
        // Param is ignored, instead use the global variable REMOVE_STATES_OP_PARAM
        (void) param;

        auto states_to_remove = (set<State>*) (REMOVE_STATES_OP_PARAM);
        auto tds = (Transition_Destination_Set *) mtbdd_getvalue(dd);

        auto new_tds = new Transition_Destination_Set(); // Make leaf value copy.

        for (auto state : tds->destination_set) {
            bool should_persist = states_to_remove->find(state) == states_to_remove->end();
            if (should_persist) new_tds->insert_sorted(state);
        }

        if (new_tds->destination_set.empty()) {
            delete new_tds;
            return mtbdd_false;
        }

        MTBDD leaf = make_set_leaf(new_tds);
        delete new_tds;
        return leaf;
    }

    return mtbdd_invalid;
}


TASK_IMPL_2(MTBDD, rename_states_op, MTBDD, dd, uint64_t, param) {
    if (dd == mtbdd_false) return mtbdd_false;

    if (mtbdd_isleaf(dd)) {
        (void) param;
        auto state_rename_info = STATE_RENAME_OP_PARAM;
        auto old_tds = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(dd));

        // Do a heap allocation here, so that we can call mtbdd_makeleaf directly, avoiding copying state contents.
        auto new_leaf_contents = new Transition_Destination_Set();

        for (auto state : old_tds->destination_set) {
            auto new_name_it = state_rename_info->states_rename_map->find(state);

            if (new_name_it == state_rename_info->states_rename_map->end()) {
                printf("We have found a leaf state with no mapping for it??");
                printf("State name: %lu\n", state);
                printf("Available mappings:");
                for (auto mapping : *state_rename_info->states_rename_map) {
                    printf("(%lu, %lu)", mapping.first, mapping.second);
                }

                assert(false);
            }

            auto new_state_name = new_name_it->second;

            new_leaf_contents->insert(new_state_name);
        }

        new_leaf_contents->sort();
        return mtbdd_makeleaf(g_solver_context->leaf_id_store.transition_set,
                              reinterpret_cast<uint64_t>(new_leaf_contents));
    }

    return mtbdd_invalid;
}


void write_mtbdd_dot_to_tmp_file(const std::string& filename, sylvan::MTBDD mtbdd) {
    std::string output_path = "/tmp/" + filename;
    auto output_file_handle = fopen(output_path.c_str(), "w");
    sylvan::mtbdd_fprintdot(output_file_handle, mtbdd);
    fclose(output_file_handle);
}


template<typename T>
std::string array_to_str(T* array, const uint64_t array_size) {
    stringstream string_stream;
    string_stream << "[";
    if (!array_size) {
        string_stream << "]";
        return string_stream.str();
    }

    string_stream << (uint64_t) array[0];
    for (uint64_t i = 1; i < array_size; i++) {
        string_stream << "," << (uint64_t) array[i];
    }
    string_stream << "]";
    return string_stream.str();
}


TASK_IMPL_3(MTBDD, build_pad_closure_fronier_op, MTBDD *, p_extension, MTBDD *, p_frontier, u64, raw_extension_origin_state)
{
    State extension_origin_state = static_cast<State>(raw_extension_origin_state);
    MTBDD extension = *p_extension, frontier = *p_frontier;

    if (extension == mtbdd_false) {
        return frontier;
    }

    if (frontier == mtbdd_false) {
        return mtbdd_false;
    }

    if (mtbdd_isleaf(extension) && mtbdd_isleaf(frontier)) {
        auto extension_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(extension));
        auto frontier_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(frontier));

        bool is_already_present = std::binary_search(frontier_contents->destination_set.begin(),
                                                     frontier_contents->destination_set.end(),
                                                     extension_origin_state);

        if (is_already_present) {
            return frontier;
        }


        // Check whether there is a state Q such that the following run is possible: O -(a)-> Q -(a*) F
        if (!is_set_intersection_empty(extension_contents->destination_set, frontier_contents->destination_set)) {
            Transition_Destination_Set new_frontier_contents(*frontier_contents);
            new_frontier_contents.insert(extension_origin_state);
            new_frontier_contents.sort();
            MTBDD new_frontier = make_set_leaf(&new_frontier_contents);
            return new_frontier;
        }

        return frontier;
    }

    return mtbdd_invalid;
}

TASK_IMPL_3(MTBDD, build_pad_closure_bit_set_fronier_op, MTBDD *, p_extension, MTBDD *, p_frontier, u64, raw_extension_origin_state)
{
    State state_to_extend_frontier_with = static_cast<State>(raw_extension_origin_state);
    MTBDD extension = *p_extension;  // Set_Leaf
    MTBDD frontier  = *p_frontier;   // Bit_Set

    if (extension == mtbdd_false) {
        return frontier;
    }

    if (frontier == mtbdd_false) {
        return mtbdd_false;
    }


    if (mtbdd_isleaf(extension) && mtbdd_isleaf(frontier)) {
        auto extension_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(extension));
        auto frontier_contents  = reinterpret_cast<Bit_Set::Bit_Set*>(mtbdd_getvalue(frontier));

        bool is_already_present = frontier_contents->has_state(state_to_extend_frontier_with);
        if (is_already_present) {
            return frontier;
        }

        bool can_ext_post_state_reach_final = frontier_contents->has_any_state(extension_contents->destination_set);
        if (can_ext_post_state_reach_final) {
            auto new_frontier = g_solver_context->bit_set_alloc->alloc();
            u64 block_cnt = g_solver_context->bit_set_alloc->current_generation_block_cnt;
            new_frontier->populate_with(*frontier_contents, block_cnt);
            new_frontier->add_state(state_to_extend_frontier_with);

            MTBDD result = Bit_Set_Leaf::make_bit_set_leaf(new_frontier);

            g_solver_context->bit_set_alloc->dealloc(new_frontier);

            return result;
        }

        return frontier;
    }

    return sylvan::mtbdd_invalid;
}

TASK_IMPL_3(MTBDD, add_pad_transitions_bit_set_op, MTBDD *, p_transitions, MTBDD *, p_frontier, u64, raw_origin_state) {
    State origin_state = static_cast<State>(raw_origin_state);

    assert(g_pad_closure_info != nullptr);
    const Pad_Closure_Info2* pad_closure_info = g_pad_closure_info;

    MTBDD transitions = *p_transitions, frontier = *p_frontier;

    if (transitions == mtbdd_false) {
        return mtbdd_false;
    }

    if (frontier == mtbdd_false) {
        return transitions;
    }

    if (!mtbdd_isleaf(transitions) || !mtbdd_isleaf(frontier)) {
        return mtbdd_invalid;
    }

    auto frontier_states     = reinterpret_cast<Bit_Set::Bit_Set*>(mtbdd_getvalue(frontier));
    auto current_transitions = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(transitions));

    if (!frontier_states->has_state(origin_state)) {
        return transitions;
    }

    if (!frontier_states->has_any_state(current_transitions->destination_set)) {
        // It is not possible to reach a final state from origin
        return transitions;
    }

    Bit_Set::Bit_Set* final_states = pad_closure_info->final_states_bits;

    if (!final_states->has_any_state(current_transitions->destination_set)) {
        // The pad property is broken here, we need to fix it
        Transition_Destination_Set new_transition_contents(*current_transitions);

        assert(pad_closure_info->new_final_state > current_transitions->destination_set.back());

        new_transition_contents.insert_sorted(pad_closure_info->new_final_state);
        MTBDD new_destinations = sylvan::mtbdd_makeleaf(g_solver_context->leaf_id_store.transition_set,
                                                        reinterpret_cast<u64>(&new_transition_contents));
        return new_destinations;
    }

    return transitions;
}

TASK_IMPL_3(MTBDD, add_pad_transitions_op, MTBDD *, p_transitions, MTBDD *, p_frontier, u64, raw_origin_state) {
    State origin_state = static_cast<State>(raw_origin_state);

    assert(g_pad_closure_info != nullptr);
    const Pad_Closure_Info2* pad_closure_info = g_pad_closure_info;

    MTBDD transitions = *p_transitions, frontier = *p_frontier;

    if (transitions == mtbdd_false) {
        return mtbdd_false;
    }

    if (frontier == mtbdd_false) {
        return transitions;
    }

    if (mtbdd_isleaf(transitions) && mtbdd_isleaf(frontier)) {
        auto transition_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(transitions));
        auto frontier_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(frontier));

        // It must be possible to reach a final state from the current origin
        if (!frontier_contents->contains(origin_state))
            return transitions;

        // Make sure that also its post is contained in the frontier as states that are final are contained in the frontier
        // but they do not necesserily can have a path to another final state via the symbol
        // @FixMe: Maybe we should fix the frontier instead to not contain the final states (exclude epsilon reachablility)
        if (is_set_intersection_empty(transition_contents->destination_set, frontier_contents->destination_set)) {
            return transitions;
        }

        bool has_no_transition_to_fin = is_set_intersection_empty(transition_contents->destination_set.begin(),
                                                                  transition_contents->destination_set.rbegin(),
                                                                  transition_contents->destination_set.end(),
                                                                  pad_closure_info->final_states->begin(),
                                                                  pad_closure_info->final_states->rbegin(),
                                                                  pad_closure_info->final_states->end());

        if (has_no_transition_to_fin) {
            Transition_Destination_Set new_transition_contents(*transition_contents);

            assert(pad_closure_info->new_final_state > transition_contents->destination_set.back());

            new_transition_contents.insert_sorted(pad_closure_info->new_final_state);
            MTBDD new_destinations = sylvan::mtbdd_makeleaf(g_solver_context->leaf_id_store.transition_set,
                                                            reinterpret_cast<u64>(&new_transition_contents));
            return new_destinations;
        }

        return transitions;
    }

    return mtbdd_invalid;
}

inline
bool skip_product_state_due_to_no_post(Intersection_Info2& info, std::pair<State, State>& product) {
#if INTERSECTION_DETECT_STATES_WITH_NO_POST
    auto left_pos_in_postless = std::find(info.left_states_without_post.begin(), info.left_states_without_post.end(), product.first);
    auto right_pos_in_postless = std::find(info.right_states_without_post.begin(), info.right_states_without_post.end(), product.second);

    bool is_left_postless = (left_pos_in_postless != info.left_states_without_post.end());
    bool is_right_postless = (right_pos_in_postless != info.right_states_without_post.end());

    if (is_left_postless || is_right_postless) {
        bool product_has_lang = (info.left_final_states->contains(product.first) && info.right_final_states->contains(product.second));
        if (!product_has_lang) {
            ++info.skipped_states_with_no_post;
        }
        return !product_has_lang;
    }
    return false;
#else
    return false;
#endif
}

TASK_IMPL_3(MTBDD, transitions_intersection2_op, MTBDD *, pa, MTBDD *, pb, uint64_t, param) {
    MTBDD a = *pa, b = *pb;

    if (a == mtbdd_false || b == mtbdd_false) {
        return mtbdd_false; // The result is an empty set when one of the operands is an empty set (mtbdd_false)
    }

    if (!mtbdd_isleaf(a) || !mtbdd_isleaf(b)) {
        // @Note: According to the GMP implementation in Sylvan source code, swapping pointers should increase the cache
        // performance. However, doing a pointer swap causes some of the tests to fail, not sure what is up with it.
        return mtbdd_invalid;
    }

    auto intersect_info = reinterpret_cast<Intersection_Info2*>(param);

    auto left_leaf_contents  = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(a));
    auto right_leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(b));

    if (left_leaf_contents->destination_set.empty() || right_leaf_contents->destination_set.empty()) {
        return mtbdd_false;  // Equivalent to a leaf with an empty set
    }

    Transition_Destination_Set leaf_contents;

    for (auto left_state : left_leaf_contents->destination_set) {
        for (auto right_state : right_leaf_contents->destination_set) {
            std::pair<State, State> product_state = std::make_pair(left_state, right_state);

            if (skip_product_state_due_to_no_post(*intersect_info, product_state)) {
                continue;
            }

            State product_handle = intersect_info->seen_products.size();

            auto [existing_entry_it, did_insert] = intersect_info->seen_products.emplace(product_state, product_handle);

            Intersection_Discovery discovery = {.left = left_state, .right = right_state, .handle = product_handle};
            if (did_insert) {
                intersect_info->work_queue.push_back(discovery);
            } else {
                product_handle = existing_entry_it->second;
            }

            leaf_contents.insert(product_handle);
        }
    }

    leaf_contents.sort();

    MTBDD intersection_leaf = make_set_leaf(&leaf_contents);
    return intersection_leaf;
}

TASK_IMPL_2(MTBDD, replace_macrostates_with_handles_op, MTBDD, dd, uint64_t, param) {
    if (dd == mtbdd_false) {
        auto ctx = reinterpret_cast<Determinization_Context*>(param);
        ctx->is_trapstate_needed = true;

        Transition_Destination_Set new_leaf_contents;
        new_leaf_contents.insert(ctx->trapstate_handle);
        MTBDD new_leaf = make_set_leaf(&new_leaf_contents);

        return new_leaf;
    }

    if (!sylvan::mtbdd_isleaf(dd)) return sylvan::mtbdd_invalid;

    auto raw_leaf_contents = sylvan::mtbdd_getvalue(dd);
    auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(raw_leaf_contents);
    Macrostate macrostate(leaf_contents->destination_set.begin(), leaf_contents->destination_set.end());

    auto ctx = reinterpret_cast<Determinization_Context*>(param);
    auto [known_macrostates_elem, was_inserted] = ctx->known_macrostates.emplace(macrostate, ctx->known_macrostates.size());

    if (was_inserted) ctx->work_queue.push_back(&(*known_macrostates_elem));

    State macrostate_handle = known_macrostates_elem->second;
    Transition_Destination_Set new_leaf_contents;
    new_leaf_contents.insert(macrostate_handle);

    MTBDD new_leaf = make_set_leaf(&new_leaf_contents);
    return new_leaf;
}

TASK_IMPL_2(MTBDD, remove_states2_op, MTBDD, dd, uint64_t, param) {
    if (dd == mtbdd_false) return mtbdd_false;

    if (mtbdd_isleaf(dd)) {
        auto states_to_remove = reinterpret_cast<std::set<State>*>(param);
        auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(dd));

        Transition_Destination_Set new_leaf_contents;
        std::set_difference(leaf_contents->destination_set.begin(), leaf_contents->destination_set.end(),
                            states_to_remove->begin(), states_to_remove->end(),
                            std::inserter(new_leaf_contents.destination_set, new_leaf_contents.destination_set.begin()));

        MTBDD leaf = make_set_leaf(&new_leaf_contents);
        return leaf;
    }

    return mtbdd_invalid;
}


/*
 * MTBDD tasks facilitating efficient minimization support.
 */
Replace_States_With_Partition_Info* g_replace_states_with_partition_info = nullptr;

TASK_IMPL_2(MTBDD, replace_states_with_partition_ids_op, MTBDD, dd, uint64_t, iteration_number) {
    if (dd == mtbdd_false) return dd;

    assert(g_replace_states_with_partition_info);
    const Replace_States_With_Partition_Info* op_info = g_replace_states_with_partition_info;

    if (mtbdd_isleaf(dd)) {
        auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(dd));
        assert(leaf_contents->destination_set.size() == 1);

        State dest_state = *leaf_contents->destination_set.begin();
        State eq_class_id = op_info->state_to_eq_class_id.at(dest_state);

        Transition_Destination_Set new_leaf_contents;
        new_leaf_contents.insert(eq_class_id);
        MTBDD leaf = make_set_leaf(&new_leaf_contents);
        return leaf;
    }

    return mtbdd_invalid;
}
