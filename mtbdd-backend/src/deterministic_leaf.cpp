#include <sylvan.h>
#include <sylvan_common.h>
#include <sylvan_mtbdd.h>
#include <sylvan_bdd.h>
#include <sylvan_mt.h>
#include <sylvan_int.h>
#include <sylvan_mtbdd_int.h>
#include <sylvan_stats.h>
#include <lace.h>

#include "../include/base.hpp"
#include "../include/operations.hpp"
#include "../include/custom_leaf.hpp"

using sylvan::MTBDD;
using sylvan::mtbdd_applyp_CALL;

// Plan:
// 0) add tests for the new automaton representation
// 1) make sure that the created automata are always complete in the operations
//    (in intersection when one is going to bot, in union if both are going to bot)
// 2) implement intersection operation for the API
// 3) implement union operation for the API

TASK_DECL_3(sylvan::MTBDD, det_product_op, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);
TASK_DECL_3(sylvan::MTBDD, det_self_product_op, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);
TASK_DECL_3(sylvan::MTBDD, det_project_var_away_op, sylvan::MTBDD, sylvan::MTBDD, int);
TASK_DECL_3(sylvan::MTBDD, det_add_transition_op, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);

TASK_IMPL_3(MTBDD, det_product_op, MTBDD *, pa, MTBDD *, pb, uint64_t, param) {
    MTBDD a = *pa, b = *pb;
    if (a == sylvan::mtbdd_false) return a;
    if (b == sylvan::mtbdd_false) return b;

    if (!sylvan::mtbdd_isleaf(a)) return sylvan::mtbdd_invalid;
    if (!sylvan::mtbdd_isleaf(b)) return sylvan::mtbdd_invalid;

    s64 a_val = static_cast<s64>(sylvan::mtbdd_getvalue(a));
    s64 b_val = static_cast<s64>(sylvan::mtbdd_getvalue(b));

    Intersection_Info2* intersection_info = reinterpret_cast<Intersection_Info2*>(param);

    std::pair<s64, s64> state_tuple {a_val, b_val};
    State product_handle = intersection_info->seen_products.size();

    auto [existing_entry_it, did_insert] = intersection_info->seen_products.emplace(state_tuple, product_handle);
    product_handle = existing_entry_it->second;

    if (did_insert) {
        Intersection_Discovery discovery = {.left = a_val, .right = b_val, .handle = product_handle};
        intersection_info->work_queue.push_back(discovery);
    }

    return Deterministic_Leaf::create(product_handle);
}

TASK_IMPL_3(MTBDD, det_self_product_op, MTBDD *, pa, MTBDD *, pb, uint64_t, param) {
    MTBDD a = *pa, b = *pb;
    if (a == sylvan::mtbdd_false) return a;
    if (b == sylvan::mtbdd_false) return b;

    if (!sylvan::mtbdd_isleaf(a)) return sylvan::mtbdd_invalid;
    if (!sylvan::mtbdd_isleaf(b)) return sylvan::mtbdd_invalid;

    s64 a_val = static_cast<s64>(sylvan::mtbdd_getvalue(a));
    s64 b_val = static_cast<s64>(sylvan::mtbdd_getvalue(b));

    Intersection_Info2* intersection_info = reinterpret_cast<Intersection_Info2*>(param);

    std::pair<s64, s64> state_tuple {a_val, b_val};

    if (a_val > b_val) {
        std::swap(state_tuple.first, state_tuple.second);
    }
    
    State product_handle = intersection_info->seen_products.size();

    auto [existing_entry_it, did_insert] = intersection_info->seen_products.emplace(state_tuple, product_handle);
    product_handle = existing_entry_it->second;

    if (did_insert) {
        Intersection_Discovery discovery = {.left = a_val, .right = b_val, .handle = product_handle};
        intersection_info->work_queue.push_back(discovery);
    }

    return Deterministic_Leaf::create(product_handle);
}

TASK_IMPL_3(MTBDD, det_project_var_away_op, MTBDD, left_mtbdd, MTBDD, right_mtbdd, uint64_t, param) {
    // Called when we are removing a variable xi from the BDD
    MTBDD u = mtbdd_applyp(left_mtbdd, right_mtbdd, param, TASK(det_self_product_op), AMAYA_EXISTS_OPERATION_ID);
    return u;
}

TASK_IMPL_3(sylvan::MTBDD, det_add_transition_op, sylvan::MTBDD *, left_mtbdd_ptr, sylvan::MTBDD *, right_mtbdd_ptr, uint64_t, param) {
    sylvan::MTBDD left_mtbdd = *left_mtbdd_ptr, right_mtbdd = *right_mtbdd_ptr;

    if (left_mtbdd == sylvan::mtbdd_false)  return right_mtbdd;
    if (right_mtbdd == sylvan::mtbdd_false) return left_mtbdd;

    // Both are not false
    if (!sylvan::mtbdd_isleaf(left_mtbdd))  return sylvan::mtbdd_invalid;
    if (!sylvan::mtbdd_isleaf(right_mtbdd)) return sylvan::mtbdd_invalid;

    fprintf(stderr, "Adding nondeterminism to a deterministic automaton!\n");
    assert(false);
}


struct DFA : public NFA {
    void add_transition(s64 from, s64 to, u8* symbol);
};


void DFA::add_transition(s64 from, s64 to, u8* symbol) {
    sylvan::MTBDD leaf = Deterministic_Leaf::create(to);
    sylvan::MTBDD transition_mtbdd = sylvan::mtbdd_cube(this->vars, symbol, leaf);

    LACE_ME;
    auto [present_key_val_it, was_inserted] = transitions.emplace(from, transition_mtbdd);
    if (was_inserted) {
        sylvan::mtbdd_ref(transition_mtbdd);
    } else {
        sylvan::MTBDD existing_transitions = present_key_val_it->second;

        sylvan::MTBDD updated_mtbdd = mtbdd_applyp(existing_transitions,
                                                   transition_mtbdd,
                                                   0u,
                                                   TASK(det_add_transition_op),
                                                   AMAYA_UNION_OP_ID);

        sylvan::mtbdd_ref(updated_mtbdd);
        sylvan::mtbdd_deref(existing_transitions);

        transitions[from] = updated_mtbdd;
    }
}
