#ifndef AMAYA_OPERATIONS_H
#define AMAYA_OPERATIONS_H

#include "base.hpp"
#include <vector>
#include <utility>
#include <map>
#include <string>
#include <unordered_set>
#include <unordered_map>

#include <sylvan.h>
#include "../include/bit_set.hpp"

/**
Operation IDs are shifted by 40, because of the way sylvan combines the operation ID with other value parameters
to query the operation cache.
*/
#define AMAYA_EXISTS_OPERATION_ID                 (90llu) << 40u
#define AMAYA_UNION_OP_ID                         (91llu) << 40u
#define AMAYA_EXTEND_FRONTIER_OP_ID               (92llu) << 40u

/* Dynamic operation ID management
 * -------------------------------
 * Some operations e.g. determinization need a different operation id everytime they are
 * performed (on a different automaton) as reusing operation ID would cause cached values
 * from previous invocations to be used as result. Since the macrostate to handle renaming
 * that is performed is unique to the input NFA, the results cannot be reused.
 */
#define AMAYA_DYNAMIC_OP_ID_START                 (100llu) << 40u
u64 get_next_operation_id();

/**
* Global constant information used troughout a single invocation of a pad closure
*/
struct Pad_Closure_Info2 {
    State                  new_final_state;
    const std::set<State>* final_states;
    Bit_Set::Bit_Set*      final_states_bits;
};
extern Pad_Closure_Info2* g_pad_closure_info;

#define AMAYA_ADD_PAD_TRANSITIONS_OP_ID           (93llu) << 40u
#define AMAYA_TRANSITIONS_INTERSECT_OP_ID         (94llu) << 40u
#define AMAYA_REMOVE_STATES_OP                    (95llu) << 40u
#define AMAYA_REPLACE_MACROSTATES_WITH_HANDLES_OP (96llu) << 40u

#define AMAYA_TFA_UNION_OP_ID        (97llu)  << 40u
#define AMAYA_TFA_PARETO_UNION_OP_ID (98llu)  << 40u
#define AMAYA_TFA_INTERSECTION_OP_ID (99llu)  << 40u
#define AMAYA_ARE_MTBDDS_IDENTIC_OP  (10llu) << 40u

/**
 * The *abstraction* F definition.
 * Task returns a MTBDD. Task accepts two MTBDDs - left and right child (subtree) of a
 * node for variable <v> specified in variable set passed to abstract_apply with this operator.
 * The final int is a number of variables that are missing when reaching a leaf in MTBDD, but there is
 * still <k> number of variables in the variable set passed to abstract_apply.
 */
TASK_DECL_3(sylvan::MTBDD, project_variable_away_abstract_op, sylvan::MTBDD, sylvan::MTBDD, int);
TASK_DECL_3(sylvan::MTBDD, transitions_union_op, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);

TASK_DECL_2(sylvan::MTBDD, remove_states_op, sylvan::MTBDD, uint64_t);
TASK_DECL_2(sylvan::MTBDD, rename_states_op, sylvan::MTBDD, uint64_t);

TASK_DECL_3(sylvan::MTBDD, build_pad_closure_fronier_op, sylvan::MTBDD*, sylvan::MTBDD*, u64);
TASK_DECL_3(sylvan::MTBDD, build_pad_closure_bit_set_fronier_op, sylvan::MTBDD*, sylvan::MTBDD*, u64);
TASK_DECL_3(sylvan::MTBDD, add_pad_transitions_op, sylvan::MTBDD*, sylvan::MTBDD*, u64);
TASK_DECL_3(sylvan::MTBDD, add_pad_transitions_bit_set_op, sylvan::MTBDD*, sylvan::MTBDD*, u64);

TASK_DECL_3(sylvan::MTBDD, transitions_intersection2_op, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);
TASK_DECL_2(sylvan::MTBDD, replace_macrostates_with_handles_op, sylvan::MTBDD, uint64_t);
TASK_DECL_2(sylvan::MTBDD, remove_states2_op, sylvan::MTBDD, uint64_t);


struct Replace_States_With_Partition_Info {
    std::unordered_map<State, State> state_to_eq_class_id;
};
extern Replace_States_With_Partition_Info* g_replace_states_with_partition_info;

TASK_DECL_2(sylvan::MTBDD, replace_states_with_partition_ids_op, sylvan::MTBDD, uint64_t);

typedef struct
{
    std::map<State, State> *states_rename_map;
} State_Rename_Op_Info;

typedef struct
{
    std::map<std::set<State>, State>* alias_map;
    std::vector<State>* serialized_macrostates;
    std::vector<uint64_t>* macrostates_sizes;
    uint64_t macrostates_cnt;
    State first_available_state_number;
} Transform_Macrostates_To_Ints_State;

struct Intersection_Discovery {
    State left;
    State right;
    State handle;
};

struct Intersection_Info2 {
    std::map<std::pair<State, State>, State> seen_products;
    std::vector<Intersection_Discovery>& work_queue;

#if INTERSECTION_DETECT_STATES_WITH_NO_POST
    u64 skipped_states_with_no_post;
    std::set<State>* left_final_states;
    std::set<State>* right_final_states;
    std::vector<State> left_states_without_post;
    std::vector<State> right_states_without_post;
#endif
};

struct Determinization_Context {
    std::unordered_map<Macrostate, State> known_macrostates;
    std::vector<std::pair<const Macrostate, State>*>& work_queue;
    bool is_trapstate_needed;
    State trapstate_handle;
};

#endif
