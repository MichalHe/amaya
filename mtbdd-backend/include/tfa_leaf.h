#ifndef AMAYA_TFA_LEAF_H
#define AMAYA_TFA_LEAF_H

#include <inttypes.h>
#include <stdlib.h>
#include <sylvan.h>
#include "base.hpp"
#include "pareto_set.h"
#include "lazy.hpp"
#include <vector>

extern u64 mtbdd_tfa_leaf_type_id;
extern u64 mtbdd_tfa_intersection_leaf_type_id;
extern u64 mtbdd_tfa_pareto_leaf_type_id;

using std::vector;
using sylvan::MTBDD;

struct TFA_Leaf_Contents {
    s64  post;
    bool is_accepting;
};

struct TFA_Leaf_Intersection_Contents {
    vector<s64> post;
    bool is_accepting;
    bool hash_valid = false;
    u64  hash = 0; // The tuples are immutable - cache the hash for when the leaf will be inserted into Pareto Set
};

struct TFA_Pareto_Leaf {
    Pareto_Set elements;
    bool is_accepting;
    bool operator==(const TFA_Pareto_Leaf& other) const {
        return (elements == other.elements) && is_accepting == other.is_accepting;
    }
};

MTBDD make_tfa_leaf(TFA_Leaf_Contents* contents);
void mk_tfa_leaf_from_contents(u64 *target_destination_set_ptr);
void destroy_tfa_leaf(u64 leaf_value);
int tfa_leaf_equals(u64 a_ptr, u64 b_ptr);
u64 tfa_leaf_hash(const u64 contents_ptr, const u64 seed);
char* tfa_leaf_to_str(int comp, u64 leaf_val, char *buf, size_t buflen);

MTBDD make_tfa_intersection_leaf(TFA_Leaf_Intersection_Contents* contents);
void mk_tfa_intersection_leaf_from_contents(u64* contents);
void destroy_tfa_intersection_leaf(u64 leaf_value);
int tfa_intersection_leaf_equals(u64 a_ptr, u64 b_ptr);
u64 tfa_intersection_leaf_hash(const u64 contents_ptr, const u64 seed);
char* tfa_leaf_intersection_to_str(int comp, u64 leaf_val, char* buf, size_t buflen);

MTBDD make_tfa_pareto_leaf(TFA_Pareto_Leaf* contents);
void  mk_tfa_pareto_leaf_from_contents(u64* contents);
void  destroy_tfa_pareto_leaf(u64 leaf_value);
int   tfa_pareto_leaf_equals(u64 a_ptr, u64 b_ptr);
u64   tfa_pareto_leaf_hash(const u64 contents_ptr, const u64 seed);
char* tfa_pareto_leaf_to_str(int comp, u64 leaf_val, char* buf, size_t buflen);

TASK_DECL_3(sylvan::MTBDD, tfa_mtbdd_union, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);
MTBDD perform_tfa_mtbdd_union(MTBDD left, MTBDD right);

TASK_DECL_3(sylvan::MTBDD, tfa_mtbdd_intersection, sylvan::MTBDD *, sylvan::MTBDD *, uint64_t);
MTBDD perform_tfa_mtbdd_intersection(MTBDD left, MTBDD right);
MTBDD make_tfa_intersection_top();

TASK_DECL_3(sylvan::MTBDD, tfa_mtbdd_pareto_union, sylvan::MTBDD *, sylvan::MTBDD *, u64);
MTBDD perform_tfa_pareto_union(MTBDD left, MTBDD right, Formula_Structure_Info* formula_info);

TASK_DECL_3(sylvan::MTBDD, tfa_mtbdd_pareto_projection_op, sylvan::MTBDD, sylvan::MTBDD, int)
sylvan::MTBDD perform_tfa_pareto_projection(sylvan::MTBDD bdd, sylvan::BDDSET var_to_project_away, Formula_Structure_Info* formula_structure);

TASK_DECL_2(sylvan::MTBDD, tfa_make_tfa_leaves_into_macrostate, sylvan::MTBDD, uint64_t);
sylvan::MTBDD convert_tfa_leaves_into_macrostates(sylvan::MTBDD bdd, NFA_Construction_Ctx* ctx);

void init_tfa_leaves();

TASK_DECL_3(sylvan::MTBDD, are_mtbdds_identic_op, sylvan::MTBDD *, sylvan::MTBDD *, u64);
bool check_mtbdds_are_identical(MTBDD left, MTBDD right);

#endif
