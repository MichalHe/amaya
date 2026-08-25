#ifndef AMAYA_WRAPPER_H
#define AMAYA_WRAPPER_H

#include "base.hpp"
#include "lazy.hpp"

#include <sylvan.h>
#include <sylvan_common.h>
#include <sylvan_mtbdd.h>

#include <inttypes.h>

// Kept for Serialized_Atom/Serialized_Quantified_Atom_Conjunction below, which are still used
// as a plain (ctypes-free) way for the Cython wrapper (mtbdd-backend/wrapper) to pass a
// Presburger atom/conjunction across the language boundary.
struct Serialized_Atom {
    u64  type;
    s64* coefs;
    u64  coef_cnt;
    s64  modulus;
};

struct Serialized_Quantified_Atom_Conjunction {
    Serialized_Atom* atoms;
    u64              atom_cnt;
    State*           initial_state;
    u64*             vars;
    u64              var_cnt;
    u64*             quantified_vars;
    u64              quantified_var_cnt;
};

// NFA-returning construction/machinery entry points, used directly by the Cython wrapper
// (mtbdd-backend/wrapper/base.pyx) - the sole caller of everything in this header.
NFA construct_nfa_from_congruence(Serialized_Atom* congruence, s64 init_val, sylvan::BDDSET vars, u64 var_count);
NFA construct_nfa_from_ineq(Serialized_Atom* ineq, s64 init_state, sylvan::BDDSET vars, u64 var_count);
NFA construct_nfa_from_eq(Serialized_Atom* eq, s64 init_state, sylvan::BDDSET vars, u64 var_count);
NFA construct_dfa_for_atom_conjunction(Serialized_Quantified_Atom_Conjunction* raw_formula);
NFA perform_pad_closure_using_bit_sets(NFA& nfa);

void amaya_enable_bit_sets();

void shutdown_machinery();
void init_machinery();

#endif
