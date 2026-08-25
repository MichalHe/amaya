#include "../include/wrapper.hpp"
#include "../include/base.hpp"
#include "../include/custom_leaf.hpp"
#include "../include/operations.hpp"
#include "../include/algorithms.hpp"

#include <algorithm>
#include <sylvan.h>
#include <sylvan_common.h>
#include <sylvan_mtbdd.h>
#include <unistd.h>
#include <assert.h>
#include <unordered_set>
#include <lace.h>
#include <utility>
#include <iostream>
#include <limits>
#include <cstring>

using namespace sylvan;

using std::set;
using std::vector;
using std::stringstream;
using std::map;

void init_machinery()
{
    int n_workers = 1;
    size_t dequeue_size = 10000000;

    lace_init(n_workers, dequeue_size);
    //lace_startup(program_stack_size, TASK(_main), NULL);

    // THIS SEEMS TO BE THE SECRET
    // When the TASK parameter (the middle one) is set to be NULL, it does not spawn a new thread
    // and instead uses the current thread for all tasks (makes it possible to call from python)
    const size_t stack_size = 1LL << 20;
    lace_startup(0, NULL, NULL);

    sylvan_set_limits(1LL << 32, 5, 5);
    //sylvan_set_sizes(1LL << 27, 1LL << 26, 1LL << 26, 1LL << 20);
    //sylvan_set_sizes(1LL << 24, 1LL << 28, 1LL << 24, 1LL << 28);
    sylvan_init_package();
    sylvan_init_mtbdd();

    // Initialize leaf type for leaves containing sets - represents outgoing transition from a state
    g_solver_context = new Solver_Context;
    Set_Leaf::init_set_leaf(&g_solver_context->leaf_id_store);
    Bit_Set_Leaf::init_bit_set_leaf(&g_solver_context->leaf_id_store);

    g_solver_context->bit_set_alloc = new Bit_Set::Block_Arena_Allocator();
}

void shutdown_machinery()
{
    LACE_ME;

    sylvan_gc();
    sylvan_quit();
    lace_exit();

    delete g_solver_context->bit_set_alloc;
    delete g_solver_context;
}

NFA construct_dfa_for_atom_conjunction(Serialized_Quantified_Atom_Conjunction* raw_formula) {
    Formula_Description formula_desc;
    formula_desc.var_count = raw_formula->var_cnt;
    for (u64 atom_i = 0; atom_i < raw_formula->atom_cnt; atom_i++) {
        auto& atom = raw_formula->atoms[atom_i];
        switch (atom.type) {
            case (Presburger_Atom_Type::PR_ATOM_EQ):         formula_desc.equation_count   += 1; break;
            case (Presburger_Atom_Type::PR_ATOM_INEQ):       formula_desc.inequation_count += 1; break;
            case (Presburger_Atom_Type::PR_ATOM_CONGRUENCE): formula_desc.congruence_count += 1; break;
        }
    }

    Formula_Pool pool (formula_desc);
    auto formula_atoms = pool.allocator.allocate_formula(formula_desc);

    u64 next_free_congruence = 0;
    u64 next_free_equation   = 0;
    u64 next_free_inequation = 0;

    vector<s64> initial_state_data (raw_formula->atom_cnt);

    for (u64 atom_i = 0; atom_i < raw_formula->atom_cnt; atom_i++) {
        auto& atom = raw_formula->atoms[atom_i];
        switch (atom.type) {
            case (Presburger_Atom_Type::PR_ATOM_EQ): {
                Equation& eq = formula_atoms.equations.items[next_free_equation];
                std::memcpy(eq.coefs.items, atom.coefs, sizeof(s64) * formula_desc.var_count);

                initial_state_data[formula_desc.congruence_count + next_free_equation] = raw_formula->initial_state[atom_i];

                next_free_equation += 1;
                break;
            }
            case (Presburger_Atom_Type::PR_ATOM_INEQ): {
                Inequation& ineq = formula_atoms.inequations.items[next_free_inequation];
                std::memcpy(ineq.coefs.items, atom.coefs, sizeof(s64) * formula_desc.var_count);

                initial_state_data[formula_desc.congruence_count + formula_desc.equation_count + next_free_inequation] = raw_formula->initial_state[atom_i];

                next_free_inequation += 1;
                break;
            }
            case (Presburger_Atom_Type::PR_ATOM_CONGRUENCE): {
                Congruence& congruence = formula_atoms.congruences.items[next_free_congruence];
                std::memcpy(congruence.coefs.items, atom.coefs, sizeof(s64) * formula_desc.var_count);

                auto decomposed_modulus = decompose_modulus(atom.modulus);
                congruence.modulus_2pow = decomposed_modulus.modulus_2pow;
                congruence.modulus_odd  = decomposed_modulus.modulus_odd;

                initial_state_data[next_free_congruence] = raw_formula->initial_state[atom_i];

                next_free_congruence += 1;
                break;
            }
        }
    }

    vector<u64> quantified_vars;
    quantified_vars.resize(raw_formula->quantified_var_cnt);
    std::memcpy(quantified_vars.data(), raw_formula->quantified_vars, sizeof(u64) * raw_formula->quantified_var_cnt);

    sylvan::BDDSET var_set = sylvan::mtbdd_set_empty();
    for (u64 var_idx = 0u; var_idx < raw_formula->var_cnt; var_idx++) {
        var_set = sylvan::mtbdd_set_add(var_set, raw_formula->vars[var_idx]);
    }

    Quantified_Atom_Conjunction formula (formula_atoms.congruences, formula_atoms.equations,
                                         formula_atoms.inequations, quantified_vars, formula_desc.var_count);

    auto stored_formula_ptr = pool.store_formula(formula);

    Conjunction_State initial_state(initial_state_data);
    auto created_nfa = build_nfa_with_formula_entailement(stored_formula_ptr, initial_state, var_set, pool);

    return created_nfa;
}

NFA perform_pad_closure_using_bit_sets(NFA& nfa) {
    return do_pad_closure_using_bit_sets(&nfa, g_solver_context->bit_set_alloc);
}

struct Congruence_State {
    s64 modulus_odd;
    s64 modulus_2pow;
    s64 value;

    bool operator==(const Congruence_State& other) const {
        return modulus_odd == other.modulus_odd &&
               modulus_2pow == other.modulus_2pow &&
               value == other.value;
    }
};

template <>
struct std::hash<Congruence_State> {
    std::size_t operator() (const Congruence_State& state) const {
        return (1 << state.modulus_2pow) + state.modulus_odd*state.value;
    }
};

NFA construct_nfa_from_congruence(Serialized_Atom* congruence, s64 init_val, BDDSET vars, u64 var_count) {
    auto moduli = decompose_modulus(congruence->modulus);
    Congruence_State initial_state = {
        .modulus_odd = moduli.modulus_odd,
        .modulus_2pow = moduli.modulus_2pow,
        .value = init_val
    };

    Congruence_State final_state = {1, 299993, -1};
    u64 final_state_handle = 0;
    u64 init_state_handle  = 1;

    unordered_map<Congruence_State, s64> discovered_states {
        {final_state, final_state_handle},
        {initial_state, init_state_handle}
    };
    vector<pair<Congruence_State, s64>> worklist = {{initial_state, init_state_handle}};

    NFA constructed_nfa(vars);
    constructed_nfa.var_count = var_count;
    constructed_nfa.add_state_final(final_state_handle);
    constructed_nfa.initial_states.insert(init_state_handle);

    assert(var_count > 0);
    u8 symbol_arr[var_count];

    while (!worklist.empty()) {
        auto [state, handle] = worklist.back();
        worklist.pop_back();

        s64 modulus = combine_moduli(state.modulus_2pow, state.modulus_odd);
        constructed_nfa.states.insert(handle);

        for (u64 symbol = 0; symbol < (1 << var_count); symbol++) {
            s64 dot = 0;
            for (int i = 0; i < var_count; i++) {
                s64 is_bit_set = (symbol & (1u << i)) > 0;
                dot += is_bit_set * congruence->coefs[i];
            }
            s64 post = state.value - dot;
            s64 fin_post = state.value + dot;

            Congruence_State dest_state;
            dest_state.modulus_odd = state.modulus_odd;
            dest_state.modulus_2pow = 0;

            if (state.modulus_2pow > 0) {
                if ((post % 2) == 0) {
                    post /= 2;
                    s64 new_modulus = combine_moduli(state.modulus_2pow - 1, state.modulus_odd);
                    post %= new_modulus;
                    post += (post < 0) * new_modulus;

                    dest_state.modulus_2pow = state.modulus_2pow-1;
                    dest_state.value = post;
                } else {
                    continue;
                }
            } else {
                post += state.modulus_odd * ((post % 2) != 0);
                post /= 2;
                post = post % state.modulus_odd;
                post += state.modulus_odd * (post < 0);

                dest_state.value = post;
            }

            auto [insert_position, did_insert_happen] = discovered_states.emplace(dest_state,discovered_states.size());
            s64 dest_handle = insert_position->second;
            if (did_insert_happen) {
                worklist.push_back({dest_state, dest_handle});
            }

            for (int i = 0; i < var_count; i++) {
                symbol_arr[i] = (symbol >> i) & 1;
            }

            constructed_nfa.add_transition(handle, dest_handle, symbol_arr);

            if ((fin_post % modulus) == 0) {
                constructed_nfa.add_transition(handle, final_state_handle, symbol_arr);
            }
        }
    }

    return constructed_nfa;
}

NFA construct_nfa_from_ineq(Serialized_Atom* ineq, s64 init_state, BDDSET vars, u64 var_count) {
    s64 final_state_handle = 0;
    s64 init_state_handle  = 1;
    s64 final_state = std::numeric_limits<s64>::max();

    unordered_map<s64, s64> discovered_states {
        {final_state, final_state_handle},
        {init_state, init_state_handle}
    };
    vector<pair<s64, s64>> worklist = {{init_state, init_state_handle}};

    assert(var_count > 0);
    u8 symbol_arr[var_count];

    NFA constructed_nfa(vars);
    constructed_nfa.var_count = var_count;
    constructed_nfa.initial_states.insert(init_state_handle);
    constructed_nfa.add_state_final(final_state_handle);

    while (!worklist.empty()) {
        auto [state, handle] = worklist.back();
        worklist.pop_back();

        constructed_nfa.states.insert(handle);

        for (u64 symbol = 0; symbol < (1 << var_count); symbol++) {
            s64 dot = 0;
            for (int i = 0; i < var_count; i++) {
                s64 is_bit_set = (symbol & (1u << i)) > 0;
                dot += is_bit_set * ineq->coefs[i];
            }

            s64 post     = state - dot;
            s64 fin_post = state + dot;

            s64 post_div_2 = post / 2;
            s64 post_mod_2 = post % 2;
            post_div_2 -= (post_mod_2 != 0) * (post < 0);
            post = post_div_2;

            s64 post_handle = discovered_states.size();
            auto [insert_pos, insert_happend] = discovered_states.emplace(post, post_handle);
            if (insert_happend) {
                worklist.push_back({post, post_handle});
            } else {
                post_handle = insert_pos->second;
            }

            for (int i = 0; i < var_count; i++) {
                symbol_arr[i] = (symbol >> i) & 1;
            }

            constructed_nfa.add_transition(handle, post_handle, symbol_arr);

            if (fin_post >= 0) {
                constructed_nfa.add_transition(handle, final_state_handle, symbol_arr);
            }
        }
    }

    return constructed_nfa;
}

NFA construct_nfa_from_eq(Serialized_Atom* eq, s64 init_state, BDDSET vars, u64 var_count) {
    s64 final_state_handle = 0;
    s64 init_state_handle  = 1;
    s64 final_state = std::numeric_limits<s64>::max();

    unordered_map<s64, s64> discovered_states {
        {final_state, final_state_handle},
        {init_state, init_state_handle}
    };
    vector<pair<s64, s64>> worklist = {{init_state, init_state_handle}};

    assert(var_count > 0);
    u8 symbol_arr[var_count];

    NFA constructed_nfa(vars);
    constructed_nfa.var_count = var_count;
    constructed_nfa.initial_states.insert(init_state_handle);
    constructed_nfa.add_state_final(final_state_handle);

    s64 states_processed = 0;

    while (!worklist.empty()) {
        auto [state, handle] = worklist.back();
        worklist.pop_back();

        constructed_nfa.states.insert(handle);

        states_processed += 1;

        for (u64 symbol = 0; symbol < (1 << var_count); symbol++) {
            s64 dot = 0;
            for (int i = 0; i < var_count; i++) {
                s64 is_bit_set = (symbol & (1u << i)) > 0;
                dot += is_bit_set * eq->coefs[i];
            }

            s64 post     = state - dot;
            s64 fin_post = state + dot;

            if ((post % 2) != 0) {
                continue;
            }

            s64 post_div_2 = post / 2;
            s64 post_mod_2 = post % 2;
            post_div_2 -= (post_mod_2 != 0) * (post < 0);
            post = post_div_2;

            s64 post_handle = discovered_states.size();
            auto [insert_pos, insert_happend] = discovered_states.emplace(post, post_handle);
            if (insert_happend) {
                worklist.push_back({post, post_handle});
            } else {
                post_handle = insert_pos->second;
            }

            for (int i = 0; i < var_count; i++) {
                symbol_arr[i] = (symbol >> i) & 1;
            }

            constructed_nfa.add_transition(handle, post_handle, symbol_arr);

            if (fin_post == 0) {
                constructed_nfa.add_transition(handle, final_state_handle, symbol_arr);
            }
        }
    }

    return constructed_nfa;
}

void amaya_enable_bit_sets() {
    g_solver_context->config.enable_feature(SOLVER_CONFIG_USE_BIT_SETS);
}
