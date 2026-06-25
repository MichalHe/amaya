#ifndef AMAYA_LAZY_H
#define AMAYA_LAZY_H

#include "base.hpp"
#include "custom_leaf.hpp"
#include "operations.hpp"
#include "block_allocator.h"
#include "vectors.h"

#include <algorithm>
#include <bitset>
#include <list>
#include <cassert>
#include <optional>
#include <cstring>
#include <iostream>
#include <string>
#include <map>
#include <unordered_set>

using std::optional;
using std::vector;
using std::unordered_set;
using std::map;
using std::list;
using std::pair;

struct Decomposed_Modulus {
    s64 modulus_2pow, modulus_odd;
};

Decomposed_Modulus decompose_modulus(s64 modulus);
s64 combine_moduli(s64 mod_2pow, s64 mod_odd);


struct Congruence {
    Sized_Array<s64> coefs;
    s64 modulus_odd;
    s64 modulus_2pow;

    bool operator==(const Congruence& other) const {
        return coefs == other.coefs && modulus_odd == other.modulus_odd && modulus_2pow == other.modulus_2pow;
    }
};

struct Inequation {
    Sized_Array<s64> coefs;
    bool operator==(const Inequation& other) const {
        return coefs == other.coefs;
    }
};

struct Equation {
    Sized_Array<s64> coefs;
    bool operator==(const Equation& other) const {
        return coefs == other.coefs;
    }
};

enum Presburger_Atom_Type {
    PR_ATOM_INVALID = 0,
    PR_ATOM_INEQ = 1,
    PR_ATOM_EQ = 2,
    PR_ATOM_CONGRUENCE = 3
};

struct Sparse_Presburger_Atom {
    Presburger_Atom_Type type;
    u64* variables;
    s64* coefs;
    u64 var_count;
};

enum class Preferred_Var_Value_Type : unsigned {
    LOW  = 0x01,
    HIGH = 0x02,
};
constexpr Preferred_Var_Value_Type operator&(Preferred_Var_Value_Type left, Preferred_Var_Value_Type right);
constexpr Preferred_Var_Value_Type operator|(Preferred_Var_Value_Type left, Preferred_Var_Value_Type right);

struct Conjunction_State;

struct Linear_Node {
    vector<s64>      coefs; // Cannot share coefs with original atom as it might be modified in-place during simplification
    vector<u64>      vars;
    bool             is_satisfied = false;
};


struct Congruence_Node {
    vector<s64> coefs;
    vector<u64> vars;
    s64         modulus_2pow;
    s64         modulus_odd;
    bool        is_satisfied;
};

struct Hard_Bound {
    s32 atom_i;                  // Index of an inequation that represents a hard bound
};

struct Var_Node {
    const static s32 TOMBSTONE = -1;

    vector<s32> upper_bounds;     // Indices of the inequations in which the value of this var should be the smallest
    vector<s32> lower_bounds;     // Indices of the inequations in which the value of this var should be the greatest
    vector<s32> equations;        // Indices of equations that contain this var
    vector<s32> congruences;      // Indices of congruences containing this var

    Hard_Bound  hard_upper_bound = {.atom_i = TOMBSTONE};
    Hard_Bound  hard_lower_bound = {.atom_i = TOMBSTONE};

    bool is_hard_lower_bound(s32 atom_i) const {
        return (hard_lower_bound.atom_i == atom_i);
    }

    bool has_hard_lower_bound() const {
        return hard_lower_bound.atom_i != TOMBSTONE;
    }

    bool is_hard_upper_bound(s32 atom_i) {
        return (hard_upper_bound.atom_i == atom_i);
    }

    bool has_hard_upper_bound() const {
        return hard_upper_bound.atom_i != TOMBSTONE;
    }
};

struct Watched_Position_Pair {
    s32 position0;
    s32 position1;
    s64 required_value0;
    s64 required_value1;
};

struct Dep_Graph {
    vector<u64> potential_vars;
    vector<u64> quantified_vars;
    vector<u64> vars_not_removed_in_simplification;

    // Positions in conjunction states and their values that would enable further simplifications
    vector<Watched_Position_Pair> watched_positions;

    // Pairs of atoms that might imply contradiction with right RHS
    vector<std::pair<s32, s32>> complementary_pairs;

    vector<Var_Node>         var_nodes;    // Every variable has a node associated with it
    u64 protected_vars = 0; // If a constant value for a free var is implied
    u64 free_vars      = 0;

    vector<Linear_Node>      equations;    // First nodes are equations then inequations
    vector<Linear_Node>      inequations;
    vector<Congruence_Node>  congruences;

    bool dirty = false;
    bool is_false = false;

    bool is_var_free(u64 var) const {
        return free_vars & (1ull << var);
    }

    void mark_var_as_free(u64 var) {
        free_vars |= (1ull << var);
    }


    bool is_var_protected(u64 var) const {
        return protected_vars & (1ull << var);
    }

    void mark_var_as_protected(u64 var) {
        protected_vars |= (1ull << var);
    }

};

struct Quantified_Atom_Conjunction;
struct Formula_Allocator;

Dep_Graph build_dep_graph(const Quantified_Atom_Conjunction& conj);
void write_dep_graph_dot(std::ostream& output, Dep_Graph& graph);
std::ostream& operator<<(std::ostream& output, const Congruence_Node& congruence_node);
std::ostream& operator<<(std::ostream& output, const Linear_Node& lin_node);

struct Quantified_Atom_Conjunction {
    // This requires certain order: Conjunction_State, conjunction state hashing
    Sized_Array<Congruence> congruences = {nullptr, 0};
    Sized_Array<Equation>   equations   = {nullptr, 0};
    Sized_Array<Inequation> inequations = {nullptr, 0};
    vector<u64> bound_vars;
    u64         var_count;
    Dep_Graph   dep_graph;
    bool        bottom = false;
    const Quantified_Atom_Conjunction* post_formula = nullptr;  // In case that the underlying modulus changes with post, we don't have to query formula pool

    Quantified_Atom_Conjunction() {}
    Quantified_Atom_Conjunction(bool top) : bottom(!top),
                                            var_count(0),
                                            bound_vars({}) {}
    Quantified_Atom_Conjunction(Sized_Array<Congruence> congruences, Sized_Array<Equation> eqs,
                                Sized_Array<Inequation> ineqs, const vector<u64>& bound_vars, u64 var_count) :
        congruences(congruences), equations(eqs), inequations(ineqs),
        bound_vars(bound_vars), var_count(var_count)
    {
        this->dep_graph = build_dep_graph(*this);
    };

    bool operator==(const Quantified_Atom_Conjunction& other) const;

    u64 atom_count() const {
        return congruences.size + equations.size + inequations.size;
    }

    bool has_atoms() const {
        return this->atom_count() > 0;
    }

    bool is_top() const {
        return !this->has_atoms() && !bottom;
    }

    bool is_bottom() const {
        return !this->has_atoms() && bottom;
    }

    std::string fmt_with_state(Conjunction_State& state) const;
};

template <>
struct std::hash<Quantified_Atom_Conjunction> {
    std::size_t operator() (const Quantified_Atom_Conjunction& formula) const {
        std::size_t hash = formula.bottom ? 0 : 33;
        // @Optimize: The equations and inequations do not mutate during execution so we can just hash a pointer there. Only congruences need real hashing.
        for (auto& eq: formula.equations) {
            hash = hash_combine(hash, hash_array(eq.coefs));
        }

        for (auto& cg: formula.congruences) {
            hash = hash_combine(hash, hash_array(cg.coefs));
            hash = hash_combine(hash, cg.modulus_odd);
            hash = hash_combine(hash, cg.modulus_2pow);
        }
        for (auto& ineq: formula.inequations) {
            hash = hash_combine(hash, hash_array(ineq.coefs));
        }
        return hash;
    }
};

struct Conjunction_State {
    vector<s64> constants; // Congruences < Equations < Inequations

    Conjunction_State(const vector<s64>& value): constants(value) {}

    Conjunction_State(const Conjunction_State& other): constants(other.constants) {}

    bool operator==(const Conjunction_State& other) const;
    bool operator<(const Conjunction_State& other) const;
};

struct Formula_Structure {
    s32 eq_cnt;
    s32 ineq_cnt;
    s32 congruence_cnt;
};

struct Ritch_Conjunction_State {
    vector<s64> data;

    Formula_Structure formula_structure;

    s64 get_congruence_val(u64 congruence_idx) const {
        return data[congruence_idx];
    }

    void set_congruence_val(u64 congruence_idx, s64 val) {
        data[congruence_idx] = val;
    }

    s64 get_eq_val(u64 eq_idx) const {
        return data[formula_structure.congruence_cnt + eq_idx];
    }

    void set_eq_val(u64 eq_idx, s64 val) {
        data[formula_structure.congruence_cnt + eq_idx] = val;
    }

    s64 get_ineq_val(u64 ineq_idx) const {
        return data[formula_structure.congruence_cnt + formula_structure.eq_cnt + ineq_idx];
    }

    void set_ineq_val(u64 ineq_idx, s64 val) {
        data[formula_structure.congruence_cnt + formula_structure.eq_cnt + ineq_idx] = val;
    }

    void add_eq_rhs(u64 eq_val) {
        data.push_back(0);
        u64 prefix = formula_structure.eq_cnt + formula_structure.congruence_cnt;
        for (s64 i = data.size() - 1; i >= prefix; i--) {
            data[i] = data[i-1];
        }
        data[prefix] = eq_val;

        formula_structure.eq_cnt += 1;
    }
};


template <>
struct std::hash<Conjunction_State> {
    std::size_t operator() (const Conjunction_State& state) const {
        std::size_t hash = 0;

        for (u64 i = 0u; i < state.constants.size(); i++) {
            std::size_t atom_val_hash = std::hash<s64>{}(state.constants[i]);
            hash = hash + 0x9e3779b9 + (atom_val_hash << 6) + (atom_val_hash >> 2);
        }

        return hash;
    }
};

std::ostream& operator<<(std::ostream& output, const Quantified_Atom_Conjunction& formula);
std::ostream& operator<<(std::ostream& output, const Conjunction_State& atom);


struct Alphabet_Iterator {
    u64 free_bits_val;
    u64 free_bits_inc_count;

    u64 quantified_bits_val;
    u64 quantified_bits_inc_count;

    bool finished;
    bool has_more_quantif_symbols;

    u64 quantified_bits_mask;
    u64 quantified_bits_inc_limit;
    u64 free_bits_inc_limit;

    Alphabet_Iterator(u64 var_count, const vector<u64>& quantified_vars):
        free_bits_val(0u),
        free_bits_inc_count(0u),
        quantified_bits_val(0u),
        quantified_bits_inc_count(0u),
        finished(false),
        has_more_quantif_symbols(false)
    {
        quantified_bits_mask = 0u;
        for (auto quantified_var: quantified_vars) {
            quantified_bits_mask |= (1u << quantified_var);
        }

        quantified_bits_inc_limit = 1u << quantified_vars.size();
        free_bits_inc_limit = 1u << (var_count - quantified_vars.size());
    };

    u64 next_symbol() {
        quantified_bits_val = ((quantified_bits_val | ~quantified_bits_mask) + 1u) & quantified_bits_mask;
        ++quantified_bits_inc_count;

        if (quantified_bits_inc_count >= quantified_bits_inc_limit) {
            has_more_quantif_symbols = false;

            free_bits_val = ((free_bits_val | quantified_bits_mask) + 1u) & ~quantified_bits_mask;
            ++free_bits_inc_count;
            if (free_bits_inc_count >= free_bits_inc_limit) finished = true;
        }

        return free_bits_val | quantified_bits_val;
    }

    u64 init_quantif() {
        quantified_bits_val = 0u;
        quantified_bits_inc_count = 0u;
        has_more_quantif_symbols = true;

        return (free_bits_val | quantified_bits_val);
    }

    void reset() {
        free_bits_val = 0u;
        free_bits_inc_count = 0u;
        quantified_bits_val = 0u;
        quantified_bits_inc_count = 0u;
        finished = false;
    }
};

template <typename T>
struct Slab_Fragment {
    u64 next_free;
    u64 capacity;
    T*  items;

    Slab_Fragment(u64 capacity, T* items_buffer) : next_free(0), capacity(capacity), items(items_buffer) {};

    Slab_Fragment(u64 capacity) : capacity(capacity), next_free(0) {
        items = (T*) malloc(sizeof(T) * capacity);
        assert(items);
    }

    Slab_Fragment(const Slab_Fragment& other) = delete;

    ~Slab_Fragment() {
        free(items);
    }
};


struct Macrostate_Header_Elem {
    const Quantified_Atom_Conjunction* formula;
    u64 state_cnt;
};

struct Finalized_Macrostate {
    Sized_Array<Macrostate_Header_Elem> header;     // Formula information with the number of corresponding states for fast comparision
    Sized_Array<s64>                    state_data; // State constants, serialized for AVX memcmp
    bool is_accepting = false;
    u64 handle;

    bool operator==(const Finalized_Macrostate& other) const;
};

struct Formula_Description { // Formula description so that we know how to setup the allocator
    u64 congruence_count = 0;
    u64 equation_count   = 0;
    u64 inequation_count = 0;
    u64 var_count        = 0;

    Formula_Description() {};

    Formula_Description(const Quantified_Atom_Conjunction* formula) :
        congruence_count(formula->congruences.size),
        equation_count(formula->equations.size),
        inequation_count(formula->inequations.size),
        var_count(formula->var_count)
        {};

    Formula_Description(u64 congruence_count, u64 equation_count, u64 inequation_count, u64 var_count) :
        congruence_count(congruence_count),
        equation_count(equation_count),
        inequation_count(inequation_count),
        var_count(var_count)
        {};

    u64 atom_count() const {
        return congruence_count + inequation_count + equation_count;
    }
};

struct Allocator_Limits {
    u64 max_congruences, max_equations, max_inequations;
    u64 var_count;

    Allocator_Limits(const Formula_Description& root_formula):
        var_count(root_formula.var_count),
        max_congruences(root_formula.congruence_count),
        max_equations(root_formula.congruence_count + root_formula.equation_count),  // Allow for linearization
        max_inequations(root_formula.inequation_count)
    {};
};

struct Formula_Atoms {
    Sized_Array<Congruence> congruences;
    Sized_Array<Equation>   equations;
    Sized_Array<Inequation> inequations;
};

struct Temporary_Space {
    Slab_Fragment<Congruence> congruences;  // Temporary space for congruences
    Slab_Fragment<Equation>   equations;    // Temporary space for equations
    Slab_Fragment<Inequation> inequations;  // Temporary space for inequations
    Slab_Fragment<s64>        coefs;        // Coefs for all the above temporary atoms

    Temporary_Space(const Formula_Description& root_formula_desc) :
        congruences(root_formula_desc.congruence_count),
        equations(root_formula_desc.equation_count + root_formula_desc.congruence_count),
        inequations(root_formula_desc.inequation_count),
        coefs(root_formula_desc.var_count * root_formula_desc.atom_count()) {}
};


struct Formula_Allocator {
    u64 largest_congruence_block_size;
    vector<list<Slab_Fragment<Congruence>>> congruence_slabs;
    vector<list<Slab_Fragment<Equation>>>   equation_slabs;
    vector<list<Slab_Fragment<Inequation>>> inequation_slabs;

    // Macrostate data
    list<Macrostate_Header_Elem*> macrostate_headers;
    list<s64*>                    macrostate_data;    // @Design: We could probably use a stack allocator for this since we know that the memory is only acquired

    list<s64*> coef_blocks;

    const u64 items_per_slab_buffer = 16;
    const u64 var_count;

    Temporary_Space tmp_space;
    Allocator_Limits limits;

    Formula_Allocator(const Formula_Description& root_formula_desc) :
        largest_congruence_block_size(root_formula_desc.congruence_count),
        var_count(root_formula_desc.var_count),
        tmp_space(root_formula_desc),
        limits(root_formula_desc)
    {
        congruence_slabs.resize(limits.max_congruences);
        equation_slabs.resize(limits.max_equations);
        inequation_slabs.resize(limits.max_inequations);
    }

    // Formula_Allocator(const Allocator_Limits& limits, u64 var_count) :
    //     largest_congruence_block_size(limits.max_congruences),
    //     var_count(var_count),
    //     tmp_congruences(limits.max_congruences),
    //     tmp_equations(limits.max_equations),
    //     tmp_inequations(limits.max_inequations)
    // {
    //     congruence_slabs.resize(limits.max_congruences);

    //     // @Todo: Preallocate all slabs fragments with at least one buffer so that we can copy safely
    // }
    template <typename Atom_Type>
    Sized_Array<Atom_Type> alloc(list<Slab_Fragment<Atom_Type>>& slab_fragments, u64 count) {
        if (slab_fragments.empty()) {
            u64 slab_item_size = items_per_slab_buffer * count;
            slab_fragments.emplace_back(slab_item_size);
        }

        Slab_Fragment<Atom_Type>* last_slab = &slab_fragments.back();

        if (last_slab->next_free >= last_slab->capacity) {
            slab_fragments.emplace_back(last_slab->capacity);
            last_slab = &slab_fragments.back();
        }

        Atom_Type* allocated_atoms = &last_slab->items[last_slab->next_free];
        last_slab->next_free += count;

        return Sized_Array<Atom_Type>(allocated_atoms, count);
    }

    Sized_Array<Congruence> alloc_congruences(u64 count) {
        PRINTF_DEBUG("Allocating %lu congruence(s)\n", count);
        if (count == 0) return {nullptr, 0};

        auto& slabs_matching_size = congruence_slabs[count - 1];
        return alloc(slabs_matching_size, count);
    };

    Sized_Array<Equation> alloc_equations(u64 count) {
        PRINTF_DEBUG("Allocating %lu equation(s)\n", count);
        if (count == 0) return {nullptr, 0};

        auto& slabs_matching_size = equation_slabs[count - 1];
        return alloc(slabs_matching_size, count);
    }

    Sized_Array<Inequation> alloc_inequations(u64 count) {
        PRINTF_DEBUG("Allocating %lu inequation(s)\n", count);
        if (count == 0) return {nullptr, 0};

        auto& slabs_matching_size = inequation_slabs[count - 1];
        return alloc(slabs_matching_size, count);
    }

    s64* alloc_coefs(u64 count) {
        s64* new_coef_block = new s64[count];
        coef_blocks.push_back(new_coef_block);
        return new_coef_block;
    }

    template <typename Atom_Type>
    Atom_Type* alloc_tmp_atom(Slab_Fragment<Atom_Type>& tmp_atom_storage) {
        u64 atom_slot = tmp_atom_storage.next_free;
        assert(atom_slot < tmp_atom_storage.capacity);
        tmp_atom_storage.next_free += 1;

        Atom_Type* atom = &tmp_atom_storage.items[atom_slot];

        s64* coef_block_start = tmp_space.coefs.items + tmp_space.coefs.next_free;
        tmp_space.coefs.next_free += limits.var_count;

        atom->coefs = {coef_block_start, limits.var_count};

        return atom;
    }

    Congruence* alloc_temporary_congruence() {
        return alloc_tmp_atom(this->tmp_space.congruences);
    }

    Equation* alloc_temporary_equation() {
        return alloc_tmp_atom(this->tmp_space.equations);
    }

    Inequation* alloc_temporary_inequation() {
        return alloc_tmp_atom(this->tmp_space.inequations);
    }

    void ensure_tmp_clean() { // Debug
        assert(tmp_space.coefs.next_free == 0);
        assert(tmp_space.congruences.next_free == 0);
        assert(tmp_space.equations.next_free == 0);
        assert(tmp_space.inequations.next_free == 0);
    }

    Quantified_Atom_Conjunction get_tmp_formula() {
        Quantified_Atom_Conjunction formula;
        formula.congruences = Sized_Array<Congruence>(tmp_space.congruences.items, tmp_space.congruences.next_free);
        formula.equations   = Sized_Array<Equation>(tmp_space.equations.items, tmp_space.equations.next_free);
        formula.inequations = Sized_Array<Inequation>(tmp_space.inequations.items, tmp_space.inequations.next_free);
        return formula;
    }

    Quantified_Atom_Conjunction commit_tmp_space() {
        Sized_Array<Congruence> congruences = alloc_congruences(tmp_space.congruences.next_free);
        Sized_Array<Equation>   equations   = alloc_equations(tmp_space.equations.next_free);
        Sized_Array<Inequation> inequations = alloc_inequations(tmp_space.inequations.next_free);

        u64 total_atoms = tmp_space.congruences.next_free + tmp_space.equations.next_free + tmp_space.inequations.next_free;
        s64* coefs = alloc_coefs(total_atoms * limits.var_count);

        memcpy(congruences.items, tmp_space.congruences.items, sizeof(Congruence) * tmp_space.congruences.next_free);
        memcpy(equations.items, tmp_space.equations.items, sizeof(Equation) * tmp_space.equations.next_free);
        memcpy(inequations.items, tmp_space.inequations.items, sizeof(Inequation) * tmp_space.inequations.next_free);

        assert(tmp_space.coefs.next_free == total_atoms * limits.var_count);
        memcpy(coefs, tmp_space.coefs.items, sizeof(s64) * tmp_space.coefs.next_free);

        for (Congruence& congruence: congruences) {
            congruence.coefs.items = coefs;
            coefs += limits.var_count;
        }

        for (Equation& equation: equations) {
            equation.coefs.items = coefs;
            coefs += limits.var_count;
        }

        for (Inequation& inequation: inequations) {
            inequation.coefs.items = coefs;
            coefs += limits.var_count;
        }

        this->drop_tmp();

        Quantified_Atom_Conjunction new_formula;
        new_formula.congruences = congruences;
        new_formula.equations   = equations;
        new_formula.inequations = inequations;

        return new_formula;
    }

    Formula_Atoms allocate_formula(Formula_Description& desc) {
        const u64 coefs_needed = desc.atom_count() * desc.var_count;

        auto equations   = this->alloc_equations(desc.equation_count);
        auto inequations = this->alloc_inequations(desc.inequation_count);
        auto congruences = this->alloc_congruences(desc.congruence_count);
        auto coefs       = this->alloc_coefs(coefs_needed);

        u64 next_free_congruence = 0;
        u64 next_free_equation   = 0;
        u64 next_free_inequation = 0;

        for (auto& eq: equations) {
            eq.coefs.items = coefs;
            eq.coefs.size  = desc.var_count;
            coefs += desc.var_count;
        }

        for (auto& ineq: inequations) {
            ineq.coefs.items = coefs;
            ineq.coefs.size  = desc.var_count;
            coefs += desc.var_count;
        }

        for (auto& congruence: congruences) {
            congruence.coefs.items = coefs;
            congruence.coefs.size  = desc.var_count;
            coefs += desc.var_count;
        }

        return {.congruences = congruences, .equations = equations, .inequations = inequations};
    }

    void drop_tmp() {  // "Free" the temporary storage
        tmp_space.congruences.next_free = 0;
        tmp_space.equations.next_free = 0;
        tmp_space.inequations.next_free = 0;
        tmp_space.coefs.next_free = 0;
    }

    Sized_Array<Macrostate_Header_Elem> alloc_macrostate_headers(u64 count) {
        Macrostate_Header_Elem* headers = new Macrostate_Header_Elem[count];
        macrostate_headers.push_back(headers);
        return {headers, count};
    }

    Sized_Array<s64> alloc_macrostate_data(u64 state_count) {
        s64* state_data = new s64[state_count];
        macrostate_data.push_back(state_data);
        return {state_data, state_count};
    }

    ~Formula_Allocator() {
        for (auto coef_block: coef_blocks) delete[] coef_block;
        for (auto macrostate_header: macrostate_headers)  delete[] macrostate_header;
        for (auto macrostate_data_block: macrostate_data) delete[] macrostate_data_block;
    }
};



struct Formula_Pool { // Formula memory management
    unordered_set<Quantified_Atom_Conjunction> formulae;
    Formula_Allocator allocator;

    Formula_Pool(const Formula_Description& root_formula_description) : allocator(root_formula_description) {
        auto top = Quantified_Atom_Conjunction(true);
        auto bottom = Quantified_Atom_Conjunction(false);
        formulae.insert(top);
        formulae.insert(bottom);
    }

    Formula_Pool(const Quantified_Atom_Conjunction* root_formula) : allocator(root_formula) {};

    const Quantified_Atom_Conjunction* store_formula(const Quantified_Atom_Conjunction& formula);
    std::pair<const Quantified_Atom_Conjunction*, bool> store_formula_with_info(Quantified_Atom_Conjunction& formula);
};

typedef unordered_map<vector<s64>, list<Conjunction_State>> Prefix_Table;
std::ostream& operator<<(std::ostream& output, const map<const Quantified_Atom_Conjunction*, Prefix_Table>& macrostate);

struct Intermediate_Macrostate { // Macrostate that is being created, optimized for Pareto optimal insertions
    bool is_accepting = false;
    map<const Quantified_Atom_Conjunction*, Prefix_Table> formulae;
};

template <>
struct std::hash<Finalized_Macrostate> {
    std::size_t operator() (const Finalized_Macrostate& macrostate) const {
        std::size_t hash = 0u;

        for (Macrostate_Header_Elem& header: macrostate.header) {
            std::size_t formula_hash = std::hash<const Quantified_Atom_Conjunction*>{}(header.formula);
            hash = hash_combine(hash, formula_hash);
            hash = hash_combine(hash, header.state_cnt);
        }

        for (s64 state_constant: macrostate.state_data) {
            hash = hash_combine(hash, state_constant);
        }

        hash += macrostate.is_accepting * 33;

        return hash;
    }
};

char convert_cube_bit_to_char(u8 cube_bit);
void show_transitions_from_state(std::stringstream& output, const NFA& nfa, State origin, sylvan::MTBDD mtbdd);
NFA build_nfa_with_formula_entailement(const Quantified_Atom_Conjunction* formula, Conjunction_State& init_state, sylvan::BDDSET bdd_vars, Formula_Pool& formula_pool);
void init_mtbdd_libs();

struct Lazy_Construction_State {
    Formula_Pool& formula_pool;
    vector<Finalized_Macrostate>& output_queue;
    unordered_map<Finalized_Macrostate, u64> known_macrostates;
    unordered_set<u64> accepting_macrostates;

    bool  is_trap_state_needed;
    State trap_state_handle;
    bool  is_top_state_needed;
    State topstate_handle;
};


struct Stateful_Formula {
    Conjunction_State state;
    Quantified_Atom_Conjunction formula;
};

struct Stateful_Formula_Ptr {
    Conjunction_State state;
    const Quantified_Atom_Conjunction* formula;
};

struct New_Atoms_Info {
    u64  first_new_lin_atom_index;
    u64  eq_count;
    s64* new_lin_state_data;  // The data must be organized <EQ0,EQ1,...,INEQ0, INEQ1,...>
};

Stateful_Formula convert_graph_into_persistent_formula(Dep_Graph& graph, Formula_Allocator& allocator, Conjunction_State& state);
Stateful_Formula convert_graph_into_persistent_formula(Dep_Graph& graph, Formula_Allocator& allocator, Conjunction_State& state, const New_Atoms_Info& delta_info);

Stateful_Formula_Ptr try_inf_projection_on_equations(const Dep_Graph& graph, Formula_Pool& pool, Conjunction_State state);

enum class Bound_Type : unsigned {
    NONE  = 0x00,
    UPPER = 0x01,
    LOWER = 0x02,
};

template <typename T>
void vector_remove(vector<T>& vec, T& elem) {
    auto pos = std::find(vec.begin(), vec.end(), elem);
    if (pos != vec.end()) {
        vec.erase(pos);
    }
}

template <typename T>
bool vector_contains(const vector<T>& vec, const T& elem) {
    auto pos = std::find(vec.cbegin(), vec.cend(), elem);
    return (pos != vec.end());
}

s64 compute_multiplicative_inverse(s64 modulus, s64 a);

void insert_into_post_if_valuable2(Intermediate_Macrostate& post, const Quantified_Atom_Conjunction* formula, Conjunction_State& successor);

template <typename T>
Sized_Array<T> make_sized_array(const vector<T>& items) {
    T* buf = new T[items.size()];
    u64 item_idx = 0;
    for (auto& item: items) {
        buf[item_idx] = item;
        item_idx += 1;
    }
    return Sized_Array<T> {.items = buf, .size = items.size()};
}

// ----- MODULO LINEARIZATION -----


struct Atom {
    unordered_map<s64, sylvan::MTBDD> post_cache;

    vector<s64> coefs;
    vector<u64> vars;
    sylvan::BDDSET var_set;

    Atom(const vector<u64>& vars, const vector<s64>& coefs);

    Atom(const Atom& other) : coefs(other.coefs), vars(other.vars), var_set(other.var_set) {
        sylvan::mtbdd_ref(other.var_set);
    };

    Atom(Atom&& other) : coefs(std::move(other.coefs)), vars(std::move(other.vars)), var_set(other.var_set) {
        sylvan::mtbdd_ref(var_set);
    };

    ~Atom();
    s64 dot_with_symbol(u64 symbol) const;

    template <typename Post_Maker>
    sylvan::MTBDD make_extended_post(Post_Maker& maker, s64 rhs);

    void invalidate_cache();
};

struct Inequation2 : Atom {
    Inequation2(const vector<u64>& vars, const vector<s64>& coefs) : Atom(vars, coefs) {};

    s64  post(s64 rhs, u64 symbol) const;
    bool accepts(s64 rhs, u64 symbol) const;

    sylvan::MTBDD compute_entire_post(s64 rhs);
    sylvan::MTBDD extend_post(sylvan::MTBDD current_post, vector<u8> ritch_symbol_space, s64 rhs, u64 symbol);
};

struct Equation2 : Atom {
    Equation2(const vector<u64>& vars, const vector<s64>& coefs) : Atom(vars, coefs) {};

    optional<s64> post(s64 rhs, u64 symbol) const;
    bool accepts(s64 rhs, u64 symbol) const;

    sylvan::MTBDD compute_entire_post(s64 rhs);
    sylvan::MTBDD extend_post(sylvan::MTBDD current_post, vector<u8> ritch_symbol_space, s64 rhs, u64 symbol);
};

struct Congruence2 : Atom {
    s64 modulus_2pow = 0;
    s64 modulus_odd  = 0;

    Congruence2(const vector<u64>& vars, const vector<s64>& coefs, s64 modulus_2pow, s64 modulus_odd) :
        Atom(vars, coefs), modulus_2pow(modulus_2pow), modulus_odd(modulus_odd) {
    };

    Congruence2(const vector<u64>& vars, const vector<s64>& coefs, s64 modulus) : Atom(vars, coefs) {
        auto decomposed_modulus = decompose_modulus(modulus);
        modulus_2pow = decomposed_modulus.modulus_2pow;
        modulus_odd = decomposed_modulus.modulus_odd;
    };

    optional<s64> post(s64 rhs, u64 symbol) const;
    bool accepts(s64 rhs, u64 symbol) const;

    sylvan::MTBDD compute_entire_post(s64 rhs);
    sylvan::MTBDD extend_post(sylvan::MTBDD current_post, vector<u8> ritch_symbol_space, s64 rhs, u64 symbol);


    bool post_results_in_new_formula() const {
        return modulus_2pow > 1;
    }
};

struct Formula_Structure_Info {
    u64 prefix_size;
    u64 post_size;
};


struct Formula2 {
    vector<Congruence2> congruences;
    vector<Equation2>   equations;
    vector<Inequation2> inequations;

    sylvan::BDDSET quantif_vars;

    u64 atom_count() const {
        return congruences.size() + equations.size() + inequations.size();
    }

    Formula_Structure_Info describe() const {
        return {
            .prefix_size = congruences.size() + equations.size(),
            .post_size = congruences.size() + equations.size() + inequations.size()
        };
    }

    sylvan::BDDSET get_all_vars() {
        using sylvan::BDDSET;

        BDDSET vars = sylvan::mtbdd_set_empty();
        sylvan::mtbdd_ref(vars);

        for (auto& congruence: congruences) {
            for (auto var: congruence.vars) {
                BDDSET new_set = sylvan::mtbdd_set_add(vars, var);
                sylvan::mtbdd_ref(new_set);
                sylvan::mtbdd_deref(vars);
                vars = new_set;
            }
        }

        for (auto& atom: inequations) {
            for (auto var: atom.vars) {
                BDDSET new_set = sylvan::mtbdd_set_add(vars, var);
                sylvan::mtbdd_ref(new_set);
                sylvan::mtbdd_deref(vars);
                vars = new_set;
            }
        }

        for (auto& atom: equations) {
            for (auto var: atom.vars) {
                BDDSET new_set = sylvan::mtbdd_set_add(vars, var);
                sylvan::mtbdd_ref(new_set);
                sylvan::mtbdd_deref(vars);
                vars = new_set;
            }
        }

        return vars;
    }
};


struct Macrostate_Data {
    struct Factored_States { // States sharing the same prefix
        vector<s64> prefix;
        Chunked_Array<s64> suffixes;

        bool operator==(const Factored_States& other) const { return prefix == other.prefix && suffixes == other.suffixes; }
        bool operator<(const Factored_States& other) const { return prefix < other.prefix; }
    };

    const Formula2* formula;
    vector<Factored_States> states;

    struct Iterator {
        const Macrostate_Data* data;
        Sized_Array<s64> buffer;
        s64 prefix_idx;
        s64 suffix_idx;

        using value_type = Sized_Array<s64>;
        using pointer    = Sized_Array<s64>*;
        using reference  = Sized_Array<s64>&;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::random_access_iterator_tag;

        Iterator(): data(nullptr), buffer({nullptr, 0}), prefix_idx(0), suffix_idx(0) {};
        Iterator(const Macrostate_Data* m): data(m), prefix_idx(0), suffix_idx(0) {
            if (m->states.empty()) {
                buffer = {nullptr, 0};
                return;
            }

            Formula_Structure_Info formula_structure = m->formula->describe();
            u64 post_size = formula_structure.post_size;

            s64* raw_buffer = new s64[post_size];
            assert(raw_buffer != nullptr);
            buffer = {raw_buffer, post_size};
            fill_buffer_with_data();
        }

        void fill_buffer_with_data() {
            auto& entry = data->states[prefix_idx];
            std::memcpy(buffer.items, entry.prefix.data(), entry.prefix.size() * sizeof(s64));

            u64 suffix_size = data->formula->inequations.size();
            std::memcpy(buffer.items + entry.prefix.size(), entry.suffixes.get_nth_chunk_data(suffix_idx), suffix_size * sizeof(s64));
        }

        Iterator(const Macrostate_Data* m, u64 prefix_idx, u64 suffix_idx):
            data(m),
            prefix_idx(prefix_idx),
            suffix_idx(suffix_idx) {};

        Iterator(const Iterator& other) :
            data(other.data),
            buffer(other.buffer),
            prefix_idx(other.prefix_idx),
            suffix_idx(other.suffix_idx)
        {
            if (buffer.items != nullptr) {
                buffer.items = new s64[buffer.size];
                memcpy(buffer.items, other.buffer.items, other.buffer.size * sizeof(s64));
            }
        };

        Iterator(Iterator&& other) :
            data(other.data),
            buffer(other.buffer),
            prefix_idx(other.prefix_idx),
            suffix_idx(other.suffix_idx)
        {
            other.buffer.items = nullptr;
        };

        Iterator& operator=(const Iterator& other) = default;

        reference operator*() {
            return buffer;
        }
        pointer operator->() {
            return &buffer;
        }

        Iterator& operator++() {
            auto& entry = data->states[prefix_idx];
            suffix_idx += 1;

            if (suffix_idx >= entry.suffixes.chunk_count) {
                suffix_idx = 0;
                prefix_idx += 1;
            }

            if (prefix_idx < data->states.size()) {
                fill_buffer_with_data();
            }
            return *this;
        }

        bool operator==(const Iterator& other) const {
            return data == other.data && prefix_idx == other.prefix_idx && suffix_idx == other.suffix_idx;
        }

        bool operator!=(const Iterator& other) {
            return !(*this == other);
        }

        ~Iterator() {
            delete[] buffer.items;
        }
    };

    Iterator begin() const {
        return Iterator(this);
    }

    Iterator end() const {
        return Iterator(this, this->states.size(), 0);
    }

    bool operator==(const Macrostate_Data& other) const {
        return (formula == other.formula) && (states == other.states);
    }
};

struct Formula_State_Pair {
    const Formula2* formula;
    Sized_Array<s64> state;
};

struct Macrostate2 {
    vector<Macrostate_Data> states;
    bool accepting;

    Formula_Structure_Info* formula_structure = nullptr;
    State handle;

    struct Iterator {
        const Macrostate2* macrostate;
        vector<Macrostate_Data>::const_iterator current_states_block;
        Macrostate_Data::Iterator macrostate_data_iter;

        Formula_State_Pair out;

        using value_type = Formula_State_Pair;
        using pointer    = Formula_State_Pair*;
        using reference  = Formula_State_Pair&;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::random_access_iterator_tag;

        Iterator(): macrostate(nullptr) {};

        Iterator(const Macrostate2* m, const vector<Macrostate_Data>::const_iterator& start_at): macrostate(m), current_states_block(start_at) {};

        Iterator(const Macrostate2* m):
            macrostate(m),
            current_states_block(m->states.begin()),
            macrostate_data_iter(m->states.empty() ? Macrostate_Data::Iterator() :
                                                     m->states.begin()->begin())
        {
            if (m->states.empty()) {
                Sized_Array<s64> out_arr = {nullptr, 0};
                out = {nullptr, out_arr};
                return;
            }
            out = {
                .formula = current_states_block->formula,
                .state = *macrostate_data_iter,
            };
        }

        Iterator(const Iterator& other) = delete;
        Iterator(Iterator&& other) = delete;

        reference operator*() { return out; }
        pointer operator->() { return &out; }

        Iterator& operator++() {
            ++macrostate_data_iter;
            if (macrostate_data_iter == current_states_block->end()) {
                ++current_states_block;
                if (current_states_block != macrostate->states.end()) {
                    macrostate_data_iter = current_states_block->begin();
                    out.formula = current_states_block->formula;
                    out.state = *macrostate_data_iter;
                }
            } else {
                out.state = *macrostate_data_iter;
            }
            return *this;
        }

        bool operator!=(const Iterator &other) const {
            return !(*this == other);
        }

        bool operator==(const Iterator &other) const {
            bool same_block = (current_states_block == other.current_states_block);
            if (!same_block) return false;

            if (current_states_block == macrostate->states.end()) {
                return true; // Both terminated
            }

            return (macrostate_data_iter == other.macrostate_data_iter);
        }
    };

    Iterator begin() const {
        return Iterator(this);
    }

    Iterator end() const {
        return Iterator(this, this->states.end());
    }

    friend std::ostream& operator<<(std::ostream& os, const Macrostate2& m);
    bool operator==(const Macrostate2& other) const {
        bool are_eq = (states == other.states && accepting == other.accepting);
        return are_eq;
    }

};

template<> struct std::hash<Macrostate2> {
    std::size_t operator()(Macrostate2 const& macrostate) const noexcept {
        std::size_t hash = 0;
        for (auto& entry: macrostate.states) {
            size_t formula_hash = std::hash<const Formula2*>{}(entry.formula);
            hash = hash_combine(hash, formula_hash);
            for (auto& factored_state: entry.states) {
                hash = hash_combine(hash, hash_vector(factored_state.prefix, 0));
                hash = hash_combine(hash, hash_chunked_array(factored_state.suffixes));
            }
        }
        hash += (macrostate.accepting ? 33 : 0);
        return hash;
    }
};

struct NFA_Construction_Ctx {
    unordered_map<Macrostate2, State> known_states;
    vector<const Macrostate2*>        macrostates_to_explore;
    Block_Allocator                   macrostate_block_alloc;
    NFA*                              constructed_nfa;
    Formula_Structure_Info            structure_info;
    Formula2*                         formula = nullptr;
    State                             trapstate_handle = 0;
    bool                              trapstate_needed = false;
    unordered_map<vector<s64>, sylvan::MTBDD> cache;
    sylvan::MTBDD                     intersection_top;
};

void exp_macrostate(Formula2& formula, const Macrostate2* state, NFA_Construction_Ctx* ctx);
NFA build_nfa_for_conjunction(Formula2& formula, Macrostate2& initial_macrostate);

Formula_Structure describe_formula(const Quantified_Atom_Conjunction* formula);
Formula_Structure describe_formula(const Dep_Graph* graph);
#endif

