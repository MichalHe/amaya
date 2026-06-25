#include "../include/lazy.hpp"
#include "../include/tfa_leaf.h"
#include "../include/algorithms.hpp"
#include "../include/rewrites.h"

#include <cmath>
#include <optional>
#include <stdlib.h>

#include <algorithm>
#include <bitset>
#include <chrono>
#include <iostream>
#include <list>
#include <cstring>
#include <string>
#include <sstream>
#include <sylvan_mtbdd.h>
#include <vector>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#define VAR_ID_TO_BIT_POS(var) (var - 1)
#define VAR_ID_TO_BIT_MASK(var) (1ull << VAR_ID_TO_BIT_POS(var))

using std::list;
using std::map;
using std::vector;

using std::pair;
using std::optional;

using namespace sylvan;

#define DEBUG_RUNTIME 0

typedef Quantified_Atom_Conjunction Formula;

std::size_t hash_array(const Sized_Array<s64>& arr) {
    std::size_t hash = 0;
    for (u64 i = 0; i < arr.size; i++) {
        std::size_t coef_hash = std::hash<s64>{}(arr.items[i]);
        hash = hash + 0x9e3779b9 + (coef_hash << 6) + (coef_hash >> 2);
    }
    return hash;
}

std::size_t hash_chunked_array(const Chunked_Array<s64>& arr) {
    std::size_t hash = 0;
    u64 total_size = arr.total_size();
    for (u64 i = 0; i < total_size; i++) {
        std::size_t coef_hash = std::hash<s64>{}(arr.data[i]);
        hash = hash_combine(hash, coef_hash);
    }
    return hash;
}

s64 vector_dot(const Sized_Array<s64>& coefs, const u64 symbol) {
    s64 dot = 0;
    for (u64 var_i = 0; var_i < coefs.size; var_i++) {
        s64 is_bit_set = (symbol & (1u << var_i)) > 0;
        dot += is_bit_set * coefs.items[var_i];
    }
    return dot;
};

s64 combine_moduli(s64 mod_2pow, s64 mod_odd) {
    s64 modulus = (1ull << mod_2pow) * mod_odd;
    return modulus;
}

Decomposed_Modulus decompose_modulus(s64 modulus) {
    s64 modulus_pow2 = 0;
    while (modulus % 2 == 0) {
        modulus_pow2 += 1;
        modulus      /= 2;
    }
    modulus += (modulus == 0); // If odd modulus = 0, then make it 1
    return {.modulus_2pow = modulus_pow2, .modulus_odd = modulus};
}

typedef s64 Modulus;

optional<s64> congruence_compute_post(Congruence& congruence, s64 state, u64 symbol) {
    s64 dot  = vector_dot(congruence.coefs, symbol);
    s64 post = state - dot;

    if (congruence.modulus_2pow > 0) {
        if (post % 2 == 0) {
            post /= 2;
            s64 new_modulus = combine_moduli(congruence.modulus_2pow - 1, congruence.modulus_odd);
            post %= new_modulus;
            post += (post < 0) * new_modulus;
            return post;
        }
        return std::nullopt;
    }

    post += congruence.modulus_odd * ((post % 2) != 0);
    post /= 2;
    post = post % congruence.modulus_odd;
    post += congruence.modulus_odd * (post < 0);
    return post;
};

bool congruence_accepts_symbol(Congruence& congruence, s64 state, u64 symbol) {
    s64 dot = vector_dot(congruence.coefs, symbol);
    s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);
    return ((state + dot) % modulus) == 0;
}

std::optional<s64> equation_compute_post(Equation& eq, s64 state, u64 symbol) {
    s64 dot = vector_dot(eq.coefs, symbol);
    s64 post = state - dot;
    s64 post_div_2 = post / 2;
    s64 post_mod_2 = post % 2;

    if (post_mod_2) return std::nullopt;

    post_div_2 -= (post_mod_2 != 0) * (post < 0); // Floor the division
    return post_div_2;
}

bool equation_accepts_symbol(Equation& eq, s64 state, u64 symbol) {
    s64 dot = vector_dot(eq.coefs, symbol);
    return (state + dot) == 0;
}

s64 inequation_compute_post(Inequation& ineq, s64 state, u64 symbol) {
    s64 dot = vector_dot(ineq.coefs, symbol);
    s64 post = state - dot;
    s64 post_div_2 = post / 2;
    s64 post_mod_2 = post % 2;
    post_div_2 -= (post_mod_2 != 0) * (post < 0); // Floor the division
    return post_div_2;
}

bool inequation_accepts_symbol(Inequation& ineq, s64 state, u64 symbol) {
    s64 dot = vector_dot(ineq.coefs, symbol);
    return (state + dot) >= 0;
}

bool Conjunction_State::operator==(const Conjunction_State& other) const {
    return constants == other.constants;
}

bool Quantified_Atom_Conjunction::operator==(const Quantified_Atom_Conjunction& other) const {
    return other.bottom == bottom &&
           other.var_count == var_count &&
           other.congruences == congruences &&
           other.inequations == inequations &&
           other.equations == equations &&
           other.bound_vars == other.bound_vars;
}

struct Successor {
    const Formula* formula = nullptr;
    Conjunction_State state;
};

optional<Successor> compute_successor(Formula_Pool& formula_pool, const Formula* formula, s64* state_data, u64 symbol) {
    vector<s64> successor_values(formula->atom_count());

    u64 atom_idx = 0;
    for (auto& cong: formula->congruences) {
        auto maybe_successor = congruence_compute_post(cong, state_data[atom_idx], symbol);

        if (!maybe_successor.has_value()) {
            return std::nullopt;
        }

        s64 new_state = maybe_successor.value();

        successor_values[atom_idx] = new_state;
        atom_idx += 1;
    }

    for (auto& eq: formula->equations) {
        auto successor_value = equation_compute_post(eq, state_data[atom_idx], symbol);

        if (!successor_value.has_value()) return std::nullopt;

        successor_values[atom_idx] = successor_value.value();
        atom_idx += 1;
    }

    for (auto& ineq: formula->inequations) {
        s64 post = inequation_compute_post(ineq, state_data[atom_idx], symbol);
        successor_values[atom_idx] = post;
        atom_idx += 1;
    };

    Conjunction_State post(successor_values);

    // Determine if we actually will need to allocate memory
    if (!formula->post_formula) {
        // All components, including all congruences had post (none returned empty optional). As
        // FA are synchronous, it does not matter what symbol did we compute post with since with
        // every other symbol with successful post computation we will modify the congruence moduli
        // in the same way although the target state might be different. The was_post_computed
        // field is not hashed, so it is OK to drop const and set it.
        bool should_allocate = false;
        for (auto& cong: formula->congruences) {
            if (cong.modulus_2pow > 0) {
                should_allocate = true;
                break;
            }
        }

        if (should_allocate) {
            Sized_Array<Congruence> new_congruences = formula_pool.allocator.alloc_congruences(formula->congruences.size);

            for (u64 congruence_i = 0; congruence_i < formula->congruences.size; congruence_i++) {
                Congruence& old_congruence = formula->congruences.items[congruence_i];
                Congruence new_congruence = {
                    .coefs = old_congruence.coefs,
                    .modulus_odd = old_congruence.modulus_odd,
                    .modulus_2pow = old_congruence.modulus_2pow - 1
                };
                new_congruences.items[congruence_i] = new_congruence;
            }

            Formula new_formula = Formula(new_congruences, formula->equations, formula->inequations,
                                          formula->bound_vars, formula->var_count);
            const Formula* new_formula_canon_ptr = formula_pool.store_formula(new_formula);

            { // Make sure we do not need to recompute the thing
                const_cast<Formula*>(formula)->post_formula = new_formula_canon_ptr;
            }

            Successor successor = {.formula = new_formula_canon_ptr, .state = post};
            return successor;
        } else {
            // All congruences have odd moduli, make sure we don't try allocating a new formula due
            // to modulus change ever again (self loop in dependency graph)
            const_cast<Formula*>(formula)->post_formula = formula;
        }
    }

    Successor successor = {.formula = formula->post_formula, .state = post};
    return successor;
}

bool accepts_last_symbol(const Formula* formula, s64* state_data, u64 symbol) {
    bool accepts = true;

    u64 atom_i = 0;
    for (auto& congr: formula->congruences) {
        accepts &= congruence_accepts_symbol(congr, state_data[atom_i], symbol);
        atom_i += 1;
    }

    for (auto& eq: formula->equations) {
        accepts &= equation_accepts_symbol(eq, state_data[atom_i], symbol);
        atom_i += 1;
    }

    for (auto& ineq: formula->inequations) {
        accepts &= inequation_accepts_symbol(ineq, state_data[atom_i], symbol);
        atom_i += 1;
    }

    return accepts;
}


constexpr
Preferred_Var_Value_Type operator|(Preferred_Var_Value_Type left, Preferred_Var_Value_Type right)
{
    auto left_raw = static_cast<std::underlying_type_t<Preferred_Var_Value_Type>>(left);
    auto right_raw = static_cast<std::underlying_type_t<Preferred_Var_Value_Type>>(right);
    return static_cast<Preferred_Var_Value_Type>(left_raw | right_raw);
}

constexpr
Preferred_Var_Value_Type operator&(Preferred_Var_Value_Type left, Preferred_Var_Value_Type right)
{
    auto left_raw = static_cast<std::underlying_type_t<Preferred_Var_Value_Type>>(left);
    auto right_raw = static_cast<std::underlying_type_t<Preferred_Var_Value_Type>>(right);
    return static_cast<Preferred_Var_Value_Type>(left_raw & right_raw);
}


std::ostream& operator<<(std::ostream& output, const Conjunction_State& atom) {
    output << "(";
    if (!atom.constants.empty()) {
        auto constants_it = atom.constants.begin();
        output << *constants_it;
        ++constants_it;

        for (; constants_it != atom.constants.end(); ++constants_it) {
            output << ", " << *constants_it;
        }
    }

    output << ")"; // "[" << atom.formula << "]";
    return output;
}


void write_memview(std::ostream& output, s64* data, s64 count) {
    for (s64 i = 0; i < count; i++) {
        if (i > 0) output << ", ";
        output << data[i];
    }
}

std::ostream& operator<<(std::ostream& output, const Finalized_Macrostate& macrostate) {
    output << "{";
    s64 constants_written = 0;
    for (s64 formula_idx = 0; formula_idx < macrostate.header.size; formula_idx++) {
        const Macrostate_Header_Elem& header = macrostate.header.items[formula_idx];

        if (formula_idx > 0) output << ", ";
        // output << "`" << *header.formula << "`: [";
        output << "[";

        for (s64 state_idx = 0; state_idx < header.state_cnt; state_idx++) {
            if (state_idx > 0) output << ", ";

            output << "(";
            write_memview(output, macrostate.state_data.items + constants_written, header.formula->atom_count());
            output << ")";
            constants_written += header.formula->atom_count();
        }

        output << "]";
    }

    if (macrostate.is_accepting) {
        output << " (+ ACCEPTING)";
    }
    output << "}";
    return output;
}

bool Finalized_Macrostate::operator==(const Finalized_Macrostate& other) const {
    if (is_accepting != other.is_accepting) return false;
    if (header.size  != other.header.size) return false;
    if (state_data.size != other.state_data.size) return false;

    // @Optimize: Ensure that these loops get properly vectorized
    for (s64 i = 0; i < header.size; i++) {
        bool is_equal = (header.items[i].formula == other.header.items[i].formula) && (header.items[i].state_cnt == other.header.items[i].state_cnt);
        if (!is_equal) return false;
    }

    for (s64 i = 0; i < state_data.size; i++) {
        if (state_data.items[i] != other.state_data.items[i]) return false;
    }

    return true;
};

Dep_Graph build_dep_graph(const Quantified_Atom_Conjunction& conj) {
    Dep_Graph graph;
    graph.var_nodes = vector<Var_Node>(conj.var_count);
    graph.equations.reserve(conj.equations.size);
    graph.inequations.reserve(conj.inequations.size);
    graph.congruences.reserve(conj.congruences.size);

    for (u64 var : conj.bound_vars) {
        graph.mark_var_as_free(var);
    }
    graph.free_vars = ~graph.free_vars;

    for (s32 eq_idx = 0; eq_idx < conj.equations.size; eq_idx++) {
        auto& eq = conj.equations.items[eq_idx];
        vector<s64> coefs(eq.coefs.begin(), eq.coefs.end());
        Linear_Node node = {.coefs = coefs, .vars = {}, .is_satisfied = false};

        for (auto var = 0; var < conj.var_count; var++) {
            Var_Node& var_node = graph.var_nodes[var];
            if (eq.coefs.items[var] != 0) {
                var_node.equations.push_back(eq_idx);
                node.vars.push_back(var);
            }
        }

        graph.equations.push_back(node);
    }

    for (s32 ineq_idx = 0; ineq_idx < conj.inequations.size; ineq_idx++) {
        auto& ineq = conj.inequations.items[ineq_idx];
        vector<s64> coefs(ineq.coefs.begin(), ineq.coefs.end());
        Linear_Node atom = {.coefs = coefs, .vars = {}, .is_satisfied = false};

        for (auto var = 0; var < conj.var_count; var++) {
            Var_Node& var_node = graph.var_nodes[var];
            s64 coef           = ineq.coefs.items[var];
            if (coef) {
                if (coef < 0) var_node.lower_bounds.push_back(ineq_idx);
                else          var_node.upper_bounds.push_back(ineq_idx);
                atom.vars.push_back(var);
            }
        }

        graph.inequations.push_back(atom);
    }

    for (s32 congr_idx = 0; congr_idx < conj.congruences.size; congr_idx++) {
        auto& congr = conj.congruences.items[congr_idx];
        vector<s64> coefs(congr.coefs.begin(), congr.coefs.end());
        Congruence_Node congruence = {
            .coefs = coefs,
            .vars = {},
            .modulus_2pow = congr.modulus_2pow,
            .modulus_odd  = congr.modulus_odd,
            .is_satisfied = false,
        };

        for (auto var = 0; var < conj.var_count; var++) {
            Var_Node& var_node = graph.var_nodes[var];
            s64 coef           = congr.coefs.items[var];
            if (coef) {
                var_node.congruences.push_back(congr_idx);
                congruence.vars.push_back(var);
            }
        }

        graph.congruences.push_back(congruence);
    }

    // Detect hard bounds
    for (s32 ineq_idx = 0; ineq_idx < graph.inequations.size(); ineq_idx++) {
        Linear_Node node = graph.inequations[ineq_idx];
        if (node.vars.size() == 1) {
            u64 var            = node.vars[0];
            s64 coef           = node.coefs[var];
            Var_Node& var_node = graph.var_nodes[var];

            Hard_Bound bound_info = {.atom_i = ineq_idx};
            if (coef > 0) var_node.hard_upper_bound = bound_info;
            else          var_node.hard_lower_bound = bound_info;
        }
    }

    s32 offset = graph.congruences.size() + graph.equations.size();
    for (u64 var = 0; var < graph.var_nodes.size(); var++) {
        auto& var_node = graph.var_nodes[var];
        if (var_node.has_hard_lower_bound() && var_node.has_hard_upper_bound()) {
            auto& lower_bound = graph.inequations[var_node.hard_lower_bound.atom_i];
            auto& upper_bound = graph.inequations[var_node.hard_upper_bound.atom_i];
            assert(abs(lower_bound.coefs[var]) == 1);

            s32 lower_bound_pos = offset + var_node.hard_lower_bound.atom_i;
            s32 upper_bound_pos = offset + var_node.hard_upper_bound.atom_i;
            Watched_Position_Pair watched_positions = {
                .position0 = lower_bound_pos,
                .position1 = upper_bound_pos,
                .required_value0 = 0,
                .required_value1 = 0,
            };
            graph.watched_positions.push_back(watched_positions);
        }
    }

    graph.quantified_vars = conj.bound_vars;
    graph.vars_not_removed_in_simplification = conj.bound_vars;

    {
        unordered_map<vector<s64>, s32> complementary_ineqs;
        for (s32 ineq_idx = 0; ineq_idx < graph.inequations.size(); ineq_idx++) {
            auto& ineq = graph.inequations[ineq_idx];
            auto complement_pos = complementary_ineqs.find(ineq.coefs);
            if (complement_pos != complementary_ineqs.end()) {
                auto complement_idx = complement_pos->second;

                if (complement_idx < ineq_idx) {
                    graph.complementary_pairs.push_back({complement_idx, ineq_idx});
                } else {
                    graph.complementary_pairs.push_back({ineq_idx, complement_idx});
                }
            } else {
                vector<s64> neg_coefs = ineq.coefs;
                for (auto& coef: neg_coefs) coef = -coef;
                complementary_ineqs[neg_coefs] = ineq_idx;
            }
        }
    }

    return graph;
}


std::string get_node_attrs_for_hard_bound(Bound_Type type) {
    switch (type) {
        case Bound_Type::LOWER:
            return ", style=filled, fillcolor=\"#6bb7ea\"";
        case Bound_Type::UPPER: // Upper
            return ", style=filled, fillcolor=\"#ea6b78\"";
        default:
            return "";
    }
}


void write_dep_graph_dot(std::ostream& output, Dep_Graph& graph) {
    output << "graph deps {\n";

    for (u64 var = 0; var < graph.var_nodes.size(); var++) {
        bool is_quantified = (std::find(graph.quantified_vars.begin(), graph.quantified_vars.end(), var) != graph.quantified_vars.end());
        std::string quantif_attrs = is_quantified  ? ", color=green" : "";
        output << "  v" << var << " [label=\"x" << var << "\",shape=box" <<  quantif_attrs << "]\n";
    }

    for (s32 ineq_idx = 0; ineq_idx < graph.inequations.size(); ineq_idx++) {
        auto& ineq = graph.inequations[ineq_idx];

        if (ineq.is_satisfied) continue;

        Bound_Type bound_type = Bound_Type::NONE;
        for (auto var: ineq.vars) { // Check whether the current inequations represents a bound for some of its vars
            auto& var_node = graph.var_nodes[var];
            if (var_node.is_hard_lower_bound(ineq_idx)) {
                bound_type = Bound_Type::LOWER;
                break;
            }
            if (var_node.is_hard_upper_bound(ineq_idx)) {
                bound_type = Bound_Type::UPPER;
                break;
            }
        }

        std::string hard_bound_attrs = get_node_attrs_for_hard_bound(bound_type);

        output << "  ineq" << ineq_idx << " [label=\"" << ineq << "\"" << hard_bound_attrs << "]\n";
    }

    for (s32 eq_idx = 0; eq_idx < graph.equations.size(); eq_idx++) {
        auto& eq = graph.equations[eq_idx];
        output << "  eq" << eq_idx << " [label=\"" << eq << "\"]\n";
    }

    for (s32 congr_idx = 0; congr_idx < graph.equations.size(); congr_idx++) {
        auto& eq = graph.congruences[congr_idx];
        output << "  congr" << congr_idx << " [label=\"" << eq << "\"]\n";
    }

    for (u64 var = 0; var < graph.var_nodes.size(); var++) {
        auto& var_node = graph.var_nodes[var];
        for (auto& atom_i: var_node.congruences) {
            output << "  v" << var << " -- " << "congr" << atom_i << "\n";
        }
        for (auto atom_i: var_node.lower_bounds) {
            output << "  v" << var << " -- " << "ineq" << atom_i << " [color=\"blue\"]" << "\n";
        }
        for (auto atom_i: var_node.upper_bounds) {
            output << "  v" << var << " -- " << "ineq" << atom_i << " [color=\"red\"]" << "\n";
        }
        for (auto atom_i: var_node.equations) {
            output << "  v" << var << " -- " << "eq" << atom_i  << "\n";
        }
    }

    // for (auto quantif_var: graph.quantified_vars) {
    //     unordered_set<u64> affected_vars          = compute_nonlinearly_affected_vars(graph, quantif_var);
    //     unordered_set<u64> linearly_affected_vars = compute_free_vars_affected_linearly(graph, quantif_var);
    //     for (auto affected_var: affected_vars) {
    //         if (!linearly_affected_vars.contains(affected_var)) {
    //             output << "  v" << quantif_var << " -- v" << affected_var << " [style=dotted]\n";
    //         }
    //     }
    // }

    output << "}\n";
}


s64 compute_multiplicative_inverse(s64 modulus, s64 a) {
    s64 prev_reminder = modulus;
    s64 reminder = a;
    s64 prev_s = 1;
    s64 s = 0;
    s64 prev_t = 0;
    s64 t = 1;

    s64 aux;
    while (reminder != 0) {
        s64 q = prev_reminder / reminder;

        aux = reminder;
        reminder = prev_reminder - q * reminder;
        prev_reminder = aux;

        aux = s;
        s = prev_s - q * s;
        prev_s = aux;

        aux = t;
        t = prev_t - q * t;
        prev_t = aux;
    }

    // Normalize prev_t to be in [0..modulus)
    prev_t += (prev_t < 0) * modulus;
    return prev_t;
}

Stateful_Formula convert_graph_into_tmp_formula(Dep_Graph& graph, Formula_Allocator& allocator, Ritch_Conjunction_State& state) {
    vector<s64> formula_state;

    for (u64 congr_i = 0; congr_i < graph.congruences.size(); congr_i++) {
        Congruence_Node& congruence_node = graph.congruences[congr_i];
        if (congruence_node.is_satisfied) continue;

        formula_state.push_back(state.get_congruence_val(congr_i));

        Congruence* congruence = allocator.alloc_temporary_congruence();

        memcpy(congruence->coefs.items, congruence_node.coefs.data(), sizeof(s64) * congruence_node.coefs.size());

        congruence->modulus_2pow = congruence_node.modulus_2pow;
        congruence->modulus_odd  = congruence_node.modulus_odd;
    }

    for (u64 eq_idx = 0; eq_idx < graph.equations.size(); eq_idx++) {
        Linear_Node& eq_node = graph.equations[eq_idx];

        if (eq_node.is_satisfied) continue;

        s64 state_constant = state.get_eq_val(eq_idx);
        formula_state.push_back(state_constant);

        Equation* eq = allocator.alloc_temporary_equation();
        memcpy(eq->coefs.items, eq_node.coefs.data(), sizeof(s64) * eq_node.coefs.size());
        eq->coefs.size = eq_node.coefs.size();
    }

    for (u64 ineq_idx = 0; ineq_idx < graph.inequations.size(); ineq_idx++) {
        Linear_Node& ineq_node = graph.inequations[ineq_idx];

        if (ineq_node.is_satisfied) continue;

        s64 state_constant = state.get_ineq_val(ineq_idx);
        formula_state.push_back(state_constant);

        Inequation* ineq = allocator.alloc_temporary_inequation();
        memcpy(ineq->coefs.items, ineq_node.coefs.data(), sizeof(s64) * ineq_node.coefs.size());
        ineq->coefs.size = ineq_node.coefs.size();
    }


    Quantified_Atom_Conjunction conjunction = allocator.get_tmp_formula();
    conjunction.bound_vars = graph.quantified_vars;
    conjunction.var_count  = graph.var_nodes.size();

    Conjunction_State new_state(formula_state);
    return {.state = new_state, .formula = conjunction};
}

Stateful_Formula convert_graph_into_persistent_formula(Dep_Graph& graph, Formula_Allocator& allocator, Ritch_Conjunction_State& state) {
    auto tmp_formula = convert_graph_into_tmp_formula(graph, allocator, state);
    auto presistent_formula = allocator.commit_tmp_space();
    presistent_formula.var_count  = tmp_formula.formula.var_count;
    presistent_formula.bound_vars = tmp_formula.formula.bound_vars;
    return {.state = tmp_formula.state, .formula = presistent_formula};
}

/*
std::pair<const Formula*, Conjunction_State> simplify_stateful_formula(const Formula* formula, Conjunction_State& state, Formula_Pool& pool) {
    // std::cout << "Simplifying formula: " << *formula << std::endl;
    if (formula->dep_graph.potential_vars.empty())
        return {formula, state};

    return {formula, state};
#if 0
    Dep_Graph* simplified_graph = simplify_graph(formula->dep_graph, state);  // If the graph is simplified, then state will be modified

    if (simplified_graph == nullptr) return {formula, state};

    auto new_stateful_formula = convert_graph_into_tmp_formula(*simplified_graph, pool.allocator, state);
    const auto& [formula_ptr, was_formula_new] = pool.store_formula_with_info(new_stateful_formula.formula);
    if (was_formula_new) {
        // The formula that was inserted has pointers referring to the temporary storage
        // that will be used in the future so that the formula coefficients might get
        // overwritten with something else. We have to replace the formula pointers
        // with the ones pointing to a commited memory.
        Formula commited_formula = pool.allocator.commit_tmp_space();
        // We are only changing pointers to point to a different memory with the exact same contents.
        // Since we are hashing the pointer contents and not pointers, temporary dropping const should be ok.
        Formula* modif_formula_ptr = const_cast<Formula*>(formula_ptr);
        modif_formula_ptr->congruences.items = commited_formula.congruences.items;
        modif_formula_ptr->equations.items   = commited_formula.equations.items;
        modif_formula_ptr->inequations.items = commited_formula.inequations.items;

        modif_formula_ptr->dep_graph = build_dep_graph(*modif_formula_ptr);
    } else {
       pool.allocator.drop_tmp();
    }

    // @Optimize: Reuse the simplified graph instead of deleting it?
    delete simplified_graph;  // The new formula has a new graph built for it; this one is not reused

    return {formula_ptr, new_stateful_formula.state};
#endif
}
*/


void add_var_coef_term(std::stringstream& dest, u64 var, s64 coef) {
    switch (coef) {
        case 1:
            dest << "x" << var;
            break;
        case -1:
            dest << "(- x" << var << ")";
            break;
        default:
            dest << "(* " << coef << " x" << var << ")";
    }
}

optional<list<Conjunction_State>::iterator> find_pareto_optimal_position(std::list<Conjunction_State>& queue, const u64 ineq_offset, Conjunction_State& state) {
    bool should_be_inserted    = true;
    bool insert_position_found = false;

    auto bucket_iter = queue.begin();
    list<Conjunction_State>::iterator insert_position;
    while (bucket_iter != queue.end()) {
        auto& other_state = *bucket_iter;

        // Compute pareto optimality
        bool is_smaller = false; // successor <= other_successor at some fragment of the state
        bool is_larger  = false; // successor >= other_successor at some fragment of the state
        bool is_other_smaller_than_inserted = true;

        for (u64 state_fragment_i = 0u; state_fragment_i < state.constants.size(); state_fragment_i++) {
            if (state.constants[state_fragment_i] < other_state.constants[state_fragment_i]) {
                is_smaller = true; // The successor is subsumed at the current field
                is_other_smaller_than_inserted = false;
            }
            else if (state.constants[state_fragment_i] > other_state.constants[state_fragment_i]) {
                is_larger = true;
            }
        }

        // We use the insert_position to track a correct place to put the element in so that the bucket
        // is kept in sorted order. This does not affect the time complexity of the pareto optimality
        // but we have a canonical representation of the macrostate.
        if (!is_other_smaller_than_inserted && !insert_position_found) {
            // @Note: The usage of the insert_position iterator should not get invalidated future list erasures, because
            //        the iterator points to a state that is lexicographically larger than the inserted state. As the state
            //        is larger, it cannot be that it is simulated by the inserted - either it is larger in some plain constant,
            //        or larger in some inequation -> no simulation.
            insert_position = bucket_iter;
            insert_position_found = true;
        }

        if (is_larger && is_smaller) { // Incomparable
            ++bucket_iter;
            continue;
        }
        else if (is_larger) {
            queue.erase(bucket_iter++);
        }
        else {
            // Either the inserted atom is smaller (is_smaller = true), or they are the same (is_smaller = is_larger = false)
            should_be_inserted = false;
            break;
        }
    }

    if (should_be_inserted) {
        if (!insert_position_found) insert_position = queue.end();

        return std::make_optional(insert_position);
    }
    return std::nullopt;
}

void insert_into_post_if_valuable2(Intermediate_Macrostate& post, const Formula* formula, Conjunction_State& successor) {
    Prefix_Table& formula_bucket = post.formulae[formula];

    u64 prefix_size = formula->congruences.size + formula->equations.size;
    vector<s64> prefix(prefix_size);
    for (u64 i = 0; i < prefix_size; i++) {
        prefix[i] = successor.constants[i];
    }

    // @Optimize: Currently we are storing the entire state (including congruence and equation data)
    //            which is redundant since we already have this information in post.

    list<Conjunction_State>& prefix_bucket = formula_bucket[prefix];
    auto insert_post = find_pareto_optimal_position(prefix_bucket, prefix_size, successor);
    if (insert_post.has_value()) {
        prefix_bucket.insert(insert_post.value(), successor);
    }
}

Finalized_Macrostate finalize_macrostate(Formula_Allocator& alloc, Intermediate_Macrostate& intermediate_macrostate) {
    // Finalize the intermediate macrostate into a final form that is canonical (atoms are sorted)
    auto comparator = [](const Conjunction_State& left, const Conjunction_State& right) {
        // Is left < right ?
        for (u64 i = 0; i < left.constants.size(); i++) {
            if (left.constants[i] > right.constants[i]) return false;
            else if (left.constants[i] < right.constants[i]) return true;
        }
        return false;
    };

    // formulae is a map, and therefore, the formula should  be kept in sorted order,
    // no need to sort them right now.
    Sized_Array<Macrostate_Header_Elem> headers = alloc.alloc_macrostate_headers(intermediate_macrostate.formulae.size());
    s64 header_idx = 0;
    s64 max_states_per_formula = 0;
    s64 required_constant_count = 0;
    for (const auto& [formula, prefix_table]: intermediate_macrostate.formulae) {
        headers.items[header_idx].formula   = formula;

        u64 state_count = 0;
        for (auto& [prefix, states_with_prefix]: prefix_table) state_count += states_with_prefix.size();
        headers.items[header_idx].state_cnt = state_count;

        max_states_per_formula = prefix_table.size() > max_states_per_formula ? prefix_table.size() : max_states_per_formula;

        header_idx += 1;
    }

    vector<Conjunction_State> sort_space; // This can be reused by an allocator that caches the space pointer and does a malloc only if the current size < request
    sort_space.reserve(max_states_per_formula);

    // Count how many s64's will have to be in the allocated block
    for (auto& [formula, prefix_table]: intermediate_macrostate.formulae) {
        u64 states_with_this_formula = 0; // How many states are there in the prefix table
        for (auto& [prefix, prefix_entries]: prefix_table) {
            states_with_this_formula += prefix_entries.size();
        }
        required_constant_count += states_with_this_formula * formula->atom_count();
    }

    Sized_Array<s64> macrostate_data = alloc.alloc_macrostate_data(required_constant_count);
    s64 macrostate_data_next_free_slot = 0;

    for (auto& [formula, prefix_table]: intermediate_macrostate.formulae) {
        sort_space.clear();

        for (auto& [prefix, prefix_entries]: prefix_table) {
            for (auto& state: prefix_entries) {
                sort_space.push_back(state);
            }
        }
        std::sort(sort_space.begin(), sort_space.end(), comparator);

        for (const auto& state: sort_space) {
            // Memcpy
            for (const auto& constant: state.constants) {
                macrostate_data.items[macrostate_data_next_free_slot] = constant;
                macrostate_data_next_free_slot += 1;
            }
        }
    }

    return {.header = headers, .state_data = macrostate_data, .is_accepting = intermediate_macrostate.is_accepting};
}

Finalized_Macrostate make_trivial_macrostate(Formula_Pool& pool, bool polarity) {
    Formula formula(polarity);
    auto formula_ptr = pool.store_formula(formula);

    Finalized_Macrostate macrostate = {
        .header = {nullptr, 0},
        .state_data = {nullptr, 0},
        .is_accepting = polarity,
    };
    return macrostate;
}


vector<s64> extract_prefix(const Formula* formula, const vector<s64>& state) {
    u64 prefix_size = formula->congruences.size + formula->equations.size;
    vector<s64> prefix(prefix_size);
    for (u64 i = 0; i < prefix_size; i++) {
        prefix[i] = state[i];
    }
    return prefix;
}

const Quantified_Atom_Conjunction* convert_graph_and_commit_if_unique(
    Dep_Graph* graph,
    Formula_Pool* pool,
    Conjunction_State* state)
{
    Formula_Structure structure = describe_formula(graph);

    // @Optimize: This is inefficient, maybe it would be better if the ritch conjunction
    //            state had just a pointer to where the data is?
    Ritch_Conjunction_State ritch_state = {.data = state->constants, .formula_structure = structure};

    auto new_stateful_formula = convert_graph_into_tmp_formula(*graph, pool->allocator, ritch_state);
    const auto& [formula_ptr, was_formula_new] = pool->store_formula_with_info(new_stateful_formula.formula);
    if (was_formula_new) {
        // The formula that was inserted has pointers referring to the temporary
        // storage We have to replace the formula pointers with the ones
        // pointing to a commited memory.
        Formula commited_formula = pool->allocator.commit_tmp_space();

        // We are only changing pointers to point to a different memory with the
        // exact same contents. Since we are hashing the pointer contents and
        // not pointers, temporary dropping const should be ok.
        Formula* modif_formula_ptr = const_cast<Formula*>(formula_ptr);
        modif_formula_ptr->congruences.items = commited_formula.congruences.items;
        modif_formula_ptr->equations.items   = commited_formula.equations.items;
        modif_formula_ptr->inequations.items = commited_formula.inequations.items;

        modif_formula_ptr->dep_graph = build_dep_graph(*modif_formula_ptr);
    } else {
       pool->allocator.drop_tmp();
    }

    // Conversion into a temporary formula filtered out state items that belonged to satisfied atoms
    *state = new_stateful_formula.state;

    return formula_ptr;
}


void explore_macrostate(NFA& constructed_nfa,
                        Finalized_Macrostate& macrostate,
                        Alphabet_Iterator& alphabet_iter,
                        Lazy_Construction_State& constr_state)
{
    alphabet_iter.reset();

    while (!alphabet_iter.finished) {
        Intermediate_Macrostate post;
        bool is_accepting = false;

        u64 transition_symbol = alphabet_iter.init_quantif();  // The quantified bits will be masked away, so it is sufficient to take the first one

        bool is_post_top = false;
        bool dbg_was_rewritten = false;
        for (u64 symbol = transition_symbol; alphabet_iter.has_more_quantif_symbols; symbol = alphabet_iter.next_symbol()) {
#if DEBUG_RUNTIME
            auto start = std::chrono::system_clock::now();
#endif
            s64 state_data_read_idx = 0;
            for (auto& macrostate_header: macrostate.header) {
                const Formula* const formula = macrostate_header.formula;
                for (s64 formula_state_idx = 0; formula_state_idx < macrostate_header.state_cnt; formula_state_idx++) {
                    s64* current_origin_state_data = macrostate.state_data.items + state_data_read_idx;
                    state_data_read_idx += formula->atom_count();

                    auto maybe_successor = compute_successor(constr_state.formula_pool, formula, current_origin_state_data, symbol);

                    if (!maybe_successor.has_value()) continue;

                    auto successor = maybe_successor.value();

                    bool contradicts = detect_contradictions(&successor.formula->dep_graph, &successor.state);
                    if (contradicts) {
                        continue;
                    }

                    // The old formula needs to be used to determine whether the post is accepting
                    post.is_accepting |= accepts_last_symbol(formula, current_origin_state_data, symbol);
                    auto post_formula = successor.formula;

                    if (post_formula->is_top()) {
                        is_post_top = true;
                        break;
                    }

                    if (post_formula->is_bottom()) continue;

                    // Check whether the state is of any value
                    Prefix_Table& formula_buckets = post.formulae[post_formula];
                    vector<s64> prefix = extract_prefix(post_formula, successor.state.constants);
                    auto& bucket = formula_buckets[prefix];
                    u64 prefix_size = post_formula->equations.size + post_formula->congruences.size;

                    auto insert_pos = find_pareto_optimal_position(bucket, prefix_size, successor.state);
                    if (!insert_pos.has_value()) continue;

                    // It is valuable, try rewriting the post formula
                    Dep_Graph* work_graph = const_cast<Dep_Graph*> (&post_formula->dep_graph);
                    bool was_rewritten = perform_watched_rewrites(&work_graph, &successor.state);
                    if (!was_rewritten) {
                        bucket.insert(insert_pos.value(), successor.state);
                        continue;
                    }

                    if (work_graph->is_false) {
                        continue;
                    }

                    // Store the formula if we have not seen it before
                    post_formula = convert_graph_and_commit_if_unique(work_graph, &constr_state.formula_pool, &successor.state);
                    insert_into_post_if_valuable2(post, post_formula, successor.state);
                    dbg_was_rewritten = true;
                    delete work_graph;
                }

                if (is_post_top) break;
            }

#if DEBUG_RUNTIME
            auto end = std::chrono::system_clock::now();
            std::chrono::duration<double> elapsed_seconds = end - start;
            std::cout << "Number of formulae: " << macrostate.formulae.size()
                      << "; insertion took: " << elapsed_seconds.count() << " seconds." << std::endl;
#endif
        }
        if (post.formulae.empty()) {
            constr_state.is_trap_state_needed = true;
            constructed_nfa.add_transition(macrostate.handle, constr_state.trap_state_handle, transition_symbol, alphabet_iter.quantified_bits_mask);
            continue;
        };

        if (is_post_top) {
            constr_state.is_trap_state_needed = true;
            constructed_nfa.add_transition(macrostate.handle, constr_state.trap_state_handle, transition_symbol, alphabet_iter.quantified_bits_mask);
            continue;
        }

        Finalized_Macrostate finalized_post = finalize_macrostate(constr_state.formula_pool.allocator, post);

        if (dbg_was_rewritten) {
            // std::cout << finalized_post << std::endl;
        }

        // Assign a unique integer to every state
        finalized_post.handle = constr_state.known_macrostates.size();
        auto [element_iter, was_inserted] = constr_state.known_macrostates.emplace(finalized_post, finalized_post.handle);
        if (was_inserted) {
            // @Simplicity: Maybe the known_macrostates should be a set instead of a map since we are storing the handle
            //              inside the macrostate either way.
            constr_state.output_queue.push_back(finalized_post);

            if (post.is_accepting) { // Do the hash-query only if we see the macrostate for the first time
                constr_state.accepting_macrostates.emplace(finalized_post.handle);
            }
        } else {
            finalized_post.handle = element_iter->second;  // Use the already existing handle
        }

        constructed_nfa.add_transition(macrostate.handle, finalized_post.handle, transition_symbol, alphabet_iter.quantified_bits_mask);
    }
}

// @Cleanup: Figure out where should we put this
void init_mtbdd_libs() {
    int n_workers = 1;
    size_t dequeue_size = 10000000;

    lace_init(n_workers, dequeue_size);
    const size_t stack_size = 1LL << 20;
    lace_startup(0, NULL, NULL);
    sylvan::sylvan_set_limits(512*1024ll*1024ll, 10, 10);
    sylvan::sylvan_init_package();
    sylvan::sylvan_init_mtbdd();


    g_solver_context = new Solver_Context();
    Bit_Set_Leaf::init_bit_set_leaf(&g_solver_context->leaf_id_store);
    Set_Leaf::init_set_leaf(&g_solver_context->leaf_id_store);

    init_tfa_leaves();
}


// @Cleanup: Move this into base.cpp

char convert_cube_bit_to_char(u8 cube_bit) {
    switch (cube_bit) {
        case 0:
            return '0';
        case 1:
            return '1';
        default:
            return '*';
    }
}


void show_transitions_from_state(std::stringstream& output, const NFA& nfa, State origin, sylvan::MTBDD mtbdd) {
    u8 symbol[nfa.var_count];

    sylvan::MTBDD leaf = sylvan::mtbdd_enum_first(mtbdd, nfa.vars, symbol, NULL);
    while (leaf != sylvan::mtbdd_false) {
        output << origin << " (" << convert_cube_bit_to_char(symbol[0]);
        for (u64 symbol_i = 1; symbol_i < nfa.var_count; symbol_i++) {
            output << ", " << convert_cube_bit_to_char(symbol[symbol_i]);
        }
        output << ") ";

        auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(sylvan::mtbdd_getvalue(leaf));

        if (leaf_contents->destination_set.empty()) {
            output << "{}";
            continue;
        }

        auto contents_iter = leaf_contents->destination_set.begin();
        output << "{" << *contents_iter;
        ++contents_iter;
        for (; contents_iter != leaf_contents->destination_set.end(); ++contents_iter) {
            output << ", " << *contents_iter;
        }
        output << "}";

 	    leaf = sylvan::mtbdd_enum_next(mtbdd, nfa.vars, symbol, NULL);
        if (leaf != sylvan::mtbdd_false) output << "\n";
    }
}

std::string NFA::show_transitions() const {
    std::stringstream str_builder;

    if (transitions.empty()) {
        return "{}\n";
    }

    std::cout << "Number of states: " << transitions.size() << std::endl;
    for (auto& [origin_state, mtbdd]: this->transitions) {
        show_transitions_from_state(str_builder, *this, origin_state, mtbdd);
        str_builder << std::endl;
    }

    return str_builder.str();
}

NFA make_trivial_rejecting_nfa(sylvan::BDDSET vars, u64 var_count) {
    auto nfa = NFA(vars, var_count, {0}, {}, {0});
    nfa.add_transition(0, 0, 0, static_cast<u64>(-1));
    return nfa;
}

#if 0
bool does_variable_allow_inf_projection(const Dep_Graph& graph, u64 var, bool positive_inf, u64 ignored_atom) {
    auto& node = graph.var_nodes[var];
    bool inf_projection_possible = true;

    if (positive_inf) {
        for (u64 lin_atom_idx: node.upper_bounds) {
            if (lin_atom_idx == ignored_atom) continue;
            inf_projection_possible = false;
            break;
        }
    } else {
        for (u64 lin_atom_idx: node.lower_bounds) {
            if (lin_atom_idx == ignored_atom) continue;
            inf_projection_possible = false;
            break;
        }
    }

    return inf_projection_possible;
}


bool can_var_affect_free_variable_via_equations(const Dep_Graph& graph, u64 var) {
    auto& var_node = graph.var_nodes[var];

    u64 eq_count = 0;
    for (auto& bound_i: var_node.lower_bounds) {
        auto& node = graph.linear_nodes[bound_i];
        eq_count += (node.type == Linear_Node_Type::EQ);
    }

    // @Incomplete: This is underapproximation. Generally, we can be dealing with multiple equations
    //              that all contain free variables and none of these can change the value of a free variable.

    // @Incomplete: We need a notion of "almost" equation - (a.x <= K1 && and a.x => K2) - these
    //              would break the logic implemented here.
    return eq_count > 1;
};


struct Linear_Term {
    u64 var;
    s64 coef;
};

struct Inf_Projection_Info {
    bool can_be_inf = false;
    bool has_granularity_1 = false;
};

Inf_Projection_Info can_eq_side_be_inf_with_granularity(const Dep_Graph& graph, vector<Linear_Term>& eq_side, bool positive_inf, u64 eq_idx) {
    Inf_Projection_Info projection_info;

    for (auto& term: eq_side) {
        bool can_be_inf = does_variable_allow_inf_projection(graph, term.var, positive_inf, eq_idx);
        if (!can_be_inf) continue;

        auto& var_node = graph.var_nodes[term.var];
        bool is_granularity_1 = var_node.congruences.empty() && abs(term.coef) == 1;

        projection_info.can_be_inf = true;
        projection_info.has_granularity_1 |= is_granularity_1;
    }
    return projection_info;
}

Stateful_Formula_Ptr perform_inf_projection(const Dep_Graph& graph, Formula_Pool& pool, Conjunction_State& state, u64 eq_idx) {
    auto& eq = graph.linear_nodes[eq_idx];
    Dep_Graph graph_copy(graph);

    for (u64 var: eq.vars) {
        auto& var_node = graph.var_nodes[var];
        for (u64 var_atom_idx: var_node.lower_bounds) {
            auto& atom_node = graph_copy.linear_nodes[var_atom_idx];
            atom_node.is_satisfied = true;
        }
        for (u64 var_atom_idx: var_node.upper_bounds) {
            auto& atom_node = graph_copy.linear_nodes[var_atom_idx];
            atom_node.is_satisfied = true;
        }
    }

    Stateful_Formula formula_with_state = convert_graph_into_persistent_formula(graph_copy, pool.allocator, state);
    auto formula_ptr = pool.store_formula(formula_with_state.formula);
    return {.state = formula_with_state.state, .formula = formula_ptr};
}

Stateful_Formula_Ptr try_inf_projection_on_equations(const Dep_Graph& graph, Formula_Pool& pool, Conjunction_State state) {
    // For now limit to only one equation that cannot influence (via equations) free variables
    Linear_Node* target_equation = nullptr;

    vector<Linear_Term> lhs, rhs;
    lhs.reserve(graph.var_nodes.size());
    rhs.reserve(graph.var_nodes.size());

    for (s64 lin_atom_idx = 0; lin_atom_idx < graph.linear_nodes.size(); lin_atom_idx++) {
        auto& node = graph.linear_nodes[lin_atom_idx];
        if (node.type != Linear_Node_Type::EQ) break;

        bool all_vars_quantified = true;
        for (u64 var: node.vars) {
            if (!vector_contains(graph.quantified_vars, var)) {
                all_vars_quantified = false;
                break;
            }
        }

        if (!all_vars_quantified) continue;

        bool would_inf_projection_cause_problems = false;
        for (u64 var: node.vars) {
            would_inf_projection_cause_problems = can_var_affect_free_variable_via_equations(graph, var);
            if (would_inf_projection_cause_problems) break;
        }

        if (would_inf_projection_cause_problems) continue;

        for (s64 term_i = 0; term_i < node.vars.size(); term_i++) {
            u64 var = node.vars[term_i];
            s64 coef = node.coefs[var];
            if (coef < 0) rhs.push_back({.var = var, .coef = -coef});
            else lhs.push_back({.var = var, .coef = coef});
        }


        {   // Try +\inf projection
            auto lhs_proj_info = can_eq_side_be_inf_with_granularity(graph, lhs, true, lin_atom_idx);
            auto rhs_proj_info = can_eq_side_be_inf_with_granularity(graph, rhs, true, lin_atom_idx);

            bool do_inf_projection = false;
            if (lhs_proj_info.can_be_inf && rhs_proj_info.can_be_inf) {
                do_inf_projection = (lhs_proj_info.has_granularity_1 || rhs_proj_info.has_granularity_1);
            }

            if (do_inf_projection) {
                return perform_inf_projection(graph, pool, state, lin_atom_idx);
            }
        }

        {   // Try -\inf projection
            auto lhs_proj_info = can_eq_side_be_inf_with_granularity(graph, lhs, false, lin_atom_idx);
            auto rhs_proj_info = can_eq_side_be_inf_with_granularity(graph, rhs, false, lin_atom_idx);

            bool do_inf_projection = false;
            if (lhs_proj_info.can_be_inf && rhs_proj_info.can_be_inf) {
                do_inf_projection = (lhs_proj_info.has_granularity_1 || rhs_proj_info.has_granularity_1);
            }

            if (do_inf_projection) {
                return perform_inf_projection(graph, pool, state, lin_atom_idx);
            }
        }
    }
    return {.state = state, .formula = nullptr};
}
#endif


Formula_Structure describe_formula(const Formula* formula) {
    return {
        .eq_cnt   = static_cast<s32>(formula->equations.size),
        .ineq_cnt = static_cast<s32>(formula->inequations.size),
        .congruence_cnt = static_cast<s32>(formula->congruences.size),
    };
}

Formula_Structure describe_formula(const Dep_Graph* graph) {
    return {
        .eq_cnt         = static_cast<s32>(graph->equations.size()),
        .ineq_cnt       = static_cast<s32>(graph->inequations.size()),
        .congruence_cnt = static_cast<s32>(graph->congruences.size()),
    };
}


NFA build_nfa_with_formula_entailement(const Formula* formula, Conjunction_State& init_state, sylvan::BDDSET bdd_vars, Formula_Pool& formula_pool) {
    vector<Finalized_Macrostate> work_queue;
    Lazy_Construction_State constr_state = {.formula_pool = formula_pool, .output_queue = work_queue};

    // Prepare a trapstate in case it is needed
    {
        auto trapstate = make_trivial_macrostate(formula_pool, false);
        auto [container_pos, was_insterted] = constr_state.known_macrostates.emplace(trapstate, constr_state.known_macrostates.size());
        constr_state.trap_state_handle = container_pos->second;
    }

    // Prepare TRUE state
    {
        auto topstate = make_trivial_macrostate(formula_pool, true);
        auto [container_pos, was_insterted] = constr_state.known_macrostates.emplace(topstate, constr_state.known_macrostates.size());
        constr_state.topstate_handle = container_pos->second;
    }

    // Try to simplify the formula as much as possible
    {
        Dep_Graph* graph_to_rewrite = const_cast<Dep_Graph*>(&formula->dep_graph);
        PRINT_DEBUG("Initial simplification of:" << *formula);
        PRINT_DEBUG(" -> State:" << init_state.constants);
        Ritch_Conjunction_State state = {.data = init_state.constants, .formula_structure = describe_formula(formula)};
        bool was_anything_rewritten = perform_max_simplification_on_graph(&graph_to_rewrite, &state);
        if (was_anything_rewritten) {
            if (graph_to_rewrite->is_false) {
                return make_trivial_rejecting_nfa(bdd_vars, formula->var_count);
            }
            auto formula_state_pair = convert_graph_into_persistent_formula(*graph_to_rewrite, formula_pool.allocator, state);
            init_state = formula_state_pair.state;

            // If an quantifier has been instantiated, it still means that we need to iterate
            // over the entire alphabet that includes the removed variable. This is because of
            // how we explore_macrostate - we iterate over a fixed alphabet. We would have to
            // construct a new alphabet iterator for the remaining variables, which is problematic
            // if one macrostate formula still has the original variable that was removed in the other
            // parts
            formula_state_pair.formula.bound_vars = formula->bound_vars;

            formula    = formula_pool.store_formula(formula_state_pair.formula);
            delete graph_to_rewrite;
        }
        PRINT_DEBUG("Result:" << *formula);
    }

    if (formula->is_bottom()) {
        return make_trivial_rejecting_nfa(bdd_vars, formula->var_count);
    }

    if (formula->is_top()) {
        State init_state = 0;
        State acc_state  = 1;
        NFA nfa(bdd_vars, formula->var_count, {init_state, acc_state}, {acc_state}, {init_state});
        nfa.add_transition(init_state, acc_state, 0u, static_cast<u64>(-1));
        nfa.add_transition(acc_state, acc_state, 0u, static_cast<u64>(-1));
        return nfa;
    }

    // Populate the queue with the initial states
    const u64 init_state_handle = constr_state.known_macrostates.size();
    {
        Sized_Array<Macrostate_Header_Elem> header = formula_pool.allocator.alloc_macrostate_headers(1);
        header.items[0].formula = formula;
        header.items[0].state_cnt = 1;

        Sized_Array<s64> macrostate_data = formula_pool.allocator.alloc_macrostate_data(formula->atom_count());
        for (s64 state_constant_idx = 0; state_constant_idx < init_state.constants.size(); state_constant_idx++) {
            macrostate_data.items[state_constant_idx]  = init_state.constants[state_constant_idx];
        }

        Finalized_Macrostate init_macrostate = {
            .header = header,
            .state_data = macrostate_data,
            .is_accepting = false,
            .handle = init_state_handle,
        };
        work_queue.push_back(init_macrostate);

        auto [container_pos, was_inserted] = constr_state.known_macrostates.emplace(init_macrostate, constr_state.known_macrostates.size());
    }


    NFA nfa(bdd_vars, formula->var_count, {}, {}, {static_cast<State>(init_state_handle)});

    Alphabet_Iterator alphabet_iter = Alphabet_Iterator(formula->var_count, formula->bound_vars);
    PRINT_DEBUG("The following vars are quantified: " << formula->bound_vars);
    PRINT_DEBUG("Using the following mask: " << std::bitset<8>(alphabet_iter.quantified_bits_mask));

    u64 processed = 0;
    u64 processed_batch = 0;
    while (!work_queue.empty()) {
        auto macrostate = work_queue.back();
        work_queue.pop_back();

        PRINT_DEBUG("Proccessing" << macrostate << " (Queue size " << work_queue.size() << ')');

        nfa.states.insert(macrostate.handle);
        if (macrostate.is_accepting) {
            nfa.final_states.insert(macrostate.handle);
        }

        explore_macrostate(nfa, macrostate, alphabet_iter, constr_state);

        processed       += 1;
        processed_batch += 1;
        if (processed_batch >= 2000) {
            PRINTF_DEBUG("Processed %lu states\n", processed);
            processed_batch = 0;
        }
    }

    const u64 all_bits_dont_care_mask = static_cast<u64>(-1);
    if (constr_state.is_trap_state_needed) {
        nfa.states.insert(constr_state.trap_state_handle);
        nfa.add_transition(constr_state.trap_state_handle, constr_state.trap_state_handle, 0u, all_bits_dont_care_mask);
    }

    if (constr_state.is_top_state_needed) {
        nfa.states.insert(constr_state.topstate_handle);
        nfa.add_transition(constr_state.topstate_handle, constr_state.topstate_handle, 0u, all_bits_dont_care_mask);
    }

    PRINTF_DEBUG("The constructed NFA has %lu states\n", nfa.states.size());
    PRINT_DEBUG("States: " << nfa.states);
    PRINT_DEBUG("Initial states: " << nfa.initial_states);
    PRINT_DEBUG("Final states: " << nfa.final_states);

    for (auto& [macrostate, handle]: constr_state.known_macrostates) {
        PRINT_DEBUG(handle << "::" << macrostate);
        PRINT_DEBUG(handle << "::" << macrostate);
    }

    if (!formula->bound_vars.empty()) {
        if (g_solver_context->config.is_feature_enabled(SOLVER_CONFIG_USE_BIT_SETS)) {
            std::cout << "Using bit sets!\n";
            NFA result = do_pad_closure_using_bit_sets(&nfa, g_solver_context->bit_set_alloc);
            return determinize_nfa(result);
        }
        // Use the old implementation
        nfa.perform_pad_closure();
        return determinize_nfa(nfa);
    }

    return nfa;
}


const Quantified_Atom_Conjunction* Formula_Pool::store_formula(const Quantified_Atom_Conjunction& formula) {
    auto [it, did_insertion_happen] = formulae.emplace(formula);
    const Quantified_Atom_Conjunction* stored_formula_ptr = &(*it);
    return &(*it);
}

pair<const Formula*, bool> Formula_Pool::store_formula_with_info(Quantified_Atom_Conjunction& formula) {
    auto [it, did_insertion_happen] = formulae.emplace(formula);
    const Quantified_Atom_Conjunction* stored_formula_ptr = &(*it);
    return {&(*it), did_insertion_happen};
}

template<typename InputIt>
std::string fmt_coef_var_sum(InputIt coef_first, InputIt coef_end) {
    std::stringstream builder;

    u64 i = 0;
    for (; coef_first != coef_end; ++coef_first) {
        s64 coef  = *coef_first;

        if (coef == 0) {
            i += 1;
            continue;
        }

        char sign = coef >= 0 ? '+' : '-';
        if (i > 0) {
            builder << ' ' << sign << ' ';
            coef = abs(coef);
        }
        builder << coef << "*x" << i;
        i += 1;
    }

    return builder.str();
}

std::ostream& operator<<(std::ostream& output, const Linear_Node& lin_node) {
    output << fmt_coef_var_sum(lin_node.coefs.begin(), lin_node.coefs.end());
    // const char* log_symbol = lin_node.type == Linear_Node_Type::EQ ? " = ?" : " <= ?";
    // output << log_symbol;
    return output;
}

std::ostream& operator<<(std::ostream& output, const Congruence_Node& congruence_node) {
    s64 modulus = combine_moduli(congruence_node.modulus_2pow, congruence_node.modulus_odd);
    output << fmt_coef_var_sum(congruence_node.coefs.begin(), congruence_node.coefs.end());
    output << " ~ ? (mod " << modulus << ")";
    return output;
}

std::ostream& operator<<(std::ostream& output, const map<const Quantified_Atom_Conjunction*, Prefix_Table>& macrostate) {
    if (macrostate.empty()) {
        output << "{}";
        return output;
    }

    u64 row_cnt = 0;
    output << "{\n";
    for (auto& [formula_ptr, prefix_table]: macrostate) {
        output << "  " << formula_ptr << " :: ";

        for (auto& [prefix, states]: prefix_table) {
            for (auto& state: states) output << state << ", ";
        }

        if (row_cnt < macrostate.size()) output << "\n";
        row_cnt += 1;
    }
    output << "}";
    return output;

}
std::ostream& operator<<(std::ostream& output, const Congruence& congruence) {
    output << fmt_coef_var_sum(congruence.coefs.begin(), congruence.coefs.end())
           << " ~= (mod "
           << combine_moduli(congruence.modulus_2pow, congruence.modulus_odd) << ")";
    return output;
}

std::ostream& operator<<(std::ostream& output, const Equation& equation) {
    output << fmt_coef_var_sum(equation.coefs.begin(), equation.coefs.end()) << " = ?";
    return output;
}

std::ostream& operator<<(std::ostream& output, const Inequation& equation) {
    output << fmt_coef_var_sum(equation.coefs.begin(), equation.coefs.end()) << " <= ?";
    return output;
}

template <typename Atom_Type>
void write_atoms(std::ostream& output, const Sized_Array<Atom_Type>& atoms) {
    for (u64 atom_idx = 0; atom_idx < atoms.size; atom_idx++) {
        if (atom_idx > 0) {
            output << " && ";
        }
        Atom_Type& atom = atoms.items[atom_idx];
        output << "(" << atom << ")";
    }
}

std::ostream& operator<<(std::ostream& output, const Quantified_Atom_Conjunction& formula) {
    if (!formula.has_atoms()) {
        const char* formula_str = formula.is_top() ? "(TRUE)" : "(FALSE)";
        output << formula_str;
        return output;
    }

    output << "(";
    if (!formula.bound_vars.empty()) {
        output << "exists (";
        auto quantified_vars_iter = formula.bound_vars.begin();
        output << "x" << *quantified_vars_iter;
        ++quantified_vars_iter;
        for (; quantified_vars_iter != formula.bound_vars.end(); ++quantified_vars_iter)
            output << ", " << "x" << *quantified_vars_iter;
        output << ")";
    }

    write_atoms(output, formula.congruences);
    bool wrote_atoms = formula.congruences.size > 0;

    if (wrote_atoms) output << " && ";
    write_atoms(output, formula.equations);
    wrote_atoms = formula.equations.size > 0;

    if (wrote_atoms) output << " && ";
    write_atoms(output, formula.inequations);

    output << ")";
    return output;
}


#if 0
bool do_any_hard_bounds_imply_contradiction(const Dep_Graph& graph, const Conjunction_State& state) {
    for (u64 var = 0; var < graph.var_nodes.size(); var++) {
        auto& var_node = graph.var_nodes[var];
        if (!var_node.has_hard_lower_bound() || !var_node.has_hard_upper_bound()) continue;

        s64 raw_upper_bound_val = state.get_lin_atom_val(graph.congruence_nodes.size(), var_node.hard_upper_bound.atom_i);
        s64 raw_lower_bound_val = state.get_lin_atom_val(graph.congruence_nodes.size(), var_node.hard_lower_bound.atom_i);

        auto& upper_bound = graph.linear_nodes[var_node.hard_upper_bound.atom_i];
        auto& lower_bound = graph.linear_nodes[var_node.hard_lower_bound.atom_i];

        s64 upper_bound_val = div_bound_by_coef(raw_upper_bound_val, upper_bound.coefs[var]);
        s64 lower_bound_val = div_bound_by_coef(raw_lower_bound_val, lower_bound.coefs[var]);

        if (upper_bound_val < lower_bound_val) {
            PRINTF_DEBUG("The hard bounds for variable x%lu imply contradiction. Lower bound = %ld, upper bound %ld\n", var, lower_bound_val, upper_bound_val);
            return true;
        }
    }
    return false;
}
#endif

Atom::Atom(const vector<u64>& vars, const vector<s64>& coefs) {
    this->vars = vars;
    this->coefs = coefs;

    var_set = sylvan::mtbdd_set_empty();
    sylvan::mtbdd_ref(var_set);
    for (auto var: vars) {
        sylvan::BDDSET new_var_set = sylvan::mtbdd_set_add(var_set, var);
        sylvan::mtbdd_ref(new_var_set);
        sylvan::mtbdd_deref(var_set);
        var_set = new_var_set;
    }
}

s64 Atom::dot_with_symbol(u64 symbol) const {
    s64 dot = 0;
    for (s64 lin_term_idx = 0; lin_term_idx < vars.size(); lin_term_idx++) {
        s64 coef = coefs[lin_term_idx];
        u64 var  = vars[lin_term_idx];
        u64 mask = (1ull << lin_term_idx);
        dot += ((symbol & mask) > 0) * coef;
    }
    return dot;
}

template <typename Maker>
sylvan::MTBDD Atom::make_extended_post(Maker& maker, s64 rhs) {
    auto cache_entry = post_cache.find(rhs);
    if (cache_entry != post_cache.end()) return cache_entry->second;

    u64 symbol = (1ull << vars.size()) - 1; // Make lower #var.size bits 1s
    symbol = ~symbol;  // Make variable bits 0, non-variable 1

    vector<u8> ritch_symbol(this->vars.size());

    sylvan::MTBDD post = sylvan::mtbdd_false;

    for (; symbol != 0; symbol += 1) {
        post = maker.extend_post(post, ritch_symbol, rhs, symbol);
    }

    sylvan::mtbdd_ref(post);
    post_cache.insert({rhs, post});
    return post;
}

void make_rich_symbol_from_bits(vector<u8>& dest, u64 symbol, const vector<u64>& vars) {
    for (s64 var_i = 0; var_i < vars.size(); var_i++) {
        u64 mask = (1ull << var_i);
        dest[var_i] = (symbol & mask) > 0;
    }
}

sylvan::MTBDD extend_post_with_cube(
    const Atom& atom,
    sylvan::MTBDD post,
    TFA_Leaf_Contents& content,
    vector<u8>& ritch_symbol_space,
    u64 symbol)
{
    make_rich_symbol_from_bits(ritch_symbol_space, symbol, atom.vars);
    auto leaf = make_tfa_leaf(&content);
    auto cube = sylvan::mtbdd_cube(atom.var_set, ritch_symbol_space.data(), leaf);
    sylvan::MTBDD new_post = perform_tfa_mtbdd_union(post, cube);
    // sylvan::mtbdd_ref(new_post);
    // sylvan::mtbdd_deref(post);
    return new_post;
}

sylvan::MTBDD Inequation2::extend_post(
    sylvan::MTBDD current_post,
    vector<u8> ritch_symbol_space,
    s64 rhs,
    u64 symbol)
{
    s64 post = this->post(rhs, symbol);
    bool is_accepting = accepts(rhs, symbol);
    TFA_Leaf_Contents leaf_contents = {.post = post, .is_accepting = is_accepting};
    return extend_post_with_cube(*this, current_post, leaf_contents, ritch_symbol_space, symbol);
}


s64 Inequation2::post(s64 rhs, u64 symbol) const {
    const s64 dot = dot_with_symbol(symbol);
    s64 post = rhs - dot;
    s64 has_reminder = (post % 2) != 0;
    post = (post / 2) - (post < 0) * has_reminder;
    return post;
}

bool Inequation2::accepts(s64 rhs, u64 symbol) const {
    const s64 dot = dot_with_symbol(symbol);
    s64 post = rhs + dot;
    return post >= 0;
}

sylvan::MTBDD Inequation2::compute_entire_post(s64 rhs) {
    return make_extended_post(*this, rhs);
}

optional<s64> Equation2::post(s64 rhs, u64 symbol) const {
    s64 dot = dot_with_symbol(symbol);
    s64 post = rhs - dot;

    s64 has_reminder = (post % 2) != 0;
    if (has_reminder) return std::nullopt;

    post /= 2;
    return post;
}

bool Equation2::accepts(s64 rhs, u64 symbol) const {
    s64 dot = dot_with_symbol(symbol);
    s64 post = rhs + dot;
    return post == 0;
}

sylvan::MTBDD Equation2::extend_post(sylvan::MTBDD current_post,
    vector<u8> ritch_symbol_space,
    s64 rhs,
    u64 symbol)
{
    optional<s64> post = this->post(rhs, symbol);
    if (!post.has_value()) return current_post;
    bool is_accepting = accepts(rhs, symbol);
    TFA_Leaf_Contents leaf_contents = {.post = post.value(), .is_accepting = is_accepting};
    return extend_post_with_cube(*this, current_post, leaf_contents, ritch_symbol_space, symbol);
}

sylvan::MTBDD Equation2::compute_entire_post(s64 rhs) {
    return make_extended_post(*this, rhs);
}

optional<s64> Congruence2::post(s64 rhs, u64 symbol) const {
    s64 dot = dot_with_symbol(symbol);
    s64 modulus = combine_moduli(modulus_2pow, modulus_odd);
    s64 post = (rhs - dot) % modulus;
    post += modulus * (post < 0);

    if (modulus_2pow > 1) {
        if (post % 2) return std::nullopt;
        return (post / 2);
    }

    post = ((post % 2) * modulus + post) / 2;
    return post;
}

bool Congruence2::accepts(s64 rhs, u64 symbol) const {
    s64 dot = dot_with_symbol(symbol);
    s64 modulus = combine_moduli(modulus_2pow, modulus_odd);
    return ((rhs + dot) % modulus) == 0;
}

sylvan::MTBDD Congruence2::extend_post(sylvan::MTBDD current_post,
    vector<u8> ritch_symbol_space,
    s64 rhs,
    u64 symbol)
{
    optional<s64> post = this->post(rhs, symbol);
    if (!post.has_value()) {
        return current_post;
    };
    bool is_accepting = accepts(rhs, symbol);
    TFA_Leaf_Contents leaf_contents = {.post = post.value(), .is_accepting = is_accepting};
    return extend_post_with_cube(*this, current_post, leaf_contents, ritch_symbol_space, symbol);
}

sylvan::MTBDD Congruence2::compute_entire_post(s64 rhs) {
    return make_extended_post(*this, rhs);
}

template <typename Atom>
void extend_post_mtbdd_with_atoms(vector<sylvan::MTBDD>& post_to_extend, vector<Atom>& atoms, Sized_Array<s64>& state, s64& state_idx) {
    for (auto& atom: atoms) {
        s64 rhs = state.items[state_idx];
        state_idx += 1;
        sylvan::MTBDD post = atom.compute_entire_post(rhs);
        // sylvan::mtbdd_refs_push(post);
        post_to_extend.push_back(post);
    }
}

void exp_macrostate(Formula2& formula, const Macrostate2* macrostate, NFA_Construction_Ctx* ctx)
{
    vector<MTBDD> macrostate_post;
    macrostate_post.reserve(formula.atom_count());

    MTBDD exploration_result = sylvan::mtbdd_false;
    sylvan::mtbdd_ref(exploration_result);

    std::vector<s64> cache_query;
    cache_query.reserve(10);

    for (auto& macrostate_elem: *macrostate) {
        cache_query.clear();

        s64 state_idx = 0;

        extend_post_mtbdd_with_atoms(macrostate_post, formula.congruences, macrostate_elem.state, state_idx);
        extend_post_mtbdd_with_atoms(macrostate_post, formula.equations,   macrostate_elem.state, state_idx);
        extend_post_mtbdd_with_atoms(macrostate_post, formula.inequations, macrostate_elem.state, state_idx);

        MTBDD intersection_mtbdd = ctx->intersection_top;

        bool missed_cache = false;
        for (s64 i = 0; i < macrostate_elem.state.size; i++) {
            cache_query.push_back(macrostate_elem.state.items[i]);

            if (!missed_cache) {
                auto cache_pos = ctx->cache.find(cache_query);
                if (cache_pos != ctx->cache.end()) {
                    intersection_mtbdd = cache_pos->second;
                    continue;
                } else {
                    missed_cache = true;
                }
            }

            MTBDD mtbdd = macrostate_post[i];
            MTBDD new_intersection = perform_tfa_mtbdd_intersection(intersection_mtbdd, mtbdd);
            sylvan::mtbdd_ref(new_intersection);
            ctx->cache[cache_query] = new_intersection;
            intersection_mtbdd = new_intersection;
        }

        // All information is now contained in the intersection MTBDD, we can release post MTBDDs
        // sylvan::mtbdd_refs_pop(macrostate_post.size());

        MTBDD after_projection = perform_tfa_pareto_projection(intersection_mtbdd, formula.quantif_vars, &ctx->structure_info);
        sylvan::mtbdd_ref(after_projection);

        MTBDD new_exploration_result = perform_tfa_pareto_union(exploration_result, after_projection, &ctx->structure_info);
        sylvan::mtbdd_ref(new_exploration_result);
        sylvan::mtbdd_deref(after_projection);

        sylvan::mtbdd_deref(exploration_result);
        exploration_result = new_exploration_result;
        macrostate_post.clear();
    }

    MTBDD result = convert_tfa_leaves_into_macrostates(exploration_result, ctx);
    sylvan::mtbdd_ref(result);

    sylvan::mtbdd_deref(exploration_result);

    ctx->constructed_nfa->transitions[macrostate->handle] = result;
}

void show_known_states(std::unordered_map<Macrostate2, s64>& states) {
    std::cout << "Known states\n";
    for (auto& [state, handle]: states) {
        std::cout << handle << " :: " << state << std::endl;
    }
}

const Macrostate2* inject_initial_macrostate(Macrostate2& initial_macrostate, NFA_Construction_Ctx* ctx) {
    auto [pos, was_inserted] = ctx->known_states.emplace(initial_macrostate, ctx->known_states.size());
    auto result_ptr = &pos->first;
    const_cast<Macrostate2*>(result_ptr)->handle = pos->second;

    ctx->constructed_nfa->initial_states.insert(pos->second);
    ctx->macrostates_to_explore.push_back(result_ptr);

    return result_ptr;
}

void inject_trapstate(NFA_Construction_Ctx* ctx) {
    Macrostate2 trap = {
        .states = {},
        .accepting = false,
        .formula_structure = &ctx->structure_info
    };
    auto [pos, was_inserted] = ctx->known_states.emplace(trap, ctx->known_states.size());
    auto result_ptr = &pos->first;
    ctx->trapstate_handle = pos->second;
    ctx->trapstate_needed = false;

    const_cast<Macrostate2*>(result_ptr)->handle = pos->second;
}

NFA build_nfa_for_conjunction(Formula2& formula, Macrostate2& initial_macrostate) {
    sylvan::BDDSET vars = formula.get_all_vars();
    u64 var_count = sylvan::mtbdd_set_count(vars);

    NFA constructed_nfa = NFA(formula.get_all_vars(), var_count);
    NFA_Construction_Ctx ctx = {
        .known_states = {},
        .macrostates_to_explore = {},
        .macrostate_block_alloc = Block_Allocator(),
        .constructed_nfa = &constructed_nfa,
        .structure_info = {
            .prefix_size = formula.congruences.size() + formula.equations.size(),
            .post_size = formula.atom_count()
        },
        .formula = &formula,
        .cache = {},
        .intersection_top = make_tfa_intersection_top()
    };

    sylvan::mtbdd_ref(ctx.intersection_top);

    inject_trapstate(&ctx);
    inject_initial_macrostate(initial_macrostate, &ctx);

    while (!ctx.macrostates_to_explore.empty()) {
        auto macrostate = ctx.macrostates_to_explore.back();
        constructed_nfa.states.insert(macrostate->handle);
        if (macrostate->accepting) {
            constructed_nfa.mark_state_final(macrostate->handle);
        }
        ctx.macrostates_to_explore.pop_back();
        exp_macrostate(formula, macrostate, &ctx);
    }

    if (ctx.trapstate_needed) {
        constructed_nfa.states.insert(ctx.trapstate_handle);
        u8* symbol = new u8[constructed_nfa.var_count];
        for (s64 i = 0; i < constructed_nfa.var_count; i++) {
            symbol[i] = 2;
        }
        constructed_nfa.add_transition(ctx.trapstate_handle, ctx.trapstate_handle, symbol);
        delete[] symbol;
    }

    sylvan::mtbdd_deref(ctx.intersection_top);

    return constructed_nfa;
}

std::ostream& operator<<(std::ostream& output, const Macrostate2& macrostate) {
    bool written_elem = false;
    output << "Macrostate" << (macrostate.accepting ? "+" : "-") <<"{";
    for (auto& elem: macrostate) {
        if (written_elem) output << ",";
        // output << elem.formula
        //        << ": " << elem.state;
        output << elem.state;
        written_elem = true;
    }
    output << "}";
    return output;
}

Atom::~Atom() {
    sylvan::mtbdd_deref(var_set);
    for (auto& [rhs, cached_post]: post_cache) {
        if (cached_post != mtbdd_false) sylvan::mtbdd_deref(cached_post);
    }
}
