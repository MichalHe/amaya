#include "../include/lazy.hpp"
#include "../include/base.hpp"
#include "../include/rewrites.h"

#include <numeric>

struct Linear_Function { // y = a*x + b
    s64 a, b;
    bool valid = true;
};

struct Linearization_Info {
    u64              congruence_idx;
    Linear_Function  resulting_fn;
    Captured_Modulus captured_mod;
};

/**
 * Evaluate congruence of the form: m ~ <other_var_coef>*point - abs_part
 */
s64 eval_mod_congruence_at_point(s64 modulus, s64 other_var_coef, s64 abs_part, Captured_Modulus& mod, s64 point) {
    // m ~ n*y - K  (mod MODULUS)
    s64 congruence_val = ((other_var_coef * point % modulus) - abs_part) % modulus;
    return congruence_val + (congruence_val < 0) * modulus;
}

s64 get_point_for_mod_congruence_to_obtain_value(const Congruence_Node& congruence, s64 K, Captured_Modulus& mod, s64 value) {
    // n*y + u*m ~ K  (mod MODULUS)
    s64 n = congruence.coefs[mod.leading_var];
    s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);
    // Transform `n*y + u*m ~ K  (mod MODULUS)` into `y = z*u*m + K  (mod MODULUS)`
    s64 z = compute_multiplicative_inverse(modulus, n);
    assert(z != 0);
    s64 zum = ((-congruence.coefs[mod.subordinate_var] * value % modulus) * z) % modulus;
    s64 rhs = zum + (K % modulus);
    rhs += (rhs < 0) * modulus;
    return rhs;
}

void shift_interval(Interval& interval, Var_Preference preference, s64 modulus) {
    s64 shift = 0;
    if (preference.type == Var_Preference_Type::C_DECREASING) {
        shift = preference.c / modulus;
        shift += (preference.c % modulus != 0);
        shift *= modulus;
    } else {
        shift = preference.c / modulus;
        shift -= (preference.c % modulus != 0);
        shift *= modulus;
    }
    interval.high += shift;
    interval.low  += shift;
}

Var_Preference determine_var_preference(const Dep_Graph& graph, Ritch_Conjunction_State* state, u64 var) {
    const Var_Node& var_node = graph.var_nodes[var];
    u64 offset = graph.congruences.size();

    if (var_node.lower_bounds.size() == 1 && var_node.has_hard_lower_bound()) {
        s64 c = state->get_ineq_val(var_node.hard_lower_bound.atom_i);
        return {.type = Var_Preference_Type::C_DECREASING, .c = c};
    } else if (var_node.upper_bounds.size() == 1 && var_node.has_hard_upper_bound()) {
        s64 c = state->get_ineq_val(var_node.hard_upper_bound.atom_i);
        return {.type = Var_Preference_Type::C_INCREASING, .c = c};
    }

    return {.type  = Var_Preference_Type::NONE, .c = 0};
}

bool are_var_values_withing_range(
    const Dep_Graph& graph,
    Ritch_Conjunction_State* state,
    u64 var,
    s64 low,
    s64 high)
{
    if (low > high) return false;

    auto& var_node = graph.var_nodes[var];
    bool has_both_bounds = var_node.has_hard_lower_bound() && var_node.has_hard_upper_bound();
    if (!has_both_bounds) return false;

    auto& upper_bound_atom = graph.inequations[var_node.hard_upper_bound.atom_i];
    s64 upper_bound = state->get_ineq_val(var_node.hard_upper_bound.atom_i);
    upper_bound = div_bound_by_coef(upper_bound, upper_bound_atom.coefs[var]);

    auto& lower_bound_atom = graph.inequations[var_node.hard_lower_bound.atom_i];
    s64 lower_bound = state->get_ineq_val(var_node.hard_lower_bound.atom_i);
    lower_bound = div_bound_by_coef(lower_bound, lower_bound_atom.coefs[var]);

    return (low <= lower_bound && upper_bound <= high);
}

Captured_Modulus does_congruence_capture_modulus(
    const Dep_Graph& graph,
    Ritch_Conjunction_State& state,
    const Congruence_Node& congruence)
{
    if (congruence.is_satisfied)
        return {.leading_var = 0, .subordinate_var = 0};

    if (congruence.vars.size() != 2) return {.leading_var = 0, .subordinate_var = 0};

    s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);
    u64 leading_var = congruence.vars[0];
    u64 subordinate_var = congruence.vars[1];

    if (are_var_values_withing_range(graph, &state, leading_var, 0, modulus)) {
        std::swap(leading_var, subordinate_var);
    } else {
        if (!are_var_values_withing_range(graph, &state, subordinate_var, 0, modulus)) {
            // None of the vars represents a modulus
            return {.leading_var = 0, .subordinate_var = 0};
        }
    }

    return {.leading_var = leading_var, .subordinate_var = subordinate_var};
}

// Modulo linearization:
// 1) find a variable "m" that comes from modulo term:
//     .. has its value limited to an interval smaller than [0..MODULUS]
//     .. is congruent to a single variable (does not have to be free)
// 2) ensure that "m" comes from (y mod MODULUS) where y is existentially bound and c-increasing/c-decreasing
//     .. because in order to construct a linear function for m, we need to know the interval of y-values we are picking from
//        - if "y" was a free variable, some other portion of the formula actually desire opposite values as c-increasing/d-decreasing
//          and thus y values might be in different places on the number axis, and the linear function would return wrong results
//          for these different places
// 3) Identify the range of y-values needed to match all the values of m (domain of the linear function)
//     .. move the interval points to be located next to `c`, producing an interval [L, R]
//     .. check whether the interval alone (after translation) trully spans the supposed range of `m` (is there a y for which `m = n*y - K  mod M` is 0?)
//        if yes, overapproximate into [L1, R] or [L, R1] so that R - L1 = MODULUS
// 4) so far we have c-increasing formula + a congruence of the form (n*y - m ~ K mod M) - produce an equivalent linear function for the congruence:
//     .. rearange the congruence into `m = n*y - K  mod M`
//     .. check whether there is a solution to `m = n*y - K  mod M` in the [L, R] interval, if yes, abort - this would require a disjuntion - two linear functions
//     .. compute the linear function 1) compute m in `m0 = n*y - K  mod M` for L and m1 for `m = n*y - K` for L, and produce a linear function `m = n*y - K - (m1 - m1)`
// 5) return a formula with the congruence being replaced by `m = n*y - K - (m1 - m1)`
Linear_Function linearize_congruence(
    const Dep_Graph& graph,
    Ritch_Conjunction_State& state,
    u64 congruence_idx,
    Captured_Modulus& captured_mod,
    Var_Preference& preference)
{
    const Congruence_Node& congruence = graph.congruences[congruence_idx];
    Interval modulus_values;
    { // Determine the interval of the modulus
        auto& mod_var_node  = graph.var_nodes[captured_mod.subordinate_var];

        // @Fixme: This is wrong - the variable in question might have a coefficient the bound value
        //         Although we want the cofficients to be as small as possible, we cannot guarantee
        //         that this is not called after some optimization pass that did not yet divide by GCD

        u64 sub_var = captured_mod.subordinate_var;
        s64 high_bound_coef = graph.inequations[mod_var_node.hard_upper_bound.atom_i].coefs[sub_var];
        modulus_values.high = div_bound_by_coef(state.get_ineq_val(mod_var_node.hard_upper_bound.atom_i), high_bound_coef);

        s64 low_bound_coef = graph.inequations[mod_var_node.hard_lower_bound.atom_i].coefs[sub_var];
        modulus_values.low  = div_bound_by_coef(state.get_ineq_val(mod_var_node.hard_lower_bound.atom_i), low_bound_coef);
    }

    PRINT_DEBUG("Linearizing y=x" << captured_mod.leading_var <<
                " subordinate m=x" << captured_mod.subordinate_var);

    PRINT_DEBUG("The interval of the modulo variable x" << captured_mod.subordinate_var <<
                " is [" << modulus_values.low << "," << modulus_values.high << "]");

    s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);

    s64 leading_var_coef = congruence.coefs[captured_mod.leading_var];
    Interval y_values = {
        .low = 0,
        .high = modulus - 1,
    };

    s64 K = state.get_congruence_val(congruence_idx);  // n*y - m ~ K (mod MODULUS)

    if (std::abs(leading_var_coef) == 1) {
        // We can have a precise interval only when the leading var coef is 1 because other group generators might jump around the entire
        // interval as they generate the group, and the values they generate might fall outside the mod values interval
        y_values.low  = get_point_for_mod_congruence_to_obtain_value(congruence, K, captured_mod, modulus_values.low);
        y_values.high = get_point_for_mod_congruence_to_obtain_value(congruence, K, captured_mod, modulus_values.high);

        if (y_values.high - y_values.low != modulus_values.high - modulus_values.low) {
            std::swap(y_values.low, y_values.high);
            y_values.high += modulus;
        }
    }

    PRINTF_DEBUG("The range of leading var values to achieve such mod interval is [%ld, %ld]\n", y_values.low, y_values.high);

    // It might be the case that as we do modulo on intervals we obtained [L, H] that contains less values than the origial modulo interval
    if (y_values.high - y_values.low != modulus_values.high - modulus_values.low) {
       return {.valid = false};
    }

    shift_interval(y_values, preference, modulus);

    PRINTF_DEBUG("The shifted interval is [%ld, %ld]\n", y_values.low, y_values.high);

    bool crosses_zero = ((y_values.high / modulus) != (y_values.low / modulus));
    PRINT_DEBUG("Crosses zero? " << (crosses_zero ? "Yes." : "No.") << "\n");
    if (crosses_zero) {
        // @ToDo @Incomplete
        // If there is a point where at which the congruence is valued 0 and it is not one of the border points
        // then we need to do a disjunctive branching and produce two linear functions instead
        return {.valid = false};
    }

    // @Note: Implemented for the general case: n*y - u*m ~ K (mod MODULUS)
    s64 mod_var_coef = congruence.coefs[captured_mod.subordinate_var];
    s64 mod_inverse = compute_multiplicative_inverse(modulus, -mod_var_coef);
    // Transform n*y - u*m ~ K (mod MODULUS) into m ~ mod_inverse(u)*n*y - K (mod MODULUS)
    s64 linear_function_dir = (mod_inverse * leading_var_coef) % abs(modulus);
    s64 left_val = linear_function_dir * y_values.low - K;

    // m = (linear_function_dir*Y - K) -- plug in <y_values.low> for Y
    s64 left_mod_val  = eval_mod_congruence_at_point(modulus, linear_function_dir, K, captured_mod, y_values.low);

    PRINTF_DEBUG("Evaluating the congruence at %ld would yield %ld, evaluating a linear function would yield %ld\n", y_values.low, left_mod_val, left_val);

    s64 linear_offset = left_mod_val - left_val;
    PRINTF_DEBUG("The offset of the created linear function would be: %ld\n", linear_offset);

    PRINTF_DEBUG("The resulting linear function is: m = %ld*y + %ld\n", linear_function_dir, linear_offset);
    return {.a = linear_function_dir, .b = linear_offset, .valid = true};
}


Dep_Graph* ensure_writable_graph(Dep_Graph** graph) {
    Dep_Graph* current_graph = *graph;
    if (current_graph->dirty) return current_graph;

    Dep_Graph* new_graph = new Dep_Graph(*current_graph);
    new_graph->dirty = true;
    *graph = new_graph;
    return new_graph;
}


bool linearize_moduli(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state) {
    s64 linearizations_performed = 0;

    Dep_Graph* graph = *graph_ptr;

    for (u64 congruence_idx = 0; congruence_idx < graph->congruences.size();  congruence_idx++) {
        auto& congruence = graph->congruences[congruence_idx];
        if (congruence.is_satisfied) continue;

        auto captured_mod = does_congruence_capture_modulus(*graph, *state, congruence);
        if (!captured_mod.is_mod_captured()) continue;

        // Is the leading variable C-increasing/decreasing
        auto var_preference = determine_var_preference(*graph, state, captured_mod.leading_var);
        if (var_preference.type == Var_Preference_Type::NONE) continue;

        Linear_Function fn = linearize_congruence(*graph, *state, congruence_idx, captured_mod, var_preference);
        if (!fn.valid) continue;

        graph = ensure_writable_graph(graph_ptr);

        // Make sure that we use the new graph
        graph->congruences[congruence_idx].is_satisfied = true;

        // Make an equation for the linear function m = a*y + b --> -b = a*y - m
        vector<s64> lin_node_coefs;
        lin_node_coefs.resize(graph->var_nodes.size());
        lin_node_coefs[captured_mod.leading_var]     = fn.a;
        lin_node_coefs[captured_mod.subordinate_var] = -1;

        state->add_eq_rhs(-fn.b);

        vector<u64> vars = {captured_mod.leading_var, captured_mod.subordinate_var};
        if (captured_mod.leading_var > captured_mod.subordinate_var) {
            std::swap(vars[0], vars[1]);
        }

        Linear_Node node = {
            .coefs = lin_node_coefs,
            .vars = vars,
            .is_satisfied = false
        };
        s32 node_idx = graph->equations.size();
        graph->equations.push_back(node);

        graph->var_nodes[captured_mod.leading_var].equations.push_back(node_idx);
        graph->var_nodes[captured_mod.subordinate_var].equations.push_back(node_idx);

        linearizations_performed += 1;
    }

    return linearizations_performed;
}

enum class Bounds_Implication_Result : u8 {
    NONE          = 0x0,
    VALUE         = 0x1,
    CONTRADICTION = 0x2,
};

Bounds_Implication_Result get_constant_value_implied_by_bounds(const Dep_Graph& graph, u64 var, Ritch_Conjunction_State& state, s64* val) {
    auto& var_node = graph.var_nodes[var];
    if (!var_node.has_hard_lower_bound() || !var_node.has_hard_upper_bound()) {
        return Bounds_Implication_Result::NONE;
    }

    u64 upper_bound_i      = var_node.hard_upper_bound.atom_i;
    auto& upper_bound_node = graph.inequations[upper_bound_i];
    if (upper_bound_node.is_satisfied) return Bounds_Implication_Result::NONE;
    s64 upper_bound_val    = div_bound_by_coef(state.get_ineq_val(upper_bound_i), upper_bound_node.coefs[var]);

    u64 lower_bound_i      = var_node.hard_lower_bound.atom_i;
    auto& lower_bound_node = graph.inequations[lower_bound_i];
    if (lower_bound_node.is_satisfied) return Bounds_Implication_Result::NONE;
    s64 lower_bound_val    = div_bound_by_coef(state.get_ineq_val(lower_bound_i), lower_bound_node.coefs[var]);

    if (lower_bound_val > upper_bound_val) {
        return Bounds_Implication_Result::CONTRADICTION;
    }

    if (upper_bound_val == lower_bound_val) {
        *val = upper_bound_val;
        return Bounds_Implication_Result::VALUE;
    }

    return Bounds_Implication_Result::NONE;
}


void set_var_value_in_eq(
    Dep_Graph* graph,
    Ritch_Conjunction_State* state,  // To query values of other atoms
    u64& eq_idx,
    u64 var,
    s64 val)
{
    auto& eq = graph->equations[eq_idx];

    bool var_present = eq.coefs[var] != 0;
    if (!var_present) return;

    if (eq.vars.size() == 1 && graph->is_var_protected(var)) {
        return;
    }

    s64 current_val = state->get_eq_val(eq_idx);
    state->set_eq_val(eq_idx, current_val - eq.coefs[var] * val);

    eq.coefs[var] = 0;
    vector_remove(eq.vars, var);

    if (eq.vars.empty()) {
        eq.is_satisfied = true;
        // @ Todo: Do sanity check here
    } else if (eq.vars.size() == 1) { // The atom has became a new bound for the remaining variable
        u64 last_var      = eq.vars[0];
        u64 last_var_coef = eq.coefs[last_var];
        auto& var_node    = graph->var_nodes[last_var];

        var_node.hard_lower_bound.atom_i = eq_idx;
        var_node.hard_upper_bound.atom_i = eq_idx;
    }
}

void set_var_value_in_ineq(
    Dep_Graph* graph,
    Ritch_Conjunction_State* state,  // To query values of other atoms
    u64& ineq_idx,
    u64 var,
    s64 val)
{
    auto& ineq = graph->inequations[ineq_idx];

    s64 current_val = state->get_ineq_val(ineq_idx);
    state->set_ineq_val(ineq_idx, current_val - ineq.coefs[var] * val);

    bool is_var_present = ineq.coefs[var] != 0;
    if (!is_var_present) return;

    if (ineq.vars.size() == 1 && graph->is_var_protected(var)) {
        return;
    }

    ineq.coefs[var] = 0;
    vector_remove(ineq.vars, var);

    if (ineq.vars.empty()) {
        ineq.is_satisfied = true;

    } else if (ineq.vars.size() == 1) { // The atom has became a new bound for the remaining variable
        u64 last_var      = ineq.vars[0];
        s64 last_var_coef = ineq.coefs[last_var];
        auto& var_node    = graph->var_nodes[last_var];

        if (last_var_coef < 0) { // The variable has a new lower bound
            var_node.lower_bounds.push_back(ineq_idx);
            if (var_node.has_hard_lower_bound()) {
                u64 old_bound        = var_node.hard_lower_bound.atom_i;
                auto& old_bound_node = graph->inequations[old_bound];

                s64 old_bound_val = div_bound_by_coef(state->get_ineq_val(old_bound),
                                                      old_bound_node.coefs[last_var]);
                s64 new_bound_val = div_bound_by_coef(state->get_ineq_val(ineq_idx),
                                                      last_var_coef);
                var_node.hard_lower_bound.atom_i = old_bound_val > new_bound_val ? old_bound : ineq_idx;
            } else {
                var_node.hard_lower_bound.atom_i = ineq_idx;
            }
        } else { // New upper bound
            var_node.upper_bounds.push_back(ineq_idx);
            if (var_node.has_hard_upper_bound()) {
                u64 old_bound        = var_node.hard_upper_bound.atom_i;
                auto& old_bound_node = graph->inequations[old_bound];

                u64 off = graph->inequations.size();
                s64 old_bound_val = div_bound_by_coef(state->get_ineq_val(old_bound),
                                                      old_bound_node.coefs[last_var]);
                s64 new_bound_val = div_bound_by_coef(state->get_ineq_val(ineq_idx),
                                                      last_var_coef);
                var_node.hard_upper_bound.atom_i = old_bound_val < new_bound_val ? old_bound : ineq_idx;
            } else {
                var_node.hard_upper_bound.atom_i = ineq_idx;
            }
        }
    }
}

s64 normalize_reminder(s64 reminder, s64 modulus) {
    reminder %= modulus;
    reminder += (reminder < 0) * modulus;
    return reminder;
}

void substitute_var_for_value(Dep_Graph* graph, Ritch_Conjunction_State* state, u64 var, s64 val) {
    auto& var_node = graph->var_nodes[var];

    if (graph->is_var_free(var)) {
        graph->mark_var_as_protected(var);
    }

    for (u64 ineq_idx = 0; ineq_idx < graph->inequations.size(); ineq_idx++) {
        set_var_value_in_ineq(graph, state, ineq_idx, var, val);
    }

    for (u64 eq_idx = 0; eq_idx < graph->equations.size(); eq_idx++) {
        set_var_value_in_eq(graph, state, eq_idx, var, val);
    }

    for (u64 congruence_idx = 0; congruence_idx < graph->congruences.size(); congruence_idx++) {
        auto& congruence = graph->congruences[congruence_idx];

        // Congruences are at the front of the state, no need to introduce offset
        s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);
        s64 congruence_val = state->get_congruence_val(congruence_idx);
        s64 new_val = congruence_val - congruence.coefs[var] * val;
        new_val = normalize_reminder(new_val, modulus);
        state->set_congruence_val(congruence_idx, new_val);

        congruence.coefs[var] = 0;
        vector_remove(congruence.vars, var);
        if (congruence.vars.empty()) congruence.is_satisfied = true;
    }

    graph->var_nodes[var].upper_bounds.clear();
    graph->var_nodes[var].lower_bounds.clear();
    graph->var_nodes[var].hard_lower_bound.atom_i = Var_Node::TOMBSTONE;
    graph->var_nodes[var].hard_upper_bound.atom_i = Var_Node::TOMBSTONE;

    vector_remove(graph->quantified_vars, var);
}

bool substitute_vars_with_known_value(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state) {
    PRINT_DEBUG("Trying to substitute variables with known value.");
    Dep_Graph* work_graph = *graph_ptr;

    bool any_value_known = false;
    for (s64 var = 0; var < work_graph->var_nodes.size(); var++) {
        if (work_graph->is_var_protected(var)) continue;
        if (work_graph->is_false) break;

        PRINT_DEBUG("-> Trying variable x" << var);
        auto& node = work_graph->var_nodes[var];

        bool was_substituted_due_to_equation = false;
        for (auto eq_idx: node.equations) {
            if (eq_idx == Var_Node::TOMBSTONE) continue;
            auto& eq = work_graph->equations[eq_idx];

            if (eq.is_satisfied) continue;

            if (eq.vars.size() == 1 && eq.coefs[var] != 0) {
                work_graph = ensure_writable_graph(graph_ptr);

                s64 val = state->get_eq_val(eq_idx);
                s64 coef = eq.coefs[var];
                if (val % coef) {
                    work_graph->is_false = true;
                    return true;
                }

                val /= coef;
                substitute_var_for_value(work_graph, state, var, val);
                any_value_known = true;
                was_substituted_due_to_equation = true;

                PRINT_DEBUG("-> Value of x" << var << " is known to be " << val << "(due to eq)");
            }
        }

        if (was_substituted_due_to_equation) continue;

        s64 var_value = 0;
        auto bounds_implication_result = get_constant_value_implied_by_bounds(*work_graph, var, *state, &var_value);
        switch (bounds_implication_result) {
            case Bounds_Implication_Result::CONTRADICTION:
                PRINT_DEBUG("-> Bounds for x" << var << " imply a contradiction");
                work_graph = ensure_writable_graph(graph_ptr);
                work_graph->is_false = true;
                any_value_known = true;
                break;
            case Bounds_Implication_Result::VALUE:
                PRINT_DEBUG("-> Value of x" << var << " is known to be " << var_value << " (due to ineqs)");
                work_graph = ensure_writable_graph(graph_ptr);
                substitute_var_for_value(work_graph, state, var, var_value);
                any_value_known = true;
                break;
            default:
                break;
        }
    }

    PRINT_DEBUG("Any variable substituted? " << bool_into_yes_no(any_value_known));
    return any_value_known;
}

void simplify_graph_with_unbound_var(Dep_Graph* graph, u64 var) {
    auto& var_node = graph->var_nodes[var];

    for (auto& ineq: graph->inequations) {
        if (ineq.coefs[var] == 0) continue;
        ineq.is_satisfied = true;
    }

    for (auto& eq: graph->equations) {
        if (eq.coefs[var] == 0) continue;
        eq.is_satisfied = true;
    }

    for (auto& congr: graph->congruences) {
        if (congr.coefs[var] == 0) continue;
        congr.is_satisfied = true;
    }

    var_node.congruences.clear();
    var_node.lower_bounds.clear();
    var_node.upper_bounds.clear();
    var_node.hard_lower_bound.atom_i = Var_Node::TOMBSTONE;
    var_node.hard_lower_bound.atom_i = Var_Node::TOMBSTONE;
}

bool instantiate_quantifs_with_inf(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state) {
    Dep_Graph* work_graph = *graph_ptr;

    bool any_quantif_instantiated = false;

    PRINT_DEBUG("Trying to remove quantifiers on unbound vars.");
    for (auto var: work_graph->quantified_vars) {
        auto var_node = work_graph->var_nodes[var];
        bool can_be_neg_inf = var_node.lower_bounds.empty();
        bool can_be_pos_inf = var_node.upper_bounds.empty();
        bool is_not_in_eq = var_node.equations.empty();
        bool all_congruences_have_granularity_1 = true;
        for (auto congr_i: var_node.congruences) {
            auto& congr = work_graph->congruences[congr_i];
            auto coef = congr.coefs[var];
            if (abs(coef) > 1) {
                all_congruences_have_granularity_1 = false;
                break;
            }
        }

        bool can_be_inst = all_congruences_have_granularity_1 && is_not_in_eq && (can_be_neg_inf || can_be_pos_inf);
        if (can_be_inst) {

            work_graph = ensure_writable_graph(graph_ptr);

            simplify_graph_with_unbound_var(work_graph, var);

            vector_remove(work_graph->quantified_vars, var); //  Quantifier is instantiated

            any_quantif_instantiated = true;
        }
    }

    PRINT_DEBUG("Any quantifier instantiated? " << bool_into_yes_no(any_quantif_instantiated));
    return any_quantif_instantiated;
}

bool get_value_close_to_bounds(Dep_Graph* graph, Ritch_Conjunction_State* state, u64 var, s64* value) {
    // if (!is_safe_to_instantiate(graph, var)) {
    //     return false;
    // }

    auto& var_node = graph->var_nodes[var];
    u64 bound_node_i = 0;

    Bound_Type bound_type = Bound_Type::NONE;
    bool has_multiple_upper_bounds = var_node.upper_bounds.size() > 1;
    bool has_multiple_lower_bounds = var_node.lower_bounds.size() > 1;

    // Note the direction from which will be searching for an optimal value
    if (var_node.has_hard_lower_bound() && !has_multiple_lower_bounds) {
        // All reminding bounds are upper, preferring the smallest value possible
        bound_node_i = var_node.hard_lower_bound.atom_i;
        bound_type = Bound_Type::LOWER;
    } else if (var_node.has_hard_upper_bound() && !has_multiple_upper_bounds) {
        // All reminding bounds are lower, preferring the largest value possible
        bound_node_i = var_node.hard_upper_bound.atom_i;
        bound_type = Bound_Type::UPPER;
    }

    if (bound_type == Bound_Type::NONE) return false;

    auto& bound = graph->inequations[bound_node_i];
    if (bound.is_satisfied) return false;

    // Var has a clear lower bound and its all of its ussages would like it to be some low value
    s64 bound_raw_val = state->get_ineq_val(bound_node_i);
    s64 bound_value   = div_bound_by_coef(bound_raw_val, bound.coefs[var]);

    s32 active_congruence_idx = -1;
    for (s32 congr_idx = 0; congr_idx < graph->congruences.size(); congr_idx++) {
        auto& congr = graph->congruences[congr_idx];

        if (congr.is_satisfied) continue;
        if (congr.coefs[var] != 0) {
            if (active_congruence_idx == -1) {
                active_congruence_idx = congr_idx;
            } else {
                return false;  // More than one congruence contains the variable
            }
        }
    }

    if (active_congruence_idx == -1) {
        *value = bound_value;
        return true;
    }

    auto& congruence = graph->congruences[active_congruence_idx];

    if (congruence.vars.size() > 1) {
        // @Research: In case there are multiple variables in a congruence, but we affect only free vars,
        // we can maybe still instantiate the value if the congruence variables are not restristed too much.
        return false;   // We don't know how to infer value when there are multiple vars in congruence
    }

    u64 nonzero_coefs = 0;
    for (auto coef: congruence.coefs) nonzero_coefs += (coef != 0);
    if (nonzero_coefs > 1) return false;

    // Find a solution in the unshifted congruence range, e.g., -y ~ 100 (mod 303)
    s64 modulus = combine_moduli(congruence.modulus_2pow, congruence.modulus_odd);

    s64 rhs  = normalize_reminder(state->get_congruence_val(active_congruence_idx), modulus);
    s64 coef = normalize_reminder(congruence.coefs[var], modulus);

    s64 mult_inv = compute_multiplicative_inverse(modulus, coef);
    rhs = (rhs * mult_inv) % modulus; // e.g., y ~ 200 (mod 303), rhs is now a solution

    s64 shift_coef = bound_value / modulus;
    shift_coef    -= (bound_value < 0); // A signed floor division
    s64 congruence_shift = modulus * shift_coef;

    s64 instantiated_value = rhs + congruence_shift;

    // Both bound and the proposed solution lie in the same block of reminders [kM ... (k+1)M]
    // but the proposed solution might be slightly above/bellow the bound, correct it.
    if (bound_type == Bound_Type::LOWER) {
        // (x >= 5) and the suggested solution is x = 3
        instantiated_value += (instantiated_value < bound_value) * modulus;
    } else {
        // (x <= 5) and the suggested solution is x = 8
        instantiated_value -= (bound_value < instantiated_value) * modulus;
    }

    // std::cout << "Instantiating x" << var << " with value " << instantiated_value << std::endl;
    // std::cout << congruence << std::endl;
    // std::cout << state.constants[congruence_i] << std::endl;
    // std::cout << state << std::endl;
    // std::cout << "Modulus " << modulus << std::endl;

    *value = instantiated_value;
    return true;
}

bool instantiate_quantifs_with_c_monotonicity(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state) {
    PRINT_DEBUG("Instantiating quantifiers with c-monotonicity.");
    Dep_Graph* work_graph = *graph_ptr;
    bool was_any_quantif_instantiated = false;
    for (auto var: work_graph->quantified_vars) {

        if (work_graph->var_nodes[var].equations.size() > 0) continue;

        s64  optimal_var_value = 0;
        bool optimal_value_known = get_value_close_to_bounds(work_graph, state, var, &optimal_var_value);

        if (optimal_value_known) {
            PRINT_DEBUG("Simplifying graph - instantiating var: x" << var << " with value " << optimal_var_value);

            work_graph = ensure_writable_graph(graph_ptr);

            substitute_var_for_value(work_graph, state, var, optimal_var_value);
            vector_remove(work_graph->vars_not_removed_in_simplification, var);

            was_any_quantif_instantiated = true;
        }
    }
    PRINT_DEBUG("Any quantifier instantiated? " << bool_into_yes_no(was_any_quantif_instantiated));

    return was_any_quantif_instantiated;
}


s64 calc_gcd(vector<u64>& use_indices, vector<s64>& coefs) {
    if (use_indices.empty()) return 1;

    s64 gcd = abs(coefs[use_indices[0]]);
    for (auto index: use_indices) {
        s64 coef = coefs[index];
        gcd = std::gcd(coef, gcd);
    }
    return gcd;
}


void normalize_coefficients(Dep_Graph* graph, Ritch_Conjunction_State* state) {
    for (s32 eq_idx = 0; eq_idx < graph->equations.size(); eq_idx++) {
        auto& eq = graph->equations[eq_idx];
        if (eq.is_satisfied) continue;

        s64 gcd = calc_gcd(eq.vars, eq.coefs);
        s64 eq_rhs = state->get_eq_val(eq_idx);
        if (eq_rhs % gcd) {
            graph->is_false = true;
            return;
        }

        for (auto& coef: eq.coefs) coef /= gcd;
        state->set_eq_val(eq_idx, eq_rhs/gcd);
    }

    for (s32 ineq_idx = 0; ineq_idx < graph->inequations.size(); ineq_idx++) {
        auto& ineq = graph->inequations[ineq_idx];
        if (ineq.is_satisfied) continue;

        s64 gcd = calc_gcd(ineq.vars, ineq.coefs);
        if (gcd == 1) continue;

        for (auto& coef: ineq.coefs) coef /= gcd;

        s64 ineq_rhs = state->get_ineq_val(ineq_idx);
        state->set_ineq_val(ineq_idx, div_bound_by_coef(ineq_rhs, gcd));
    }
}


bool perform_max_simplification_on_graph(Dep_Graph** graph, Ritch_Conjunction_State* state) {
    PRINT_DEBUG("Performing maximal formula simplification.");

    bool was_any_rewrite_performed    = false;
    bool was_any_rewrite_in_this_iter = true;

    while (was_any_rewrite_in_this_iter) {
        was_any_rewrite_in_this_iter = false;

        was_any_rewrite_in_this_iter |= substitute_vars_with_known_value(graph, state);
        if ((*graph)->is_false) {
            break;
        }
        was_any_rewrite_in_this_iter |= instantiate_quantifs_with_inf(graph, state);
        was_any_rewrite_in_this_iter |= instantiate_quantifs_with_c_monotonicity(graph, state);
        was_any_rewrite_in_this_iter |= linearize_moduli(graph, state);

        was_any_rewrite_performed |= was_any_rewrite_in_this_iter;
    }

    was_any_rewrite_performed |= was_any_rewrite_in_this_iter; // In case we exit the loop before updating

    if (((*graph)->is_false)) return was_any_rewrite_performed;

    if (was_any_rewrite_performed) {
        normalize_coefficients(*graph, state);
    }

    return was_any_rewrite_performed;
}


bool perform_watched_rewrites(Dep_Graph** graph, Conjunction_State* state) {
    PRINT_DEBUG("Performing watched formula rewrite on state: " << state->constants);

    Dep_Graph* work_graph = *graph;
    for (auto& watched_position: work_graph->watched_positions) {
        bool match0 = state->constants[watched_position.position0] == watched_position.required_value0;
        bool match1 = state->constants[watched_position.position1] == watched_position.required_value1;
        if (match0 && match1) {
            Formula_Structure structure = {
                .eq_cnt         = static_cast<s32>(work_graph->equations.size()),
                .ineq_cnt       = static_cast<s32>(work_graph->inequations.size()),
                .congruence_cnt = static_cast<s32>(work_graph->congruences.size()),
            };
            Ritch_Conjunction_State ritch_state = {.data = state->constants, .formula_structure = structure};
            bool result = perform_max_simplification_on_graph(graph, &ritch_state);

            state->constants = ritch_state.data;

            return result;
        }
    }
    return false;
}


bool detect_contradictions(const Dep_Graph* graph, Conjunction_State* state) {
    u64 offset = graph->congruences.size() + graph->equations.size();

    for (auto [pos_idx, neg_idx]: graph->complementary_pairs) {
        // Negative: -a.x <= A    <---> a.x >= -A
        // Positive   a.x <= B    <---> a.x <=  B
        // if -A > B, then contradiction
        auto pos_val = state->constants[offset + pos_idx]; // B
        auto neg_val = state->constants[offset + neg_idx]; // A

        if (-neg_val > pos_val) return true;
    }

    for (auto& var_node: graph->var_nodes) {
        if (!var_node.has_hard_lower_bound() || !var_node.has_hard_upper_bound()) continue;

        s64 lower_bound_val = state->constants[offset + var_node.hard_lower_bound.atom_i];
        s64 upper_bound_val = state->constants[offset + var_node.hard_upper_bound.atom_i];
        if (-lower_bound_val > upper_bound_val) return true;
    }

    return false;
}
