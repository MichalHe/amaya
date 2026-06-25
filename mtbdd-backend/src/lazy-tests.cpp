#define DOCTEST_CONFIG_IMPLEMENT
#include "../external/doctest.h"
#include "../include/lazy.hpp"
#include "../include/base.hpp"
#include "../include/pareto_set.h"
#include "../include/vectors.h"
#include "../include/tfa_leaf.h"
#include "../include/wrapper.hpp"
#include "../include/rewrites.h"
#include "../include/algorithms.hpp"

#include <algorithm>
#include <vector>
#include <unordered_map>

typedef Quantified_Atom_Conjunction Formula;

using std::pair;
using std::vector;
using std::unordered_map;

using sylvan::MTBDD;
using sylvan::BDDSET;


#define DEBUG_TESTS 0
#if DEBUG_TESTS
#define TEST_PRINT_DEBUG(it) do { std::cerr << it << std::endl; } while (0)
#define TEST_PRINTF_DEBUG(...) do { fprintf(stderr, __VA_ARGS__); } while (0)
#else
#define TEST_PRINT_DEBUG(it)
#define TEST_PRINTF_DEBUG(...)
#endif


struct Atom_Allocator {
    vector<s64*> coef_blocks;
    vector<Congruence*> congruence_blocks;
    vector<Equation*>   equation_blocks;
    vector<Inequation*> inequation_blocks;

    ~Atom_Allocator() {
        for (s64* coef_block: coef_blocks) delete[] coef_block;
        for (Congruence* congruence_block: congruence_blocks) delete[] congruence_block;
        for (Equation* equation_block: equation_blocks) delete[] equation_block;
        for (Inequation* inequation_block: inequation_blocks) delete[] inequation_block;
    }
};

Sized_Array<Congruence> alloc_congruences(Atom_Allocator& alloc, const vector<pair<vector<s64>, s64>>& congruence_coefs) {
    if (congruence_coefs.empty()) return {nullptr, 0};
    u64 var_count = congruence_coefs[0].first.size();

    s64* coef_block = new s64[var_count * congruence_coefs.size()];
    alloc.coef_blocks.push_back(coef_block);
    u64 next_free_coef_slot = 0;

    Congruence* congruence_block = new Congruence[congruence_coefs.size()];
    alloc.congruence_blocks.push_back(congruence_block);
    u64 next_free_congruence_slot = 0;

    for (auto& [coefs, modulus]: congruence_coefs) {
        // Make a sized array out of coefficients
        s64* congruence_coef_block = coef_block + next_free_coef_slot * var_count;

        for (auto coef: coefs) {
            coef_block[next_free_coef_slot] = coef;
            next_free_coef_slot += 1;
        }

        Sized_Array<s64> coefs_block(congruence_coef_block, var_count);

        // Make a congruence and push it back
        auto decomposed_modulus = decompose_modulus(modulus);
        Congruence congruence = {.coefs = coefs_block, .modulus_odd = decomposed_modulus.modulus_odd, .modulus_2pow = decomposed_modulus.modulus_2pow};
        congruence_block[next_free_congruence_slot] = congruence;
        next_free_congruence_slot += 1;
    }

    return Sized_Array<Congruence>(congruence_block, congruence_coefs.size());
};

Sized_Array<Equation> alloc_equations(Atom_Allocator& alloc, const vector<vector<s64>>& equation_coefs) {
    if (equation_coefs.empty()) return Sized_Array<Equation>(nullptr, 0);

    u64 var_count = equation_coefs[0].size();

    s64* coef_block = new s64[var_count * equation_coefs.size()];
    alloc.coef_blocks.push_back(coef_block);
    u64 next_free_coef_slot = 0;

    Equation* equation_block = new Equation[equation_coefs.size()];
    alloc.equation_blocks.push_back(equation_block);
    u64 next_free_equation_slot = 0;

    for (auto& coefs: equation_coefs) {
        s64* eq_coef_block = coef_block + next_free_equation_slot * var_count;
        for (auto coef: coefs) {
            coef_block[next_free_coef_slot] = coef;
            next_free_coef_slot += 1;
        }
        Sized_Array<s64> coefs_block(eq_coef_block, var_count);

        Equation equation = {.coefs = coefs_block};
        equation_block[next_free_equation_slot] = equation;
        next_free_equation_slot += 1;
    }

    return Sized_Array<Equation>(equation_block, equation_coefs.size());
};

Sized_Array<Inequation> alloc_inequations(Atom_Allocator& alloc, const vector<vector<s64>>& ineq_coefs) {
    if (ineq_coefs.empty()) return {nullptr, 0};

    u64 var_count = ineq_coefs[0].size();

    s64* coef_block = new s64[var_count * ineq_coefs.size()];
    alloc.coef_blocks.push_back(coef_block);
    u64 next_free_coef_slot = 0;

    Inequation* inequation_block = new Inequation[ineq_coefs.size()];
    alloc.inequation_blocks.push_back(inequation_block);
    u64 next_free_inequation_slot = 0;

    for (auto& coefs: ineq_coefs) {
        s64* eq_coef_block = coef_block + var_count * next_free_inequation_slot;
        for (auto coef: coefs) {
            coef_block[next_free_coef_slot] = coef;
            next_free_coef_slot += 1;
        }
        Sized_Array<s64> coefs_block(eq_coef_block, var_count);

        Inequation ineq = {.coefs = coefs_block};
        inequation_block[next_free_inequation_slot] = ineq;
        next_free_inequation_slot += 1;
    }

    return {inequation_block, ineq_coefs.size()};
};

Formula make_formula(Atom_Allocator& allocator,
                     const vector<pair<vector<s64>, s64>>& congruences_coefs,
                     const vector<vector<s64>>& eqs,
                     const vector<vector<s64>>& ineqs,
                     const vector<u64> bound_vars) {
    Sized_Array<Congruence> congruences = alloc_congruences(allocator, congruences_coefs);
    Sized_Array<Equation> equations     = alloc_equations(allocator, eqs);
    Sized_Array<Inequation> inequations = alloc_inequations(allocator, ineqs);

    u64 var_count = 0;
    if (!congruences_coefs.empty()) var_count = congruences_coefs[0].first.size();
    else if (!ineqs.empty())        var_count = ineqs[0].size();
    else if (!eqs.empty())          var_count = eqs[0].size();

    return Formula(congruences, equations, inequations, bound_vars, var_count);
}

void assert_dfas_are_isomorphic(const NFA& expected, const NFA& actual) {
    CHECK(expected.initial_states.size() == 1);
    CHECK(actual.initial_states.size() == 1);

    CHECK(expected.states.size() == actual.states.size());
    CHECK(expected.final_states.size() == actual.final_states.size());

    unordered_map<State, State> isomorphism {{*expected.initial_states.begin(), *actual.initial_states.begin()}};

    vector<State> work_queue {*expected.initial_states.begin()};
    while (!work_queue.empty()) {
        auto expected_state = work_queue.back();
        auto actual_state_it = isomorphism.find(expected_state);

        work_queue.pop_back();

        // Make sure that the (expected, actual) mapping has been inserted when the expected state has been discovered
        CHECK(actual_state_it != isomorphism.end());
        auto actual_state = actual_state_it->second;
        TEST_PRINTF_DEBUG("Checking transitions between states: %lu (expected) <> %lu (actual)\n", expected_state, actual_state);

        auto expected_transitions = expected.get_symbolic_transitions_for_state(expected_state);
        auto actual_transitions   = actual.get_symbolic_transitions_for_state(actual_state);
        if (expected_transitions.size() != actual_transitions.size()) {
            TEST_PRINT_DEBUG("Found mismatch between symbolic transition sizes.\n");
            TEST_PRINT_DEBUG("  (expected): ");
            for (Transition& et: expected_transitions) TEST_PRINT_DEBUG(et << ", ");
            TEST_PRINT_DEBUG("\n");
            TEST_PRINT_DEBUG("  (actual): ");
            for (Transition& at: actual_transitions) TEST_PRINT_DEBUG(at << ", ");
            TEST_PRINT_DEBUG("\n");
            CHECK(expected_transitions.size() == actual_transitions.size());
        }

        for (auto& expected_transition: expected_transitions) {
            // Find a transition matching origin and the transition symbol; make sure that there is exactly 1 as the automaton is a DFA
            Transition& matching_transition = actual_transitions[0];
            u64 match_count = 0;
            for (auto& actual_transition: actual_transitions) {
                if (actual_transition.symbol == expected_transition.symbol) {
                    matching_transition = actual_transition;
                    match_count++;
                }
            }

            CHECK(match_count == 1);

            // In case there the already was an (expected, actual) mapping in the isomorphism check that it
            // is consistent with the currently matching transition
            auto [pos, was_inserted] = isomorphism.emplace(expected_transition.to, matching_transition.to);
            if (!was_inserted) {
                CHECK(matching_transition.to == pos->second);
            } else {
                work_queue.push_back(expected_transition.to);
            }
        }
    }

    for (auto expected_final_state: expected.final_states) {
        auto mapping_it = isomorphism.find(expected_final_state);
        CHECK(mapping_it != isomorphism.end());

        // if (mapping_it == isomorphism.end()) {
        //     std::cout << "Cloud not map expected final state " << expected_final_state << " to an actual one!" << std::endl;
        //     std::cout << "Mappings: " << std::endl;
        //     for (auto [key, value]: isomorphism) {
        //         std::cout << key << " -> " << value << std::endl;
        //     }

        //     std::cout << "Actual final states: " << std::endl;
        //     for (auto actual: actual.final_states) {
        //         std::cout << actual << std::endl;
        //     }
        // }

        CHECK(actual.final_states.find(mapping_it->second) != actual.final_states.end());
    }
}

TEST_CASE("lazy_construct `\\exists x (x + y <= 0)`")
{
    Atom_Allocator allocator;
    Formula formula = make_formula(allocator, {}, {}, {{1, 1}}, {0});;
    Formula_Pool pool = Formula_Pool(&formula);
    auto formula_id = pool.store_formula(formula);
    Conjunction_State init_state({0});

    sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
    vars = sylvan::mtbdd_set_add(vars, 1);
    vars = sylvan::mtbdd_set_add(vars, 2);

    auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

    NFA expected_nfa(vars, 2, {0, 1}, {1}, {0});

    vector<Transition> symbolic_transitions {
        {.from = 0, .to = 1, .symbol = {2, 2}},
        {.from = 1, .to = 1, .symbol = {2, 2}},
    };

    for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

    assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
}

TEST_CASE("lazy_construct simple atoms")
{
    SUBCASE("atom `x - y <= 2`") {
        Atom_Allocator alloc;
        Formula formula = make_formula(alloc, {}, {}, {{1, 1}}, {});
        Formula_Pool pool = Formula_Pool(&formula);
        auto formula_id = pool.store_formula(formula);
        Conjunction_State init_state({2});

        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);
        vars = sylvan::mtbdd_set_add(vars, 2);

        auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

        NFA expected_nfa(
            vars, 2,
            {
                0,  // {2}
                1,  // {1, F}
                2,  // {0, F}
                3,  // {-1, F}
                4,  // {-1}
                5,  // {-2, F}
                6,  // {-2}
            },
            {1, 2, 3, 5},
            {0}
        );

        vector<Transition> symbolic_transitions {
            // {2}
            {.from = 0, .to = 1, .symbol = {0, 0}},
            {.from = 0, .to = 2, .symbol = {0, 1}},
            {.from = 0, .to = 2, .symbol = {1, 2}},
            // {1, F}
            {.from = 1, .to = 2, .symbol = {0, 2}},
            {.from = 1, .to = 2, .symbol = {1, 0}},
            {.from = 1, .to = 3, .symbol = {1, 1}},
            // {0, F}
            {.from = 2, .to = 2, .symbol = {0, 0}},
            {.from = 2, .to = 3, .symbol = {0, 1}},
            {.from = 2, .to = 3, .symbol = {1, 2}},
            // {-1, F}
            {.from = 3, .to = 4, .symbol = {0, 0}},
            {.from = 3, .to = 3, .symbol = {0, 1}},
            {.from = 3, .to = 3, .symbol = {1, 0}},
            {.from = 3, .to = 5, .symbol = {1, 1}},
            // {-1}
            {.from = 4, .to = 4, .symbol = {0, 0}},
            {.from = 4, .to = 3, .symbol = {0, 1}},
            {.from = 4, .to = 3, .symbol = {1, 0}},
            {.from = 4, .to = 5, .symbol = {1, 1}},
            // {-2, F}
            {.from = 5, .to = 4, .symbol = {0, 0}},
            {.from = 5, .to = 6, .symbol = {0, 1}},
            {.from = 5, .to = 6, .symbol = {1, 0}},
            {.from = 5, .to = 5, .symbol = {1, 1}},
            // {-2}
            {.from = 6, .to = 4, .symbol = {0, 0}},
            {.from = 6, .to = 6, .symbol = {0, 1}},
            {.from = 6, .to = 6, .symbol = {1, 0}},
            {.from = 6, .to = 5, .symbol = {1, 1}},
        };

        for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

        assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
    }

    SUBCASE("atom `2x - y = 0`") {
        Atom_Allocator alloc;
        Formula formula = make_formula(alloc, {}, {{2, -1}}, {}, {});
        Formula_Pool pool = Formula_Pool(&formula);
        auto formula_id = pool.store_formula(formula);
        Conjunction_State init_state({0});

        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);
        vars = sylvan::mtbdd_set_add(vars, 2);

        auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

        NFA expected_nfa(
            vars, 2,
            {
                0,  // {0}
                1,  // {0, F}
                2,  // {-1}
                3,  // {-1, F}
                4,  // Trap
            },
            {1, 3},
            {0}
        );

        vector<Transition> symbolic_transitions {
            // {0}
            {.from = 0, .to = 1, .symbol = {0, 0}},
            {.from = 0, .to = 4, .symbol = {0, 1}},
            {.from = 0, .to = 2, .symbol = {1, 0}},
            {.from = 0, .to = 4, .symbol = {1, 1}},
            // {0, F}
            {.from = 1, .to = 1, .symbol = {0, 0}},
            {.from = 1, .to = 4, .symbol = {0, 1}},
            {.from = 1, .to = 2, .symbol = {1, 0}},
            {.from = 1, .to = 4, .symbol = {1, 1}},
            // {-1}
            {.from = 2, .to = 4, .symbol = {0, 0}},
            {.from = 2, .to = 0, .symbol = {0, 1}},
            {.from = 2, .to = 4, .symbol = {1, 0}},
            {.from = 2, .to = 3, .symbol = {1, 1}},
            // {-1, F}
            {.from = 3, .to = 4, .symbol = {0, 0}},
            {.from = 3, .to = 0, .symbol = {0, 1}},
            {.from = 3, .to = 4, .symbol = {1, 0}},
            {.from = 3, .to = 3, .symbol = {1, 1}},
            // Trap
            {.from = 4, .to = 4, .symbol = {2, 2}},
        };

        for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

        assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
    }

    SUBCASE("atom `x + 3y = 1 (mod 3)`") {
        Atom_Allocator alloc;
        Formula formula = make_formula(alloc, {{{1, 3}, 3}}, {}, {}, {});
        Formula_Pool pool = Formula_Pool(&formula);
        auto formula_id = pool.store_formula(formula);
        Conjunction_State init_state({1});

        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);
        vars = sylvan::mtbdd_set_add(vars, 2);

        auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

        NFA expected_nfa(
            vars, 2,
            {
                0,  // {1}
                1,  // {2}
                2,  // {2, F}
                3,  // {0}
                4,  // {0, F}
            },
            {2, 4},
            {0}
        );

        vector<Transition> symbolic_transitions {
            // {1}
            {.from = 0, .to = 1, .symbol = {0, 2}},
            {.from = 0, .to = 3, .symbol = {1, 2}},
            // {2}
            {.from = 1, .to = 0, .symbol = {0, 2}},
            {.from = 1, .to = 2, .symbol = {1, 2}},
            // {2, F}
            {.from = 2, .to = 0, .symbol = {0, 2}},
            {.from = 2, .to = 2, .symbol = {1, 2}},
            // {0}
            {.from = 3, .to = 4, .symbol = {0, 2}},
            {.from = 3, .to = 0, .symbol = {1, 2}},
            // {0, F}
            {.from = 4, .to = 4, .symbol = {0, 2}},
            {.from = 4, .to = 0, .symbol = {1, 2}},
        };

        for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

        assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
    }
    SUBCASE("atom `x + y = 0 (mod 4)`") {
        Atom_Allocator alloc;
        Formula formula = make_formula(alloc, {{{1, 1}, 4}}, {}, {}, {});
        Formula_Pool pool = Formula_Pool(&formula);
        auto formula_id = pool.store_formula(formula);
        Conjunction_State init_state({0});

        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);
        vars = sylvan::mtbdd_set_add(vars, 2);

        auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

        NFA expected_nfa(
            vars, 2,
            {
                0,  // {0 (mod 4)}
                1,  // {0 (mod 2), TOP}
                2,  // {1 (mod 2)}
                3,  // {0 (mod 1), TOP}
                4,  // {BOTTOM}
            },
            {1, 3},
            {0}
        );

        vector<Transition> symbolic_transitions {
            // {0 (mod 4)}
            {.from = 0, .to = 1, .symbol = {0, 0}},
            {.from = 0, .to = 4, .symbol = {0, 1}},
            {.from = 0, .to = 4, .symbol = {1, 0}},
            {.from = 0, .to = 2, .symbol = {1, 1}},
            // {0 (mod 2), TOP}
            {.from = 1, .to = 3, .symbol = {0, 0}},
            {.from = 1, .to = 4, .symbol = {0, 1}},
            {.from = 1, .to = 4, .symbol = {1, 0}},
            {.from = 1, .to = 3, .symbol = {1, 1}},
            // {1 (mod 2), TOP}
            {.from = 2, .to = 4, .symbol = {0, 0}},
            {.from = 2, .to = 3, .symbol = {0, 1}},
            {.from = 2, .to = 3, .symbol = {1, 0}},
            {.from = 2, .to = 4, .symbol = {1, 1}},
            // {0 (mod 1), TOP}
            {.from = 3, .to = 3, .symbol = {2, 2}},
            // {BOTTOM}
            {.from = 4, .to = 4, .symbol = {2, 2}},
        };

        for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

        assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
    }
}

/*
TEST_CASE("lazy_construct(1) `\\exists y,m (x - y <= -1 && y <= -1 && -m <= 0 && m <= 1 && m - y ~ 0 (mod 3))`")
{
    Formula formula = {
        .atoms = {
            Presburger_Atom(Presburger_Atom_Type::PR_ATOM_INEQ, {0, 1, -1}),        // (<= (+ x (- y)) -1)
            Presburger_Atom(Presburger_Atom_Type::PR_ATOM_INEQ, {0, 0, 1}),         // (<= y -1)
            Presburger_Atom(Presburger_Atom_Type::PR_ATOM_INEQ, {-1, 0, 0}),        // (<= (- m) 0)
            Presburger_Atom(Presburger_Atom_Type::PR_ATOM_INEQ, {1, 0, 0}),         // (<= m 0)
            Presburger_Atom(Presburger_Atom_Type::PR_ATOM_CONGRUENCE, {1, 0, -1}, 3),  // (= (mod (+ m (- y)) 3) 0)
        },
        .bound_vars = {0, 2},
        .var_count = 3
    };

    Formula_Pool pool = Formula_Pool();
    auto formula_id = pool.store_formula(formula);
    Conjunction_State init_state({-1, -1, 0, 1, 0});

    sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
    vars = sylvan::mtbdd_set_add(vars, 1);
    vars = sylvan::mtbdd_set_add(vars, 2);
    vars = sylvan::mtbdd_set_add(vars, 3);

    auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);

    NFA expected_nfa(
        vars, 3,
        {
            0, // {(-1, -1, 0, 0, 0)}, formula: input
            1, // {(-2)}, formula: x <= ?
            2, // {(-1)}, formula: x <= ?
            3  // {(-1), F} formula: x <= ?
        },
        {3},
        {0}
    );

    // Symbols are (m, x, y)
    vector<Transition> symbolic_transitions {
        {.from = 0, .to = 1, .symbol = {2, 2, 2}},
        {.from = 1, .to = 2, .symbol = {2, 0, 2}},
        {.from = 1, .to = 1, .symbol = {2, 1, 2}},
        {.from = 2, .to = 2, .symbol = {2, 0, 2}},
        {.from = 2, .to = 3, .symbol = {2, 1, 2}},
        {.from = 3, .to = 2, .symbol = {2, 0, 2}},
        {.from = 3, .to = 3, .symbol = {2, 1, 2}},
    };

    for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

    assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
}
*/

TEST_CASE("complex formula :: lazy_construct `\\exists y,m (x - y <= 5 && z - m <= -1 && y <= -1 && -m <= 0 && m <= 1 && m - y ~ 0 (mod 3))`")
{
    // (exists ((y Int), (m Int))
    //   (land
    //     (<= (+ x (- y)) -1)
    //     (<= (- z m) -1)
    //     (<= y -1)
    //     (<= (- m) 0)
    //     (<= m 0)
    //     (= (mod (+ m (- y)) 299_993) 303)
    //   )
    // )
    //
    // Variables are renamed as: m -> x0, x -> x1, y -> x2, z -> x3
    //
    Atom_Allocator allocator;
    Formula formula = make_formula(allocator,
                                   {{{1, 0, -1, 0}, 3}},
                                   {},
                                   {
                                       {0, 1, -1, 0},   // (<= (- x y) 5)
                                       {-1, 0, 0, 1},   // (<= (- z m) -1)
                                       {0, 0, 1, 0},    // (<= y -1)
                                       {-1, 0, 0, 0},   // (<= (- m) 0)
                                       {1, 0, 0, 0},    // (<= m 0)
                                   },
                                   {0, 2});

    Conjunction_State init_state({0 /*congruence*/, 5, -1, -1, 0, 0});

    Formula_Pool pool = Formula_Pool(&formula);
    const Formula* canon_formula_ptr = pool.store_formula(formula);

    u32 var_ids[] = {1, 2, 3, 4};
    sylvan::BDDSET vars = sylvan::mtbdd_set_from_array(var_ids, 4);

    NFA actual_dfa = build_nfa_with_formula_entailement(canon_formula_ptr, init_state, vars, pool);

    std::cout << "Break!" << sylvan::mtbdd_count_refs << std::endl;

    // The formula should be simplified into: x <= 2 && z <= -1
    NFA expected_dfa(vars,
                     4,
                     {
                        0,  // (2, -1)
                        1,  // (1, -1) + ACC
                        2,  // (1, -1)
                        3,  // (0, -1)
                        4,  // (0, -1) + ACC
                        5,  // (-1, -1)
                        6   // (-1, -1) + ACC
                     },
                     {1, 4, 6}, {0});

    vector<Transition> expected_transitions {
        // (2, -1)
        {.from = 0, .to = 2, .symbol = {2, 0, 2, 0}},
        {.from = 0, .to = 1, .symbol = {2, 0, 2, 1}},
        {.from = 0, .to = 3, .symbol = {2, 1, 2, 0}},
        {.from = 0, .to = 4, .symbol = {2, 1, 2, 1}},
        // (1, -1) + ACC
        {.from = 1, .to = 3, .symbol = {2, 2, 2, 0}},
        {.from = 1, .to = 4, .symbol = {2, 2, 2, 1}},
        // (1, -1)
        {.from = 2, .to = 3, .symbol = {2, 2, 2, 0}},
        {.from = 2, .to = 4, .symbol = {2, 2, 2, 1}},
        // (0, -1)
        {.from = 3, .to = 3, .symbol = {2, 0, 2, 0}},
        {.from = 3, .to = 4, .symbol = {2, 0, 2, 1}},
        {.from = 3, .to = 5, .symbol = {2, 1, 2, 0}},
        {.from = 3, .to = 6, .symbol = {2, 1, 2, 1}},
        // (0, -1) + ACC
        {.from = 4, .to = 3, .symbol = {2, 0, 2, 0}},
        {.from = 4, .to = 4, .symbol = {2, 0, 2, 1}},
        {.from = 4, .to = 5, .symbol = {2, 1, 2, 0}},
        {.from = 4, .to = 6, .symbol = {2, 1, 2, 1}},
        // (-1, -1)
        {.from = 5, .to = 5, .symbol = {2, 0, 2, 2}},
        {.from = 5, .to = 5, .symbol = {2, 1, 2, 0}},
        {.from = 5, .to = 6, .symbol = {2, 1, 2, 1}},
        // (-1, -1) + ACC
        {.from = 6, .to = 5, .symbol = {2, 0, 2, 2}},
        {.from = 6, .to = 5, .symbol = {2, 1, 2, 0}},
        {.from = 6, .to = 6, .symbol = {2, 1, 2, 1}},
    };

    for (Transition& transition: expected_transitions)
        expected_dfa.add_transition(transition.from, transition.to, transition.symbol.data());

    assert_dfas_are_isomorphic(expected_dfa, actual_dfa);
}

TEST_CASE("NFA::pad_closure (simple)") {
    sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
    vars = sylvan::mtbdd_set_add(vars, 1);

    NFA nfa(vars, 1, {1, 2, 3}, {3}, {1});

    u8 symbol[] = {1};
    nfa.add_transition(1, 2, symbol);
    nfa.add_transition(2, 3, symbol);

    std::vector<Transition> expected_transitions = nfa_unpack_transitions(nfa);
    expected_transitions.push_back({.from=1, .to=4, .symbol={1}});

    nfa.perform_pad_closure();
    auto transitions = nfa_unpack_transitions(nfa);
    CHECK(transitions.size() == 3);
    for (auto& expected_transition: expected_transitions) {
        CHECK(std::find(transitions.begin(), transitions.end(), expected_transition) != transitions.end());
    }
}

TEST_CASE("NFA::determinize (simple)") {
    sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
    vars = sylvan::mtbdd_set_add(vars, 1);
    NFA nfa(vars, 1, {1, 2, 3}, {3}, {1});

    nfa.add_transition(1, 1, vector<u8>{0});
    nfa.add_transition(1, 2, vector<u8>{0});
    nfa.add_transition(2, 3, vector<u8>{0});

    auto actual_dfa = determinize_nfa(nfa);

    NFA expected_dfa(
        vars, 1,
        {
            1, // {1}
            2, // {1, 2}
            3, // {1, 2, 3}
            4, // trap
        },
        {3},
        {1}
    );
    expected_dfa.add_transition(1, 2, vector<u8>{0});
    expected_dfa.add_transition(1, 4, vector<u8>{1});

    expected_dfa.add_transition(2, 3, vector<u8>{0});
    expected_dfa.add_transition(2, 4, vector<u8>{1});

    expected_dfa.add_transition(3, 3, vector<u8>{0});
    expected_dfa.add_transition(3, 4, vector<u8>{1});

    expected_dfa.add_transition(4, 4, vector<u8>{2});

    assert_dfas_are_isomorphic(expected_dfa, actual_dfa);
}


TEST_CASE("NFA::intersection (simple)") {
    u32 var_ids[] = {1, 2};
    sylvan::BDDSET vars = sylvan::mtbdd_set_from_array(var_ids, 2);

    NFA left_nfa(vars), right_nfa(vars);
    {
        left_nfa.var_count = 2;
        left_nfa.states = {1, 2, 3, 4, 5};
        left_nfa.initial_states = {1};
        left_nfa.final_states = {5};

        left_nfa.add_transition(1, 2, {1, 1});
        left_nfa.add_transition(1, 3, {0, 0});
        left_nfa.add_transition(3, 4, {1, 1});
        left_nfa.add_transition(3, 5, {0, 0});
    }
    {
        right_nfa.var_count = 2;
        right_nfa.states = {1, 2, 3, 4, 5};
        right_nfa.initial_states = {1};
        right_nfa.final_states = {5};

        right_nfa.add_transition(1, 2, {0, 1}); // < differs in 1st bit from left
        right_nfa.add_transition(1, 3, {0, 0});
        right_nfa.add_transition(3, 4, {0, 1}); // < differs in 1st bit from left
        right_nfa.add_transition(3, 5, {0, 0});
    }

    auto result = compute_nfa_intersection(left_nfa, right_nfa);

    NFA expected_nfa(vars, 2u, {1, 2, 3}, {3}, {1});

    expected_nfa.add_transition(1, 2, {0, 0});
    expected_nfa.add_transition(2, 3, {0, 0});
    assert_dfas_are_isomorphic(expected_nfa, result);
}

TEST_CASE("remove_nonfinishing_states :: simple") {
    u32 var_arr[] = {1, 2};
    sylvan::BDDSET vars = sylvan::mtbdd_set_from_array(var_arr, 2);

    NFA dfa(vars, 2, {1, 2, 3, 4, 5, 6}, {3}, {1});
    dfa.add_transition(1, 2, {0, 0});
    dfa.add_transition(2, 3, {0, 0});

    // Transitions to states not reaching any of the final states
    dfa.add_transition(1, 4, {0, 1});
    dfa.add_transition(1, 5, {1, 0});
    dfa.add_transition(2, 5, {1, 1});
    dfa.add_transition(4, 5, {1, 1});

    remove_nonfinishing_states(dfa);

    NFA expected_dfa(vars, 2, {1, 2, 3}, {3}, {1});

    expected_dfa.add_transition(1, 2, {0, 0});
    expected_dfa.add_transition(2, 3, {0, 0});

    assert_dfas_are_isomorphic(expected_dfa, dfa);
}

TEST_CASE("Minimization - already minimal DFA ") {
    u32 var_arr[] = {1};
    sylvan::BDDSET vars = sylvan::mtbdd_set_from_array(var_arr, 1);
    NFA already_minimal_dfa(vars, 1, {1, 2, 3}, {2}, {1});

    already_minimal_dfa.add_transition(1, 1, (std::vector<u8>){0});
    already_minimal_dfa.add_transition(1, 2, (std::vector<u8>){1});
    already_minimal_dfa.add_transition(2, 2, (std::vector<u8>){0});
    already_minimal_dfa.add_transition(2, 3, (std::vector<u8>){1});
    already_minimal_dfa.add_transition(3, 3, (std::vector<u8>){2});

    NFA result = minimize_hopcroft(already_minimal_dfa);

    assert_dfas_are_isomorphic(already_minimal_dfa, result);
}

TEST_CASE("Minimization - Wiki automaton") {
    u32 var_arr[] = {1};
    sylvan::BDDSET vars = sylvan::mtbdd_set_from_array(var_arr, 1);

    NFA input(
        vars, 1,
        {
            1, // a
            2, // b
            3, // c
            4, // d
            5, // e
            6, // f
        },
        {3, 4, 5},
        {1}
    );

    input.add_transition(1, 2, (std::vector<u8>){0});
    input.add_transition(1, 3, (std::vector<u8>){1});

    input.add_transition(2, 1, (std::vector<u8>){0});
    input.add_transition(2, 4, (std::vector<u8>){1});

    input.add_transition(3, 5, (std::vector<u8>){0});
    input.add_transition(3, 6, (std::vector<u8>){1});

    input.add_transition(4, 5, (std::vector<u8>){0});
    input.add_transition(4, 6, (std::vector<u8>){1});

    input.add_transition(5, 5, (std::vector<u8>){0});
    input.add_transition(5, 6, (std::vector<u8>){1});

    input.add_transition(6, 6, (std::vector<u8>){2});

    NFA expected_result(vars, 1, {1, 2, 3}, {2}, {1});

    expected_result.add_transition(1, 1, (std::vector<u8>){0});
    expected_result.add_transition(1, 2, (std::vector<u8>){1});
    expected_result.add_transition(2, 2, (std::vector<u8>){0});
    expected_result.add_transition(2, 3, (std::vector<u8>){1});
    expected_result.add_transition(3, 3, (std::vector<u8>){2});

    NFA result = minimize_hopcroft(input);

    assert_dfas_are_isomorphic(expected_result, result);
}


TEST_CASE("substitute vars with known vars") {
    SUBCASE("Value known due to inequations") {
        // Input :: -x <= -1 && x <= 1 && x - y <=1
        // Output:: -y <=0
        vector<Var_Node> var_nodes = {
            // x0 = x
            {
                .upper_bounds = {1, 2},
                .lower_bounds = {0},
                .equations = {},
                .congruences = {},
                .hard_upper_bound = {.atom_i = 1},
                .hard_lower_bound = {.atom_i = 0},
            },
            // x1 = y
            {.upper_bounds = {}, .lower_bounds = {2}, .equations = {}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {},
            .var_nodes = var_nodes,
            .equations = {},
            .inequations = {
                {.coefs = {-1,  0}, .vars = {0}},
                {.coefs = { 1,  0}, .vars = {0}},
                {.coefs = { 1, -1}, .vars = {0, 1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 0,
            .ineq_cnt = 3,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {-1, 1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_substitution_performed = substitute_vars_with_known_value(&new_graph, &state);
        CHECK(was_any_substitution_performed);

        CHECK( new_graph->inequations[0].is_satisfied);
        CHECK( new_graph->inequations[1].is_satisfied);
        CHECK(!new_graph->inequations[2].is_satisfied);

        if (new_graph != &dep_graph) delete new_graph;

        CHECK(state.get_ineq_val(2) == 0);
    }

    SUBCASE("Value known due to equations") {
        // Input :: (Eq0) x = 1 && (Ineq0) x - y <=1
        // Output:: -y <=0
        vector<Var_Node> var_nodes = {
            // x0 = x
            {
                .upper_bounds = {0},
                .lower_bounds = {},
                .equations = {0},
                .congruences = {},
            },
            // x1 = y
            {.upper_bounds = {}, .lower_bounds = {0}, .equations = {}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {},
            .var_nodes = var_nodes,
            .equations = {
                {.coefs = { 1,  0}, .vars = {0}},
            },
            .inequations = {
                {.coefs = { 1, -1}, .vars = {0, 1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 1,
            .ineq_cnt = 1,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_substitution_performed = substitute_vars_with_known_value(&new_graph, &state);
        CHECK(was_any_substitution_performed);

        CHECK( new_graph->equations[0].is_satisfied);
        CHECK(!new_graph->inequations[0].is_satisfied);

        if (new_graph != &dep_graph) delete new_graph;
    }
}

TEST_CASE("Instantiate quantif with unbound var") {
    SUBCASE("instantiation possible") {
        // Input :: (Ineq0) x - 2y <= 1 &&
        //          (Ineq1) -y <= 1 &&
        //          (Ineq2) z - x <= 0
        // Output:: z - x <= 0
        // Vars x0 = x, x1 = y, x2 = z
        vector<Var_Node> var_nodes = {
            // x0 = x
            {.upper_bounds = {0}, .lower_bounds = {2}, .equations = {}, .congruences = {}},
            // x1 = y
            {.upper_bounds = {}, .lower_bounds = {0, 1}, .equations = {}, .congruences = {}, .hard_lower_bound = {.atom_i = 1}},
            // x2 = z
            {.upper_bounds = {2}, .lower_bounds = {}, .equations = {}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {1},
            .var_nodes = var_nodes,
            .equations = {},
            .inequations = {
                {.coefs = { 1, -2, 0}, .vars = {0, 1}},
                {.coefs = { 0, -1, 0}, .vars = {1}},
                {.coefs = {-1,  0, 1}, .vars = {0, 1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 0,
            .ineq_cnt = 3,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {1, 1, 0}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_quantif_instantiated = instantiate_quantifs_with_inf(&new_graph, &state);
        CHECK(was_any_quantif_instantiated);

        CHECK( new_graph->inequations[0].is_satisfied);
        CHECK( new_graph->inequations[1].is_satisfied);
        CHECK(!new_graph->inequations[2].is_satisfied);

        CHECK(state.get_ineq_val(2) == 0);

        if (new_graph != &dep_graph) delete new_graph;
    }
    SUBCASE("instantiation not possible due to equation") {
        // Input :: (Ineq0) x - 2y <= 1 &&
        //          (Ineq1) -y <= 1 &&
        //          (Eq0)   z - y = 0
        // Output:: z - x <= 0
        // Vars x0 = x, x1 = y, x2 = z
        vector<Var_Node> var_nodes = {
            // x0 = x
            {.upper_bounds = {0}, .lower_bounds = {}, .equations = {}, .congruences = {}},
            // x1 = y
            {.upper_bounds = {}, .lower_bounds = {0, 1}, .equations = {0}, .congruences = {}, .hard_lower_bound = {.atom_i = 1}},
            // x2 = z
            {.upper_bounds = {}, .lower_bounds = {}, .equations = {0}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {1},
            .var_nodes = var_nodes,
            .equations = {
                {.coefs = { 0, -1, 1}, .vars = {1, 2}},
            },
            .inequations = {
                {.coefs = { 1, -2, 0}, .vars = {0, 1}},
                {.coefs = { 0, -1, 0}, .vars = {1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 1,
            .ineq_cnt = 2,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {0, 1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_quantif_instantiated = instantiate_quantifs_with_inf(&new_graph, &state);
        CHECK(!was_any_quantif_instantiated);
        CHECK(new_graph == &dep_graph);
    }
}

TEST_CASE("Instantiate quantifier with c monotonicity") {
    SUBCASE("instantiation possible, no congruence") {
        // Input  :: (Ineq0) x - 2y <= 1 &&
        //           (Ineq1)      y <= 1 &&
        // Output :: x <= 3
        // Vars x0 = x, x1 = y
        vector<Var_Node> var_nodes = {
            // x0 = x
            {.upper_bounds = {0}, .lower_bounds = {}, .equations = {}, .congruences = {}},
            // x1 = y
            {.upper_bounds = {1}, .lower_bounds = {0}, .equations = {}, .congruences = {}, .hard_upper_bound = {.atom_i = 1}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {1},
            .var_nodes = var_nodes,
            .equations = {},
            .inequations = {
                {.coefs = { 1, -2, 0}, .vars = {0, 1}},
                {.coefs = { 0,  1, 0}, .vars = {1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 0,
            .ineq_cnt = 2,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_quantif_instantiated = instantiate_quantifs_with_c_monotonicity(&new_graph, &state);

        CHECK(was_any_quantif_instantiated);
        CHECK(state.get_eq_val(0) == 3);
        CHECK(new_graph->inequations[0].vars == vector<u64>{0});

        if (new_graph != &dep_graph) delete new_graph;
    }
    SUBCASE("instantiation possible, with congruence") {
        // Input  :: (Ineq0) x - 2y <= 1 &&
        //           (Ineq1)      y <= 1 &&
        //           (Congr0)     y  ~ 2 (mod 3)&&
        // Output :: x <= -1
        // Vars x0 = x, x1 = y
        vector<Var_Node> var_nodes = {
            // x0 = x
            {.upper_bounds = {0}, .lower_bounds = {}, .equations = {}, .congruences = {}},
            // x1 = y
            {.upper_bounds = {1}, .lower_bounds = {0}, .equations = {}, .congruences = {0}, .hard_upper_bound = {.atom_i = 1}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {1},
            .var_nodes = var_nodes,
            .equations = {},
            .inequations = {
                {.coefs = { 1, -2, 0}, .vars = {0, 1}},
                {.coefs = { 0,  1, 0}, .vars = {1}},
            },
            .congruences = {
                {.coefs = {0, 1, 0}, .vars = {1}, .modulus_2pow = 0, .modulus_odd = 3},
            },
        };
        Formula_Structure structure = {
            .eq_cnt = 0,
            .ineq_cnt = 2,
            .congruence_cnt = 1,
        };
        Ritch_Conjunction_State state = {.data = {2, 1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_quantif_instantiated = instantiate_quantifs_with_c_monotonicity(&new_graph, &state);
        CHECK(was_any_quantif_instantiated);

        CHECK(!new_graph->inequations[0].is_satisfied);
        CHECK( new_graph->inequations[1].is_satisfied);
        CHECK( new_graph->congruences[0].is_satisfied);

        CHECK(state.get_ineq_val(0) == -1);

        if (new_graph != &dep_graph) delete new_graph;
    }
    SUBCASE("instantiation not possible due to equation") {
        // Input  :: (Ineq0) x - 2y <= 1 &&
        //           (Ineq1)     1y <= 1 &&
        //           (Eq0)   z + 1y  = 1 &&
        // Output :: Nothing is changed
        // Vars x0 = x, x1 = y, x2 = z
        vector<Var_Node> var_nodes = {
            // x0 = x
            {.upper_bounds = {0}, .lower_bounds = {}, .equations = {}, .congruences = {}},
            // x1 = y
            {.upper_bounds = {1}, .lower_bounds = {0}, .equations = {0}, .congruences = {}, .hard_upper_bound = {.atom_i = 1}},
            // x2 = z
            {.upper_bounds = {}, .lower_bounds = {}, .equations = {0}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {1},
            .var_nodes = var_nodes,
            .equations = {
                {.coefs = { 0,  1, 1}, .vars = {1, 2}},
            },
            .inequations = {
                {.coefs = { 1, -2, 0}, .vars = {0, 1}},
                {.coefs = { 0,  1, 0}, .vars = {1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 1,
            .ineq_cnt = 2,
            .congruence_cnt = 0,
        };
        Ritch_Conjunction_State state = {.data = {1, 1, 1}, .formula_structure = structure};

        Dep_Graph* new_graph = &dep_graph;
        bool was_any_quantif_instantiated = instantiate_quantifs_with_c_monotonicity(&new_graph, &state);

        CHECK(!was_any_quantif_instantiated);
        if (new_graph != &dep_graph) delete new_graph;
    }
}

TEST_CASE("congruence linearization - `y - m ~ 0 && 1 <= m <= 4 && y <= -1` (real formula)") {
    // Input  :: (Ineq0) -m <= -1 &&
    //           (Ineq1)  m <=  4 &&
    //           (Ineq2)  y <= -1 &&
    //           (Ineq3)  x - y <= 0 &&
    //           (Congr0) y - m ~ 5

    // Output :: (Ineq0) -m <= -1 &&
    //           (Ineq1)  m <=  4 &&
    //           (Ineq2)  y <= -1 &&
    //           (Ineq3)  x - y <= 0 &&
    //           (Eq0)    y = m + 5
    // Vars x0 = m, x1 = x, x2 = y
    vector<Var_Node> var_nodes = {
        // x0 = m
        {
            .upper_bounds = {1},
            .lower_bounds = {0},
            .equations = {},
            .congruences = {0},
            .hard_upper_bound = {.atom_i = 1}, .hard_lower_bound = {.atom_i = 0}
        },
        // x2 = x
        {.upper_bounds = {3}, .lower_bounds = {}, .equations = {}, .congruences = {}},
        // x1 = y
        {
            .upper_bounds = {2},
            .lower_bounds = {3},
            .equations = {},
            .congruences = {0},
            .hard_upper_bound = {.atom_i = 2}
        },
    };
    Dep_Graph dep_graph = {
        .quantified_vars = {1},
        .var_nodes = var_nodes,
        .equations = {},
        .inequations = {
            {.coefs = {-1,  0, 0}, .vars = {0}},
            {.coefs = { 1,  0, 0}, .vars = {0}},
            {.coefs = { 0,  0, 1}, .vars = {2}},
            {.coefs = { 0,  1,-1}, .vars = {1, 2}},
        },
        .congruences = {
            {.coefs = {-1,  0, 1}, .vars = {0, 2}, .modulus_2pow = 0, .modulus_odd = 5},
        },
    };
    Formula_Structure structure = {.eq_cnt = 0, .ineq_cnt = 4, .congruence_cnt = 1};
    Ritch_Conjunction_State state = {.data = {0, -1, 4, -1, 0}, .formula_structure = structure};

    auto new_graph = &dep_graph;
    auto was_modulus_linearized = linearize_moduli(&new_graph, &state);

    CHECK(was_modulus_linearized);
    CHECK(new_graph->equations.size() == 1);

    auto& eq = new_graph->equations[0];
    CHECK(eq.vars == vector<u64>{0, 2});
    CHECK(eq.coefs == vector<s64>{-1, 0, 1});
    CHECK(state.get_eq_val(0) == -5);
    CHECK(new_graph->congruences[0].is_satisfied);

    if (new_graph != &dep_graph) delete new_graph;
}

TEST_CASE("Max simplification") {
    SUBCASE("Multiple unbound vars") {
        Atom_Allocator alloc;
        Formula formula = make_formula(
            alloc,
            {{{1, 0, 0, -1}, 13}}, // x0 ~ x3
            {},
            {
                {-1, 0, 0, 0},  // 0  <= x0
                {0, -1, 0, 0},  // 23 <= x1
                {-1, 5, 0, 0},  // 5*x1 - x0 <= 0
                {0, 0, -1, 1},  // x3 <= x2
                {0, 0, 0, -1},  // x3 >= 0
                {0, 0, 0,  1}   // x3 <= 12
            },
            {0, 1, 3} // Quantified vars
        );

        auto graph = build_dep_graph(formula);

        Ritch_Conjunction_State state = {.data = {0, 0, -23, 0, 0, 0, 12}, .formula_structure = describe_formula(&formula)};

        Dep_Graph* resulting_graph = &graph;
        bool anything_rewritten = perform_max_simplification_on_graph(&resulting_graph, &state);
        CHECK(anything_rewritten);

        // 0)  0 <= x0, 23 <= x1, 5x1 <= x0, x3 <= x2, x3 >= 0, x3 <= 12, x0 ~ x3
        // 1)  23 <= x1, x3 <= x2, x3 >= 0, x3 <= 12
        // 2)  x3 <= x2, x3 >= 0, x3 <= 12
        // 3)  0 <= x2
        CHECK( resulting_graph->inequations[0].is_satisfied);
        CHECK( resulting_graph->inequations[1].is_satisfied);
        CHECK( resulting_graph->inequations[2].is_satisfied);
        CHECK(!resulting_graph->inequations[3].is_satisfied);
        CHECK( resulting_graph->inequations[4].is_satisfied);
        CHECK( resulting_graph->inequations[5].is_satisfied);
        CHECK( resulting_graph->congruences[0].is_satisfied);

        CHECK(state.get_ineq_val(3) == 0);

        if (anything_rewritten) delete resulting_graph;
    }

    SUBCASE("Presentation formula") {
        Atom_Allocator allocator;
        // m(0) < x < y < z
        const u64 modulus = 299993;
        Formula formula = make_formula(
            allocator,
            {{{1, 0, -1, 0}, modulus}},// m - y ~ 303
            {},
            {
                {0, 1, -1, 0},   // x - y <= -1
                {1, 0, 0, -1},   // m - z <= -1
                {0, 0, 1,  0},   // y <= -1
                {-1, 0, 0, 0},   // -m <= 0
                {1, 0, 0,  0},   // m  <= 0
            },
            {0, 2}
        );

        Dep_Graph graph = build_dep_graph(formula);
        Ritch_Conjunction_State state = {.data = {303, -1, -1, -1, 0, 0}, .formula_structure = describe_formula(&formula)};

        Dep_Graph* res_graph = &graph;
        bool any_rewrite_happen = perform_max_simplification_on_graph(&res_graph, &state);
        CHECK(any_rewrite_happen);

        // 0)  x - y <= -1, m - z <= -1, y <= -1, -m <= 0, m <= 0, m - y ~ 303
        //     |- Instantiate m=0
        // 0)  x - y <= -1, -z <= -1, y <= -1, -y ~ 303
        //     |- Instantiate y=-303
        // 0)  x <= -304, -z <= -1
        CHECK(!res_graph->inequations[0].is_satisfied);
        CHECK(!res_graph->inequations[1].is_satisfied);
        CHECK( res_graph->inequations[2].is_satisfied);
        CHECK( res_graph->inequations[3].is_satisfied);
        CHECK( res_graph->inequations[4].is_satisfied);
        CHECK( res_graph->congruences[0].is_satisfied);

        std::cout << state.data << std::endl;
        CHECK(state.get_ineq_val(0) == -304);
        CHECK(state.get_ineq_val(1) == -1);

        if (any_rewrite_happen) delete res_graph;
    }
}


#if 0
TEST_CASE("Infinite projection with equation") {
    Atom_Allocator allocator;

    Formula formula = make_formula(
        allocator,
        {},
        {{1, -1, -5, 0}},  //  x0 - x1 - 5*x2 = 0
        {
            {1, 0, 0, 0},  //  x0 <= -13
            {0, -1, 0, 0}, //  -x1 <= -1
            {0, 1, 0, 0},  //  x1 <= 5
            {0, 0, 1, -1}, //  x3 - x4 <= 10
        },
        {0, 1, 2}
    );

    auto graph = build_dep_graph(formula);
    identify_potential_variables(graph);

    Formula_Pool pool(&formula);
    Conjunction_State state({0, -13, -1, 5, 10});
    auto result = try_inf_projection_on_equations(graph, pool, state);
    CHECK(result.formula != nullptr);

    vector<s64> expected_state({});
    CHECK(result.state == expected_state);

    CHECK(result.formula->is_top());
}

#endif

TEST_CASE("Test Structured_Macrostate insertions (pareto optimality)") {
    Atom_Allocator alloc;
    Formula formula1 = make_formula(alloc, {{{1, 2}, 3}}, {{1, 2}}, {{1, 2}}, {});

    Intermediate_Macrostate macrostate;

    Conjunction_State post1({1, 2, 3});
    insert_into_post_if_valuable2(macrostate, &formula1, post1);
    CHECK(macrostate.formulae[&formula1].size() == 1);

    insert_into_post_if_valuable2(macrostate, &formula1, post1);
    CHECK(macrostate.formulae[&formula1].size() == 1);

    Conjunction_State post2({1, 2, 4});
    insert_into_post_if_valuable2(macrostate, &formula1, post2);
    CHECK(macrostate.formulae[&formula1].size() == 1);

    insert_into_post_if_valuable2(macrostate, &formula1, post1);
    CHECK(macrostate.formulae[&formula1].size() == 1);


    Conjunction_State post3({1, 3, 4});
    insert_into_post_if_valuable2(macrostate, &formula1, post3);
    CHECK(macrostate.formulae[&formula1].size() == 2);
    CHECK(macrostate.formulae[&formula1][{1, 3}].size() == 1);
    CHECK(macrostate.formulae[&formula1][{1, 2}].size() == 1);


    Formula formula2 = make_formula(alloc, {}, {}, {{1, 2}, {1, 3}}, {});
    Conjunction_State post2_1({1, 1});
    Conjunction_State post2_2({1, 2});
    Conjunction_State post2_3({2, 1});
    Conjunction_State post2_4({2, 2});
    insert_into_post_if_valuable2(macrostate, &formula2, post2_1);
    insert_into_post_if_valuable2(macrostate, &formula2, post2_2);
    insert_into_post_if_valuable2(macrostate, &formula2, post2_3);
    insert_into_post_if_valuable2(macrostate, &formula2, post2_4);

    CHECK(macrostate.formulae[&formula2].size() == 1);
}

TEST_CASE("Test extended Euclidean") {
    CHECK(compute_multiplicative_inverse(900, 37) == 73);
    CHECK(compute_multiplicative_inverse(13, 12) == 12);
}

TEST_CASE("Test get_point_for_mod_congruence_to_obtain_value") {
    SUBCASE("atom `3*y - m = 0 (mod 5)`") {
        Atom_Allocator alloc;
        Formula formula1 = make_formula(alloc, {{{3, -1}, 5}}, {}, {}, {});

        Formula_Allocator formula_allocator (&formula1);

        CHECK(formula1.dep_graph.congruences.size() == 1);
        Congruence_Node& node = formula1.dep_graph.congruences[0];

        Captured_Modulus mod = {.leading_var = 0, .subordinate_var = 1};
        s64 value = get_point_for_mod_congruence_to_obtain_value(node, 0, mod, 0);
        CHECK(value == 0);

        value = get_point_for_mod_congruence_to_obtain_value(node, 0, mod, 3);
        CHECK(value == 1);

        value = get_point_for_mod_congruence_to_obtain_value(node, 0, mod, 4);
        CHECK(value == 3);
    }
    SUBCASE("atom `y - m = 0 (mod 5)` (real formula)") {
        Atom_Allocator alloc;
        Formula formula1 = make_formula(alloc, {{{1, -1}, 5}}, {}, {}, {});
        Formula_Allocator formula_allocator (&formula1);

        CHECK(formula1.dep_graph.congruences.size() == 1);
        Congruence_Node& node = formula1.dep_graph.congruences[0];

        Captured_Modulus mod = {.leading_var = 0, .subordinate_var = 1};
        s64 value = get_point_for_mod_congruence_to_obtain_value(node, 0, mod, 1);
        CHECK(value == 1);

        value = get_point_for_mod_congruence_to_obtain_value(node, 0, mod, 4);
        CHECK(value == 4);
    }
}


TEST_CASE("Test linearize real (benchmark) formula") {
    //  \\exists y (x - y <= 0 && m - z <= 60_000 && y <= -1 && y - m ~ 0 (mod 299_993) && 1 <= m <= 299_992)`

    Atom_Allocator alloc;
    // Vars: m -> x0, x -> x1, y -> x2, z -> x3
    Formula formula = make_formula(alloc,
                                   {{{-1, 0, 1, 0}, 299993}},  // y - m ~ 0 (mod 299_993)
                                   {},                   // No equations
                                   {
                                    {0, 1, -1, 0},       // x - y <= 0
                                    {1, 0, 0, -1},       // m - z <= 60_000
                                    {0, 0, 1, 0},        // y <= -1
                                    {-1, 0, 0, 0},       // -m <= -1  (equivalent to m >= 1)
                                    {1, 0, 0, 0},        // m <= 299_992
                                   },
                                   {});
    Formula_Allocator allocator(&formula);
    Ritch_Conjunction_State state = {
        .data = {0 /*congruence*/, 0, 60000, -1, -1, 299992},
        .formula_structure = describe_formula(&formula)
    };

    Dep_Graph* dep_graph = &formula.dep_graph;

    bool was_linearized = linearize_moduli(&dep_graph, &state);
    CHECK(was_linearized);

    CHECK(dep_graph->congruences.size() <= 1);
    if (dep_graph->congruences.size() == 1) {
        CHECK(dep_graph->congruences[0].is_satisfied);
    }

    CHECK(dep_graph->equations.size() == 1);
    auto& equation = dep_graph->equations[0];
    CHECK(equation.coefs == vector<s64>{-1, 0, 1, 0});
    CHECK(state.data == vector<s64>{0, -299993, 0, 60000, -1, -1, 299992});
}

TEST_CASE("Test shift_interval") {
    SUBCASE("[0, 3] <= -1 with (mod 4)") {
        Interval interval = {.low = 0, .high = 3};
        Var_Preference preference = {.type = Var_Preference_Type::C_INCREASING, .c = -1};
        shift_interval(interval, preference, 4);

        CHECK(interval.high == -1);
        CHECK(interval.low  == -4);
    }

    SUBCASE("[0, 3] <= 10 with (mod 4)") {
        Interval interval = {.low = 0, .high = 3};
        Var_Preference preference = {.type = Var_Preference_Type::C_INCREASING, .c = -1};
        shift_interval(interval, preference, 4);

        CHECK(interval.high == -1);
        CHECK(interval.low  == -4);
    }
}

// TEST_CASE("Test pareto set") {
//     SUBCASE("Pushing identical element") {
//         Pareto_Set set (1);
//         set.insert({1, 2}, 0);
//         set.insert({2, 1}, 0);
//         set.insert({1, 2}, 0);

//         Pareto_Set expected_set(1);
//         expected_set.insert({1, 2}, 0);
//         expected_set.insert({2, 1}, 0);
//         CHECK(set == expected_set);
//     }

//     SUBCASE("Pushing unoptimal element") {
//         Pareto_Set set(1);
//         set.insert({1, 3}, 0);
//         set.insert({1, 2}, 0);

//         Pareto_Set expected_set(1);
//         expected_set.insert({1, 3}, 0);
//         CHECK(set == expected_set);
//     }

//     SUBCASE("Pushing incomparable element") {
//         {
//             Pareto_Set set(0);
//             set.insert({2, 0}, 0);
//             set.insert({1, 2}, 0);

//             Pareto_Set expected_set(0);
//             expected_set.insert({2, 0}, 0);
//             expected_set.insert({1, 2}, 0);
//             CHECK(set == expected_set);
//         }
//     }

//     SUBCASE("Everything is prefix") {
//         Pareto_Set set (2);
//         set.insert({1, 1}, 0);
//         set.insert({1, 2}, 0);

//         Pareto_Set expected_set(2);
//         expected_set.insert({1, 1}, 0);
//         expected_set.insert({1, 2}, 0);
//         CHECK(set == expected_set);
//     }

//     SUBCASE("Merge pareto sets") {
//         Pareto_Set expected_result(1);
//         Pareto_Set* result = nullptr;
//         {
//             Pareto_Set left(1);
//             left.insert({1, 1}, 0);
//             left.insert({2, 1}, 0);

//             Pareto_Set right(1);
//             right.insert({1, 2}, 0);
//             right.insert({2, 0}, 0);
//             right.insert({3, 1}, 0);

//             expected_result.insert({1, 2}, 0);
//             expected_result.insert({2, 1}, 0);
//             expected_result.insert({3, 1}, 0);

//             result = new Pareto_Set(merge_pareto_sets(left, right));
//         }
//         CHECK(*result == expected_result);
//         delete result;
//     }

//     SUBCASE("Pareto set equality") {
//         Pareto_Set left(1);
//         left.insert({1, 1}, 0);

//         Pareto_Set right(1);
//         right.insert({2, 0}, 0);

//         CHECK(left != right);
//     }
// }

// TEST_CASE("Test mtbdd pareto union") {
//     Formula_Structure_Info info = {.prefix_size = 1, .post_size = 2};

//     SUBCASE("Two pareto leaves") {
//         TFA_Pareto_Leaf left_leaf  = {.elements = Pareto_Set(1)};
//         TFA_Pareto_Leaf right_leaf = {.elements = Pareto_Set(1)};
//         left_leaf.elements.insert({1, 2}, 0);
//         right_leaf.elements.insert({1, 3}, 0);

//         MTBDD left  = make_tfa_pareto_leaf(&left_leaf);
//         sylvan::mtbdd_refs_push(left);
//         MTBDD right = make_tfa_pareto_leaf(&right_leaf);
//         sylvan::mtbdd_refs_push(right);
//         MTBDD result = perform_tfa_pareto_union(left, right, &info);
//         sylvan::mtbdd_refs_pop(2);

//         CHECK(sylvan::mtbdd_isleaf(result));
//         CHECK(sylvan::mtbdd_gettype(result) == mtbdd_tfa_pareto_leaf_type_id);

//         auto result_value = reinterpret_cast<TFA_Pareto_Leaf*>(sylvan::mtbdd_getvalue(result));
//         Pareto_Set expected_value(1);
//         expected_value.insert({1, 3}, 0);
//         CHECK(result_value->elements == expected_value);
//     }

//     SUBCASE("One pareto leaf, one intersection") {
//         TFA_Pareto_Leaf left_leaf = {.elements = Pareto_Set(1)};
//         left_leaf.elements.insert({1, 2}, 0);
//         left_leaf.elements.insert({2, 0}, 0);

//         TFA_Leaf_Intersection_Contents right_leaf = {.post = {1, 3}, .is_accepting = true};

//         MTBDD left  = make_tfa_pareto_leaf(&left_leaf);
//         sylvan::mtbdd_refs_push(left);

//         MTBDD right = make_tfa_intersection_leaf(&right_leaf);
//         sylvan::mtbdd_refs_push(right);

//         MTBDD result = perform_tfa_pareto_union(left, right, &info);
//         sylvan::mtbdd_refs_pop(2);

//         CHECK(sylvan::mtbdd_isleaf(result));
//         CHECK(sylvan::mtbdd_gettype(result) == mtbdd_tfa_pareto_leaf_type_id);

//         auto result_value = reinterpret_cast<TFA_Pareto_Leaf*>(sylvan::mtbdd_getvalue(result));
//         Pareto_Set expected_value(1);
//         expected_value.insert({1, 3}, 0);
//         expected_value.insert({2, 0}, 0);
//         CHECK(result_value->elements == expected_value);
//     }
// }

// MTBDD make_cube(const vector<u8>& symbol, const vector<s64>& post, BDDSET& vars) {
//     TFA_Leaf_Intersection_Contents leaf_contents = {.post = post};
//     MTBDD leaf = make_tfa_intersection_leaf(&leaf_contents);
//     vector<u8> mut_symbol = symbol;
//     return sylvan::mtbdd_cube(vars, mut_symbol.data(), leaf);
// }

// TEST_CASE("Test mtbdd pareto projection") {
//     u32 vars_array[] = {1, 2};
//     BDDSET vars = sylvan::mtbdd_set_from_array(vars_array, 2);

//     Formula_Structure_Info formula_structure = {.prefix_size = 1, .post_size = 2};

//     MTBDD input_mtbdd;
//     {
//         MTBDD mtbdd_cubes[3] = {
//             make_cube({0, 0}, {1, 2}, vars),
//             make_cube({0, 1}, {1, 3}, vars),
//             make_cube({1, 0}, {1, 3}, vars),
//         };

//         input_mtbdd = perform_tfa_pareto_union(mtbdd_cubes[0], mtbdd_cubes[1], &formula_structure);
//         input_mtbdd = perform_tfa_pareto_union(input_mtbdd, mtbdd_cubes[2], &formula_structure);
//     }

//     u32 quantif_vars_arr[] = {2};
//     BDDSET quantif_vars = sylvan::mtbdd_set_from_array(quantif_vars_arr, 1);

//     MTBDD output = perform_tfa_pareto_projection(input_mtbdd, quantif_vars, &formula_structure);

//     MTBDD expected_output = sylvan::mtbdd_false;
//     {
//         u32 vars_array[] = {1};
//         BDDSET expected_vars = sylvan::mtbdd_set_from_array(vars_array, 1);

//         MTBDD cubes[2];
//         {
//             TFA_Pareto_Leaf expected_contents = {.elements = Pareto_Set(1)};
//             expected_contents.elements.insert({1, 3});
//             MTBDD expected_leaf = make_tfa_pareto_leaf(&expected_contents);
//             u8 symbol[] = {0};
//             MTBDD expected_cube = sylvan::mtbdd_cube(expected_vars, symbol, expected_leaf);
//             cubes[0] = expected_cube;
//         }
//         {
//             cubes[1] = make_cube({1}, {1, 3}, expected_vars);
//         }

//         expected_output = perform_tfa_pareto_union(cubes[0], cubes[1], &formula_structure);
//     }

//     bool are_eq = check_mtbdds_are_identical(output, output);
//     CHECK(are_eq);
// }

struct Macrostate_Init {
    vector<s64> prefix;
    vector<s64> suffix_data;
    Macrostate_Init(const vector<s64>& prefix, const vector<s64>& suffix_data):
        prefix(prefix), suffix_data(suffix_data) {}
};

Macrostate2 make_macrostate(Block_Allocator& alloc, const vector<Macrostate_Init>& inits, Formula2* formula, bool accepting = false) {
    auto formula_info = formula->describe();
    u64 suffix_size = formula_info.post_size - formula_info.prefix_size;
    Macrostate_Data states;
    for (auto& init: inits) {
        u64 chunk_count = init.suffix_data.empty() ? 0 : init.suffix_data.size() / suffix_size;
        auto suffixes = Chunked_Array<s64>(alloc, init.suffix_data, chunk_count);
        Macrostate_Data::Factored_States entry = {.prefix = init.prefix, .suffixes = suffixes};
        states.states.push_back(entry);
    }
    states.formula = formula;
    vector<Macrostate_Data> data = {states};

    return {.states = data, .accepting = accepting};
}

// TEST_CASE("Leaf macrostate discovery") {
//     u32 vars_array[] = {1, 2};
//     BDDSET vars = sylvan::mtbdd_set_from_array(vars_array, 2);

//     MTBDD input_mtbdd = sylvan::mtbdd_false;
//     Formula2 formula = {
//         .congruences = {},
//         .equations = {Equation2({1, 2}, {1, 1})},
//         .inequations = {Inequation2({1, 2}, {1, -1})},
//         .quantif_vars = sylvan::mtbdd_set_empty()
//     };
//     Formula_Structure_Info info = formula.describe();

//     {
//         MTBDD mtbdd_cubes[3] = {
//             make_cube({0, 0}, {1, 3}, vars),
//             make_cube({0, 1}, {2, 2}, vars),
//             make_cube({1, 0}, {3, 1}, vars),
//         };


//         input_mtbdd = perform_tfa_pareto_union(mtbdd_cubes[0], mtbdd_cubes[1], &info);
//         input_mtbdd = perform_tfa_pareto_union(input_mtbdd, mtbdd_cubes[2], &info);
//     }

//     NFA_Construction_Ctx ctx = {.known_states = {}, .macrostates_to_explore = {}, .structure_info = formula.describe(), .formula = &formula};
//     convert_tfa_leaves_into_macrostates(input_mtbdd, &ctx);

//     std::unordered_set<Macrostate2> expected_macrostates;
//     {
//         Macrostate2 m0 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({1}, {3})}, &formula);
//         Macrostate2 m1 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({2}, {2})}, &formula);
//         Macrostate2 m2 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({3}, {1})}, &formula);

//         expected_macrostates = {m0, m1, m2};
//     };

//     std::unordered_set<Macrostate2> actual_macrostates;
//     for (auto macrostate_ptr: ctx.macrostates_to_explore) {
//         CHECK(macrostate_ptr->states.size() == 1);
//         auto& formula_states = macrostate_ptr->states[0].states;
//         CHECK(formula_states.size() == 1);
//         CHECK(formula_states[0].prefix.size() == 1);
//         CHECK(formula_states[0].suffixes.total_size() == 1);
//         actual_macrostates.insert(*macrostate_ptr);
//     }


//     CHECK(actual_macrostates == expected_macrostates);
// }


BDDSET make_var_set(std::vector<u32>&& vars) {
    return sylvan::mtbdd_set_from_array(vars.data(), vars.size());
}

TEST_CASE("Test macrostate iterator") {
    Block_Allocator alloc;

    Formula2 formula = {
        .congruences = {},
        .equations = {Equation2({1, 2}, {1, 1})},
        .inequations = {Inequation2({1, 2}, {1, -1})},
        .quantif_vars = sylvan::mtbdd_set_empty()
    };

    Macrostate2 m2 = make_macrostate(alloc, {Macrostate_Init({1}, {3, 1}), Macrostate_Init({1}, {2})}, &formula);

    vector<Sized_Array<s64>> seen_elems;
    for (auto iter = m2.begin(); iter != m2.end(); ++iter) {
        Sized_Array<s64> arr = Sized_Array<s64>(alloc, iter->state.size);
        for (s64 i = 0; i < arr.size; i++) {
            arr.items[i] = iter->state.items[i];
        }
        seen_elems.push_back(arr);
    }

    vector<Sized_Array<s64>> expected_elems = {
        Sized_Array<s64>(alloc, {1, 3}),
        Sized_Array<s64>(alloc, {1, 1}),
        Sized_Array<s64>(alloc, {1, 2}),
    };

    CHECK(seen_elems == expected_elems);
}
// TEST_CASE("Explore macrostate") {
//     SUBCASE("no projection") {
//         BDDSET vars = make_var_set({});
//         Formula2 formula = {
//             .congruences = {},
//             .equations = {Equation2({1, 2}, {1, 1})},
//             .inequations = {Inequation2({1, 2}, {1, -1})},
//             .quantif_vars = vars
//         };
//         NFA nfa;
//         NFA_Construction_Ctx ctx = {
//             .known_states = {},
//             .macrostates_to_explore = {},
//             .macrostate_block_alloc = Block_Allocator(),
//             .constructed_nfa = &nfa,
//             .structure_info = {.prefix_size = 1, .post_size = 2},
//             .formula = &formula,
//             .intersection_top = make_tfa_intersection_top(),
//         };

//         Macrostate2 m2 = make_macrostate(ctx.macrostate_block_alloc,
//                                          {Macrostate_Init({1}, {1}), Macrostate_Init({2}, {2})},
//                                          &formula);

//         exp_macrostate(formula, &m2, &ctx);

//         CHECK(ctx.macrostates_to_explore.size() == 3);

//         unordered_set<Macrostate2> expected_macrostates;
//         {
//             // All macrostates must be rejecting because the equation x + y = 1 accepts no 1-bit solution
//             Macrostate2 m0 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({1}, {1})}, &formula, false);
//             Macrostate2 m1 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({0}, {1})}, &formula, false);
//             Macrostate2 m2 = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({0}, {0})}, &formula, false);
//             expected_macrostates.insert(m0);
//             expected_macrostates.insert(m1);
//             expected_macrostates.insert(m2);
//         }

//         unordered_set<Macrostate2> actual_macrostates;
//         for (auto& m: ctx.macrostates_to_explore) {
//             actual_macrostates.insert(*m);
//         }

//         CHECK(expected_macrostates == actual_macrostates);
//     }

//     SUBCASE("with projection") {
//         BDDSET vars = make_var_set({2});
//         Formula2 formula = {
//             .congruences = {},
//             .equations = {Equation2({1, 2}, {1, 1})},
//             .inequations = {Inequation2({1, 2}, {1, -1})},
//             .quantif_vars = vars
//         };
//         NFA nfa;
//         NFA_Construction_Ctx ctx = {
//             .known_states = {},
//             .macrostates_to_explore = {},
//             .macrostate_block_alloc = Block_Allocator(),
//             .constructed_nfa = &nfa,
//             .structure_info = {.prefix_size = 1, .post_size = 2},
//             .formula = &formula,
//             .intersection_top = make_tfa_intersection_top(),
//         };

//         Macrostate2 m = make_macrostate(ctx.macrostate_block_alloc, {Macrostate_Init({1}, {1}), Macrostate_Init({2}, {2})}, &formula);

//         exp_macrostate(formula, &m, &ctx);

//         CHECK(ctx.macrostates_to_explore.size() == 2);
//         unordered_set<Macrostate2> actual_macrostates;
//         for (auto& m: ctx.macrostates_to_explore) {
//             actual_macrostates.insert(*m);
//         }

//         unordered_set<Macrostate2> expected_macrostates;
//         {
//             Macrostate2 m0 = make_macrostate(ctx.macrostate_block_alloc,
//                                              {Macrostate_Init({0}, {1}), Macrostate_Init({1}, {1})},
//                                              &formula,
//                                              false);
//             Macrostate2 m1 = make_macrostate(ctx.macrostate_block_alloc,
//                                              {Macrostate_Init({0}, {1})},
//                                              &formula,
//                                              false);
//             expected_macrostates.insert(m0);
//             expected_macrostates.insert(m1);
//         }

//         CHECK(actual_macrostates == expected_macrostates);
//     }
// }

// TEST_CASE("Construct NFA for atom") {
//     SUBCASE("(<= (- (* 2 x) y) 0") {
//         BDDSET vars = make_var_set({1, 2});
//         // States:
//         // 0 -> 0
//         // 1 -> 0,F
//         // 2 -> -1
//         // 3 -> -1,F
//         // 4 -> -2
//         // 5 -> -2,F
//         NFA expected_result(vars, 2, {0, 1, 2, 3, 4, 5}, {1, 3, 5}, {0});
//         vector<Transition> expected_transitions = {
//             {.from = 0, .to = 1, .symbol = {0, 0}},
//             {.from = 0, .to = 0, .symbol = {0, 1}},
//             {.from = 0, .to = 3, .symbol = {1, 0}},
//             {.from = 0, .to = 3, .symbol = {1, 1}},

//             {.from = 1, .to = 1, .symbol = {0, 0}},
//             {.from = 1, .to = 0, .symbol = {0, 1}},
//             {.from = 1, .to = 3, .symbol = {1, 0}},
//             {.from = 1, .to = 3, .symbol = {1, 1}},

//             {.from = 2, .to = 2, .symbol = {0, 0}},
//             {.from = 2, .to = 0, .symbol = {0, 1}},
//             {.from = 2, .to = 5, .symbol = {1, 0}},
//             {.from = 2, .to = 3, .symbol = {1, 1}},

//             {.from = 3, .to = 2, .symbol = {0, 0}},
//             {.from = 3, .to = 0, .symbol = {0, 1}},
//             {.from = 3, .to = 5, .symbol = {1, 0}},
//             {.from = 3, .to = 3, .symbol = {1, 1}},

//             {.from = 4, .to = 2, .symbol = {0, 0}},
//             {.from = 4, .to = 2, .symbol = {0, 1}},
//             {.from = 4, .to = 5, .symbol = {1, 0}},
//             {.from = 4, .to = 4, .symbol = {1, 1}},

//             {.from = 5, .to = 2, .symbol = {0, 0}},
//             {.from = 5, .to = 2, .symbol = {0, 1}},
//             {.from = 5, .to = 5, .symbol = {1, 0}},
//             {.from = 5, .to = 4, .symbol = {1, 1}},
//         };
//         for (auto& t: expected_transitions) expected_result.add_transition(t.from, t.to, t.symbol.data());

//         Formula2 formula = {
//             .congruences = {},
//             .equations = {},
//             .inequations = {Inequation2({1, 2}, {2, -1})},
//             .quantif_vars = sylvan::mtbdd_set_empty()
//         };

//         Block_Allocator alloc;
//         Formula_Structure_Info info = formula.describe();
//         Macrostate2 initial_macrostate = make_macrostate(alloc, {Macrostate_Init({}, {0})}, &formula);
//         NFA actual_nfa = build_nfa_for_conjunction(formula, initial_macrostate);

//         assert_dfas_are_isomorphic(expected_result, actual_nfa);
//     }

//     SUBCASE("Eq (= (- (* 2 x) y) 0)") {
//         BDDSET vars = make_var_set({1, 2});
//         Formula2 formula = {
//             .congruences = {},
//             .equations = {Equation2({1, 2}, {2, -1})},
//             .inequations = {},
//             .quantif_vars = sylvan::mtbdd_set_empty()
//         };
//         Block_Allocator alloc;
//         Formula_Structure_Info info = formula.describe();

//         Macrostate2 init_macrostate = make_macrostate(alloc, {Macrostate_Init({0}, {})}, &formula);

//         auto actual_nfa = build_nfa_for_conjunction(formula, init_macrostate);

//         NFA expected_nfa(
//             vars, 2,
//             {
//                 0,  // {0}
//                 1,  // {0, F}
//                 2,  // {-1}
//                 3,  // {-1, F}
//                 4,  // Trap
//             },
//             {1, 3},
//             {0}
//         );

//         vector<Transition> symbolic_transitions {
//             // {0}
//             {.from = 0, .to = 1, .symbol = {0, 0}},
//             {.from = 0, .to = 4, .symbol = {0, 1}},
//             {.from = 0, .to = 2, .symbol = {1, 0}},
//             {.from = 0, .to = 4, .symbol = {1, 1}},
//             // {0, F}
//             {.from = 1, .to = 1, .symbol = {0, 0}},
//             {.from = 1, .to = 4, .symbol = {0, 1}},
//             {.from = 1, .to = 2, .symbol = {1, 0}},
//             {.from = 1, .to = 4, .symbol = {1, 1}},
//             // {-1}
//             {.from = 2, .to = 4, .symbol = {0, 0}},
//             {.from = 2, .to = 0, .symbol = {0, 1}},
//             {.from = 2, .to = 4, .symbol = {1, 0}},
//             {.from = 2, .to = 3, .symbol = {1, 1}},
//             // {-1, F}
//             {.from = 3, .to = 4, .symbol = {0, 0}},
//             {.from = 3, .to = 0, .symbol = {0, 1}},
//             {.from = 3, .to = 4, .symbol = {1, 0}},
//             {.from = 3, .to = 3, .symbol = {1, 1}},
//             // Trap
//             {.from = 4, .to = 4, .symbol = {2, 2}},
//         };

//         for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

//         assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
//     }

//     SUBCASE("Co `x + 3y = 1 (mod 3)`") {
//         BDDSET vars = make_var_set({1, 2});
//         Formula2 formula = {
//             .congruences = {Congruence2({1, 2}, {1, -3}, 0, 3)},
//             .equations = {},
//             .inequations = {},
//             .quantif_vars = sylvan::mtbdd_set_empty()
//         };
//         Block_Allocator alloc;

//         Macrostate2 init_macrostate = make_macrostate(alloc, {Macrostate_Init({1}, {})}, &formula);

//         auto actual_nfa = build_nfa_for_conjunction(formula, init_macrostate);

//         NFA expected_nfa(
//             vars, 2,
//             {
//                 0,  // {1}
//                 1,  // {2}
//                 2,  // {2, F}
//                 3,  // {0}
//                 4,  // {0, F}
//             },
//             {2, 4},
//             {0}
//         );

//         vector<Transition> symbolic_transitions {
//             // {1}
//             {.from = 0, .to = 1, .symbol = {0, 2}},
//             {.from = 0, .to = 3, .symbol = {1, 2}},
//             // {2}
//             {.from = 1, .to = 0, .symbol = {0, 2}},
//             {.from = 1, .to = 2, .symbol = {1, 2}},
//             // {2, F}
//             {.from = 2, .to = 0, .symbol = {0, 2}},
//             {.from = 2, .to = 2, .symbol = {1, 2}},
//             // {0}
//             {.from = 3, .to = 4, .symbol = {0, 2}},
//             {.from = 3, .to = 0, .symbol = {1, 2}},
//             // {0, F}
//             {.from = 4, .to = 4, .symbol = {0, 2}},
//             {.from = 4, .to = 0, .symbol = {1, 2}},
//         };

//         for (auto it: symbolic_transitions) expected_nfa.add_transition(it.from, it.to, it.symbol.data());

//         assert_dfas_are_isomorphic(expected_nfa, actual_nfa);
//     }
// }

// Relation(-1.Var(id=11) <= 0),
// Relation(-1.Var(id=2) +1.Var(id=12) <= -449582),
// Relation(-1.Var(id=11) <= -39),
// Relation(+1.Var(id=11) <= 218),
// Relation(-1.Var(id=11) +5.Var(id=12) <= 0),
// Relation(+1.Var(id=11) -5.Var(id=12) <= 4)
TEST_CASE("Symbol vs eager approach") {
    return;
    {
        BDDSET vars = make_var_set({1, 2, 3});
        Formula2 formula = {
            .congruences = {},
            .equations = {},
            .inequations = {
                Inequation2({1}, {-1}),
                Inequation2({1}, {1}),
                Inequation2({1, 3}, {-1, 9}),
                Inequation2({1, 3}, {1, -9}),
                Inequation2({2, 3}, {-1, 1}),
            },
            .quantif_vars = make_var_set({1, 3})
        };
        Block_Allocator alloc;

        Macrostate2 init_macrostate = make_macrostate(
            alloc, {Macrostate_Init({}, {-39, 218, 0, 100, -44982})}, &formula);

        auto actual_nfa = build_nfa_for_conjunction(formula, init_macrostate);
        actual_nfa.perform_pad_closure();
        actual_nfa = determinize_nfa(actual_nfa);
        auto result = minimize_hopcroft(actual_nfa);
    }

    {
        Atom_Allocator allocator;
        vector<vector<s64>> ineqs = {
           {-1,  0,  0},
           { 1,  0,  0},
           {-1,  0,  9},
           { 1,  0, -9},
           { 0, -1,  1},
        };
        Formula formula = make_formula(allocator, {}, {}, ineqs, {0, 2});
        Formula_Pool pool = Formula_Pool(&formula);
        auto formula_id = pool.store_formula(formula);
        Conjunction_State init_state({-39, 218, 0, 100, -44982});

        sylvan::BDDSET vars = make_var_set({1, 2, 3});

        auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);
        std::cout << actual_nfa.states.size() << std::endl;
    }
}

TEST_CASE("Problem") {
    // (exists (x1, x2, x3)
    //    (1*x1 - 1*x2 ~= 0 (mod 21)) &&
    //    ( +1*x5 = 0 ?) &&
    //    ( -1*x2 = 0 ?) &&
    //    ( -1*x3 <= 0 ?) &&
    //    ( +1*x1 <= -86 ?) &&
    //    ( -1*x0 + 1*x4 <= ?) &&
    //    ( -1*x2 <= ?) &&
    //    ( -1*x2 <= ?) &&
    //    ( +1*x2 <= ?) &&
    //    ( -9*x2 + 10*x3 <= ?) &&
    //    ( + 9*x2 - 10*x3 <= ?))
    //   [0, 0, 0, 0, -86, 43, -48, 0, 20, -432, 441]

    Atom_Allocator allocator;
    vector<pair<vector<s64>, s64>> congruences = {
        {{ 0,  1, -1,  0 , 0, 0}, 21}  // (1*x1 - 1*x2 ~= 0 (mod 21))
    };
    vector<vector<s64>> eqs = {
       { 0,  0,  0,  0,  0,  1},  // x5  = 0
       { 0,  0, -1,  0,  0,  0},  // -x2 = 0 ?
    };
    vector<vector<s64>> ineqs = {
       { 0,  0,  0, -1,  0,  0},  //  -x3        <= 0
       { 0,  1,  0,  0,  0,  0},  //   x1        <= -86
       {-1,  0,  0,  0,  1,  0},  //  -x0 + x4   <= 43
       { 0,  0, -1,  0,  0,  0},  //  -x2        <= -48
       { 0,  0, -1,  0,  0,  0},  //  -x2        <= 0
       { 0,  0,  1,  0,  0,  0},  //   x2        <= 20
       { 0,  0, -9, 10,  0,  0},  // -9x2 + 10x3 <= -432
       { 0,  0,  9, 10,  0,  0},  //  9x2 - 10x3 <= 441
     };

    Formula formula = make_formula(allocator, congruences, eqs, ineqs, {1, 2, 3});
    Formula_Pool pool = Formula_Pool(&formula);
    auto formula_id = pool.store_formula(formula);
    Conjunction_State init_state({0, 0, 0, 0, -86, 43, -48, 0, 20, -432, 441});

    sylvan::BDDSET vars = make_var_set({1, 2, 3, 4, 5, 6});
    auto actual_nfa = build_nfa_with_formula_entailement(formula_id, init_state, vars, pool);
}

TEST_CASE("Watched formula rewrite") {
    SUBCASE("Values matched") {
        // Input :: -x <= 0 && x <= 0 && x - y <=1
        // Output:: -y <= 1
        Watched_Position_Pair watched_positions = {
            .position0 = 0,
            .position1 = 1,
            .required_value0 = 0,
            .required_value1 = 0,
        };
        vector<Var_Node> var_nodes = {
            // x0 = x
            {
                .upper_bounds = {1, 2},
                .lower_bounds = {0},
                .equations = {},
                .congruences = {},
                .hard_upper_bound = {.atom_i = 1},
                .hard_lower_bound = {.atom_i = 0},
            },
            // x1 = y
            {.upper_bounds = {}, .lower_bounds = {2}, .equations = {}, .congruences = {}},
        };
        Dep_Graph dep_graph = {
            .quantified_vars = {},
            .watched_positions = {watched_positions},
            .var_nodes = var_nodes,
            .equations = {},
            .inequations = {
                {.coefs = {-1,  0}, .vars = {0}},
                {.coefs = { 1,  0}, .vars = {0}},
                {.coefs = { 1, -1}, .vars = {0, 1}},
            },
            .congruences = {},
        };
        Formula_Structure structure = {
            .eq_cnt = 0,
            .ineq_cnt = 3,
            .congruence_cnt = 0,
        };
        Conjunction_State state ({0, 0, 1});

        Dep_Graph* res_graph = &dep_graph;
        bool anything_rewritten = perform_watched_rewrites(&res_graph, &state);

        CHECK(anything_rewritten);

        CHECK( res_graph->inequations[0].is_satisfied);
        CHECK( res_graph->inequations[1].is_satisfied);
        CHECK(!res_graph->inequations[2].is_satisfied);

        if (res_graph != &dep_graph) delete res_graph;
    }
}

void add_all_transitions_to_nfa(NFA& nfa, const std::vector<Transition>& transitions) {
    for (auto it: transitions) nfa.add_transition(it.from, it.to, it.symbol.data());
}

TEST_CASE("Test bit_set pad closure") {
    Bit_Set::Block_Arena_Allocator allocator = Bit_Set::create_allocator_for_n_states(0, 0);
    g_solver_context->bit_set_alloc = &allocator;
    SUBCASE("Simple (distance 2)") {
        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);

        NFA nfa (
            vars, 1,
            {0, 1, 2, 3}, {3}, {0}
        );

        vector<Transition> transitions {
            {.from = 0, .to = 1, .symbol = {1}},
            {.from = 1, .to = 2, .symbol = {1}},
            {.from = 2, .to = 3, .symbol = {1}},
        };

        add_all_transitions_to_nfa(nfa, transitions);

        allocator.start_new_generation(nfa.states.size());
        NFA result = do_pad_closure_using_bit_sets(&nfa, &allocator);

        CHECK(result.states == std::set<State>({0, 1, 2, 3, 4}));
        CHECK(result.final_states == std::set<State>({3, 4}));

        std::vector<Transition> needle_transitions = {
            {.from = 0, .to = 4, .symbol = {1}},
            {.from = 1, .to = 4, .symbol = {1}}
        };

        for (auto& needle_transition: needle_transitions) {
            auto actual_transitions = result.get_symbolic_transitions_for_state(needle_transition.from);
            auto needle_pos = std::find(actual_transitions.begin(), actual_transitions.end(), needle_transition);
            if (needle_pos == actual_transitions.end()) {
                std::cout << "Transition " << needle_transition << " has not been added during pad closure\n";
            }
            CHECK(needle_pos != actual_transitions.end());
        }
    }

    SUBCASE("Simple (multiple symbols)") {
        std::cout << "Simple!" << std::endl;
        sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
        vars = sylvan::mtbdd_set_add(vars, 1);
        vars = sylvan::mtbdd_set_add(vars, 2);
        u64 var_count = 2;

        NFA nfa (
            vars, var_count,
            {0, 1, 2, 3, 4}, {3}, {0}
        );

        vector<Transition> transitions {
            {.from = 0, .to = 1, .symbol = {1, 0}},
            {.from = 1, .to = 2, .symbol = {1, 0}},
            {.from = 2, .to = 3, .symbol = {1, 0}},
            {.from = 0, .to = 4, .symbol = {0, 1}},
            {.from = 4, .to = 3, .symbol = {0, 1}},
        };

        add_all_transitions_to_nfa(nfa, transitions);

        allocator.start_new_generation(nfa.states.size());
        NFA result = do_pad_closure_using_bit_sets(&nfa, &allocator);

        CHECK(result.states == std::set<State>({0, 1, 2, 3, 4, 5}));
        CHECK(result.final_states == std::set<State>({3, 5}));

        std::vector<Transition> needle_transitions = {
            {.from = 0, .to = 5, .symbol = {1, 0}},
            {.from = 0, .to = 5, .symbol = {0, 1}}
        };

        auto actual_transitions = result.get_symbolic_transitions_for_state(0);
        for (auto& needle_transition: needle_transitions) {
            auto needle_pos = std::find(actual_transitions.begin(), actual_transitions.end(), needle_transition);
            if (needle_pos == actual_transitions.end()) {
                std::cout << "Transition " << needle_transition << " has not been added during pad closure\n";
            }
            CHECK(needle_pos != actual_transitions.end());
        }
    }
}

int main(int argc, char* argv[]) {
    init_machinery();

    doctest::Context context(argc, argv);

    int test_overall_rc = context.run();

    if(context.shouldExit()) {
        return test_overall_rc;
    }

    shutdown_machinery();

    return 0;
}
