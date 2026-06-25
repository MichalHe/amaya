#include "../include/hopcroft_leaf.hpp"
#include "../include/custom_leaf.hpp"
#include "../include/base.hpp"
#include "../include/wrapper.hpp"
#include "../include/operations.hpp"

#include <sylvan.h>
#include <sylvan_common.h>
#include <sylvan_mtbdd.h>

#include <iostream>
#include <set>
#include <vector>
#include <utility>
#include <assert.h>
#include <string>
#include <unordered_map>
#include <sstream>

using namespace sylvan;
using namespace std;

enum Test_Result {
    TEST_RESULT_OK   = 0,
    TEST_RESULT_FAIL = 1,
};


struct Report {
    vector<string> errors;
};

MTBDD create_transition_mtbdd(BDDSET variables, vector<uint8_t>& var_value, std::vector<State>&& dest_states)
{
    Transition_Destination_Set tds;
    tds.destination_set = new std::set<State>(dest_states.begin(), dest_states.end());

    sylvan::MTBDD leaf = sylvan::mtbdd_makeleaf(mtbdd_leaf_type_set, (uint64_t) &tds);
    sylvan::MTBDD mtbdd = sylvan::mtbdd_cube(variables, var_value.data(), leaf);

    return mtbdd;
}

inline MTBDD mtbdd_union(MTBDD a, MTBDD b)
{
    LACE_ME;
    return mtbdd_applyp(a, b, 0, TASK(transitions_union_op), AMAYA_UNION_OP_ID);
}


enum Test_Result try_matching_expected_transitions_onto_dfa(
        struct NFA& dfa,
        vector<Transition>& expected_transitions,
        struct Report& report,
        const std::string error_prexix)
{
    vector<Transition> transitions = nfa_unpack_transitions(dfa);

    if (transitions.size() != expected_transitions.size()) {
        stringstream str_stream;
        str_stream << "Invalid number of transitions: expected=" << expected_transitions.size() << ", actual=" << transitions.size();
        report.errors.push_back(str_stream.str());
    }

    // Note that there is no order enforced on how are state numbers assigned to the computed equivalence classes.
    // Therefore, we have build the potential isomorphism while testing
    const State uninit_isomorphism = dfa.states.size();
    State automaton_isomorphism[dfa.states.size()] = {0}; // Utilize the fact that our expected automaton has states labeled from 1..N-1 - array indices

    for (uint64_t i = 0; i < dfa.states.size(); i++) automaton_isomorphism[i] = uninit_isomorphism;

    automaton_isomorphism[0] = *dfa.initial_states.begin();

    for (auto expected_transition: expected_transitions) {

        // Search for a matching transition
        auto transitions_iter = transitions.begin();
        for (; transitions_iter != transitions.end(); transitions_iter++) {
            // Do only a partial match, so we can gradually discover the isomorphism

            State expected_origin_after_isomorphism = automaton_isomorphism[expected_transition.origin];
            if (expected_origin_after_isomorphism == uninit_isomorphism) continue; // The state has not been mapped yet

            if (expected_origin_after_isomorphism == (*transitions_iter).origin && expected_transition.symbols == (*transitions_iter).symbols) {
                break;
            }
        }

        // Handle no matching transition found
        if (transitions_iter == transitions.end()) {
            stringstream str_stream;
            str_stream << error_prexix
                       << "Expected transition was not present in the minimized automaton: "
                       << transition_to_str(expected_transition);
            report.errors.push_back(str_stream.str());
            return TEST_RESULT_FAIL;
        }

        // Try extending the partial isomorphism. If a conflict is detected (e.g. it is not an injection) raise error
        State expected_destination_after_isomorphism = automaton_isomorphism[expected_transition.destination];

        if (expected_destination_after_isomorphism == uninit_isomorphism) {
            // The state is not contained in the isomorphism
            automaton_isomorphism[expected_transition.destination] = (*transitions_iter).destination;
        } else {
            // Check that the actual state contained in the isomorphism for the expected automaton state is the same the one given by current transition
            if (expected_destination_after_isomorphism != (*transitions_iter).destination) {
                stringstream str_stream;
                str_stream << "Detected a conflict while creating the isomorphism between the actual minimized DFA and the expected one. "
                           << "Stored isomorphism: (" << expected_transition.destination << " -> "
                           << expected_destination_after_isomorphism << "), conflicts with ("
                           << expected_transition.destination << " -> " << (*transitions_iter).destination << ")";
                report.errors.push_back(str_stream.str());
                return TEST_RESULT_FAIL;
            }
        }
    }

    return TEST_RESULT_OK;
}


enum Test_Result test_minimize_hopcroft(struct Report& report)
{
    //auto dfa = make_dfa_to_minimize();
    //minimize_hopcroft(dfa);
    BDDSET variables = sylvan::mtbdd_set_empty();
    variables = sylvan::mtbdd_set_add(variables, 1);

    vector<uint8_t> symbols[] = {
        {0},
        {1},
    };

    // States: A=0, B=1, C=2, D=3, E=4, F=5
    // Final:  C=2, D=3, E=4
    struct NFA dfa = {
        .states{0, 1, 2, 3, 4, 5},
        .final_states{2, 3, 4},
        .initial_states{1},
        .transitions{
            // (A, 0, B), (A, 1, C)
            {0, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {1}), create_transition_mtbdd(variables, symbols[1], {2}))},
            // (B, 0, B), (B, 1, D)
            {1, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {0}), create_transition_mtbdd(variables, symbols[1], {3}))},
            // (C, 0, E), (C, 1, F)
            {2, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {4}), create_transition_mtbdd(variables, symbols[1], {5}))},
            // (D, 0, E), (D, 1, F)
            {3, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {4}), create_transition_mtbdd(variables, symbols[1], {5}))},
            // (E, 0, E), (E, 1, F)
            {4, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {4}), create_transition_mtbdd(variables, symbols[1], {5}))},
            // (F, 0, F), (F, 1, F)
            {5, mtbdd_union(create_transition_mtbdd(variables, symbols[0], {5}), create_transition_mtbdd(variables, symbols[1], {5}))},
        },
        .vars = variables,
        .var_count = 1
    };

    auto minimized_dfa = minimize_hopcroft(dfa);

    if (minimized_dfa.states.size() != 3) report.errors.push_back("Minimized DFA has wrong number of states.");
    if (minimized_dfa.final_states.size() != 1) report.errors.push_back("Minimized DFA has wrong number of final states.");
    if (minimized_dfa.initial_states.size() != 1) report.errors.push_back("Minimized DFA has wrong number of initial states.");

    auto transitions = nfa_unpack_transitions(minimized_dfa);

    // The resulting automaton structure is written in a fashion allowing for building the isomorphism
    vector<Transition> expected_transitions{
        {.origin = 0, .destination = 0, .symbols = {0}},
        {.origin = 0, .destination = 1, .symbols = {1}},
        {.origin = 1, .destination = 1, .symbols = {0}},
        {.origin = 1, .destination = 2, .symbols = {1}},
        {.origin = 2, .destination = 2, .symbols = {0}},
        {.origin = 2, .destination = 2, .symbols = {1}},
    };

    return try_matching_expected_transitions_onto_dfa(minimized_dfa, expected_transitions, report, "Minimization#1 ");
}


enum Test_Result test_minimize_hopcroft2(struct Report& report) {
    BDDSET vars = sylvan::mtbdd_set_empty();
    vars = sylvan::mtbdd_set_add(vars, 1);

    vector<uint8_t> symbols[] = {{0}, {1}};  // a=0, b=1

    // q0 = 0, ...., q4 = 4
    struct NFA dfa = {
        .states = {0, 1, 2, 3, 4},
        .final_states = {4},
        .initial_states = {0},
        .transitions = {
            {0, mtbdd_union(create_transition_mtbdd(vars, symbols[0], {1}), create_transition_mtbdd(vars, symbols[1], {2}))},
            {1, mtbdd_union(create_transition_mtbdd(vars, symbols[0], {1}), create_transition_mtbdd(vars, symbols[1], {3}))},
            {2, mtbdd_union(create_transition_mtbdd(vars, symbols[0], {1}), create_transition_mtbdd(vars, symbols[1], {2}))},
            {3, mtbdd_union(create_transition_mtbdd(vars, symbols[0], {1}), create_transition_mtbdd(vars, symbols[1], {4}))},
            {4, mtbdd_union(create_transition_mtbdd(vars, symbols[0], {1}), create_transition_mtbdd(vars, symbols[1], {2}))},
        },
        .vars = vars,
        .var_count = 1,
    };

    auto minimized_dfa = minimize_hopcroft(dfa);

    if (minimized_dfa.states.size() != 4) {
        stringstream str_stream;
        str_stream << "Minimization #2: Automaton has unexpected number of states. #states=" << minimized_dfa.states.size();
        report.errors.push_back(str_stream.str());
        return TEST_RESULT_FAIL;
    }

    if (minimized_dfa.initial_states.size() != 1) {
        stringstream str_stream;
        str_stream << "Minimization #2: Automaton has unexpected number of initial states. #initial_states=" << minimized_dfa.initial_states.size();
        report.errors.push_back(str_stream.str());
        return TEST_RESULT_FAIL;
    }

    if (minimized_dfa.final_states.size() != 1) {
        stringstream str_stream;
        str_stream << "Minimization #2: Automaton has unexpected number of final states. #final_states=" << minimized_dfa.initial_states.size();
        report.errors.push_back(str_stream.str());
        return TEST_RESULT_FAIL;
    }

    // 0 = {q0, q2}, 1 = {q1}, 2 = {q3}, 2 = {q4}
    vector<Transition> expected_transitions = {
        {.origin = 0, .destination = 1, symbols[0]},
        {.origin = 0, .destination = 0, symbols[1]},
        {.origin = 1, .destination = 1, symbols[0]},
        {.origin = 1, .destination = 2, symbols[1]},
        {.origin = 2, .destination = 1, symbols[0]},
        {.origin = 2, .destination = 3, symbols[1]},
        {.origin = 3, .destination = 1, symbols[0]},
        {.origin = 3, .destination = 0, symbols[1]},
    };

    try_matching_expected_transitions_onto_dfa(minimized_dfa, expected_transitions, report, "Minimization#2 ");

    return TEST_RESULT_OK;
}


enum Test_Result test_unpack_nfa_transitions(struct Report& report)
{
    BDDSET variables = sylvan::mtbdd_set_empty();
    variables = sylvan::mtbdd_set_add(variables, 1);
    variables = sylvan::mtbdd_set_add(variables, 2);

    vector<uint8_t> symbols[] = {
        {0, 0},
        {0, 1},
        {1, 0},
        {1, 1},
    };
    struct NFA nfa = {
        .states = {0, 1}, // A = 0, B = 1
        .final_states = {},
        .initial_states = {},
        .transitions{
            // (A, (0, 1), A), (A, (1, 0), B)
            {0, mtbdd_union(create_transition_mtbdd(variables, symbols[1], {0}), create_transition_mtbdd(variables, symbols[2], {1}))},
            // (B, (1, 0), B), (B, (1, 1), B)
            {1, mtbdd_union(create_transition_mtbdd(variables, symbols[2], {1}), create_transition_mtbdd(variables, symbols[3], {1}))},
        },
        .vars = variables,
        .var_count = 2
    };

    auto transitions = nfa_unpack_transitions(nfa);

    vector<struct Transition> expected_transitions = {
        {.origin = 0, .destination = 0, .symbols = {0, 1}},
        {.origin = 0, .destination = 1, .symbols = {1, 0}},
        {.origin = 1, .destination = 1, .symbols = {1, 0}},
        {.origin = 1, .destination = 1, .symbols = {1, 1}},
    };

#if DEBUG
    std::cout << "Actual transitions size: " << transitions.size() << ", expected transitions size: " << expected_transitions.size() << std::endl;
#endif
    if (transitions.size() != expected_transitions.size()) {
        stringstream str_stream;
        str_stream << "Unpack transitions: #expected_transitions != #actual_transitions: "
                   << expected_transitions.size() << " != " << transitions.size();
        report.errors.push_back(str_stream.str());
        return TEST_RESULT_FAIL;
    }

    bool any_transition_not_found_in_expected_transitions = false;
    for (auto transition: transitions) {
        bool expected_transition_found = false;
        for (auto expected_transition: expected_transitions) {
            if (transition_is_same_as(transition, expected_transition)) expected_transition_found = true;
        }
        if (!expected_transition_found) {
            stringstream str_stream;
            str_stream << "Failed to find an unpacked transition in the expected transitions. Transition=" << transition_to_str(transition);
            report.errors.push_back(str_stream.str());
            any_transition_not_found_in_expected_transitions = true;
        }
    }

    if (any_transition_not_found_in_expected_transitions) return TEST_RESULT_FAIL;
    return TEST_RESULT_OK;
}


int main()
{
    init_machinery();
    LACE_ME;

    struct Report report = {.errors = {}};
    uint64_t overall_result = TEST_RESULT_OK;

    overall_result |= test_minimize_hopcroft(report);
    overall_result |= test_minimize_hopcroft2(report);
    overall_result |= test_unpack_nfa_transitions(report);

    if (report.errors.size() > 0) {
        std::cout << "Errors:" << std::endl;
        for (auto error: report.errors) {
            std::cout << error << std::endl;
        }
    } else {
        std::cout << "All passed." << std::endl;;
    }

    return overall_result;
}
