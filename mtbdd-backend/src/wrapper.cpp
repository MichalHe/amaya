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

static bool DEBUG_ON = false;

extern void*    REMOVE_STATES_OP_PARAM;
extern uint64_t   REMOVE_STATES_OP_COUNTER;
extern void*    ADD_TRAPSTATE_OP_PARAM;
extern uint64_t   ADD_TRAPSTATE_OP_COUNTER;

extern uint64_t         STATE_RENAME_OP_COUNTER;
extern State_Rename_Op_Info   *STATE_RENAME_OP_PARAM;

NFA deserialize_nfa(Serialized_NFA& serialized_nfa) {
    // Deserialize the DFA

    sylvan::BDDSET vars = sylvan::mtbdd_set_empty();
    sylvan::mtbdd_refs_push(vars);
    for (u64 i = 0; i < serialized_nfa.var_count; i++) {
        vars = sylvan::mtbdd_set_add(vars, serialized_nfa.vars[i]);
        sylvan::mtbdd_refs_pop(1);
        sylvan::mtbdd_refs_push(vars);
    }
    NFA nfa(vars, serialized_nfa.var_count);
    sylvan::mtbdd_refs_pop(1);

    for (u64 i = 0; i < serialized_nfa.state_count; i++){
        nfa.states.insert(serialized_nfa.states[i]);
        nfa.transitions[serialized_nfa.states[i]] = serialized_nfa.mtbdds[i];
    }

    for (u64 i = 0; i < serialized_nfa.final_state_count; i++) nfa.final_states.insert(serialized_nfa.final_states[i]);
    for (u64 i = 0; i < serialized_nfa.initial_state_count; i++) nfa.initial_states.insert(serialized_nfa.initial_states[i]);


    return nfa;
}

Serialized_NFA* serialize_nfa(NFA& nfa) {
    Serialized_NFA* serialized_nfa = (Serialized_NFA*) malloc(sizeof(Serialized_NFA));
    assert(serialized_nfa != nullptr);

    set<State>::iterator state_it;
    uint64_t i = 0;

    serialized_nfa->states = (State*) malloc(sizeof(State) * nfa.states.size()); assert(serialized_nfa->states != nullptr);
    for (state_it = nfa.states.begin(), i = 0; state_it != nfa.states.end(); state_it++, i++) {
        serialized_nfa->states[i] = *state_it;
    }
    serialized_nfa->state_count = nfa.states.size();

    serialized_nfa->final_states = (State*) malloc(sizeof(State) * nfa.final_states.size());
    assert(serialized_nfa->final_states != nullptr);
    for (state_it = nfa.final_states.begin(), i = 0; state_it != nfa.final_states.end(); ++state_it, i++) {
        serialized_nfa->final_states[i] = *state_it;
    }
    serialized_nfa->final_state_count = nfa.final_states.size();

    serialized_nfa->initial_states = (State*) malloc(sizeof(State) * nfa.initial_states.size());
    assert(serialized_nfa->initial_states);
    for (state_it = nfa.initial_states.begin(), i = 0; state_it != nfa.initial_states.end(); ++state_it, i++) {
        serialized_nfa->initial_states[i] = *state_it;
    }
    serialized_nfa->initial_state_count = nfa.initial_states.size();

    serialized_nfa->mtbdds = (sylvan::MTBDD*) malloc(sizeof(sylvan::MTBDD) * nfa.states.size());
    assert(serialized_nfa->mtbdds);

    i = 0;
    for (State state: nfa.states) {
        serialized_nfa->mtbdds[i] = nfa.transitions[state];
        i++;
    }

    u64* used_vars = (u64*) malloc(sizeof(u64) * nfa.var_count);
    { // Extract variables from BDD set into a temporary u32 array and move them into u64 one
        u32 bdd_vars[nfa.var_count];
        sylvan::mtbdd_set_to_array(nfa.vars, bdd_vars);
        for (u64 i = 0; i < nfa.var_count; i++) {
            used_vars[i] = bdd_vars[i];
        }
    }
    serialized_nfa->vars      = used_vars;
    serialized_nfa->var_count = nfa.var_count;

    return serialized_nfa;
}

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

MTBDD amaya_mtbdd_build_single_terminal(
    uint8_t*  transition_symbols,  // 2D array of size (variable_count) * transition_symbols_count
    uint32_t  transition_symbols_count,
    uint32_t  variable_count,
    State*    destination_set,
    uint32_t  destination_set_size)
{
    // CALL(mtbdd_union_cube(mtbdd, variables, cube, terminal)
    // Cube (transitions symbols) have to be in format -- suppose the transition_symbols are ready
    // x_0 = 0  ===> low transition
    // x_0 = 1  ===> high transition
    // x_0 = 2  ===> any
    // Construct variables set containing all the variables.
    BDDSET variables = mtbdd_set_empty();
    for (uint32_t i=1; i <= variable_count; i++) {
        variables = mtbdd_set_add(variables, i); // Variables are numbered from 1
    }

    // Construct the destination set

    Transition_Destination_Set leaf_contents;
    for (uint32_t i = 0; i < destination_set_size; i++) {
        leaf_contents.insert(destination_set[i]);
    }
    leaf_contents.sort();

    MTBDD leaf = make_set_leaf(&leaf_contents);

    // Construct the initial MTBDD, then add the rest of the symbols
    // signature: mtbdd_cube(MTBDD variables, uint8_t *cube, MTBDD terminal)
    // initial_cube = transition_symbols[0*variable_count + (0..variable_count)] (size: variable_count)
    MTBDD mtbdd = mtbdd_cube(variables, transition_symbols, leaf);

    LACE_ME;
    for (uint32_t i = 1; i < transition_symbols_count; i++) {
        // Cube for this iteration:
        //   i*variable_count + (0..variable_count)
        mtbdd = CALL(mtbdd_union_cube, mtbdd, variables, &transition_symbols[i*variable_count], leaf);
    }

    return mtbdd;
}

Transition_Destination_Set* _get_transition_target(
    MTBDD root,
    uint32_t current_variable,
    uint8_t* variable_assigments,
    uint32_t var_count)
{
    int is_leaf = mtbdd_isleaf(root);
    if (var_count == 0) {
        if (is_leaf) {
            if (root == mtbdd_false) return NULL;
            auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(root));
            auto leaf_contents_copy = new Transition_Destination_Set(*leaf_contents);
            return leaf_contents_copy;
        } else {
        // We have exhausted all variables, yet we did not hit a leaf.
        // That means the cube did not contain all the variables.
        return NULL;  // Not enough information to decide.
        }
    }

    if (is_leaf) {
        if (root == mtbdd_false) return NULL;
        else {
            // Found a solution
            auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(root));
            auto leaf_contents_copy = new Transition_Destination_Set(*leaf_contents);
            return leaf_contents_copy;
        }
    }

    // If we got here then root is not a leaf and we still have some variables
    uint32_t root_var = mtbdd_getvar(root);

    if (root_var == current_variable) {
        if (*variable_assigments == 0) {
            // Go low
            return _get_transition_target(mtbdd_getlow(root), current_variable + 1, variable_assigments + 1, var_count - 1);
        } else if (*variable_assigments == 1) {
            // Go high
            return _get_transition_target(mtbdd_gethigh(root), current_variable + 1, variable_assigments + 1, var_count - 1);
        } else {
            // That means that the current assigment is don't care (2)
            // Then we need to explore both branches and return the results
            auto low_tds  = _get_transition_target(mtbdd_getlow(root), current_variable + 1, variable_assigments + 1, var_count - 1);
            auto high_tds = _get_transition_target(mtbdd_gethigh(root), current_variable + 1, variable_assigments + 1, var_count - 1);

            // Now decide what to do with the results
            if (low_tds == NULL) return high_tds; // Might return NULL
            if (high_tds == NULL) return low_tds; // The low result is not NULL

            // Perform state merging.
            std::vector<State> reachable_states;
            std::set_union(low_tds->destination_set.begin(), low_tds->destination_set.end(),
                           high_tds->destination_set.begin(), high_tds->destination_set.end(),
                           std::inserter(reachable_states, reachable_states.begin()));
            low_tds->destination_set = reachable_states;

            delete high_tds; // Only low result will be propagated upwards
            return low_tds;
        }
    } else {
        // The current variable in the tree skipped a variable. That means the current variable assignment did not
        // matter and we can just move to the next variable (current_variable + 1)
        return _get_transition_target(root, current_variable + 1, variable_assigments + 1, var_count - 1);
    }
}

State* amaya_mtbdd_get_transition_target(MTBDD mtbdd, uint8_t* cube, uint32_t cube_size, uint32_t* result_size) {
    auto search_result_tds = _get_transition_target(mtbdd, 1, cube, cube_size);
    if (search_result_tds == NULL) {
        *result_size = 0;
        return NULL;
    } else {
        const uint32_t rs = search_result_tds->destination_set.size();
        *result_size = rs;
        auto result_arr = (State*) malloc(sizeof(uint32_t) * rs);
        uint32_t i = 0;
        for (auto state : search_result_tds->destination_set) {
           result_arr[i++] = state;
        }
        return result_arr;
    }
}

void amaya_do_free(void *ptr) {
  free(ptr);
}


void collect_mtbdd_leaves(MTBDD root, std::set<MTBDD>& dest) {
    LACE_ME;
    MTBDD support = mtbdd_support(root);
    uint32_t support_size = mtbdd_set_count(support);

    // Stores the tree path to the leaf
    uint8_t* arr = (uint8_t*) malloc(sizeof(uint8_t) * support_size);

    MTBDD leaf = mtbdd_enum_first(root, support, arr, NULL);

    while (leaf != mtbdd_false) {
        dest.insert(leaf);
        leaf = mtbdd_enum_next(root, support, arr, NULL);
    }

    free(arr);
}

MTBDD* amaya_mtbdd_rename_states(
    MTBDD*    mtbdd_roots,
    uint32_t  root_count,
    State*    names, // [(old, new), (old, new), (old, new)]
    uint32_t  name_count)
{
    State old_state, new_state;

    std::map<State, State> state_names_map;
    for (uint32_t i = 0; i < name_count; i++) {
        old_state = names[2*i];
        new_state = names[2*i + 1];
        state_names_map.insert(std::make_pair(old_state, new_state));
    }

    State_Rename_Op_Info op_info = {0};
    op_info.states_rename_map = &state_names_map;
    STATE_RENAME_OP_PARAM = &op_info;

    auto renamed_mtbdds = (MTBDD*) malloc(sizeof(MTBDD) * root_count);
    assert(renamed_mtbdds != NULL);

    LACE_ME;
    for (uint32_t i = 0; i < root_count; i++) {
        MTBDD result = mtbdd_uapply(mtbdd_roots[i], TASK(rename_states_op), STATE_RENAME_OP_COUNTER);
        mtbdd_ref(result);
        renamed_mtbdds[i] = result;
    }
    STATE_RENAME_OP_COUNTER += (1LL << 32);

    return renamed_mtbdds;
}


State* amaya_mtbdd_get_leaves(
    MTBDD root,
    uint32_t** leaf_sizes,  // OUT, Array containing the sizes of leaves inside dest
    uint32_t*  leaf_cnt,  // OUT, Number of leaves in the tree
        void***    leaf_ptrs)   // Pointer to an array of pointers to MTBDD leaves
{
    std::set<MTBDD> leaves {};
    collect_mtbdd_leaves(root, leaves);

    // This probably is not the most efficient way how to do it.
    // First compute the destination size (for malloc)
    uint32_t size_cnt = 0; // Counter for the total number of states.
    for (MTBDD leaf : leaves) {
        Transition_Destination_Set* leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(leaf));
        size_cnt += leaf_contents->destination_set.size();
    }

    // Do the allocations
    auto _leaf_sizes = (uint32_t*) malloc(sizeof(uint32_t) * leaves.size());  // One slot for each leaf
    auto _leaf_states = (State*) malloc(sizeof(State) * size_cnt);

    // Populate
    uint32_t state_i = 0;
    uint32_t size_i = 0;

    for (MTBDD leaf : leaves) {
        auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(leaf));
        for (int state : leaf_contents->destination_set) {
           _leaf_states[state_i] = state;
           state_i++;
        }
        _leaf_sizes[size_i] = leaf_contents->destination_set.size();
        size_i++;
    }

    if (leaf_ptrs != NULL) {
        void** leaf_ptr_arr = (void**) malloc(sizeof(void*) * leaves.size());

        uint32_t i = 0;
        for (auto leaf : leaves) {
            auto leaf_contents_ptr = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(leaf));
            leaf_ptr_arr[i] = (void*) leaf_contents_ptr;
            i++;
        }
        *leaf_ptrs = leaf_ptr_arr;
    }

    *leaf_sizes = _leaf_sizes;
    *leaf_cnt = (uint32_t) leaves.size();
    return _leaf_states;
}

void amaya_print_dot(MTBDD m, int32_t fd)
{
  FILE* file = fdopen(fd, "w");
  mtbdd_fprintdot(file, m);
  fflush(file);
  // fclose(file);  The file will be closed in python
}

MTBDD amaya_project_variables_away(MTBDD m, uint32_t *variables, uint32_t var_count)
{
  // Construct the variables set.
  BDDSET var_set = mtbdd_set_empty();
  for (uint32_t i = 0; i < var_count; i++) {
    var_set = mtbdd_set_add(var_set, variables[i]);
  }

  // Do the projection itself.
  LACE_ME;
  MTBDD result = mtbdd_abstract(m, var_set, TASK(project_variable_away_abstract_op));

  //mtbdd_fprintdot(stdout, result);
  return result;
}

State* amaya_mtbdd_get_state_post(MTBDD dd, uint32_t *post_size)
{
  set<MTBDD> leaves;
  collect_mtbdd_leaves(dd, leaves);

  set<State> state_post_set;

  for (auto leaf: leaves) {
    auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(mtbdd_getvalue(leaf));
    state_post_set.insert(leaf_contents->destination_set.begin(), leaf_contents->destination_set.end());
  }

  auto result = (State*) malloc(sizeof(State) * state_post_set.size());
  uint32_t i = 0;

  for (int state: state_post_set) {
    result[i++] = state;
  }

  *post_size = state_post_set.size();
  return result;
}


uint8_t* amaya_mtbdd_get_transitions(
    MTBDD     root,   // The mtbdd
    uint32_t*   vars,
    uint32_t  var_count,
    uint32_t*   symbols_cnt,
    State**   dest_states,
    uint32_t**  dest_states_sizes)
{
  LACE_ME;

  // Construct MTBDD set from given vars
  MTBDD variable_set = mtbdd_set_empty();
  for (uint32_t i = 0; i < var_count; i++) {
    variable_set= mtbdd_set_add(variable_set, vars[i]);
  }

  // Stores the tree path to the leaf
  auto arr = (uint8_t*) malloc(sizeof(uint8_t) * var_count);

  MTBDD leaf = mtbdd_enum_first(root, variable_set, arr, NULL);

  vector<State> dest_states_vec;
  vector<uint8_t> symbols;
  vector<uint32_t> state_sizes;
  while (leaf != mtbdd_false)
  {
    // Add the destination states to the oveall vector
    auto tds = (Transition_Destination_Set*) mtbdd_getvalue(leaf);
    for (int state: tds->destination_set) {
      dest_states_vec.push_back(state);
    }

    for (uint32_t i = 0; i < var_count; i++) {
      symbols.push_back(arr[i]);
    }

    state_sizes.push_back(tds->destination_set.size());

      leaf = mtbdd_enum_next(root, variable_set, arr, NULL);
  }

  // Create output arrays
  auto symbols_out = (uint8_t*) malloc(sizeof(uint8_t) * symbols.size());
  for (uint32_t i = 0; i < symbols.size(); i++) symbols_out[i] = symbols.at(i);

  auto dest_states_sizes_out = (uint32_t*) malloc(sizeof(uint32_t) * state_sizes.size());
  for (uint32_t i = 0; i < state_sizes.size(); i++) dest_states_sizes_out[i] = state_sizes.at(i);

  auto  dest_states_out = (State*) malloc(sizeof(State) * dest_states_vec.size());
  for (uint32_t i = 0; i < dest_states_vec.size(); i++) dest_states_out [i] = dest_states_vec.at(i);

  // Do the return arrays assignment
  *dest_states = dest_states_out;
  *dest_states_sizes = dest_states_sizes_out;

  *symbols_cnt = state_sizes.size(); // For every destination size, there exists 1 symbol leading to it.
  return symbols_out;
}


MTBDD amaya_unite_mtbdds(MTBDD m1, MTBDD m2) {
  LACE_ME;
  MTBDD u = mtbdd_applyp(m1, m2, (uint64_t) 0, TASK(transitions_union_op), AMAYA_UNION_OP_ID);
  return u;
}

void amaya_set_debugging(bool debug) {
  DEBUG_ON = debug;
}

State* amaya_get_state_post_with_some_transition(
    MTBDD mtbdd,
    uint32_t* variables,
    uint32_t variable_cnt,
    uint8_t** out_symbols,
    uint32_t* transition_cnt)
{
  LACE_ME;

  // Create a MTBDD Cube containing all requred variables.
  MTBDD variable_set = mtbdd_set_empty();
  for (uint32_t i = 0; i < variable_cnt; i++) {
    variable_set = mtbdd_set_add(variable_set, variables[i]);
  }

  // Stores the tree path to the leaf
  uint8_t* arr = (uint8_t*) malloc(sizeof(uint8_t) * variable_cnt);

  MTBDD leaf = mtbdd_enum_first(mtbdd, variable_set, arr, NULL);

  vector<State>   reachable_states;
  vector<uint8_t> transition_symbols;

  while (leaf != mtbdd_false) {
    auto tds = (Transition_Destination_Set*) mtbdd_getvalue(leaf);
    for (auto state : tds->destination_set) {

      // @Optimize: We use linear search over vector - there should be a relatively small number of states
      //        reachable from everystate, therefore it should be faster to use ordinary vector (chache lines)
      bool state_already_located = false;
      for (auto already_located_state : reachable_states) {
        if (already_located_state == state) {
          state_already_located = true;
          break;
        }
      }

      if (!state_already_located) {
        reachable_states.push_back(state);
        // Copy the transition symbol so that the Python side will have the information available
        // (this method is used in DFS)

        for (uint32_t i = 0; i < variable_cnt; i++) {
          transition_symbols.push_back(arr[i]);
        }
      }
    }

      leaf = mtbdd_enum_next(mtbdd, variable_set, arr, NULL);
  }

  free(arr);

  auto _out_symbols = (uint8_t*) malloc(sizeof(uint8_t) * transition_symbols.size());
  for (uint32_t i = 0; i < transition_symbols.size(); i++) {
    _out_symbols[i] = transition_symbols.at(i);
  }

  *out_symbols = _out_symbols;
  *transition_cnt = (uint32_t) reachable_states.size();

  auto _reachable_states = (State*) malloc(sizeof(State) * reachable_states.size());
  for (uint32_t i = 0; i < reachable_states.size(); i++) _reachable_states[i] = reachable_states.at(i);

  return _reachable_states;
}


MTBDD* amaya_remove_states_from_transitions(
  MTBDD*    transition_roots,
  uint32_t  transition_cnt,
  State*    states_to_remove,
  uint32_t  states_to_remove_cnt)
{

  auto mtbdds_after_removal = (MTBDD*) malloc(sizeof(MTBDD) * transition_cnt);
  LACE_ME;

  set<State> states_to_remove_set;
  for (uint32_t i = 0; i < states_to_remove_cnt; i++) {
    states_to_remove_set.insert(states_to_remove[i]);
  }

  REMOVE_STATES_OP_PARAM = &states_to_remove_set;
  for (uint32_t i = 0; i < transition_cnt; i++) {
    MTBDD result_mtbdd = mtbdd_uapply(transition_roots[i], TASK(remove_states_op), REMOVE_STATES_OP_COUNTER);
    mtbdd_ref(result_mtbdd);
    mtbdds_after_removal[i] = result_mtbdd;
  }

  REMOVE_STATES_OP_COUNTER++;

  return mtbdds_after_removal;
}

State* amaya_get_states_in_mtbdd_leaves(MTBDD* mtbdds, uint32_t mtbdd_cnt, uint32_t* out_state_cnt) {
  // Garther a set of all unique leaves present in the given MTBDDs
  std::set<MTBDD> mtbdd_leaves;
  for (uint32_t i = 0; i < mtbdd_cnt; i++) {
    collect_mtbdd_leaves(mtbdds[i], mtbdd_leaves);
  }

  // Gather unique states in the previously extraced leaves
  std::set<State> states;
  for (auto mtbdd_leaf : mtbdd_leaves) {
    auto leaf_tds = (Transition_Destination_Set*) mtbdd_getvalue(mtbdd_leaf);
    for (auto state : leaf_tds->destination_set) {
      states.insert(state);
    }
  }

  State* out_states = (State*) malloc(states.size() * sizeof(State*));

  uint32_t i = 0;
  for (auto state : states) {
    out_states[i++] = state;
  }

  *out_state_cnt = states.size();

  return out_states;
}


void amaya_mtbdd_ref(MTBDD dd) {
  mtbdd_ref(dd);
}

void amaya_mtbdd_deref(MTBDD dd) {
  mtbdd_deref(dd);
}

void amaya_sylvan_gc() {
  LACE_ME;
  sylvan_gc();
}

void amaya_sylvan_try_performing_gc() {
  LACE_ME;
  sylvan_gc_test();
}

void amaya_sylvan_clear_cache() {
    LACE_ME;
    sylvan_clear_cache();
}

Serialized_NFA* amaya_construct_dfa_for_atom_conjunction(Serialized_Quantified_Atom_Conjunction* raw_formula) {
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

    auto result = serialize_nfa(created_nfa);
    return result;
}

Serialized_NFA* amaya_minimize_hopcroft(Serialized_NFA* serialized_dfa) {
    NFA dfa = deserialize_nfa(*serialized_dfa);
    NFA minimized_dfa = minimize_hopcroft(dfa);
    auto output_dfa = serialize_nfa(minimized_dfa);
    return output_dfa;
}

Serialized_NFA* amaya_compute_nfa_intersection(Serialized_NFA* left_serialized, Serialized_NFA* right_serialized) {
    assert(left_serialized);
    assert(right_serialized);

    NFA left  = deserialize_nfa(*left_serialized);
    NFA right = deserialize_nfa(*right_serialized);

    auto result = compute_nfa_intersection(left, right);
    auto serialized_result = serialize_nfa(result);

    return serialized_result;
}

Serialized_NFA* amaya_determinize(Serialized_NFA* serialized_nfa) {
    NFA nfa = deserialize_nfa(*serialized_nfa);
    NFA dfa = determinize_nfa(nfa);
    auto output_dfa = serialize_nfa(dfa);
    return output_dfa;
}

Serialized_NFA* amaya_perform_pad_closure(Serialized_NFA* serialized_nfa) {
    NFA nfa = deserialize_nfa(*serialized_nfa);
    nfa.perform_pad_closure();
    auto output = serialize_nfa(nfa);
    return output;
}

Serialized_NFA* amaya_perform_pad_closure_using_bit_sets(Serialized_NFA* serialized_nfa) {
    NFA nfa = deserialize_nfa(*serialized_nfa);
    NFA result = do_pad_closure_using_bit_sets(&nfa, g_solver_context->bit_set_alloc);
    auto output = serialize_nfa(result);
    return output;
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

Serialized_NFA* construct_nfa_from_congruence(Serialized_Atom* congruence, s64 init_val, BDDSET vars, u64 var_count) {
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

    Serialized_NFA* serialized_result = serialize_nfa(constructed_nfa);
    return serialized_result;
}

Serialized_NFA* amaya_construct_nfa_from_congruence(
    Serialized_Atom* congruence,
    s64  init_val,
    u32* vars,
    u64  var_cnt)
{
    BDDSET var_set = sylvan::mtbdd_set_from_array(vars, var_cnt);
    sylvan::mtbdd_ref(var_set);
    auto result = construct_nfa_from_congruence(congruence, init_val, var_set, var_cnt);
    sylvan::mtbdd_deref(var_set);
    return result;
}

Serialized_NFA* construct_nfa_from_ineq(Serialized_Atom* ineq, s64 init_state, BDDSET vars, u64 var_count) {
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

    auto result_ptr = serialize_nfa(constructed_nfa);
    return result_ptr;
}

Serialized_NFA* construct_nfa_from_eq(Serialized_Atom* eq, s64 init_state, BDDSET vars, u64 var_count) {
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

    auto result_ptr = serialize_nfa(constructed_nfa);
    return result_ptr;
}

Serialized_NFA* amaya_construct_nfa_from_ineq(
    Serialized_Atom* ineq,
    s64  init_val,
    u32* vars,
    u64  var_cnt)
{
    BDDSET var_set = sylvan::mtbdd_set_from_array(vars, var_cnt);
    sylvan::mtbdd_ref(var_set);
    auto result = construct_nfa_from_ineq(ineq, init_val, var_set, var_cnt);
    sylvan::mtbdd_deref(var_set);
    return result;
}

Serialized_NFA* amaya_construct_nfa_from_eq(
    Serialized_Atom* eq,
    s64  init_val,
    u32* vars,
    u64  var_cnt)
{
    BDDSET var_set = sylvan::mtbdd_set_from_array(vars, var_cnt);
    sylvan::mtbdd_ref(var_set);
    auto result = construct_nfa_from_eq(eq, init_val, var_set, var_cnt);
    sylvan::mtbdd_deref(var_set);
    return result;
}

void amaya_enable_bit_sets() {
    g_solver_context->config.enable_feature(SOLVER_CONFIG_USE_BIT_SETS);
}
