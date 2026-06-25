#include "lazy.hpp"

//
// Infrastructure used internally, exported in this header only to be able to run tests against it
//
struct Captured_Modulus {
    u64 leading_var;      // y in (y mod K)
    u64 subordinate_var;  // Variable representing modulus

    bool is_mod_captured() {
        return leading_var != subordinate_var;
    }
};

enum class Var_Preference_Type : u8 {
    NONE = 0x00,
    C_INCREASING = 0x01,
    C_DECREASING = 0x02, // The number of soutions to free variables grows as the value of y decreases
};

struct Var_Preference {  // Captures the notion of C-{increasing/decreasing}
    Var_Preference_Type type;
    s64 c;
};

struct Interval {
     s64 low, high;
};

s64 eval_mod_congruence_at_point(
  const Congruence_Node& congruence,
  s64 K,
  Captured_Modulus& mod,
  s64 point);

s64 get_point_for_mod_congruence_to_obtain_value(
  const Congruence_Node& congruence,
  s64 K,
  Captured_Modulus& mod,
  s64 value);

void shift_interval(Interval& interval, Var_Preference preference, s64 modulus);


//
// Formula rewriters:
//
bool linearize_moduli(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state);
bool substitute_vars_with_known_value(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state);
bool instantiate_quantifs_with_inf(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state);
bool instantiate_quantifs_with_c_monotonicity(Dep_Graph** graph_ptr, Ritch_Conjunction_State* state);
bool perform_max_simplification_on_graph(Dep_Graph** graph, Ritch_Conjunction_State* state);
bool perform_watched_rewrites(Dep_Graph** graph, Conjunction_State* state);

// Returns True if the graph contains a contradiction
bool detect_contradictions(const Dep_Graph* graph_ptr, Conjunction_State* state);
