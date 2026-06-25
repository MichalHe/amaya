#ifndef AMAYA_CUSTOM_LEAF_H
#define AMAYA_CUSTOM_LEAF_H

#include <inttypes.h>
#include <stdlib.h>
#include <sylvan.h>
#include "base.hpp"
#include "bit_set.hpp"

struct Leaf_Type_Id_Store {
    u64 bit_set;
    u64 singleton;
    u64 transition_set;
};

enum Solver_Config_Flags {
    SOLVER_CONFIG_USE_BIT_SETS = 1,
};

struct Solver_Configuration {
    u64 flags;

    bool is_feature_enabled(Solver_Config_Flags flag_feature) {
        return (this->flags & flag_feature) > 0;
    }

    void enable_feature(Solver_Config_Flags flag_feature) {
        this->flags = this->flags | flag_feature;
    }
};

struct Solver_Context {
    Leaf_Type_Id_Store   leaf_id_store;
    Solver_Configuration config;
    Bit_Set::Block_Arena_Allocator* bit_set_alloc;
};

extern Solver_Context* g_solver_context;


#ifndef rotl64
static inline uint64_t rotl64(uint64_t x, int8_t r)
{
    return ((x << r) | (x >> (64 - r)));
}
#endif

sylvan::MTBDD make_set_leaf(Transition_Destination_Set* value);
void mk_set_leaf(uint64_t *target_destination_set_ptr);
void destroy_set_leaf(uint64_t leaf_value);
int set_leaf_equals(uint64_t a_ptr, uint64_t b_ptr);
uint64_t set_leaf_hash(const uint64_t contents_ptr, const uint64_t seed);
char* set_leaf_to_str(int comp, uint64_t leaf_val, char *buf, size_t buflen);

char* write_str_into_buf_or_alloc_new(const std::string& str, char *buf, size_t buflen);

namespace Set_Leaf {
    void init_set_leaf(Leaf_Type_Id_Store* type_store);
}


namespace Deterministic_Leaf {
    sylvan::MTBDD create(s64 value);
    void create_from_value(uint64_t* value_ptr);
    void destroy(uint64_t leaf_value);
    int equals(uint64_t a_value, uint64_t b_value);
    uint64_t hash(const uint64_t contents, const uint64_t seed);
    char* into_str(int comp, uint64_t leaf_val, char *buf, size_t buflen);
}

namespace Bit_Set_Leaf {
    sylvan::MTBDD make_bit_set_leaf(Bit_Set::Bit_Set* bit_set);
    void create_from_value(u64* bit_set_to_copy);
    void destroy_leaf(u64 bit_set_raw_ptr);
    int leaf_equals(u64 left_bit_set_raw_ptr, u64 right_bit_set_raw_ptr);
    u64 leaf_hash(const u64 bit_set_raw_ptr, const u64 seed);
    char* into_str(int comp, uint64_t leaf_val, char *buf, size_t buflen);

    void init_bit_set_leaf(Leaf_Type_Id_Store* type_store);
    std::vector<Transition> unpack_mtbdd(sylvan::MTBDD bdd, State origin_state, sylvan::BDDSET support_vars, u64 support_size);
}

#endif
