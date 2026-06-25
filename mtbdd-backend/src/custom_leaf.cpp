#include "../include/custom_leaf.hpp"
#include "../include/base.hpp"

#include <inttypes.h>

#include <string>
#include <cstring>
#include <utility>
#include <stdlib.h>
#include <sstream>
#include <sylvan.h>

uint64_t mtbdd_leaf_type_singleton;

Solver_Context* g_solver_context;


sylvan::MTBDD make_set_leaf(Transition_Destination_Set* value) {
    sylvan::MTBDD leaf = sylvan::mtbdd_makeleaf(g_solver_context->leaf_id_store.transition_set,
                                                (uint64_t) value);
    return leaf;
}

/**
 * Function is called when a new node is being inserted to the hash table.
 * @param state_set_ptr  Pointer to the contents of the created leaf.
 */
void mk_set_leaf(uint64_t* target_destination_set_ptr) {
    auto leaf_contents_ptr = reinterpret_cast<Transition_Destination_Set**>(target_destination_set_ptr);

    auto leaf_contents = *leaf_contents_ptr;
    auto new_leaf_contents = new Transition_Destination_Set(*leaf_contents); // Copy construct

    // According to the GMP leaf implementation, it should suffice to just write the new value to the state_set_ptr.
    *leaf_contents_ptr = new_leaf_contents;
}

void destroy_set_leaf(uint64_t leaf_value) {
    auto tds = reinterpret_cast<Transition_Destination_Set*>(leaf_value);
    delete tds;
}

int set_leaf_equals(uint64_t left_leaf_raw_ptr, uint64_t right_leaf_raw_ptr) {
    auto left_leaf_contents  = reinterpret_cast<Transition_Destination_Set*>(left_leaf_raw_ptr);
    auto right_leaf_contents = reinterpret_cast<Transition_Destination_Set*>(right_leaf_raw_ptr);
    return (left_leaf_contents->destination_set == right_leaf_contents->destination_set);
}

uint64_t set_leaf_hash(const uint64_t leaf_contents_raw_ptr, const uint64_t seed) {
    auto leaf_contents = reinterpret_cast<Transition_Destination_Set *>(leaf_contents_raw_ptr);

    const uint64_t prime = 1099511628211;
    uint64_t hash = seed;

    for (auto state : leaf_contents->destination_set) {
        hash = hash ^ state;
        hash = rotl64(hash, 47);
        hash = hash * prime;
    }

    return hash ^ (hash >> 32);
}


char* write_str_into_buf_or_alloc_new(const std::string& str, char *buf, size_t buflen) {
    // Does the resulting string fit into the provided buffer?
    const size_t required_buf_size = str.size() + 1; // With '\0' at the end
    if (required_buf_size <= buflen) {
        const char *cstr = str.c_str();
        std::memcpy(buf, cstr, sizeof(char) * required_buf_size);
        return buf;
    }

    char *new_buf = (char*) malloc(sizeof(char) * required_buf_size);
    assert(new_buf != nullptr);

    std::memcpy(new_buf, str.c_str(), sizeof(char) * required_buf_size);
    return new_buf;
}


char* set_leaf_to_str(int comp, uint64_t leaf_contents_raw_ptr, char *buf, size_t buflen) {
    (void)comp;

    std::stringstream ss;
    auto leaf_contents = reinterpret_cast<Transition_Destination_Set*>(leaf_contents_raw_ptr);
    ss << "{";
    uint32_t cnt = 1;
    for (auto i : leaf_contents->destination_set) {
        ss << i;
        if (cnt < leaf_contents->destination_set.size()) {
            ss << ",";
        }
        cnt++;
    }
    ss << "}";

    const std::string str(ss.str());
    return write_str_into_buf_or_alloc_new(str, buf, buflen);
}


void Set_Leaf::init_set_leaf(Leaf_Type_Id_Store* type_store) {
    type_store->transition_set = sylvan::sylvan_mt_create_type();
    sylvan::sylvan_mt_set_hash(type_store->transition_set, set_leaf_hash);
    sylvan::sylvan_mt_set_equals(type_store->transition_set, set_leaf_equals);
    sylvan::sylvan_mt_set_create(type_store->transition_set, mk_set_leaf);
    sylvan::sylvan_mt_set_destroy(type_store->transition_set, destroy_set_leaf);
    sylvan::sylvan_mt_set_to_str(type_store->transition_set, set_leaf_to_str);
}


namespace Deterministic_Leaf {
    sylvan::MTBDD create(s64 value) {
        sylvan::MTBDD leaf = sylvan::mtbdd_makeleaf(mtbdd_leaf_type_singleton, (uint64_t) value);
        return leaf;
    }

    void create_form_value(uint64_t* value_ptr) {
        *value_ptr = *value_ptr; // NOP
    }

    void destroy() {}

    int equals(uint64_t a_value, uint64_t b_value) {
        return a_value == b_value;
    }

    uint64_t hash(const uint64_t value, const uint64_t seed) {
        return value;
    }
    
    char* into_str(int comp, uint64_t leaf_val, char *buf, size_t buflen) {
        std::stringstream ss;
        ss << leaf_val;
        return write_str_into_buf_or_alloc_new(ss.str(), buf, buflen);
    }

}