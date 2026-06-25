#include "../include/base.hpp"
#include "../include/bit_set.hpp"
#include "../include/custom_leaf.hpp"
#include <sylvan.h>

#include <sstream>

sylvan::MTBDD Bit_Set_Leaf::make_bit_set_leaf(Bit_Set::Bit_Set* bit_set) {
    sylvan::MTBDD leaf = sylvan::mtbdd_makeleaf(g_solver_context->leaf_id_store.bit_set,
                                                reinterpret_cast<u64>(bit_set));
    return leaf;
};

// Sylvan handlers:
void Bit_Set_Leaf::create_from_value(u64* bit_set_to_copy) {
    Bit_Set::Bit_Set** value_ptr_to_copy = reinterpret_cast<Bit_Set::Bit_Set**>(bit_set_to_copy);

    Bit_Set::Bit_Set* new_value = g_solver_context->bit_set_alloc->alloc();
    new_value->populate_with(*(*value_ptr_to_copy), g_solver_context->bit_set_alloc->current_generation_block_cnt);

    *value_ptr_to_copy = new_value;
}

void Bit_Set_Leaf::destroy_leaf(u64 bit_set_raw_ptr) {
    Bit_Set::Bit_Set* bit_set = reinterpret_cast<Bit_Set::Bit_Set*>(bit_set_raw_ptr);
    g_solver_context->bit_set_alloc->dealloc(bit_set);
}

int Bit_Set_Leaf::leaf_equals(u64 left_bit_set_raw_ptr, u64 right_bit_set_raw_ptr) {
    auto left_bit_set  = reinterpret_cast<Bit_Set::Bit_Set*>(left_bit_set_raw_ptr);
    auto right_bit_set = reinterpret_cast<Bit_Set::Bit_Set*>(right_bit_set_raw_ptr);

    u64 block_count = g_solver_context->bit_set_alloc->current_generation_block_cnt;

    return left_bit_set->equals(*right_bit_set, block_count);
}

u64 Bit_Set_Leaf::leaf_hash(const u64 bit_set_raw_ptr, const u64 seed) {
    auto bit_set = reinterpret_cast<Bit_Set::Bit_Set*>(bit_set_raw_ptr);
    
    const u64 prime = 1099511628211u;
    u64 hash = seed;

    const u64 chunk_count = g_solver_context->bit_set_alloc->current_generation_block_cnt;

    for (int chunk_idx = 0; chunk_idx < chunk_count; chunk_idx++) {
        u64 chunk = bit_set->data[chunk_idx];

        hash = hash ^ chunk;
        hash = rotl64(hash, 47);
        hash = hash * prime;
    }

    return hash;    
}

char* Bit_Set_Leaf::into_str(int comp, uint64_t leaf_contents_raw_ptr, char *buf, size_t buflen) {
    (void)comp;

    std::stringstream ss;
    auto leaf_contents = reinterpret_cast<Bit_Set::Bit_Set*>(leaf_contents_raw_ptr);
    ss << "{";
    uint32_t cnt = 1;
    for (State state = 0; state < g_solver_context->bit_set_alloc->current_generation_state_cnt; state++) {
        bool is_present = leaf_contents->has_state(state);
        if (!is_present) continue;

        ss << state;
        ss << ",";
        cnt++;
    }
    ss << "}";

    const std::string str(ss.str());
    return write_str_into_buf_or_alloc_new(str, buf, buflen);
}

void Bit_Set_Leaf::init_bit_set_leaf(Leaf_Type_Id_Store* type_store) {
    type_store->bit_set = sylvan::sylvan_mt_create_type();
    sylvan::sylvan_mt_set_hash(type_store->bit_set,    Bit_Set_Leaf::leaf_hash);
    sylvan::sylvan_mt_set_equals(type_store->bit_set,  Bit_Set_Leaf::leaf_equals);
    sylvan::sylvan_mt_set_create(type_store->bit_set,  Bit_Set_Leaf::create_from_value);
    sylvan::sylvan_mt_set_destroy(type_store->bit_set, Bit_Set_Leaf::destroy_leaf);
    sylvan::sylvan_mt_set_to_str(type_store->bit_set,  Bit_Set_Leaf::into_str);
}

std::vector<Transition> Bit_Set_Leaf::unpack_mtbdd(sylvan::MTBDD bdd, State origin_state, sylvan::BDDSET support_vars, u64 support_size) {
    std::vector<Transition> transitions;
    u8 raw_symbol[support_size];

    u64 state_count = g_solver_context->bit_set_alloc->current_generation_block_cnt;
    sylvan::MTBDD leaf = sylvan::mtbdd_enum_first(bdd, support_vars, raw_symbol, NULL);
    while (leaf != sylvan::mtbdd_false) {
        auto leaf_contents = reinterpret_cast<Bit_Set::Bit_Set*>(sylvan::mtbdd_getvalue(leaf));

        for (State dest_state = 0; dest_state < state_count; dest_state++) {
            if (!leaf_contents->has_state(static_cast<u64>(dest_state))) continue;                
            
            std::vector<u8> symbol(support_size);
            for (u64 i = 0; i < support_size; i++) symbol[i] = raw_symbol[i];

            Transition transition = {.from = origin_state, .to = dest_state, .symbol = symbol};
            transitions.push_back(transition);
        }

        leaf = sylvan::mtbdd_enum_next(bdd, support_vars, raw_symbol, NULL);
    }

    return transitions;
}
