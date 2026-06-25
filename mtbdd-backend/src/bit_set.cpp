#include "../include/bit_set.hpp"
#include "../include/custom_leaf.hpp"
#include <cstring>


Bit_Set::Bit_Set* Bit_Set::make_union(Block_Arena_Allocator* allocator, const Bit_Set* left, const Bit_Set* right) {
    Bit_Set* new_set = allocator->alloc();

    for (u64 i = 0; i < allocator->current_generation_block_cnt; i++) {
        new_set->data[i] = left->data[i] | right->data[i];
    }

    return new_set;
}

Bit_Set::Bit_Set* Bit_Set::add_state(Block_Arena_Allocator* allocator, const Bit_Set* set, u64 state) {
    Bit_Set* new_set = allocator->alloc();
    
    for (u64 i = 0; i < allocator->current_generation_block_cnt; i++) {
        new_set[i] = set[i];
    }

    new_set->add_state(state);

    return new_set;
}

Bit_Set::Block_Arena_Allocator Bit_Set::create_allocator_for_n_states(u64 state_cnt, u64 bulk_alloc) {
    (void) bulk_alloc;

    u64 block_cnt = state_cnt / sizeof(u64);
    u64 reminder = state_cnt % sizeof(u64);
    block_cnt += (reminder > 0);

    return Block_Arena_Allocator();
}

std::ostream& Bit_Set::operator<<(std::ostream& output, const Bit_Set& bit_set) {
    output << "{";
    for (u64 i = 0; i < g_solver_context->bit_set_alloc->current_generation_state_cnt; i++) {
        if (bit_set.has_state(i)) {
            output << i << ", ";
        }
    }
    output << "}";
    return output;
}
