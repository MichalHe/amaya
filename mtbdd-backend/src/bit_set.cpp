#include "../include/bit_set.hpp"
#include "../include/custom_leaf.hpp"
#include <cstring>


Bit_Set::Bit_Set* Bit_Set::make_union(Block_Arena_Allocator* allocator, const Bit_Set* left, const Bit_Set* right) {
    Bit_Set* new_set = allocator->alloc_uninitialized();

    for (u64 i = 0; i < new_set->block_cnt; i++) {
        new_set->data[i] = left->data[i] | right->data[i];
    }

    return new_set;
}

Bit_Set::Bit_Set* Bit_Set::add_state(Block_Arena_Allocator* allocator, const Bit_Set* set, u64 state) {
    Bit_Set* new_set = allocator->alloc_uninitialized();

    // Note: this copies the *blocks*, not the Bit_Set structs - `new_set` is a single Bit_Set,
    // so indexing it as an array of block_cnt Bit_Sets ran off the end of the allocation.
    new_set->populate_with(*set);
    new_set->add_state(state);

    return new_set;
}

Bit_Set::Block_Arena_Allocator Bit_Set::create_allocator_for_n_states(u64 state_cnt, u64 bit_sets_per_chunk) {
    Block_Arena_Allocator allocator(bit_sets_per_chunk);
    if (state_cnt > 0) allocator.start_new_generation(state_cnt);
    return allocator;
}

std::ostream& Bit_Set::operator<<(std::ostream& output, const Bit_Set& bit_set) {
    output << "{";
    for (u64 i = 0; i < bit_set.capacity(); i++) {
        if (bit_set.has_state(i)) {
            output << i << ", ";
        }
    }
    output << "}";
    return output;
}
