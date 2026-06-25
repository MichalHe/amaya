#pragma once
#include "../include/base.hpp"
#include <list>

namespace Bit_Set {
    struct Block_Arena_Allocator;

    struct Bit_Set {
        u64 generation;
        u64* data;

        bool has_state(u64 state) const {
            u64 target_chunk = state / 64;
            u64 chunk_offset = state % 64;

            return (this->data[target_chunk] & (1ul << chunk_offset)) > 0;
        }

        bool has_any_state(std::vector<State>& states) {
            return has_any_state(states.begin(), states.end());
        }

        bool has_any_state(std::set<State>& states) {
            return has_any_state(states.begin(), states.end());
        }

        template <typename Iterator>
        bool has_any_state(Iterator first, Iterator end) {
            for (Iterator it = first; it != end; it++) {
                if (has_state(*it)) return true;
            }
            return false;
        }

        void add_state(State state) {
            u64 target_chunk = state / 64;
            u64 chunk_offset = state % 64;
            
            this->data[target_chunk] = this->data[target_chunk] | (1ul << chunk_offset);
        }

        void populate_with(const Bit_Set& other, u64 block_cnt) {
            for (u64 i = 0; i < block_cnt; i++) {
                this->data[i] = other.data[i];
            }
        }

        bool equals(const Bit_Set& other, u64 block_count) const {
            if (this->generation != other.generation) {
                return false;
            }
            
            for (u64 i = 0; i < block_count; i++) {
                if (this->data[i] != other.data[i]) return false;
            }
            return true;
        }
    };

    std::ostream& operator<<(std::ostream& output, const Bit_Set& bit_set);

    struct Block_Arena_Allocator {
        u64 current_generation = 0;
        u64 current_generation_state_cnt;
        u64 current_generation_block_cnt;

        Block_Arena_Allocator() {}
        
        Bit_Set* alloc() {
            Bit_Set* result = new Bit_Set;
            result->generation = current_generation;
            result->data = new u64[this->current_generation_block_cnt];
            for (u64 i = 0; i < this->current_generation_block_cnt; i++) result->data[i] = 0;
            assert(result->data != nullptr);
            return result;
        }

        void dealloc(Bit_Set* bit_set) {
            delete[] bit_set->data;
            delete bit_set;
        };

        void destroy() {
        }

        void start_new_generation(u64 state_cnt) {
            current_generation += 1;
            current_generation_state_cnt = state_cnt;
            current_generation_block_cnt = state_cnt / 64 + ((state_cnt % 64) > 0);
        }
    };

    Bit_Set* make_union(Block_Arena_Allocator* allocator, const Bit_Set* left, const Bit_Set* right);
    Bit_Set* add_state(Block_Arena_Allocator* allocator, const Bit_Set* set, u64 state);
    Block_Arena_Allocator create_allocator_for_n_states(u64 state_cnt, u64 bulk_alloc_cnt);
}
