#pragma once
#include "../include/base.hpp"

#include <cassert>
#include <unordered_map>
#include <utility>
#include <vector>

namespace Bit_Set {
    struct Block_Arena_Allocator;

    /*
    A set of states, stored as a bit per state and indexed by the state *number*. `block_cnt` is
    carried in the set itself rather than looked up from the allocator's current generation: sylvan
    owns the bit sets that end up in MTBDD leaves and may hash, compare or destroy one long after
    the generation it was allocated in stopped being current, at which point the current
    generation's width says nothing about how wide *this* set is.
    */
    struct Bit_Set {
        u64 generation;
        u64 block_cnt;
        u64* data;

        /*
        NFA states are arbitrary signed 64-bit values (e.g. states built directly from a linear
        inequality's RHS are frequently negative), but a bit set only has non-negative indices.
        `state_bias` is the smallest state number present when the set's generation was opened
        (`Block_Arena_Allocator::start_new_generation`) - every state is shifted by it before being
        turned into an index, so `has_state`/`add_state` work for whatever range of (possibly
        negative) state numbers the generation was sized for.
        */
        s64 state_bias;

        bool has_state(s64 state) const {
            u64 biased_state = static_cast<u64>(state - this->state_bias);
            u64 target_chunk = biased_state / 64;
            u64 chunk_offset = biased_state % 64;

            assert(target_chunk < this->block_cnt);
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
            u64 biased_state = static_cast<u64>(state - this->state_bias);
            u64 target_chunk = biased_state / 64;
            u64 chunk_offset = biased_state % 64;

            assert(target_chunk < this->block_cnt);
            this->data[target_chunk] = this->data[target_chunk] | (1ul << chunk_offset);
        }

        /* The number of states this set can hold - `block_cnt` blocks worth of bits. */
        u64 capacity() const { return this->block_cnt * 64; }

        void populate_with(const Bit_Set& other) {
            assert(other.block_cnt >= this->block_cnt);
            for (u64 i = 0; i < this->block_cnt; i++) {
                this->data[i] = other.data[i];
            }
        }

        bool equals(const Bit_Set& other) const {
            // Sets from different generations are never equal, which also means the loop below
            // only ever runs over two sets that are known to be the same width.
            if (this->generation != other.generation) {
                return false;
            }

            for (u64 i = 0; i < this->block_cnt; i++) {
                if (this->data[i] != other.data[i]) return false;
            }
            return true;
        }
    };

    std::ostream& operator<<(std::ostream& output, const Bit_Set& bit_set);

    /*
    Pool allocator for bit sets, grouped into generations.

    Every pad closure opens a generation, and all the bit sets in one generation have the same
    width, so they can be carved out of a few large chunks instead of being malloc'd one at a time.
    Handing a bit set back pushes it onto the generation's free list rather than releasing it, so a
    generation's memory stays bounded by how many of its bit sets are alive at once - the frontier
    fixpoint allocates a short-lived temporary per leaf pair, and those addresses get reused
    immediately.

    A generation cannot be released as soon as the pad closure that opened it returns: sylvan owns
    the bit sets stored in MTBDD leaves and calls destroy_leaf on them whenever it collects those
    nodes, which may be several generations later. Each generation therefore counts its outstanding
    bit sets and is released once it has been retired (a newer generation was started) *and* the
    last of its bit sets has come back.
    */
    struct Block_Arena_Allocator {
        static constexpr u64 DEFAULT_BIT_SETS_PER_CHUNK = 128;

        // Offset of the blocks from the start of a bit set's allocation. The blocks are carved out
        // of the same allocation as the header, right behind it.
        static constexpr u64 HEADER_SIZE = sizeof(Bit_Set);

        struct Generation {
            u64 id;
            u64 block_cnt;
            s64 state_bias;                // smallest state number this generation's sets can hold
            u64 bit_set_size;              // bytes: the header plus `block_cnt` blocks
            std::vector<u8*> chunks;
            u8* bump      = nullptr;       // next unused byte of the last chunk
            u8* chunk_end = nullptr;
            Bit_Set* free_list = nullptr;  // returned bit sets, linked through their `data` field
            u64 live_bit_sets = 0;
            bool retired = false;
        };

        // Kept in sync with `current` - several call sites read these directly.
        u64 current_generation = 0;
        u64 current_generation_state_cnt = 0;
        u64 current_generation_block_cnt = 0;

        u64 bit_sets_per_chunk;
        std::unordered_map<u64, Generation*> generations;
        Generation* current = nullptr;

        explicit Block_Arena_Allocator(u64 bit_sets_per_chunk = DEFAULT_BIT_SETS_PER_CHUNK)
            : bit_sets_per_chunk(bit_sets_per_chunk > 0 ? bit_sets_per_chunk : DEFAULT_BIT_SETS_PER_CHUNK) {}

        Block_Arena_Allocator(const Block_Arena_Allocator&) = delete;
        Block_Arena_Allocator& operator=(const Block_Arena_Allocator&) = delete;

        Block_Arena_Allocator(Block_Arena_Allocator&& other) noexcept { *this = std::move(other); }

        Block_Arena_Allocator& operator=(Block_Arena_Allocator&& other) noexcept {
            if (this == &other) return *this;
            destroy();
            current_generation           = other.current_generation;
            current_generation_state_cnt = other.current_generation_state_cnt;
            current_generation_block_cnt = other.current_generation_block_cnt;
            bit_sets_per_chunk           = other.bit_sets_per_chunk;
            generations                  = std::move(other.generations);
            current                      = other.current;
            other.generations.clear();
            other.current = nullptr;
            return *this;
        }

        ~Block_Arena_Allocator() { destroy(); }

        /* A bit set whose blocks are left as they were - only for callers that overwrite all of them. */
        Bit_Set* alloc_uninitialized() {
            assert(current != nullptr);

            Bit_Set* result = current->free_list;
            if (result != nullptr) {
                current->free_list = reinterpret_cast<Bit_Set*>(result->data);
            } else {
                // The short-circuit matters: a generation starts with no chunk at all, and forming
                // `nullptr + bit_set_size` to compare it would be undefined behaviour.
                if (current->bump == nullptr || current->bump + current->bit_set_size > current->chunk_end) {
                    add_chunk(current);
                }
                result = reinterpret_cast<Bit_Set*>(current->bump);
                current->bump += current->bit_set_size;
            }

            result->generation  = current->id;
            result->block_cnt   = current->block_cnt;
            result->state_bias  = current->state_bias;
            result->data        = reinterpret_cast<u64*>(reinterpret_cast<u8*>(result) + HEADER_SIZE);

            current->live_bit_sets += 1;
            return result;
        }

        /* A bit set with every block zeroed - i.e. the empty set. */
        Bit_Set* alloc() {
            Bit_Set* result = alloc_uninitialized();
            for (u64 i = 0; i < result->block_cnt; i++) result->data[i] = 0;
            return result;
        }

        void dealloc(Bit_Set* bit_set) {
            if (bit_set == nullptr) return;

            auto generation_entry = generations.find(bit_set->generation);

            // A generation is only released once its last bit set has come back, so a live bit set
            // always has a generation to return to. Sylvan drives this path from its GC sweep
            // though, so rather than run off the end of the map if that ever stops holding, drop
            // the bit set and leak it - the generation it belongs to is already gone anyway.
            assert(generation_entry != generations.end());
            if (generation_entry == generations.end()) return;

            Generation* generation = generation_entry->second;

            // The bit set is dead now, so its `data` pointer is free to link the free list with.
            bit_set->data = reinterpret_cast<u64*>(generation->free_list);
            generation->free_list = bit_set;

            assert(generation->live_bit_sets > 0);
            generation->live_bit_sets -= 1;

            if (generation->live_bit_sets == 0 && generation->retired) release(generation);
        }

        void start_new_generation(u64 state_cnt, s64 state_bias = 0) {
            if (current != nullptr) {
                current->retired = true;
                if (current->live_bit_sets == 0) release(current);
                current = nullptr;
            }

            current_generation += 1;
            current_generation_state_cnt = state_cnt;
            current_generation_block_cnt = state_cnt / 64 + ((state_cnt % 64) > 0);

            Generation* generation = new Generation;
            generation->id           = current_generation;
            generation->block_cnt    = current_generation_block_cnt;
            generation->state_bias   = state_bias;
            generation->bit_set_size = HEADER_SIZE + generation->block_cnt * sizeof(u64);

            generations[generation->id] = generation;
            current = generation;
        }

        /*
        Release everything, including generations that still have bit sets outstanding. Only safe
        once nothing can hand a bit set back any more - shutdown_machinery() calls sylvan_quit()
        (which destroys every remaining leaf) before the allocator goes away.
        */
        void destroy() {
            for (auto& [id, generation] : generations) {
                for (u8* chunk : generation->chunks) delete[] chunk;
                delete generation;
            }
            generations.clear();
            current = nullptr;
            current_generation_state_cnt = 0;
            current_generation_block_cnt = 0;
        }

    private:
        void add_chunk(Generation* generation) {
            u64 chunk_size = bit_sets_per_chunk * generation->bit_set_size;
            u8* chunk = new u8[chunk_size];
            generation->chunks.push_back(chunk);
            generation->bump      = chunk;
            generation->chunk_end = chunk + chunk_size;
        }

        void release(Generation* generation) {
            for (u8* chunk : generation->chunks) delete[] chunk;
            generations.erase(generation->id);
            if (current == generation) current = nullptr;
            delete generation;
        }
    };

    Bit_Set* make_union(Block_Arena_Allocator* allocator, const Bit_Set* left, const Bit_Set* right);
    Bit_Set* add_state(Block_Arena_Allocator* allocator, const Bit_Set* set, State state);
    Block_Arena_Allocator create_allocator_for_n_states(u64 state_cnt, u64 bit_sets_per_chunk, s64 state_bias = 0);
}
