#ifndef AMAYA_BLOCK_ALLOCATOR_H
#define AMAYA_BLOCK_ALLOCATOR_H

#include "base.hpp"

#include <list>

struct Block_Allocator {

    std::list<u8*> allocated_blocks;


    u8* alloc_block(u64 block_size) {
        u8* block = new u8[block_size];
        allocated_blocks.push_back(block);
        return block;
    }

    ~Block_Allocator() {
        for (auto& block: allocated_blocks) {
            delete[] block;
            block = nullptr;
        }
    }
};

#endif
