#pragma once
#include "base.hpp"
#include "bit_set.hpp"

NFA do_pad_closure_using_bit_sets(NFA* nfa, Bit_Set::Block_Arena_Allocator* alloc);