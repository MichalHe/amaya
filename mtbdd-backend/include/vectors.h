#ifndef AMAYA_CHUNKED_VECTOR_H
#define AMAYA_CHUNKED_VECTOR_H

#include "base.hpp"
#include "block_allocator.h"

#include <initializer_list>

template <typename T>
struct Sized_Array {
    T* items;
    u64 size;

    struct Iterator {
        const Sized_Array<T>* arr;
        u64                   idx;

        using value_type = T;
        using pointer    = T*;
        using reference  = T&;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::random_access_iterator_tag;

        Iterator():                    arr(nullptr), idx(0) {}
        Iterator(const Sized_Array<T>* arr, u64 start_idx): arr(arr), idx(start_idx) {}

        reference  operator*() {
            return (arr->items)[idx];
        }
        pointer operator->() {
            return &(arr->items[idx]);
        }
        const pointer operator->() const {
            return &(arr->items[idx]);
        }
        reference  operator[](int offset) {
            return arr->items[idx + offset];
        }
        // const reference operator*() const {
        //     return arr->items[idx];
        // }
        // const reference operator[](int offset) const {
        //     return arr->items[idx + offset];
        // }

        Iterator& operator++() {
            ++idx;
            return *this;
        }

        Iterator operator++(int) {
            Iterator r(*this);
            ++r;
            return r;
        }

        Iterator& operator--() {
            --idx;
            return *this;
        }

        Iterator operator--(int) {
            Iterator r(*this);
            --r;
            return r;
        }

        Iterator& operator+=(int offset) {
            idx += offset;
            return *this;
        }
        Iterator& operator-=(int offset) {
            idx -= offset;
            return *this;
        }

        Iterator operator+(int offset) const {
            Iterator r(*this);
            return r += offset;
        }
        Iterator operator-(int offset) const {
            Iterator r(*this);
            return r -= offset;
        }

        difference_type operator-(Iterator const& r) const {
            return idx - r.idx;
        }

        bool operator<(Iterator const& r)  const {
            return idx <  r.idx;
        }
        bool operator<=(Iterator const& r) const {
            return idx <= r.idx;
        }
        bool operator>(Iterator const& r)  const {
            return idx >  r.idx;
        }
        bool operator>=(Iterator const& r) const {
            return idx >= r.idx;
        }
        bool operator!=(const Iterator &r) const {
            return idx != r.idx;
        }
        bool operator==(const Iterator &r) const {
            return idx == r.idx;
        }
    };

    Iterator begin() const {
        return Iterator(this, 0);
    };

    Iterator end() const {
        return Iterator(this, this->size);
    };

    bool operator==(const Sized_Array<T>& other) const {
        if (other.size != this->size) return false;

        for (u64 i = 0; i < size; i++) {
            if (items[i] != other.items[i]) return false;
        }
        return true;
    }

    Sized_Array(Block_Allocator& alloc, const std::vector<T>& contents) : size(contents.size()) {
        items = reinterpret_cast<T*>(alloc.alloc_block(sizeof(T) * contents.size())) ;

        s64 i = 0;
        for (auto& it: contents) {
            items[i] = it;
            i += 1;
        }
    }

    Sized_Array(Block_Allocator& alloc, std::initializer_list<T> contents) : size(contents.size()) {
        items = reinterpret_cast<T*>(alloc.alloc_block(sizeof(T) * contents.size())) ;

        s64 i = 0;
        for (auto& it: contents) {
            items[i] = it;
            i += 1;
        }
    }

    Sized_Array() : items(nullptr), size(0) {}
    Sized_Array(T* items, u64 size) : items(items), size(size) {}
    Sized_Array(const Sized_Array<T>& other) : items(other.items), size(other.size) {}
    Sized_Array(Sized_Array<T>&& other) : items(other.items), size(other.size) {}

    Sized_Array(Block_Allocator& alloc, u64 size) : size(size) {
        items = reinterpret_cast<T*>(alloc.alloc_block(sizeof(T) * size));
    }

    template <typename X>
    friend std::ostream& operator<<(std::ostream& os, const Sized_Array<X>& arr);

    Sized_Array<T>& operator=(const Sized_Array<T>& other) = default;
};

template <typename T>
struct Chunked_Array {
    T*  data;       // The underlying memory is not owned at the moment
    u64 chunk_size;
    u64 chunk_count;

    Chunked_Array(T* data, u64 chunk_size, u64 chunk_count):
        data(data), chunk_size(chunk_size), chunk_count(chunk_count) {};

    Chunked_Array(Block_Allocator& alloc, std::initializer_list<T> contents, u64 chunk_count):
        chunk_count(chunk_count)
    {
        if (chunk_count == 0) {
            data = nullptr;
            chunk_size = 0;
            return;
        }
        data = reinterpret_cast<s64*>(alloc.alloc_block(sizeof(T) * contents.size()));
        s64 write_idx = 0;
        for (const T& elem: contents) {
            data[write_idx] = elem;
            write_idx += 1;
        }
        chunk_size = contents.size() / chunk_count;
    };

    Chunked_Array(Block_Allocator& alloc, const std::vector<T>& contents, u64 chunk_count) : chunk_count(chunk_count) {
        if (chunk_count == 0) {
            data = nullptr;
            chunk_size = 0;
            return;
        }

        data = reinterpret_cast<s64*>(alloc.alloc_block(sizeof(T) * contents.size()));
        s64 write_idx = 0;
        for (const T& elem: contents) {
            data[write_idx] = elem;
            write_idx += 1;
        }
        chunk_size = contents.size() / chunk_count;
    }


    T* get_nth_chunk_data(u64 n) const {
        return this->data + n*chunk_size;
    }

    u64 total_size() const noexcept {
        return this->chunk_count * this->chunk_size;
    }

    struct Iterator {
        const Chunked_Array<T>* arr;
        Sized_Array<T> current_elem;

        using value_type = T;
        using pointer    = T*;
        using reference  = T&;
        using difference_type   = std::ptrdiff_t;
        using iterator_category = std::random_access_iterator_tag;

        Iterator(): arr(nullptr), current_elem(Sized_Array<T>(nullptr, 0)) {}
        Iterator(const Chunked_Array<T>* arr, u64 start_idx):
            arr(arr),
            current_elem(Sized_Array<T>(arr->get_nth_chunk_data(start_idx), arr->chunk_size)) {}

        reference operator*() {
            return current_elem;
        }
        pointer operator->() {
            return &current_elem;
        }
        const pointer operator->() const {
            return &current_elem;
        }
        reference operator[](int offset) {
            return current_elem.items + arr->chunk_size*offset;
        }

        Iterator& operator++() {
            current_elem.items += arr->chunk_size;
            return *this;
        }

        Iterator operator++(int) {
            Iterator r(*this);
            ++r;
            return r;
        }

        Iterator& operator--() {
            current_elem.items -= arr->chunk_size;
            return *this;
        }
        Iterator operator--(int) {
            Iterator r(*this);
            --r;
            return r;
        }

        Iterator& operator+=(int offset) {
            current_elem.items += offset*arr->chunk_size;
            return *this;
        }
        Iterator& operator-=(int offset) {
            current_elem.items -= offset*arr->chunk_size;
            return *this;
        }

        Iterator operator+(int offset) const {
            Iterator r(*this);
            return r += offset;
        }

        Iterator operator-(int offset) const {
            Iterator r(*this);
            return r -= offset;
        }

        difference_type operator-(Iterator const& r) const {
            return (current_elem.items - r.items) / arr->chunk_size;
        }

        bool operator<(Iterator const& r)  const {
            return current_elem.items < r.current_elem.items;
        }

        bool operator<=(Iterator const& r) const {
            return current_elem.items <= r.current_elem.items;
        }

        bool operator>(Iterator const& r)  const {
            return current_elem.items > r.current_elem.items;
        }

        bool operator>=(Iterator const& r) const {
            return current_elem.items >= r.current_elem.items;
        }

        bool operator!=(const Iterator &r) const {
            return current_elem.items != r.current_elem.items;
        }

        bool operator==(const Iterator &r) const {
            return current_elem.items == r.items;
        }
    };

    Iterator begin() const {
        return Iterator(this, 0);
    };

    Iterator end() const {
        return Iterator(this, this->chunk_count);
    };

    bool operator==(const Chunked_Array<T>& other) const {
        if (other.chunk_size != this->chunk_size)   return false;
        if (other.chunk_count != this->chunk_count) return false;

        u64 item_count = chunk_size*chunk_count;
        for (u64 i = 0; i < item_count; i++) {
            if (data[i] != other.data[i]) return false;
        }
        return true;
    }

    Sized_Array<T> as_sized_array() const {
        return {.items = data, .size = this->chunk_size};
    }
};


std::size_t hash_array(const Sized_Array<s64>& arr);
std::size_t hash_chunked_array(const Chunked_Array<s64>& arr);

template <typename T>
std::ostream& operator<<(std::ostream& os, const Sized_Array<T>& arr) {
    if (arr.size == 0) {
        os << "Arr[]";
        return os;
    }
    auto iter = arr.begin();
    os << "(" << *iter;
    ++iter;

    for (; iter != arr.end(); ++iter) {
        os << "," << *iter;
    }
    os << ")";
    return os;
}

#endif
