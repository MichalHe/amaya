#ifndef AMAYA_PARETO_SET_H
#define AMAYA_PARETO_SET_H

#include "base.hpp"

#include <unordered_map>
#include <memory>
#include <vector>


struct Pareto_Set {
    typedef std::vector<s64> Prefix;
    typedef std::vector<s64> Suffix;

    struct Bucket_Entry {
        Suffix* suffix = nullptr;
        Bucket_Entry(Suffix* suffix) : suffix(suffix) {
            // suffix = new Suffix(*suffix);
        };

        Bucket_Entry(const Bucket_Entry& other) = delete;
        Bucket_Entry& operator=(const Bucket_Entry& other) = delete;


        Bucket_Entry(Bucket_Entry&& other) : suffix(other.suffix) {
            other.suffix = nullptr;
        };

        Bucket_Entry& operator=(Bucket_Entry&& other) {
            if (this != &other) {
                delete suffix;
                suffix = other.suffix;
                other.suffix = nullptr;
            }
            return *this;
        };

        bool operator==(const Bucket_Entry& other) const {
            if (suffix == nullptr) return other.suffix == nullptr;
            return *suffix == *other.suffix;
        }

        ~Bucket_Entry() {
            delete suffix;
            suffix = nullptr;
        }

        bool empty() const {
            return suffix == nullptr;
        }

        void empty_out() {
            delete this->suffix;
            this->suffix = nullptr;
        }
    };

    Pareto_Set(const Pareto_Set& other) {
        for (auto& [other_prefix, other_suffix_buckets]: other.data) {
            auto& dest_bucket = data[other_prefix];
            for (auto& suffix: other_suffix_buckets) {
                if (suffix.empty()) continue;
                Suffix* suffix_copy = new std::vector<s64>(*suffix.suffix);
                dest_bucket.emplace_back(suffix_copy);
            }
        }
        prefix_size = other.prefix_size;
    }

    Pareto_Set(Pareto_Set&& pareto_set) {
        this->data = std::move(pareto_set.data);
    };
    Pareto_Set(u64 prefix_size): prefix_size(prefix_size) {};

    typedef std::vector<Bucket_Entry> Bucket;

    std::unordered_map<Prefix, Bucket> data = {};
    u64 prefix_size;

    bool insert(const std::vector<s64>& elem, u64 hash = 0);
    bool insert_into_bucket(Bucket& bucket, Suffix* suffix);
    bool operator==(const Pareto_Set& other) const;
    u64 hash(u64 seed) const;

    friend std::ostream& operator<<(std::ostream& os, const Pareto_Set& obj);
};

Pareto_Set merge_pareto_sets(Pareto_Set& left, Pareto_Set& right);

#endif
