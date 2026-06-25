#include "../include/pareto_set.h"
#include <algorithm>

enum class Pareto_Cmp_Result : u8 {
    REMOVE_LOWER = 0x01,
    REMOVE_UPPER = 0x02,
    INCOMPARABLE = 0x03,
};

void swap(Pareto_Set::Bucket_Entry& lhs, Pareto_Set::Bucket_Entry& rhs) {
    std::swap(lhs.suffix, rhs.suffix);
}

Pareto_Cmp_Result cmp_pareto_optimal(const std::vector<s64>& upper, const std::vector<s64>& lower) {
    bool lower_is_covered = true;
    bool upper_is_covered = true;
    for (s64 elem_i = 0; elem_i < upper.size(); elem_i++) {
        s64 upper_elem = upper[elem_i];
        s64 lower_elem = lower[elem_i];
        if (lower_elem > upper_elem) {
           lower_is_covered = false;
        } else if (lower_elem < upper_elem) {
           upper_is_covered = false;
        }
    }

    if (lower_is_covered && upper_is_covered) { // Both are equal
        return Pareto_Cmp_Result::REMOVE_LOWER;
    } else if (lower_is_covered) {
        return Pareto_Cmp_Result::REMOVE_LOWER;
    } else if (upper_is_covered) {
        return Pareto_Cmp_Result::REMOVE_UPPER;
    } else {
        return Pareto_Cmp_Result::INCOMPARABLE;
    }
}

void sort_bucket(Pareto_Set::Bucket& bucket) {
    typedef std::vector<s64> vec;
    auto comparator = [](const Pareto_Set::Bucket_Entry& left_entry, const Pareto_Set::Bucket_Entry& right_entry) {
        // Is left < right ?std::vector<>
        if (left_entry.suffix == nullptr) return true;
        if (right_entry.suffix == nullptr) return false;

        auto& left  = *left_entry.suffix;
        auto& right = *right_entry.suffix;

        for (u64 i = 0; i < left.size(); i++) {
            if (left[i] > right[i]) return false;
            else if (left[i] < right[i]) return true;
        }
        return false;
    };
    std::sort(bucket.begin(), bucket.end(), comparator);
}

bool Pareto_Set::insert(const std::vector<s64>& elem, u64 hash) {
   Prefix prefix(prefix_size);
   for (s64 i = 0; i < prefix_size; i++) prefix[i] = elem[i];

   const auto& [pos, was_inserted] = data.emplace(prefix, Pareto_Set::Bucket{});
   u64 suffix_size = elem.size() - prefix_size;
   if (suffix_size > 0) {
        auto& bucket = pos->second;
        Suffix* suffix = new Suffix(elem.size() - prefix_size);
        for (s64 i = prefix_size; i < elem.size(); i++) (*suffix)[i - prefix_size] = elem[i];

        bool was_inserted = insert_into_bucket(bucket, suffix);
        if (!was_inserted) delete suffix;
   }

   return was_inserted;
}

bool Pareto_Set::insert_into_bucket(Bucket& bucket, Suffix* suffix) {
   bool should_be_inserted = true;

   s64 dest_bucket = -1;
   for (s64 bucket_slot_i = 0; bucket_slot_i < bucket.size(); bucket_slot_i++) {
      auto& bucket_entry = bucket[bucket_slot_i];
      if (bucket_entry.empty()) {
          if (dest_bucket == -1) dest_bucket = bucket_slot_i;
          continue;
      }

      auto cmp_result = cmp_pareto_optimal(*bucket_entry.suffix, *suffix);
      switch (cmp_result) {
         case Pareto_Cmp_Result::REMOVE_LOWER:
            should_be_inserted = false;
            break;
         case Pareto_Cmp_Result::REMOVE_UPPER:
            bucket_entry.empty_out();  // Clean out the pareto sub-optimal suffix
            dest_bucket = dest_bucket == -1 ? bucket_slot_i : dest_bucket;
            break;
         case Pareto_Cmp_Result::INCOMPARABLE:
            continue;
      }
   }

   if (should_be_inserted) {
       if (dest_bucket == -1) {
           bucket.emplace_back(suffix);
       } else {
           bucket[dest_bucket].suffix = suffix;
       }
       sort_bucket(bucket);
   }

   return should_be_inserted;
}


bool Pareto_Set::operator==(const Pareto_Set& other) const {
    bool are_eq = (data == other.data);
    return are_eq;
}

u64 Pareto_Set::hash(u64 seed) const {
    u64 hash = seed;

    for (auto& [prefix, suffix_buckets]: data) {
        hash = hash_combine(hash, hash_vector(prefix, 0));
        for (auto& bucket: suffix_buckets) {
            if (bucket.suffix == nullptr) continue;
            hash = hash_combine(hash, hash_vector(*bucket.suffix, 0));
        }
    }

    return hash;
}

Pareto_Set merge_pareto_sets(Pareto_Set& left, Pareto_Set& right) {
    Pareto_Set result = left;
    for (auto& [right_prefix, right_suffix_buckets]: right.data) {
        auto& result_bucket = result.data[right_prefix];
        if (result_bucket.empty()) {
            for (auto& right_suffix: right_suffix_buckets) {
                if (right_suffix.empty()) continue;
                Pareto_Set::Suffix* suffix_copy = new Pareto_Set::Suffix(*right_suffix.suffix);
                result_bucket.emplace_back(suffix_copy);
            }
        } else {
            for (auto& right_suffix: right_suffix_buckets) {
                if (right_suffix.empty()) continue;
                Pareto_Set::Suffix* suffix_copy = new Pareto_Set::Suffix(*right_suffix.suffix);
                bool was_inserted = result.insert_into_bucket(result_bucket, suffix_copy);
                if (!was_inserted) delete suffix_copy;
            }
        }
    }
    return result;
}

void write_prefix_with_bucket_contents(std::ostream& os, const Pareto_Set::Prefix& prefix, const Pareto_Set::Bucket& bucket) {
    os << prefix << ": {";
    bool written_elem = false;
    for (auto& bucket_entry: bucket) {
        if (bucket_entry.empty()) continue;

        if (written_elem) os << ", ";

        os << *bucket_entry.suffix;
        written_elem = true;
    }
    os << "}";
}

std::ostream& operator<<(std::ostream& os, const Pareto_Set& set) {
    if (set.data.empty()) {
        os << "Pareto_Set {}";
        return os;
    }
    os << "Pareto_Set { ";
    auto data_it = set.data.begin();
    write_prefix_with_bucket_contents(os, data_it->first, data_it->second);
    ++data_it;

    for (; data_it != set.data.end(); ++data_it) {
        os << ", ";
        write_prefix_with_bucket_contents(os, data_it->first, data_it->second);
    }
    os << "}";
    return os;
}

