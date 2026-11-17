#pragma once

// A conventional (not oblivious) hash table with our table's shape -- 64-slot
// buckets at load 1/2 -- and two ways to rebuild it from half-loaded tables of
// the same shape: the rebuild comparators of
// cpu_byteslice_table_rebuild_benchmark's `sort-merge` and `direct-merge`
// modes.  K4 keys, V8 values, distinct keys.
//
// A slot is {tag, key, value}, 16 bytes.  The tag's top bit is the occupancy
// bit (set: empty); the other 31 bits are the key's hash, whose top bits are
// its bucket.  A rebuild hashes every record again.
//
// SortRebuild, in place: one forward pass hashes each occupied slot's record
// and compacts the records to the front of the storage, std::sort orders them
// by tag (one comparison), and one backward pass moves each bucket's run to
// the bucket's first slot and marks the slots between runs empty.  The
// backward pass is safe when every record moves right: the records of
// buckets 0..b-1 must number at most 64 b.  With 32 records per bucket on
// average that fails only when the first buckets overflow (about 1e-7 per
// build); the pass then caps every unplaced bucket at 64 records, the rest
// going to a small stash, and continues.
//
// DirectRebuild, into separate storage: one pass hashes each occupied slot's
// record into slot 64 b + count[b] of its bucket b (a full bucket's records go
// to the stash), then one pass over the buckets marks each one's unused slots
// empty.
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <vector>

namespace benchmark_support {

class BucketTable {
 public:
  struct Slot {
    uint32_t tag;  // kEmpty, or the key's hash
    uint32_t key;
    uint8_t value[8];
  };
  static constexpr uint32_t kEmpty = uint32_t{1} << 31;
  static constexpr size_t kSlots = 64;

  static uint32_t Tag(uint32_t key) {  // MurmurHash3's finalizer, top 31 bits
    key ^= key >> 16;
    key *= 0x85ebca6bu;
    key ^= key >> 13;
    key *= 0xc2b2ae35u;
    return (key ^ (key >> 16)) >> 1;
  }

  // A table of `buckets` (a power of two) buckets over caller storage of
  // 64 * buckets slots.
  BucketTable(Slot* slots, size_t buckets) : slots_(slots), buckets_(buckets) {
    if (buckets == 0 || (buckets & (buckets - 1)) != 0) {
      throw std::invalid_argument("bucket table: buckets must be a power of two");
    }
    while ((size_t{1} << bits_) < buckets) ++bits_;
    stash_.reserve(kStashReserve);
  }

  size_t slots() const { return buckets_ * kSlots; }
  const std::vector<Slot>& stash() const { return stash_; }

  // Rebuilds the table in place from the records in its storage, which may
  // lie anywhere among empty slots (two tables of half its buckets, say).
  void SortRebuild() {
    stash_.clear();
    size_t n = 0;
    for (size_t i = 0; i < slots(); ++i) {
      if (slots_[i].tag & kEmpty) continue;
      Slot s = slots_[i];
      s.tag = Tag(s.key);
      slots_[n++] = s;
    }
    std::sort(slots_, slots_ + n, [](const Slot& a, const Slot& b) { return a.tag < b.tag; });
    size_t end = slots();  // the first slot of the last run placed
    for (size_t i = n; i > 0;) {
      const size_t bucket = Bucket(slots_[i - 1].tag);
      size_t j = i - 1;
      while (j > 0 && Bucket(slots_[j - 1].tag) == bucket) --j;
      const size_t first = bucket * kSlots;
      if (first < j) {  // earlier buckets overflowed
        i = CapBuckets(i);
        continue;
      }
      size_t count = i - j;
      if (count > kSlots) {
        stash_.insert(stash_.end(), slots_ + j + kSlots, slots_ + i);
        count = kSlots;
      }
      if (first != j) std::memmove(slots_ + first, slots_ + j, count * sizeof(Slot));
      for (size_t k = first + count; k < end; ++k) slots_[k].tag = kEmpty;
      end = first;
      i = j;
    }
    for (size_t k = 0; k < end; ++k) slots_[k].tag = kEmpty;
  }

  // Rebuilds the table from the records among `source_slots` slots of
  // `source` (separate storage).  `counts` has one zero per bucket and is
  // left zero.
  void DirectRebuild(const Slot* source, size_t source_slots, uint32_t* counts) {
    stash_.clear();
    for (size_t i = 0; i < source_slots; ++i) {
      if (source[i].tag & kEmpty) continue;
      Slot s = source[i];
      s.tag = Tag(s.key);
      const size_t bucket = Bucket(s.tag);
      const uint32_t c = counts[bucket]++;
      if (c < kSlots) {
        slots_[bucket * kSlots + c] = s;
      } else {
        stash_.push_back(s);
      }
    }
    for (size_t b = 0; b < buckets_; ++b) {
      for (size_t k = std::min<size_t>(counts[b], kSlots); k < kSlots; ++k) {
        slots_[b * kSlots + k].tag = kEmpty;
      }
      counts[b] = 0;
    }
  }

  // The value of `key`, if present.
  bool Find(uint32_t key, uint8_t* value) const {
    const uint32_t tag = Tag(key);
    const Slot* bucket = slots_ + Bucket(tag) * kSlots;
    for (size_t i = 0; i < kSlots && !(bucket[i].tag & kEmpty); ++i) {
      if (bucket[i].key == key) {
        std::memcpy(value, bucket[i].value, sizeof(bucket[i].value));
        return true;
      }
    }
    for (const Slot& s : stash_) {
      if (s.key == key) {
        std::memcpy(value, s.value, sizeof(s.value));
        return true;
      }
    }
    return false;
  }

  // Occupied slots plus stash records.
  size_t Count() const {
    size_t n = stash_.size();
    for (size_t i = 0; i < slots(); ++i) n += !(slots_[i].tag & kEmpty);
    return n;
  }

 private:
  static constexpr size_t kStashReserve = 1024;

  size_t Bucket(uint32_t tag) const { return size_t((uint64_t{tag} << bits_) >> 31); }

  // Keeps at most 64 records of each bucket among sorted slots [0, n), in
  // order, and stashes the rest; returns how many it kept.
  size_t CapBuckets(size_t n) {
    size_t kept = 0, run = 0, previous = 0;
    for (size_t i = 0; i < n; ++i) {
      const size_t bucket = Bucket(slots_[i].tag);
      run = i != 0 && bucket == previous ? run + 1 : 1;
      previous = bucket;
      if (run > kSlots) {
        stash_.push_back(slots_[i]);
      } else {
        slots_[kept++] = slots_[i];
      }
    }
    return kept;
  }

  Slot* slots_;
  size_t buckets_;
  unsigned bits_ = 0;
  std::vector<Slot> stash_;
};

}  // namespace benchmark_support
