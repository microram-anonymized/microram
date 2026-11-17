#pragma once

// Ownership fixture shared by rebuild tests that need one residual stash per
// routing level.

#include <cstddef>
#include <cstring>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"

namespace microram {
namespace byteslice {
namespace test_support {

// Public fields keep setup concise in tests that inspect or deliberately
// resize individual slots.
struct OwnedLevelStashes {
  std::vector<ResidualStash> slots;
  Aligned64Ptr data;
  size_t bytes = 0;

  template <typename LayoutType>
  OwnedLevelStashes(unsigned num_slots, size_t buckets,
                    const LayoutType& layout) {
    bytes = static_cast<size_t>(num_slots) * buckets * layout.BucketBytes();
    data = AllocateAligned64(bytes);
    std::memset(data.get(), 0, bytes);
    slots.resize(num_slots);
    for (unsigned s = 0; s < num_slots; ++s) {
      slots[s].data = data.get() + s * buckets * layout.BucketBytes();
      slots[s].num_buckets = buckets;
      slots[s].entry_bytes = layout.EntryBytes();
    }
  }

  ResidualStash* ptr() { return slots.data(); }

  size_t Count() const {
    size_t count = 0;
    for (const ResidualStash& stash : slots) count += stash.Count();
    return count;
  }

  size_t total_count() const { return Count(); }

  bool SameAs(const OwnedLevelStashes& other) const {
    if (slots.size() != other.slots.size() || bytes != other.bytes) return false;
    for (size_t s = 0; s < slots.size(); ++s) {
      for (size_t b = 0; b < kMaxResidualStashBuckets; ++b) {
        if (slots[s].masks[b] != other.slots[s].masks[b]) return false;
      }
    }
    return std::memcmp(data.get(), other.data.get(), bytes) == 0;
  }
};

}  // namespace test_support
}  // namespace byteslice
}  // namespace microram

