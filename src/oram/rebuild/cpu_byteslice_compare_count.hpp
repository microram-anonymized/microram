#pragma once

// How many key comparisons a merge makes, by kind -- compiled in only
// with MICRORAM_BYTESLICE_COMPARE_COUNT (a benchmark build; refused by release
// builds).  Each count is one 64 x 64 all-pairs nest of one key field across
// two buckets (Q: an 8-byte field, D: a 4-byte one) or one within a bucket
// (self). Wide counts are one exact two-qword nest, rather than independent
// field memberships; under kWideKeySegmentMatch a 16-byte comparison is
// instead four D counts. The merge is oblivious, so counts are a public function of the
// schedule; multiplied by each kind's per-call time from a long loop
// (cpu_byteslice_dedup_kernel_benchmark) they give the comparison time inside
// a merge without timing any single call.  Every hook site is rebuild-only
// (cpu_byteslice_dedup_masks.hpp); online probes are not counted.

#include "src/core/release_guard.hpp"

#include <cstdint>

#ifdef MICRORAM_BYTESLICE_COMPARE_COUNT
#include <atomic>
#endif

namespace microram {
namespace byteslice {

enum class CompareKind : unsigned {
  kPairQ, kPairD, kSelfQ, kSelfD, kPairWide, kSelfWide, kKinds
};

#ifdef MICRORAM_BYTESLICE_COMPARE_COUNT
inline std::atomic<uint64_t> g_compare_counts[static_cast<unsigned>(CompareKind::kKinds)];
inline void CountCompare(CompareKind kind) {
  g_compare_counts[static_cast<unsigned>(kind)].fetch_add(1, std::memory_order_relaxed);
}
inline uint64_t CompareCount(CompareKind kind) {
  return g_compare_counts[static_cast<unsigned>(kind)].load(std::memory_order_relaxed);
}
#else
inline void CountCompare(CompareKind) {}
#endif

}  // namespace byteslice
}  // namespace microram
