#pragma once

// OCCUPANCY OBSERVER: a diagnostic hook that reports how full each residual
// structure of a rebuild job gets, for comparing observed tails against the
// certified capacities (benchmarks/oram/cpu_byteslice_occupancy_observer.cpp).
//
// WHAT IT IS FOR.  The certificate bounds the probability that some residual
// structure of a rebuild job overflows its public capacity.  This header lets
// a diagnostic driver watch those structures at the one moment each is at its
// maximum, and nothing else:
//
//   kStageStash        a butterfly bit-level's shed stash (index = the bit).
//                      It only accumulates during the route, so its count when
//                      the residual pass that consumes it begins is its
//                      maximum for the job.  A swept slot is observed at the
//                      pass's first task (before the pool dedup clears
//                      anything); a drain-only slot, which the ridden routing
//                      pass sheds into AFTER the range table was built, at the
//                      first task of the pass's epilogue.
//   kRadixStash        the radix pass's shed (same rule).
//   kMergeStash        the fixed merge's shed (same rule).
//   kRetainedCarry     the top preparation's retained carry (a drain of the
//                      preparation pass, swept by the merge pass).
//   kRangeLeaf         a DFS leaf of a pass's range table (index = the pass):
//                      the sum over the leaf's stacked pages, in entries, right
//                      after the table is built and before any offer clears a
//                      bit.  Padding leaves are skipped.  Direct plans have no
//                      range event and report nothing.
//   kFinalTier         the published tier, when its job's last phase ends; the
//                      tier changes only by the finish's drains.
//
// The occupancy of a structure is a secret.  EVERYTHING here is therefore
// compiled out unless MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER is defined: the
// counting (popcounts, Count()), the hook load and the call vanish, and so do
// the job's observation members and the stage marks the planners attach.
// Only the diagnostic benchmark target defines it, and a build that does is
// not measuring anything.  release_guard.hpp turns the macro together with
// CPU_BYTESLICE_ORAM_RELEASE into a build error; a performance build must
// define that.
//
// The hook is a plain function pointer like the pause hook's: global, set once
// before the engine starts and cleared before the fixture's state goes out of
// scope.  It may be called from several owner threads, so a driver that runs
// owners or helpers must lock inside it.
//
// An occupancy above its capacity cannot be represented: every insertion is
// checked, and an overflow is a thrown, declared failure (the engine's "the
// certified depth did not hold"), not an observation.

#include <atomic>
#include <cstddef>
#include <cstdint>

#include "src/core/release_guard.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

enum class OccupancyKind : uint8_t {
  kStageStash,
  kRadixStash,
  kMergeStash,
  kRetainedCarry,
  kRangeLeaf,
  kFinalTier,
  kCount,
};

inline const char* OccupancyKindName(OccupancyKind kind) {
  switch (kind) {
    case OccupancyKind::kStageStash: return "stage_stash";
    case OccupancyKind::kRadixStash: return "radix_stash";
    case OccupancyKind::kMergeStash: return "merge_stash";
    case OccupancyKind::kRetainedCarry: return "retained_carry";
    case OccupancyKind::kRangeLeaf: return "range_leaf";
    case OccupancyKind::kFinalTier: return "final_tier";
    case OccupancyKind::kCount: break;
  }
  return "unknown";
}

// One exposure.  `job` counts the merge jobs of one level from 1 (a job is one
// bound merge or one direct initialization), so a reducer can group exposures
// into per-job blocks.  `occupancy` and `capacity` are in entries.
struct OccupancyEvent {
  OccupancyKind kind = OccupancyKind::kCount;
  unsigned level = 0;
  unsigned index = 0;
  uint64_t job = 0;
  size_t occupancy = 0;
  size_t capacity = 0;
};

using OccupancyHookFn = void (*)(const OccupancyEvent&);

inline std::atomic<OccupancyHookFn>& OccupancyHook() {
  static std::atomic<OccupancyHookFn> hook{nullptr};
  return hook;
}

inline void SetOccupancyHook(OccupancyHookFn hook) {
  OccupancyHook().store(hook, std::memory_order_release);
}

inline constexpr bool kOccupancyObserverCompiled =
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
    true;
#else
    false;
#endif

// Delivers one event.  With the macro off the arguments are discarded.
inline void ObserveOccupancy(const OccupancyEvent& event) {
#ifdef MICRORAM_BYTESLICE_OCCUPANCY_OBSERVER
  const OccupancyHookFn hook = OccupancyHook().load(std::memory_order_acquire);
  if (hook != nullptr) hook(event);
#else
  (void)event;
#endif
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
