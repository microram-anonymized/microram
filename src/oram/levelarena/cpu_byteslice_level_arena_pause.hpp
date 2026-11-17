#pragma once

// DETERMINISTIC PAUSE POINTS for the threaded engine's tests: named points
// before/after plan install, Ready enqueue, credit return, epoch waiter
// registration and group parking (plus the value workers' handoffs) at which
// a test fixture can stop an owner thread.
//
// WHY THIS EXISTS AT ALL.  Every interesting window in the threading protocol
// is a few instructions wide -- between the plan install and the slot handoff,
// between a credit reaching the ring and its owner being told, between an
// epoch waiter registering and the requester noticing -- and a fixture cannot
// be in one of them by chance.  A test that tried would be asserting a
// scheduling outcome, and such a test passes or fails with the load on the
// machine rather than with the code.  With a
// pause point the fixture STOPS the owner in the window and then takes its
// time, so what it checks is a state rather than a race it hopes to win.
//
// COMPILED OUT ENTIRELY without MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE, like the
// probe audit next door: the call becomes two discarded arguments and nothing
// remains in the object.  Only a fixture defines it, and a fixture that does
// is not measuring anything.
//
// THE HOOK IS A PLAIN FUNCTION POINTER, not a std::function: it is read from
// several owner threads at once and installed once before they start, so a
// single relaxed-acquire load is the whole of its synchronisation.  It is
// global because the points are inside objects the engine composes privately,
// and a fixture that runs two engines with hooks at once would have to tell
// them apart by `who` -- which is why the engine has no per-instance hook to
// suggest otherwise.

#include <atomic>

#include "src/core/release_guard.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// `who` is the LEVEL for publication/credit points, the GROUP INDEX for
// polling, epoch registration and parking points, and 0 for the one
// requester point.
enum class ArenaPause {
  kBeforePlanInstall,         // the delta is composed, nothing is installed
  kAfterPlanInstall,          // installed and probeable; the slot is not handed
                              // over and no Ready has been sent
  kAfterReadyEnqueue,         // the carry is in the receiver's ring and signalled
  kBeforeCreditReturn,        // retired inboxes are about to be reclaimed
  kAfterCreditReturn,         // their credits are in the producer's ring
  kAfterEpochWaiterRegistered,  // registered, before the final recheck
  kBeforeGroupPark,           // a round moved nothing; about to wait
  kAfterGroupPark,            // woken
  kAfterGroupPoll,            // poll returned, progress not yet recorded
  kBeforeEpochWaiterRegistered,  // failed poll, not yet registered
  // The REQUESTER, just inside a reader epoch it will close and announce:
  // an access, a batch or a plan diagnostic.  The one window in which an
  // owner can register against an epoch a requester is holding open.
  kInsideReaderEpoch,
  kBeforeValueThreadCreate,
  kBeforeValuePendingWrite,
  kBeforeValueRead,
  kBeforeValueDone,
  kCount,
};

using ArenaPauseFn = void (*)(ArenaPause point, unsigned who);

inline std::atomic<ArenaPauseFn>& ArenaPauseHook() {
  static std::atomic<ArenaPauseFn> hook{nullptr};
  return hook;
}

// Install before the owner threads start and clear before the fixture's own
// state goes out of scope; a hook that outlives what it captures is the one
// way to misuse this.
inline void SetArenaPauseHook(ArenaPauseFn hook) {
  ArenaPauseHook().store(hook, std::memory_order_release);
}

inline void ArenaPauseAt(ArenaPause point, unsigned who) {
#ifdef MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE
  const ArenaPauseFn hook = ArenaPauseHook().load(std::memory_order_acquire);
  if (hook != nullptr) hook(point, who);
#else
  (void)point;
  (void)who;
#endif
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
