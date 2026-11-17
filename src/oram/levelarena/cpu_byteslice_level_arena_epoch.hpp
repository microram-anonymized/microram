#pragma once

// The reader epoch: the one counter that says when a retired buffer's bytes
// stop being reachable.  The protocol is summarised in DESIGN.md,
// "Publication, readers and progress"; publication itself is
// cpu_byteslice_level_arena_publication.hpp.
//
// THE PROBLEM.  Publication is a pointer swap.  A request that has loaded the
// current plan holds raw views into main tables, tiers and mask words, and it
// keeps holding them for the rest of its cascade -- across any number of
// publications by any number of owners.  Nothing revokes those views, so the
// only safe rule is negative: a physical buffer may be written again once no
// reader that could have snapshotted it is still inside.
//
// THE COUNTER.  The requester bumps this word to an ODD value when it enters a
// plan and to an EVEN one when it leaves, so "odd" means "somebody is inside
// some plan".  An owner that has just replaced a plan samples the word as `e`
// and gives the removed sources the threshold
//
//     e + (e & 1)
//
// which is `e` itself when the requester is quiescent (its next snapshot is
// already the new plan, so the sources are unreachable now) and `e + 1` when
// it is inside (it may hold the old plan and must be allowed to finish).
// Reclamation then waits for an OBSERVED counter value to reach that
// threshold.
//
// WHAT AN EPOCH IS NOT.  It is not a publication id, not a version number and
// not a prediction.  `LevelArena::Reclaim(safe_epoch)` takes what an acquire
// load of this word has ACTUALLY reached; handing it a future threshold, or a
// count of publications, frees a buffer a reader is still in.  The two
// accessors below are named for their two roles so the wrong one is hard to
// pass: RetirementThreshold() is what a publisher STORES on a retired thing,
// Observed() is what a reclaimer COMPARES against.
//
// ONE REQUESTER.  A single odd/even word describes one active snapshot, not
// an arbitrary number of them: two readers inside at once would leave the word
// even between their entries, and an owner sampling it there would reclaim
// underneath the second.  That misuse is REJECTED rather than documented --
// Guard acquires with a compare-exchange that succeeds only from an EVEN
// value, so an odd counter is never modified and the second reader throws.
// (A fetch_add followed by a parity test is one instruction cheaper and wrong:
// between the increment and the test the counter reads even under a live
// cascade, and a reclamation in that window cannot be rolled back by the
// fetch_sub that follows.)  Several readers require registered per-reader
// epochs and a minimum-safe calculation; do not extend this counter by
// analogy.
//
// ORDERING.  Entry is a seq_cst read-modify-write and it precedes the seq_cst
// load of the plan pointer; publication is a seq_cst store of the plan pointer
// followed by a seq_cst load of this word.  That is the Dekker pair: at least
// one of the two sees the other, so a reader that missed the new plan is
// counted by the publisher, and a reader the publisher missed is one that
// already has the new plan.  Neither half works with acquire/release alone,
// which is why both are spelled seq_cst here and must stay so.

#include <atomic>
#include <cstdint>
#include <stdexcept>

namespace microram {
namespace byteslice {
namespace levelarena {

class ReaderEpoch {
 public:
  // The largest value a reader may enter at.  Entering adds one, leaving adds
  // one more, and a publisher may add one to what it samples in between, so
  // the last three values are kept out of reach rather than allowed to wrap.
  // Entry values are even, so this is the largest even one that leaves that
  // headroom.  Wrapping needs 2^63 accesses; refusing costs one predictable
  // branch per access and removes the argument.
  static constexpr uint64_t kMaxEntryEpoch = ~uint64_t{0} - 3;

  static constexpr const char* kOverlapError =
      "level arena: two requests overlapped on one reader epoch; requests "
      "must be serialized";

  ReaderEpoch() = default;

  // A counter that starts somewhere other than zero.  The engine never wants
  // this; what wants it is the exhaustion refusal above, which is otherwise
  // reachable only after 2^63 accesses and so would ship untested.  An odd
  // start would mean "a reader is inside" before any reader existed.
  explicit ReaderEpoch(uint64_t initial) : word_(initial) {
    if ((initial & 1) != 0) {
      throw std::invalid_argument(
          "level arena: a reader epoch starts quiescent, so it starts even");
    }
  }

  // The requester's snapshot.  Enter, load the plan, probe, leave -- in that
  // order, and with the plan load AFTER this constructor returns.
  class Guard {
   public:
    explicit Guard(ReaderEpoch& epoch, const char* overlap_error = kOverlapError)
        : epoch_(epoch), value_(epoch.Enter(overlap_error)) {}
    ~Guard() { epoch_.Leave(); }

    Guard(const Guard&) = delete;
    Guard& operator=(const Guard&) = delete;

    // The odd value this reader is inside.  Diagnostics: the reader's own
    // number is not what reclamation compares against.
    uint64_t value() const { return value_; }

   private:
    ReaderEpoch& epoch_;
    uint64_t value_;
  };

  // PUBLISHER, immediately after the seq_cst store that installed the new
  // plan.  The threshold to stamp on the plan and the sources it removed.
  uint64_t RetirementThreshold() const {
    const uint64_t e = word_.load(std::memory_order_seq_cst);
    return e + (e & 1);
  }

  // RECLAIMER: what the counter has actually reached.  Acquire, so that
  // everything the reader did inside its epoch happens-before the reuse of the
  // bytes it was reading.
  uint64_t Observed() const { return word_.load(std::memory_order_acquire); }

  // THE SAME VALUE, read with seq_cst, for an owner that is about to PARK on it
  // (the owner threads' wakeup protocol, cpu_byteslice_level_arena_owner.hpp).
  // An owner whose only remaining dependency is a retirement registers itself
  // as an epoch waiter and then re-reads this; the requester leaves its epoch
  // and then reads the waiter count.  That is the second Dekker pair in this
  // design -- at least one of the two sees the other, so either the owner sees
  // the epoch move and does not park, or the requester sees the registration
  // and wakes it -- and it needs both sides seq_cst for the same reason the
  // first one does.  Acquire would let each side's store sink past its own load
  // and neither would see anything, which is an owner asleep on a retirement
  // that has already come free.
  //
  // On x86 this compiles to the same load as Observed(); the ordering is a
  // statement about what the compiler and the model may do, not a cost.
  uint64_t ObservedForWaiter() const {
    return word_.load(std::memory_order_seq_cst);
  }

  // True while a request is inside a plan.  For the requester's own thread and
  // for tests that have separately established quiescence; reading it from an
  // owner tells you only what was true at some instant.
  bool Inside() const {
    return (word_.load(std::memory_order_acquire) & 1) != 0;
  }

 private:
  uint64_t Enter(const char* overlap_error) {
    uint64_t seen = word_.load(std::memory_order_seq_cst);
    for (;;) {
      if ((seen & 1) != 0) throw std::logic_error(overlap_error);
      if (seen > kMaxEntryEpoch) {
        throw std::runtime_error(
            "level arena: reader epoch exhausted; refusing to wrap a "
            "retirement threshold");
      }
      // A successful compare-exchange is a seq_cst read-modify-write, which is
      // the whole of the reader's half of the Dekker argument above.  Under
      // the one-requester contract the loop runs exactly once.
      if (word_.compare_exchange_weak(seen, seen + 1, std::memory_order_seq_cst,
                                      std::memory_order_seq_cst)) {
        return seen + 1;
      }
    }
  }

  void Leave() { word_.fetch_add(1, std::memory_order_seq_cst); }

  alignas(64) std::atomic<uint64_t> word_{0};
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
