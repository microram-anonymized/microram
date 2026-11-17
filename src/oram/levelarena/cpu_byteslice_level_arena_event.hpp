#pragma once

// ONE OWNER'S WAKEUP: the counter a signaller bumps, the park a waiter does
// when it has nothing left to do, and the argument that says no wake is ever
// lost.  Rebuild owners (cpu_byteslice_level_arena_owner.hpp) and the top's
// helper threads park here when no level of their group can make progress;
// publications, credits and flushes signal it.  The protocol -- spin,
// register, recheck, park -- depends only on this engine's own cancellation
// condition, which the caller passes in, so the argument for it is stated
// here in full.
//
// THE LOST-WAKE ARGUMENT, which is the whole of this file.  A waiter has a
// predicate it cannot cheaply re-evaluate (for an owner: "some level of my
// group can move"), so it polls instead.  The rule is:
//
//     READ THE GENERATION, THEN POLL, THEN WAIT FOR THE GENERATION TO CHANGE.
//
// and the signaller's rule is the mirror of it: MAKE THE WORK VISIBLE, THEN
// SIGNAL.  Take any signal.  Either its bump precedes the waiter's read of the
// generation -- and then the work it announced was visible before that read,
// so the poll that follows finds it -- or it does not, and then the generation
// the waiter is waiting on has already changed and the wait returns at once.
// There is no third case, and that is why `Wait` takes the generation as an
// argument rather than sampling it itself: sampling it inside would put the
// read AFTER the poll, which is exactly the window this is written to close.
//
// PARKING WITHOUT A LOCK ON THE SIGNAL PATH.  A signal is sent once per
// publication, per credit and per flush, and the waiter is usually not asleep;
// taking its mutex every time to find that out would put a cross-core
// acquire on the path every owner runs most often.  So `sleepers_` is an
// atomic the signaller reads first, and the two sides form a Dekker pair:
//
//     signaller:  bump generation (seq_cst RMW);  load sleepers (seq_cst)
//     waiter:     increment sleepers (seq_cst);   load generation (seq_cst)
//
// at least one of the two sees the other's write.  If the signaller sees a
// sleeper it takes the mutex and notifies; if the waiter sees the new
// generation it never parks.  Both orderings must stay seq_cst -- with
// acquire/release the two writes may both be reordered past the two loads and
// neither side sees anything, which is a waiter asleep with work in front of
// it.  (On x86 the cost is one locked add on the waiter's registration, which
// is on the parking path and not on the signalling one.)
//
// A COUNT, NOT A FLAG, because an event may have several waiters: a group's
// helpers all park on one (LevelHelpers).  With a flag, the first waiter to
// leave clears it while another is still asleep, the next signal reads "no
// sleeper" and skips the notify, and the one still asleep sleeps to its retry
// deadline with work in front of it.
// Each waiter adds itself before its recheck and takes itself away on either
// way out, so the count is nonzero whenever anyone is registered to park.  The
// same goes for what ends a park: it is the generation, which every waiter
// compares against its own read, and never a shared "you were signalled" word
// that one waiter could consume or clear for the rest.
//
// AND A TIMEOUT ANYWAY.  The park has a retry deadline, so a wake lost to a
// bug in the caller's own ordering degrades to a delay instead of a hang, and
// the timeout is COUNTED: a nonzero `timeouts` in a run that should have been
// event-driven is the symptom, and it is visible rather than silent.  It does
// NOT see a wake lost here, after the signal: a waiter the notify missed finds
// the generation changed when its deadline comes, which is indistinguishable
// from a signal that arrived at the deadline, and is not counted.  A test of
// this file has to check how LONG a signalled waiter took to return.

#include <immintrin.h>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <mutex>

namespace microram {
namespace byteslice {
namespace levelarena {

// One counter a waiting thread increments and somebody else reports.  ATOMIC,
// and not out of caution: the engine's statistics report the wait counts,
// which means they are read from a thread other than the one that keeps them,
// and the alternative to an atomic is a plain word torn across threads -- a
// data race whatever its consequences.  Relaxed throughout, because it orders nothing;
// the reader wants the number, not what the waiter did before it.
class WaitCounter {
 public:
  void Bump() { value_.fetch_add(1, std::memory_order_relaxed); }
  void Add(uint64_t by) { value_.fetch_add(by, std::memory_order_relaxed); }
  uint64_t get() const { return value_.load(std::memory_order_relaxed); }

 private:
  std::atomic<uint64_t> value_{0};
};

// What one waiter's parks cost, for the engine's wait statistics.
struct OwnerWaitStats {
  WaitCounter spins;          // spins that ran to their full budget
  WaitCounter spin_wakes;     // returns from the spin, before any park
  WaitCounter avoided_parks;  // the recheck under the mutex caught it
  WaitCounter parks;
  WaitCounter timeouts;  // retry deadlines reached with nothing signalled

  // HOW LONG THE WAITING TOOK, which a count of parks on its own cannot say:
  // ten parks of a microsecond and ten of a millisecond are the same count and a hundredfold difference in what the
  // hierarchy cost this thread.  Measured around the park alone -- the spin
  // is a fixed budget the caller already knows -- so a park that returned at
  // once is a park of nearly no time rather than an invisible one.
  WaitCounter park_nanos;

  uint64_t waits() const {
    return spin_wakes.get() + avoided_parks.get() + parks.get();
  }
};

class OwnerEvent {
 public:
  OwnerEvent() = default;
  OwnerEvent(const OwnerEvent&) = delete;
  OwnerEvent& operator=(const OwnerEvent&) = delete;

  // The value a waiter must read BEFORE it polls; see the header.
  uint64_t Generation() const {
    return generation_.load(std::memory_order_seq_cst);
  }

  // Signals so far, as a diagnostic snapshot.  Every signal bumps the
  // generation exactly once and nothing else does, so it IS the count; a
  // second counter would be one more locked add on every signal.
  uint64_t signals() const {
    return generation_.load(std::memory_order_relaxed);
  }

  // Whether a signal has arrived since `generation` was read.  The check a
  // running phase makes between two pieces (PhaseYield): relaxed, because it
  // orders nothing -- the owner that stops re-reads Generation() before it
  // polls, which is where the lost-wake argument above lives.
  bool ChangedSince(uint64_t generation) const {
    return generation_.load(std::memory_order_relaxed) != generation;
  }

  // SIGNALLER.  Call it AFTER the work it announces is visible -- after the
  // release store that publishes a slot, after the ring push that carries a
  // credit, after the plan install.  Signalling first announces a state the
  // waiter may not see, which is the same lost wake from the other side.
  void Signal() {
    generation_.fetch_add(1, std::memory_order_seq_cst);
    // The first half of the Dekker pair.  A false negative here is impossible;
    // a false POSITIVE (a waiter that has already left) costs one mutex
    // acquisition and a notify nobody receives.
    if (sleepers_.load(std::memory_order_seq_cst) == 0) return;
    // Nothing to write under the mutex -- the generation is the predicate --
    // but taking it is what orders this notify after the recheck of any
    // waiter that has registered: that waiter holds the mutex from its
    // registration until its wait releases it, so the notify cannot fall
    // between the two.
    { std::lock_guard<std::mutex> lock(mutex_); }
    wake_.notify_all();
  }

  // WAITER.  `generation` is what Generation() returned before the poll that
  // found nothing; `extra` is any other condition that should end the wait
  // (cancellation, and an owner's "the reader epoch moved").  Returns when the
  // generation has changed, `extra` holds, or the retry deadline passes.
  //
  // `spin_nanos` is a latency knob and nothing else: with it at zero this is a
  // pure park, which is what a fixture that means to observe a sleeping owner
  // wants.
  template <class Extra>
  void Wait(uint64_t generation, uint64_t spin_nanos,
            std::chrono::microseconds retry, Extra&& extra,
            OwnerWaitStats* stats) {
    const auto ready = [&] {
      return generation_.load(std::memory_order_seq_cst) != generation ||
             extra();
    };
    if (spin_nanos != 0) {
      const std::chrono::steady_clock::time_point begin =
          std::chrono::steady_clock::now();
      // The clock is read once every kSpinBatch pauses: a steady_clock read is
      // tens of cycles and a pause is a handful, so reading it every iteration
      // would make the spin a clock benchmark.
      constexpr unsigned kSpinBatch = 64;
      for (;;) {
        for (unsigned i = 0; i < kSpinBatch; ++i) {
          if (ready()) {
            stats->spin_wakes.Bump();
            return;
          }
          _mm_pause();
        }
        const uint64_t elapsed = static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                std::chrono::steady_clock::now() - begin)
                .count());
        if (elapsed >= spin_nanos) break;
      }
      stats->spins.Bump();
    }

    std::unique_lock<std::mutex> lock(mutex_);
    // The waiter's half of the Dekker pair: the registration PRECEDES the
    // recheck, so a signal that did not see it is a generation this recheck
    // does.  Both ways out take it back.  Relaxed there: every change to the
    // count is a read-modify-write of the one before it, so this can never
    // hide another waiter's registration, only end this one's.
    sleepers_.fetch_add(1, std::memory_order_seq_cst);
    if (ready()) {
      sleepers_.fetch_sub(1, std::memory_order_relaxed);
      stats->avoided_parks.Bump();
      return;
    }
    stats->parks.Bump();
    const std::chrono::steady_clock::time_point parked =
        std::chrono::steady_clock::now();
    const std::chrono::steady_clock::time_point deadline = parked + retry;
    while (!ready()) {
      if (wake_.wait_until(lock, deadline) == std::cv_status::timeout) {
        if (!ready()) stats->timeouts.Bump();
        break;
      }
    }
    sleepers_.fetch_sub(1, std::memory_order_relaxed);
    stats->park_nanos.Add(static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - parked)
            .count()));
  }

 private:
  // Its own line: the signaller writes it and the waiter polls it, and putting
  // it beside the mutex would make every signal invalidate the line the park
  // state lives in.
  alignas(64) std::atomic<uint64_t> generation_{0};
  alignas(64) std::atomic<uint32_t> sleepers_{0};  // registered to park
  alignas(64) std::mutex mutex_;
  std::condition_variable wake_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
