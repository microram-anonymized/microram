#pragma once

// THE BATCH PARTICIPANTS' THREAD POOL, used by the level arena's batched
// access path (cpu_byteslice_level_arena_batch.hpp).
//
// A parallel batch uses joined prepare, probe and forward phases (bucket-owned
// scans split probing into scan and merge/suffix phases) over
// `participants` tiles, and this is the only thing standing between them:
// participant 0 is the CALLING thread, participants 1..p-1 are persistent
// helpers, and `RunPhase` runs one phase on all of them and returns when the
// last has retired.  There is no work stealing, no queue and no partial join:
// each participant owns one tile for the life of the call, and the phases are
// separated by full barriers because each reads what the previous one wrote
// into another participant's bank.
//
// WHY A SEPARATE POOL FROM THE OWNER THREADS.  They wait for different things
// on different timescales.  An owner waits for a carry, a credit or a reader
// epoch and may sleep for milliseconds; a participant waits for the next
// phase of a call that is already in flight, tens of microseconds away, and a
// participant that overslept would hold up the request thread rather than the
// rebuild.  Sharing one pool would also break the engine's one-actor-per-role
// rule (each slot and message queue has exactly one thread acting for each
// role, and grouping never runs two steps of one level at once) by letting a
// thread that is inside a level's step be handed a probe.
//
// THE JOIN IS UNCONDITIONAL, INCLUDING ON FAILURE.  A phase that threw on one
// participant still has the others inside the plan, so the coordinator retires
// every participant of the phase before it looks at the error and only then
// rethrows, for the reason every probe path in this library obeys: no plan,
// slab or arena may be reclaimed while a probing participant is still in it.
//
// LOST WAKES are the OwnerEvent protocol's (read the generation, then poll,
// then wait), restated here over two events: one per helper for "there is a
// phase" and one shared for "a helper has retired".  Nothing in this file
// invents an ordering; what it owes is that the request store precedes the
// signal and the completion store precedes its signal, which is the same
// "make the work visible, then signal" both sides of the engine already obey.

#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <exception>
#include <functional>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_event.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

class BatchWorkerPool {
 public:
  struct Config {
    unsigned participants = 1;  // the caller included; helpers are p - 1
    uint64_t spin_nanos = 0;
    std::chrono::microseconds park_retry{1000};
    // Bounds the start wait and the phase join, which end the process on
    // expiry; the engine passes its AbortWaitLimit, never less than 120 s.
    std::chrono::milliseconds wait_limit{120 * 1000};
    // Run once ON each helper before it takes any phase, with its participant
    // index (>= 1).  A hook that throws is a CONSTRUCTION failure, for the
    // same reason the owner threads' is: the alternative is a surprise for
    // the first batch.
    std::function<void(unsigned)> thread_init;
  };

  explicit BatchWorkerPool(const Config& config)
      : participants_(config.participants),
        spin_nanos_(config.spin_nanos),
        park_retry_(config.park_retry),
        wait_limit_(config.wait_limit) {
    if (participants_ == 0) {
      throw std::invalid_argument(
          "level arena: a batch has at least one participant, the caller");
    }
    const unsigned helpers = participants_ - 1;
    helpers_.reserve(helpers);
    for (unsigned t = 0; t < helpers; ++t) {
      helpers_.push_back(std::make_unique<Helper>());
    }
    try {
      for (unsigned t = 1; t <= helpers; ++t) {
        threads_.emplace_back([this, t, init = config.thread_init] {
          Entry(t, init);
        });
      }
      // Every helper has reported in -- in its loop, or failed in its init
      // hook, which is then this constructor's exception.
      AwaitStarted();
      Rethrow();
    } catch (...) {
      // Thread creation can also fail after some helpers have started. They
      // must leave their hooks before Stop can safely join them.
      AwaitStarted();
      Stop();
      throw;
    }
  }

  BatchWorkerPool(const BatchWorkerPool&) = delete;
  BatchWorkerPool& operator=(const BatchWorkerPool&) = delete;

  ~BatchWorkerPool() { Stop(); }

  unsigned participants() const { return participants_; }

  // One phase over participants [0, active).  `active` may be fewer than the
  // pool was built for -- a short batch does not need every tile -- and the
  // helpers past it are not woken at all.
  template <class Fn>
  void RunPhase(unsigned active, Fn&& fn) {
    // Borrow the callable for this synchronous phase. No std::function
    // conversion or allocation, even for large captures or move-only lambdas.
    // Await joins every participant before this descriptor or fn can expire.
    const auto invoke = [&fn](unsigned t) { fn(t); };
    const PhaseFn phase{
        &invoke, [](const void* context, unsigned t) {
          (*static_cast<const decltype(invoke)*>(context))(t);
        }};
    if (active == 0 || active > participants_) {
      throw std::invalid_argument(
          "level arena: a batch phase runs on 1.." +
          std::to_string(participants_) + " participants");
    }
    uint64_t generation = 0;
    if (active > 1) {
      phase_ = &phase;
      // The job pointer is published before any helper is told there is one.
      generation = generation_.fetch_add(1, std::memory_order_seq_cst) + 1;
      for (unsigned t = 1; t < active; ++t) {
        Helper& helper = *helpers_[t - 1];
        helper.requested.store(generation, std::memory_order_release);
        helper.wake.Signal();
      }
    }
    try {
      phase(0);
    } catch (...) {
      RecordFailure(std::current_exception());
    }
    // NEVER abandon the join because this thread failed: the helpers are
    // still inside the caller's plan and tiles.
    Await(generation, active);
    phase_ = nullptr;
    Rethrow();
  }

  const OwnerWaitStats& waits(unsigned participant) const {
    if (participant == 0) return coordinator_waits_;
    return helpers_.at(participant - 1)->waits;
  }

 private:
  struct PhaseFn {
    const void* context;
    void (*invoke)(const void*, unsigned);
    void operator()(unsigned t) const { invoke(context, t); }
  };

  struct Helper {
    OwnerEvent wake;                      // the coordinator signals it
    // Coordinator and helper write different lines. The retirement event is
    // deliberately shared, but these per-helper handoffs need not ping-pong.
    alignas(64) std::atomic<uint64_t> requested{0};
    alignas(64) std::atomic<uint64_t> completed{0};
    alignas(64) OwnerWaitStats waits;
  };

  void Entry(unsigned t, const std::function<void(unsigned)>& init) {
    Helper& helper = *helpers_[t - 1];
    try {
      if (init) init(t);
    } catch (...) {
      RecordFailure(std::current_exception());
      NoteStarted();
      return;
    }
    NoteStarted();
    uint64_t seen = 0;
    for (;;) {
      // Read the generation, then poll, then wait: the OwnerEvent contract.
      const uint64_t event = helper.wake.Generation();
      const uint64_t requested =
          helper.requested.load(std::memory_order_acquire);
      if (stop_.load(std::memory_order_acquire)) return;
      if (requested == seen) {
        helper.wake.Wait(event, spin_nanos_, park_retry_,
                         [this] {
                           return stop_.load(std::memory_order_acquire);
                         },
                         &helper.waits);
        continue;
      }
      seen = requested;
      try {
        (*phase_)(t);
      } catch (...) {
        RecordFailure(std::current_exception());
      }
      // The phase's stores precede this release, and this release precedes
      // the signal: a coordinator that observes the completion observes
      // everything the phase wrote.
      helper.completed.store(seen, std::memory_order_release);
      retired_.Signal();
    }
  }

  void Await(uint64_t generation, unsigned active) {
    if (active <= 1) return;
    const std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::now() + wait_limit_;
    for (;;) {
      const uint64_t event = retired_.Generation();
      bool all = true;
      for (unsigned t = 1; t < active; ++t) {
        if (helpers_[t - 1]->completed.load(std::memory_order_acquire) !=
            generation) {
          all = false;
          break;
        }
      }
      if (all) return;
      if (std::chrono::steady_clock::now() > deadline) {
        // A DEADLOCK DETECTOR, and it ENDS THE PROCESS rather than throwing,
        // which is the honest outcome rather than a harsh one: a participant
        // that has not retired is still inside the caller's plan and tiles,
        // so returning would let them be reclaimed underneath it and
        // unwinding past this point would do the same.  The engine makes the
        // same call at the two other places where a thread can be neither
        // joined nor released (shutdown joins every worker before storage is
        // released).  On a healthy pool no wait comes near
        // this, and nothing asserts that one finished in any particular time.
        std::fprintf(stderr,
                     "level arena: a batch participant never retired its "
                     "phase, so it can be neither joined nor released while "
                     "it is still inside this batch's plan.\n");
        std::abort();
      }
      retired_.Wait(event, spin_nanos_, park_retry_, [] { return false; },
                    &coordinator_waits_);
    }
  }

  void Stop() {
    stop_.store(true, std::memory_order_release);
    for (const std::unique_ptr<Helper>& helper : helpers_) {
      helper->wake.Signal();
    }
    for (std::thread& thread : threads_) {
      if (thread.joinable()) thread.join();
    }
    threads_.clear();
  }

  void RecordFailure(std::exception_ptr error) {
    std::lock_guard<std::mutex> lock(mutex_);
    if (!failure_) failure_ = error;
  }

  void Rethrow() {
    std::lock_guard<std::mutex> lock(mutex_);
    if (!failure_) return;
    const std::exception_ptr error = failure_;
    failure_ = nullptr;  // one call reports it; the next batch may succeed
    std::rethrow_exception(error);
  }

  void NoteStarted() {
    {
      std::lock_guard<std::mutex> lock(mutex_);
      ++started_;
    }
    started_changed_.notify_all();
  }

  void AwaitStarted() {
    std::unique_lock<std::mutex> lock(mutex_);
    if (started_changed_.wait_for(lock, wait_limit_, [this] {
          return started_ == threads_.size();
        })) {
      return;
    }
    // A hook cannot be cancelled or detached safely: it still holds this
    // pool and the caller's captured state. Match the owner startup policy.
    std::fprintf(stderr,
                 "level arena: a batch participant never returned from its "
                 "thread-init hook, so it can be neither joined nor released.\n");
    std::abort();
  }

  const unsigned participants_;
  const uint64_t spin_nanos_;
  const std::chrono::microseconds park_retry_;
  const std::chrono::milliseconds wait_limit_;
  std::vector<std::unique_ptr<Helper>> helpers_;
  std::vector<std::thread> threads_;
  std::atomic<uint64_t> generation_{0};
  std::atomic<bool> stop_{false};
  const PhaseFn* phase_ = nullptr;
  OwnerEvent retired_;
  OwnerWaitStats coordinator_waits_;
  std::mutex mutex_;
  std::condition_variable started_changed_;
  size_t started_ = 0;                    // mutex_
  std::exception_ptr failure_;            // mutex_
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
