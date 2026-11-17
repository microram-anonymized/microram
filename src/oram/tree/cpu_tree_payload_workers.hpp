#pragma once

// One thread per payload plane, and the protocol that feeds them
// (src/oram/tree/DESIGN.md, "Parallel payload").
//
// WHAT CROSSES CORES, AND NOTHING ELSE.  The metadata plane is the main
// thread's alone; each payload plane is one worker's alone
// (cpu_tree_layout.hpp's A SLICE OF THE ENTRY).  Per access the only shared
// bytes are: the public leaf, the plan (permute indices and masks plus a few
// flags), the caller's value copied in for a write and written out in
// slices, and K + K completion words.  A worker that touched the
// foreground's cache lines would spend its time on them, not on
// synchronization.
//
// PUBLISHED AS EACH BECOMES READY, NOT TOGETHER.  A job is published in two
// steps, each a release store to a sequence word on its own cache line, so a
// worker waits only for the word it needs next:
//
//   leaf_seq   the public leaf and the value copy -- the workers' slice
//              loads go out, and a short slice is transposed to byte lines,
//              while the main thread is still transposing its own chunk 0
//              and planning;
//   plan_seq   the access's plan.
//
// and answers with two words per worker, each on its own line:
//
//   value_ready  this worker's slice of `value_out` is complete -- released
//                after the routing of its last chunk, before that chunk's
//                inverse transposition and write-back, so the main thread
//                returns without waiting for the write-back;
//   done         the job is finished.
//
// THE JOB RING IS TWO SLOTS AND NEEDS NO EXTRA WAIT.  A worker publishes
// `value_ready(t)` only after `done(t-1)`, so by the time the main thread
// has collected `value_ready(t)` from every worker, slot (t+1) mod 2 --
// which job t-1 used -- is free.  Publishing job t+1 is therefore
// unconditional.
//
// SPIN, THEN PARK.  A futex wake costs a syscall and an inter-processor
// interrupt, which can take several times as long as a whole access
// (more so under virtualization); so a worker spins on the word it wants for
// `spin_micros` before it blocks, and the publisher only pays the wake when
// the worker is actually parked.  Every worker spins, not one: the access
// waits for all of them, so a single parked worker would put a wake on the
// critical path of every access.
//
// FAILURE.  The overflow check runs on the main thread, on the metadata
// lines, before the plan is published.  A pass that will not run is
// published as a CANCELLED one, so the workers still retire the job and the
// engine can be destroyed cleanly; nothing is written by anyone for a
// cancelled pass.

#include <immintrin.h>

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <functional>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <utility>
#include <vector>

#include "src/core/monitor_wait.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"

namespace microram {
namespace tree {

// A 64-bit counter alone on its cache line.  Every one of these has exactly
// one writer, so no line is ever contended for write.
struct alignas(64) PayloadSeqWord {
  std::atomic<uint64_t> v{0};
  char pad[64 - sizeof(std::atomic<uint64_t>)] = {};
};

// One published access, as the workers see it.  Written by the main thread
// only, in the two steps above.  `Plane` is the kind of plane the workers
// own (cpu_tree_read_path_oram.hpp's ReadPathPlane) and names the plan and
// pass types it applies.
template <class Plane>
struct PayloadJobSlotT {
  uint64_t read_leaf = 0;
  // Published with the plan: false for a cancelled pass.
  bool run_pass = false;
  typename Plane::Plan plan;
  alignas(16) uint8_t meta[kMetaBytes] = {};
  typename Plane::Pass pass;
  // The caller's value, copied in before the job is published, so no caller
  // memory is referenced after the access returns.
  std::vector<uint8_t> value_copy;
};

// Where a worker is in a job.  TEST-ONLY instrumentation: a hook called at
// each boundary is what lets a test hold one worker at a chosen point and
// check what the rest of the engine does meanwhile.  The hook is null in
// every build that is not a test, and the branch on it is on a public field.
enum class PayloadStage {
  kLeavesReceived,  // the job's leaf is in; nothing loaded yet
  kPlanReceived,    // the plan is in; the pass has not started
  kJobDone,         // the pass is finished and `value_ready` published,
                    // before `done` is published
};

struct PayloadWorkerKnobs {
  // Microseconds a worker spins on the word it wants before it parks.  0
  // parks at once; the maximum spins for ever (and burns K cores).
  unsigned spin_micros = 200;
  // After the spin window, MONITOR the word and sleep on it in a light
  // C-state instead of parking on a futex (src/core/monitor_wait.hpp): the
  // publisher's store is then the wake, with no syscall and no IPI on either
  // side.  Off by default, and a no-op where the CPU or the hypervisor does
  // not offer MWAITX / UMWAIT -- `PayloadWorkerPoolT::monitor_wait_kind()`
  // says which path a pool actually took.  Not tuned: many virtualized hosts
  // hide both instructions, so this is an opt-in knob for hosts that expose
  // them.
  bool monitor_wait = false;
  // The sleep's timeout, which only bounds how late a sleeper notices a stop
  // request: a store to the word wakes it regardless.
  unsigned monitor_wait_timeout_micros = 100;
  // Called once on each worker thread before it takes any work, with the
  // worker's index: the place to pin a thread to a core.  A throw from it
  // fails construction.
  std::function<void(unsigned)> init;
  // Test-only (PayloadStage): called on the worker thread at each stage
  // boundary with the worker index and the job number.
  std::function<void(unsigned, uint64_t, PayloadStage)> stage_observer;
  // Test-only: throw instead of creating worker `fail_thread_creation_at`
  // (1-based), which is how the partial-startup cleanup below is exercised
  // deterministically -- an OS thread limit is the real cause and is not
  // reproducible on demand.  0, the default, never throws.
  unsigned fail_thread_creation_at = 0;
};

// K threads, one per payload plane.
template <class Plane>
class PayloadWorkerPoolT {
 public:
  PayloadWorkerPoolT(std::vector<Plane*> planes, PayloadWorkerKnobs knobs)
      : knobs_(std::move(knobs)),
        monitor_(knobs_.monitor_wait ? core::DetectMonitorWait()
                                     : core::MonitorWaitKind::kNone),
        monitor_ticks_(uint64_t{knobs_.monitor_wait_timeout_micros} *
                       core::kTscTicksPerMicroBound),
        workers_(planes.size()) {
    for (size_t k = 0; k < planes.size(); ++k) {
      workers_[k] = std::make_unique<Worker>();
      workers_[k]->plane = planes[k];
      workers_[k]->index = static_cast<unsigned>(k);
    }
    // PARTIAL STARTUP IS THE CONSTRUCTOR'S TO CLEAN UP.  If a later
    // `std::thread` constructor throws -- an OS thread limit is the ordinary
    // cause -- the workers already created stay joinable, and because this
    // constructor never finished, its destructor does not run: destroying a
    // joinable `std::thread` member calls `std::terminate` and the caller's
    // catch never sees the original exception.  Every worker record exists
    // before any thread does and `Shutdown` skips the ones with no thread,
    // so it is the cleanup path for this as well as for a failed init hook.
    try {
      unsigned created = 0;
      for (auto& w : workers_) {
        if (knobs_.fail_thread_creation_at == ++created) {
          throw std::runtime_error(
              "payload worker pool: injected thread-creation failure");
        }
        w->thread = std::thread([this, wp = w.get()] { Loop(*wp); });
      }
      // The startup handshake: every worker has run its init hook (or failed)
      // before the constructor returns, so a pinning failure is a construction
      // failure and not a silent one on the first access.
      for (auto& w : workers_) {
        std::unique_lock<std::mutex> lk(w->m);
        w->started_cv.wait(lk, [&] { return w->started; });
      }
      for (auto& w : workers_) {
        if (w->init_error) std::rethrow_exception(w->init_error);
      }
    } catch (...) {
      Shutdown();
      throw;
    }
  }

  ~PayloadWorkerPoolT() { Shutdown(); }

  PayloadWorkerPoolT(const PayloadWorkerPoolT&) = delete;
  PayloadWorkerPoolT& operator=(const PayloadWorkerPoolT&) = delete;

  // Step 1: the public leaf and the value copy.
  void PublishLeaves(uint64_t job) { Publish(leaf_seq_, job); }
  // Step 2: the plan (or its cancellation).
  void PublishPlan(uint64_t job) { Publish(plan_seq_, job); }

  // Wait for every worker's slice of `value_out`: after the routing of the
  // pass, not after its stores.
  // Every worker's word is read on every round, so the words that are ready
  // are seen together rather than one cross-core miss after another.
  void WaitValueReady(uint64_t job) {
    unsigned spins = 0;
    for (;;) {
      bool all = true;
      for (auto& w : workers_) {
        all &= w->value_ready.v.load(std::memory_order_acquire) >= job;
      }
      if (all) break;
      if (++spins == kSpinsBeforeYield) {
        spins = 0;
        std::this_thread::yield();
      }
      _mm_pause();
    }
    RethrowIfFailed();
  }
  // Wait for every worker to have retired the job entirely.
  void WaitDone(uint64_t job) {
    for (auto& w : workers_) SpinWait(w->done.v, job);
    RethrowIfFailed();
  }
  // A worker has thrown and stopped.  Nothing it owned will advance again,
  // so the engine must refuse work rather than publish into a pool that
  // cannot answer.
  bool Failed() const { return failed_.load(std::memory_order_acquire); }

  // The slot a worker reads for job `job`; the pool owns two of them.
  PayloadJobSlotT<Plane>& slot(uint64_t job) { return slots_[job & 1]; }
  // How a worker waits past its spin window: parked on a futex (kNone), or
  // asleep on the word's cache line (the knob was on AND the CPU offers it).
  core::MonitorWaitKind monitor_wait_kind() const { return monitor_; }

 private:
  struct alignas(64) Worker {
    Plane* plane = nullptr;
    unsigned index = 0;
    PayloadSeqWord value_ready;
    PayloadSeqWord done;
    // Set while the worker is blocked on `cv`; read by the publisher, which
    // only then pays for a wake.  seq_cst on both sides, so the store-then-
    // load pair on each side cannot both miss (the standard handshake).
    std::atomic<uint64_t> parked{0};
    std::thread thread;
    std::mutex m;
    std::condition_variable cv;
    std::condition_variable started_cv;
    bool started = false;
    std::exception_ptr init_error;
  };

  void Publish(PayloadSeqWord& word, uint64_t job) {
    word.v.store(job, std::memory_order_seq_cst);
    for (auto& w : workers_) {
      if (w->parked.load(std::memory_order_seq_cst) != 0) {
        std::lock_guard<std::mutex> lk(w->m);
        w->cv.notify_one();
      }
    }
  }

  // Spin on a word the main thread waits for.  The main thread never parks:
  // it has the next access to run as soon as this returns, and a wake would
  // cost more than the wait.  It does yield after a long spin, so that a
  // descheduled worker costs a timeslice and not a whole quantum.
  //
  // IT DOES NOT GIVE UP WHEN A WORKER FAILS, and that is load-bearing.
  // `failed_` is pool-wide, so giving up on it would release the wait on ALL
  // the workers at one worker's failure, and `WaitValueReady` is what stands
  // between a worker's stores into the caller's `value_out` and the caller
  // getting its buffer back: the access would throw while the surviving
  // workers were still writing, and the caller could free the buffer under
  // them.  A failed worker cannot hang this wait, because the catch in
  // `Loop` retires EVERY job -- it publishes the maximum sequence number to
  // `value_ready` and `done` before it returns, and every wait here is
  // `>= want` -- so even a job published to a worker that has already
  // stopped (the `Failed()` check in `AccessThreaded` is not atomic with the
  // failure) is answered at once, and `RethrowIfFailed` reports it.
  void SpinWait(const std::atomic<uint64_t>& word, uint64_t want) const {
    unsigned spins = 0;
    while (word.load(std::memory_order_acquire) < want) {
      if (++spins == kSpinsBeforeYield) {
        spins = 0;
        std::this_thread::yield();
      }
      _mm_pause();
    }
  }

  void RethrowIfFailed() {
    const bool failed = failed_.load(std::memory_order_acquire);
    if (!failed) return;
    std::lock_guard<std::mutex> lk(error_mutex_);
    if (error_) std::rethrow_exception(error_);
  }

  // A worker's wait: spin for the window, then park on its own condition
  // variable until the publisher wakes it.
  bool Wait(Worker& w, const PayloadSeqWord& word, uint64_t want) {
    const unsigned spin = knobs_.spin_micros;
    if (spin == kSpinForever) {
      for (;;) {
        if (word.v.load(std::memory_order_acquire) >= want) return true;
        if (stop_.load(std::memory_order_acquire)) return false;
        _mm_pause();
      }
    }
    if (spin != 0) {
      const auto deadline =
          std::chrono::steady_clock::now() + std::chrono::microseconds(spin);
      do {
        // Keep publication/shutdown responsive while amortizing clock reads.
        // The finite window can overshoot by the remaining work in one group
        // (in addition to any OS preemption), at most 16 pauses and checks.
        constexpr unsigned kClockCheckSpins = 16;
        for (unsigned i = 0; i < kClockCheckSpins; ++i) {
          if (word.v.load(std::memory_order_acquire) >= want) return true;
          if (stop_.load(std::memory_order_acquire)) return false;
          _mm_pause();
        }
      } while (std::chrono::steady_clock::now() < deadline);
    }
    if (monitor_ != core::MonitorWaitKind::kNone) {
      // Arm, re-check, sleep: the re-check between the arm and the sleep is
      // what makes a store that landed just before the arm impossible to
      // miss, and a store after it wakes the sleep.  `stop_` is on another
      // line, so the timeout is what bounds a shutdown.  The publisher does
      // nothing for this path -- `parked` stays 0 -- so it never takes the
      // mutex and never issues a wake.
      for (;;) {
        core::MonitorWaitArm(monitor_, &word.v);
        if (word.v.load(std::memory_order_acquire) >= want) return true;
        if (stop_.load(std::memory_order_acquire)) return false;
        core::MonitorWaitSleep(monitor_, monitor_ticks_);
      }
    }
    std::unique_lock<std::mutex> lk(w.m);
    while (word.v.load(std::memory_order_acquire) < want &&
           !stop_.load(std::memory_order_acquire)) {
      w.parked.store(1, std::memory_order_seq_cst);
      // Re-check under the lock: a publisher that stored the word between
      // the check above and this one either sees `parked` or blocks on `m`
      // until this wait releases it.
      if (word.v.load(std::memory_order_seq_cst) >= want ||
          stop_.load(std::memory_order_seq_cst)) {
        w.parked.store(0, std::memory_order_seq_cst);
        break;
      }
      w.cv.wait(lk);
      w.parked.store(0, std::memory_order_seq_cst);
    }
    return word.v.load(std::memory_order_acquire) >= want;
  }

  void Loop(Worker& w) {
    {
      std::lock_guard<std::mutex> lk(w.m);
      try {
        if (knobs_.init) knobs_.init(w.index);
      } catch (...) {
        w.init_error = std::current_exception();
      }
      w.started = true;
    }
    w.started_cv.notify_one();
    if (w.init_error) return;

    uint64_t job = 1;
    for (;;) {
      if (!Wait(w, leaf_seq_, job)) return;  // shutdown
      PayloadJobSlotT<Plane>& s = slots_[job & 1];
      try {
        Observe(w, job, PayloadStage::kLeavesReceived);
        // The slice's loads go out now, while the main thread is still
        // transposing its own chunk 0 and planning, and then a short slice
        // is transposed to byte lines.
        w.plane->BeginPass(s.read_leaf);
        w.plane->PrepareSlice();
        if (!Wait(w, plan_seq_, job)) return;
        // The plan's lines at once, at the slot's own address: through the
        // pass's copied pointer they were a cross-core miss after the miss
        // on the pass itself.
        PrefetchLines(&s.plan, sizeof(s.plan));
        Observe(w, job, PayloadStage::kPlanReceived);
        if (s.run_pass) {
          // The plan is shared; the SIGNAL is this worker's own, so the pass
          // is copied and completed here rather than in the slot.
          typename Plane::Pass pass = s.pass;
          pass.plan = &s.plan;
          pass.signal = &w.value_ready.v;
          pass.signal_value = job;
          w.plane->ApplyPass(pass);
        } else {
          w.value_ready.v.store(job, std::memory_order_release);
        }
        Observe(w, job, PayloadStage::kJobDone);
      } catch (...) {
        Fail(std::current_exception());
        // Retire this job AND every later one: the words are monotone and
        // every wait is `>= want`, so the maximum answers any job number.
        // Retiring only `job` would leave a race -- a worker that failed
        // after its `value_ready(t)` could have job t+1 published to it if
        // the main thread's `Failed()` check ran before `failed_` was
        // visible, and then `WaitValueReady(t+1)` and the destructor's
        // `WaitDone` would spin for ever.  A worker that has stopped never
        // answers again, so the answer to everything is "done".
        w.value_ready.v.store(~uint64_t{0}, std::memory_order_release);
        w.done.v.store(~uint64_t{0}, std::memory_order_release);
        return;
      }
      w.done.v.store(job, std::memory_order_release);
      ++job;
    }
  }

  static void PrefetchLines(const void* p, size_t bytes) {
    const char* c = static_cast<const char*>(p);
    for (size_t i = 0; i < bytes; i += 64) _mm_prefetch(c + i, _MM_HINT_T0);
  }

  void Observe(const Worker& w, uint64_t job, PayloadStage stage) {
    if (knobs_.stage_observer) knobs_.stage_observer(w.index, job, stage);
  }

  void Fail(std::exception_ptr e) {
    std::lock_guard<std::mutex> lk(error_mutex_);
    if (!error_) error_ = std::move(e);
    failed_.store(true, std::memory_order_release);
  }

  void Shutdown() {
    if (stopped_) return;
    stopped_ = true;
    {
      stop_.store(true, std::memory_order_seq_cst);
      for (auto& w : workers_) {
        std::lock_guard<std::mutex> lk(w->m);
        w->cv.notify_one();
      }
    }
    for (auto& w : workers_) {
      if (w->thread.joinable()) w->thread.join();
    }
  }

  static constexpr unsigned kSpinForever = ~0u;
  // Pauses the requesting thread spins before it yields once.
  static constexpr unsigned kSpinsBeforeYield = 4096;

  PayloadWorkerKnobs knobs_;
  core::MonitorWaitKind monitor_;
  uint64_t monitor_ticks_;
  std::vector<std::unique_ptr<Worker>> workers_;
  PayloadJobSlotT<Plane> slots_[2];
  PayloadSeqWord leaf_seq_;
  PayloadSeqWord plan_seq_;
  std::atomic<bool> stop_{false};
  std::atomic<bool> failed_{false};
  std::mutex error_mutex_;
  std::exception_ptr error_;
  bool stopped_ = false;
};

}  // namespace tree
}  // namespace microram
