#pragma once

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <condition_variable>
#include <exception>
#include <functional>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <vector>
#include "src/core/monitor_wait.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_bytes.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_value_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_pause.hpp"

namespace microram::byteslice::levelarena {

// VALUE WORKERS: optional persistent threads that extract a scalar access's
// user value in parallel with the requester's probe cascade (opt-in through
// `LevelArenaEngine::Options::value_workers`; see DESIGN.md, "Online security
// and capacity", and README.md).
//
// The value bytes of every slot are split into fixed, contiguous, public
// column ranges, one per worker.  The requester keeps the keys, occupancy and
// meta column and runs the usual first-match/tombstone cascade over the probe
// plan; as it finishes each entry it publishes the ValueProgress word
// (cpu_byteslice_level_arena_value_job.hpp).  Each worker recomputes the same
// hashed addresses from the plan, key and dummy base, prefetches the same
// buckets (a dense run whole; a hashed entry's real or dummy bucket, chosen
// exactly as the requester chooses it), and blends its columns of every
// bucket under a constant-time `take` mask.  The lines a worker reads are
// therefore those of the requester's own access, restricted to its columns.
// The requester keeps a public tail of the oldest entries (`tail`) and
// extracts those values itself; entry zero, the mutable online unit, always
// stays with the workers, which also write the previous access's insertion
// bytes into it at the start of each job.
//
// One synchronous job, no borrowed caller buffers, no hot-path allocations.
// Retirement mirrors the tree payload pool's maximum-sequence failure
// retirement; the Dekker park handshake's requester side is one fence per job
// in Join (WakeParked), not a locked store per worker. Start/done have one
// reader each; only monotone progress, the forwarded bytes and stop/failure
// have several. Requester-written and worker-written state never share a
// 128-byte line pair (the L2 spatial prefetcher's unit).
struct ValueTiming {
  uint64_t samples = 0, stamp = 0, address = 0, final_stamp = 0, insertion = 0;
};
inline uint64_t ValueStamp() { _mm_lfence(); return __rdtsc(); }
inline bool ValueSample(uint64_t sequence) {
  uint64_t x = sequence * 0x9E3779B97F4A7C15ull;
  x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ull;
  return ((x ^ (x >> 27)) & 63) == 0;
}
// Now plus a spin budget of `nanos`, saturated at the clock's last time
// point: a budget of 2^63 ns or more (UINT64_MAX is the natural spelling of
// "spin for ever") would overflow the signed clock, and it means for ever.
inline std::chrono::steady_clock::time_point SpinDeadline(uint64_t nanos) {
  using Clock = std::chrono::steady_clock;
  const Clock::time_point now = Clock::now();
  const uint64_t room = static_cast<uint64_t>(
      std::chrono::duration_cast<std::chrono::nanoseconds>(
          Clock::time_point::max() - now).count());
  if (nanos >= room) return Clock::time_point::max();
  return now + std::chrono::duration_cast<Clock::duration>(
                   std::chrono::nanoseconds(static_cast<int64_t>(nanos)));
}

class ValueWorkerPool {
 public:
  struct Config {
    unsigned workers = 0;
    bool serial = false;  // same jobs/kernels on the requester, for fixtures
    unsigned tail = 2;
    ValueKernel kernel = ValueKernel::kAuto;
    uint64_t spin_nanos = 200000;
    bool pause = true;
    bool monitor_wait = false;
    bool demote = false;
    bool profile = false;
    // Bounds the start wait and Join, which end the process on expiry; the
    // engine passes its AbortWaitLimit, never less than 120 s.
    unsigned wait_limit_millis = 120000;
    std::function<void(unsigned)> init;
    uint64_t initial_sequence = 0;  // rollover fixture; set before threads start
  };
  ValueWorkerPool(Config c, Layout layout, const AesTagKeys& aes,
                  size_t tables, size_t hashed)
      : config_(std::move(c)), layout_(layout), aes_(aes), max_tables_(tables), max_hashed_(hashed), pending_(layout.value_bytes - 1),
        monitor_(config_.monitor_wait ? core::DetectMonitorWait() : core::MonitorWaitKind::kNone) {
    if (config_.workers == 0 || config_.workers > 64)
      throw std::invalid_argument("value workers: count must be 1..64");
    if (tables > ValueProgress::kMaxEntries)
      throw std::invalid_argument("value workers: plan exceeds progress entry field");
    if (config_.kernel != ValueKernel::kAuto && config_.kernel != ValueKernel::kAccumulate &&
        config_.kernel != ValueKernel::kPermute)
      throw std::invalid_argument("value workers: invalid kernel");
    sequence_ = progress_sequence_ = config_.initial_sequence;
    progress_.store(ValueProgress::Pack(sequence_, 0, 0, 0, 0, 0, false),
                    std::memory_order_relaxed);
    const size_t width = pending_.size();
    for (unsigned t = 0; t < config_.workers; ++t) {
      auto w = std::make_unique<Worker>();
      w->start.sequence.store(sequence_, std::memory_order_relaxed);
      w->reply.done.store(sequence_, std::memory_order_relaxed);
      w->begin = width * t / config_.workers;
      w->end = width * (t + 1) / config_.workers;
      w->scratch.Resize(tables, hashed);
      w->selected.resize(tables);
      w->long_reply.resize(w->end - w->begin > 56 ? w->end - w->begin : 0);
      w->temp.resize(w->end - w->begin);
      workers_.push_back(std::move(w));
    }
    try {
      for (unsigned t = 0; t < config_.workers; ++t) {
        if (config_.serial) continue;
        ArenaPauseAt(ArenaPause::kBeforeValueThreadCreate, t);
        workers_[t]->thread = std::thread([this, t] { Loop(t); });
      }
      for (auto& w : workers_) {
        if (!w->thread.joinable()) continue;
        std::unique_lock<std::mutex> lock(w->mutex);
        if (!w->cv.wait_for(lock,std::chrono::milliseconds(config_.wait_limit_millis), [&] { return w->started; })) {
          std::fputs("value workers: init hook did not return; storage cannot be released\n",stderr);
          std::abort();
        }
      }
      Rethrow();
    } catch (...) { Shutdown(); throw; }
  }
  ~ValueWorkerPool() { Shutdown(); }
  ValueWorkerPool(const ValueWorkerPool&) = delete;
  ValueWorkerPool& operator=(const ValueWorkerPool&) = delete;
  static LevelArenaByteBill BufferBytes(unsigned workers, const Layout& layout,
                                        size_t tables, size_t hashed) {
    LevelArenaByteBill bill;
    if (!workers) return bill;
    const size_t width = layout.value_bytes - 1;
    bill.AddLineAligned(ByteRole::kRequestScratch, width);  // pool-owned forwarding
    for (unsigned t = 0; t < workers; ++t) {
      const size_t range = width * (t + 1) / workers - width * t / workers;
      for (size_t bytes : ProbeScratch::BufferSizes(tables, hashed))
        bill.AddLineAligned(ByteRole::kRequestScratch, bytes);
      bill.AddLineAligned(ByteRole::kRequestScratch, tables * sizeof(uint8_t*));
      bill.AddLineAligned(ByteRole::kRequestScratch, range);
      if (range > 56) bill.AddLineAligned(ByteRole::kRequestScratch, range);
      // Public transport records occupy separate 128-byte pairs inside Worker.
      bill.AddLineAligned(ByteRole::kBookkeeping, sizeof(ValueStart));
      bill.AddLineAligned(ByteRole::kBookkeeping, sizeof(ValueReply));
    }
    return bill;
  }
  unsigned count() const { return config_.workers; }
  unsigned tail() const { return config_.tail; }
  bool Failed() const { return failed_.load(std::memory_order_acquire); }
  ValueTiming timing(unsigned i) const { return workers_.at(i)->timing; }
  uint64_t sequence() const { return sequence_; }
  void CheckHealthy() { Rethrow(); }
  uint64_t Begin(const ProbePlan* plan, KeyWords key, uint64_t dummy,
                 size_t boundary, uint8_t* pending_bucket, size_t slot,
                 const uint8_t* pending_bytes) {
    Rethrow();
    if (active_) throw std::logic_error("value workers: overlapping jobs");
    if (sequence_ >= ~uint64_t{0} - 1)
      throw std::overflow_error("value workers: sequence exhausted");
    if (pending_bucket && slot >= 64) throw std::length_error("value workers: invalid pending slot");
    if (plan) {
      if (plan->first_live > plan->tables.size() || plan->tables.size() > max_tables_ ||
          plan->addressing.hashed > max_hashed_)
        throw std::length_error("value workers: plan exceeds reserved scratch");
      const size_t n = plan->tables.size() - plan->first_live;
      if (n > 255 || boundary > n) throw std::length_error("value workers: invalid boundary");
      for (size_t i = plan->first_live; i < plan->tables.size(); ++i)
        if (plan->tables[i].num_buckets > ValueProgress::kMaxRun &&
            plan->tables[i].kind == TableKind::kDense)
          throw std::length_error("value workers: dense run exceeds progress field");
    }
    // Null bytes: already staged (Stage), the engine's way.
    if (pending_bucket && pending_bytes) Stage(pending_bytes);
    ++sequence_;
    // No reset per job: a worker reads a word with another job's tag as no
    // progress, so its first poll can hit the stale line it holds. The word
    // must be rewritten only before its 16-bit tag could name this job.
    if (sequence_ - progress_sequence_ >= 0x10000) StoreProgress(0, 0, 0, 0, 0, false, false);
    active_ = true;
    for (auto& w : workers_) {
      w->start.plan = plan;
      w->start.key = key;
      w->start.dummy_base = dummy;
      w->start.boundary = static_cast<uint32_t>(boundary);
      w->start.pending_bucket = pending_bucket;
      w->start.pending_slot = static_cast<uint32_t>(slot);
      w->start.sequence.store(sequence_, std::memory_order_release);
      Demote(&w->start);
    }
    // Release stores, no fence: a locked store per worker would wait out each
    // line's ownership transfer in turn, before the requester's own cascade.
    // Join wakes parked workers (WakeParked).
    return sequence_;
  }
  // The next job's forwarded bytes, between jobs only. Staged right after a
  // Join, the shared line's invalidations finish before the next Begin; in
  // Begin they would be ahead of the start stores, which commit in order.
  void Stage(const uint8_t* bytes) {
    if (active_) throw std::logic_error("value workers: staging during a job");
    std::memcpy(pending_.data(), bytes, pending_.size());
  }
  void Publish(size_t r, uint64_t hit, size_t f, size_t w, unsigned s, bool final) {
    StoreProgress(r, hit, f, w, s, final, false);
  }
  void CancelAndJoin() noexcept {
    if (!active_) return;
    StoreProgress(0, 0, 0, 0, 0, true, true);
    Join();
  }
  void Finish(uint8_t* out, uint64_t take) {
    Join();
    Rethrow();
    if (out) for (auto& w : workers_)
      core::obliAssignBytes(out + w->begin, Bytes(*w), w->end - w->begin, take);
  }
  struct Guard {
    ValueWorkerPool* pool;
    ~Guard() { pool->CancelAndJoin(); }
  };
 private:
  // 128-byte pairs (the L2 spatial prefetcher's unit): the requester writes
  // the start lines and reads the reply; the worker writes its reply and its
  // scratch, whose heap storage is line-allocated for the same reason.
  template <class T> using LineVector = std::vector<T, LineAllocator<T>>;
  struct Worker {
    alignas(128) ValueStart start;
    alignas(128) ValueReply reply;
    size_t begin = 0, end = 0;
    BasicProbeScratch<LineAllocator> scratch;
    LineVector<uint8_t*> selected;
    LineVector<uint8_t> long_reply, temp;
    alignas(128) std::atomic<bool> parked{false};
    std::mutex mutex;
    std::condition_variable cv;
    bool started = false;
    std::thread thread;
    alignas(128) ValueTiming timing;
  };
  void StoreProgress(size_t r, uint64_t hit, size_t f, size_t w, unsigned s,
                     bool final, bool cancel) {
    progress_.store(ValueProgress::Pack(sequence_, r, hit, f, w, s, final, cancel),
                    std::memory_order_release);
    progress_sequence_ = sequence_;
  }
  // This job's progress, or none yet: a word tagged by an earlier job.
  uint64_t LoadProgress(uint64_t tag) const {
    const uint64_t p = progress_.load(std::memory_order_acquire);
    return (p & 0xffff) == tag ? p : 0;
  }
  uint8_t* Bytes(Worker& w) { return w.long_reply.empty() ? w.reply.bytes : w.long_reply.data(); }
  void Spin() const { if (config_.pause) _mm_pause(); }
  void Demote(const void* p) const { if (config_.demote) DemoteHint(p); }
  void DemoteHint(const void* p) const {
#if defined(__CLDEMOTE__)
    _cldemote(const_cast<void*>(p));
#else
    (void)p;
#endif
  }
  template <size_t Lines>
  void Execute(Worker& w, unsigned index) {
    struct Job {
      const ProbePlan* plan; KeyWords key; uint64_t dummy_base;
      uint8_t* pending_bucket; size_t pending_slot, boundary;
    };
    const Job job{w.start.plan,w.start.key,w.start.dummy_base,w.start.pending_bucket,
                  w.start.pending_slot,w.start.boundary};
    // The worker's own copy of the job's sequence: sampling and the tag.
    const uint64_t sequence = w.start.sequence.load(std::memory_order_relaxed);
    const bool sample = config_.profile && ValueSample(sequence) && job.plan;
    const uint64_t start = sample ? ValueStamp() : 0;
    // Own the reply line now (PREFETCHW): the requester read it at the last
    // Join, and the final stores would otherwise wait out that transfer.
    __builtin_prefetch(&w.reply, 1, 3);
    // The previous access's insertion. Its bytes are the requester's newest
    // store, a miss that would stall the address pass behind it, so they are
    // fetched now and written after that pass: before entry 0 (the unit they
    // go to) is blended, and before any cancel can return.
    const uint8_t* forwarded = pending_.data() + w.begin;
    if (job.pending_bucket && w.begin != w.end) {
      _mm_prefetch(reinterpret_cast<const char*>(forwarded), _MM_HINT_T0);
      _mm_prefetch(reinterpret_cast<const char*>(forwarded + (w.end - w.begin) - 1), _MM_HINT_T0);
    }
    const auto commit = [&] {
      ArenaPauseAt(ArenaPause::kBeforeValuePendingWrite, index);
      if (job.pending_bucket)
        WriteValueRange(job.pending_bucket, layout_.key_bytes, job.pending_slot,
                        w.begin, w.end, forwarded);
    };
    const ProbePlan* plan = job.plan;
    if (!plan) { commit(); return; }
    ArenaPauseAt(ArenaPause::kBeforeValueRead, index);
    const size_t first = plan->first_live;
    const size_t bound = job.boundary;
    for (size_t i = first; i < plan->tables.size(); ++i) {
      if (plan->tables[i].kind != TableKind::kDense) continue;
      w.scratch.bucket[2 * i] = w.scratch.bucket[2 * i + 1] = plan->tables[i].data;
    }
    ResolveHashedProbeAddresses<false>(plan->addressing, job.key, job.dummy_base,
                                      layout_.BucketBytes(), aes_, w.scratch);
    const uint64_t addressed = sample ? ValueStamp() : 0;
    if constexpr (Lines > 24) std::memset(Bytes(w), 0, w.end - w.begin);
    const size_t bucket_bytes = layout_.BucketBytes();
    const size_t column = (layout_.key_bytes + w.begin) * 64;
    size_t fetched = 0, blended = 0;
    uint64_t p = 0;
    // In plan order, at most two entries past the blend cursor, moved on after
    // every blend. A dense run is public and goes ahead of progress; a hashed
    // entry's real/dummy choice needs progress through the entry before it.
    // The pointer selection is the requester's permitted trace.
    const auto advance = [&] {
      while (fetched < bound && fetched < blended + 2) {
        const TableEntry& t = plan->tables[first + fetched];
        const bool hashed = t.kind == TableKind::kHashed;
        uint8_t* ptr = w.scratch.bucket[2 * (first + fetched)];
        // A branch on the public kind: a dense address must not wait for the
        // progress load through a select.
        if (hashed) {
          if (fetched > ValueProgress::Ready(p)) break;
          const uint64_t dummy = ValueProgress::Hit(p) &
              static_cast<uint64_t>(ValueProgress::First(p) < fetched);
          ptr = reinterpret_cast<uint8_t*>(core::obliSelectU64(
              reinterpret_cast<uintptr_t>(ptr),
              reinterpret_cast<uintptr_t>(w.scratch.bucket[2 * (first + fetched) + 1]), dummy));
        }
        w.selected[fetched] = ptr;
        const size_t buckets = hashed ? 1 : t.num_buckets;
        for (size_t b = 0; b < buckets; ++b)
          for (size_t l = 0; l < w.end - w.begin; ++l) {
            _mm_prefetch(reinterpret_cast<const char*>(ptr + b * bucket_bytes + column + l * 64),
                         _MM_HINT_T0);
          }
        ++fetched;
      }
    };
    const uint64_t tag = sequence & 0xffff;
    advance();  // no progress yet (p == 0): the dense entries
    commit();
    const uint64_t inserted = sample ? ValueStamp() : 0;
    // After the last call: vector registers are caller-saved, and the
    // accumulators must not live across a call or they go to the stack.
    ValueAccumulator<(Lines <= 24 ? Lines : 0)> acc;
    for (;;) {
      p = LoadProgress(tag);
      if (ValueProgress::Cancel(p)) return;
      advance();
      while (blended < ValueProgress::Ready(p) && blended < fetched) {
        const TableEntry& t = plan->tables[first + blended];
        const size_t buckets = t.kind == TableKind::kDense ? t.num_buckets : 1;
        for (size_t b = 0; b < buckets; ++b) {
          const uint64_t take = ValueProgress::Hit(p) &
              static_cast<uint64_t>(ValueProgress::First(p) == blended) &
              static_cast<uint64_t>(ValueProgress::Bucket(p) == b);
          const uint8_t* bucket = w.selected[blended] + b * bucket_bytes;
          if constexpr (Lines <= 24) {
            acc.Blend(bucket + column, take);
          } else {
            ExtractValueRange(bucket, layout_.key_bytes, w.begin, w.end,
                              ValueProgress::Slot(p), w.temp.data());
            core::obliAssignBytes(Bytes(w), w.temp.data(), w.end - w.begin, take);
          }
        }
        ++blended;
        advance();
      }
      if (blended == bound && ValueProgress::Final(p)) break;
      Spin();
    }
    if (sample) {
      ++w.timing.samples; w.timing.stamp += start;
      w.timing.address += addressed - start;
      w.timing.final_stamp += ValueStamp();
      w.timing.insertion += inserted - addressed;
    }
    if constexpr (Lines <= 24) acc.Finish(ValueProgress::Slot(p), Bytes(w));
  }
  template <size_t N = 0>
  void Dispatch(Worker& w, unsigned index) {
    if (w.end - w.begin == N && config_.kernel != ValueKernel::kPermute)
      Execute<N>(w, index);
    else if constexpr (N < 24) Dispatch<N + 1>(w, index);
    else Execute<25>(w, index);  // public per-bucket fallback
  }
  void Run(Worker& w, unsigned index) noexcept {
    try {
      Dispatch(w, index);
      ArenaPauseAt(ArenaPause::kBeforeValueDone, index);
      w.reply.done.store(w.start.sequence.load(std::memory_order_relaxed), std::memory_order_release);
      Demote(&w.reply);
    } catch (...) {
      Fail(std::current_exception());
      w.reply.done.store(~uint64_t{0}, std::memory_order_release);
    }
  }
  // The Dekker park handshake's requester side: the start stores (Begin), one
  // full fence, then every parked flag. The worker stores `parked` and then
  // loads its start sequence, both seq_cst, so either it sees the job or this
  // sees it parked. One fence per job, after the cascade has hidden the
  // stores' ownership transfers. Until then a parked worker sleeps on, but
  // nothing before Join waits for a worker.
  void WakeParked() noexcept {
    std::atomic_thread_fence(std::memory_order_seq_cst);
    for (auto& w : workers_)
      if (w->parked.load(std::memory_order_relaxed)) {
        std::lock_guard<std::mutex> lock(w->mutex);
        w->cv.notify_one();
      }
  }
  void Join() noexcept {
    if (!active_) return;
    if (config_.serial) for (unsigned i = 0; i < workers_.size(); ++i) Run(*workers_[i], i);
    else WakeParked();
    unsigned spins = 0;
    // The clock is read only once the wait is long: not on every access.
    std::chrono::steady_clock::time_point deadline{};
    for (;;) {
      bool all = true;
      // Every completion word is loaded in every iteration, no short circuit.
      for (auto& w : workers_)
        all &= w->reply.done.load(std::memory_order_acquire) >= sequence_;
      if (all) break;
      Spin();
      if (++spins == 4096) {
        const auto now = std::chrono::steady_clock::now();
        if (deadline == std::chrono::steady_clock::time_point{})
          deadline = now + std::chrono::milliseconds(config_.wait_limit_millis);
        else if (now > deadline) {
          std::fputs("value workers: job never retired; reader storage remains pinned\n",stderr); std::abort();
        }
        std::this_thread::yield(); spins = 0;
      }
    }
    active_ = false;
  }
  bool Wait(Worker& w, uint64_t seen) {
    auto ready = [&] { return w.start.sequence.load(std::memory_order_acquire) != seen; };
    const auto deadline = SpinDeadline(config_.spin_nanos);
    do {
      for (unsigned i = 0; i < 16; ++i) {
        if (ready()) return true;
        if (stop_.load(std::memory_order_acquire)) return false;
        Spin();
      }
    } while (std::chrono::steady_clock::now() < deadline);
    if (monitor_ != core::MonitorWaitKind::kNone) for (;;) {
      // Monitor wait REPLACES the park below: one OS-capped quantum at a
      // time until a job or stop arrives, so an idle worker stays runnable.
      core::MonitorWaitArm(monitor_, &w.start.sequence);
      if (ready()) return true;
      if (stop_.load(std::memory_order_acquire)) return false;
      core::MonitorWaitSleep(monitor_, 6000000);
    }
    std::unique_lock<std::mutex> lock(w.mutex);
    w.parked.store(true, std::memory_order_seq_cst);
    w.cv.wait(lock, [&] {
      return w.start.sequence.load(std::memory_order_seq_cst) != seen ||
          stop_.load(std::memory_order_seq_cst);
    });
    w.parked.store(false, std::memory_order_seq_cst);
    return ready();
  }
  void Loop(unsigned index) {
    Worker& w = *workers_[index];
    try { if (config_.init) config_.init(index); } catch (...) { Fail(std::current_exception()); }
    { std::lock_guard<std::mutex> lock(w.mutex); w.started = true; }
    w.cv.notify_one();
    if (Failed()) return;
    uint64_t seen = config_.initial_sequence;
    while (Wait(w, seen)) {
      seen = w.start.sequence.load(std::memory_order_acquire);
      Run(w, index);
      if (Failed()) { w.reply.done.store(~uint64_t{0}, std::memory_order_release); return; }
    }
  }
  void Fail(std::exception_ptr error) {
    std::lock_guard<std::mutex> lock(error_mutex_);
    if (!error_) error_ = error;
    failed_.store(true, std::memory_order_release);
  }
  void Rethrow() {
    if (!Failed()) return;
    std::lock_guard<std::mutex> lock(error_mutex_);
    std::rethrow_exception(error_);
  }
  void Shutdown() noexcept {
    // The requester joins every accepted job before setting stop.
    CancelAndJoin();
    stop_.store(true, std::memory_order_seq_cst);
    for (auto& w : workers_) {
      { std::lock_guard<std::mutex> lock(w->mutex); }
      w->cv.notify_one();
    }
    for (auto& w : workers_) if (w->thread.joinable()) w->thread.join();
  }
  Config config_;
  Layout layout_;
  const AesTagKeys& aes_;
  const size_t max_tables_, max_hashed_;
  LineVector<uint8_t> pending_;
  core::MonitorWaitKind monitor_;
  std::vector<std::unique_ptr<Worker>> workers_;
  alignas(128) std::atomic<uint64_t> progress_{0};
  // Read by every worker (stop_ while idle, failed_ after each job).
  alignas(128) std::atomic<bool> stop_{false}, failed_{false};
  std::mutex error_mutex_;
  std::exception_ptr error_;
  // The requester's own, written every job: on a line a worker reads, each
  // store would queue the start and progress stores behind an invalidation.
  alignas(128) uint64_t sequence_ = 0;
  uint64_t progress_sequence_ = 0;  // the job that last stored progress_
  bool active_ = false;
};
}  // namespace microram::byteslice::levelarena
