// Allocation and failure contracts of the batch worker pool and of the
// engine's steady state.  A global operator new/delete replacement counts
// every allocation while `tracking` is set.  Checked:
//   * once warmed up, a batch phase -- and a long run of batches that flushes,
//     merges and compacts the top repeatedly, with helpers and owners -- makes
//     no heap allocation at all: memory is sized from public parameters and
//     allocated up front, so no allocation can fail or stall mid-rebuild and
//     the allocator never sees a data-dependent request;
//   * a merge job's and the arena pool's allocations match an independent
//     census of the buffers they should own;
//   * a participant that throws in a phase is joined before the exception
//     propagates, and the pool stays usable afterwards;
//   * a participant whose init hook never returns makes the pool abort at its
//     startup deadline instead of hanging (run in a forked child);
//   * a requester wait long enough to be recorded (long_waits) allocates
//     nothing for the record.
// No probe audit: its diagnostic containers are deliberately allowed to
// allocate.
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <new>
#include <stdexcept>

#if defined(__unix__)
#include <csignal>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

namespace {
std::atomic<bool> tracking{false};
std::atomic<size_t> allocations{0};
std::atomic<size_t> allocation_bytes{0};
std::atomic<size_t> aligned_allocations{0};
std::atomic<size_t> aligned_bytes{0};
void CountAllocation(size_t bytes) {
  if (tracking.load(std::memory_order_relaxed)) {
    allocations.fetch_add(1, std::memory_order_relaxed);
    allocation_bytes.fetch_add(bytes, std::memory_order_relaxed);
  }
}
}

void* operator new(size_t n) {
  CountAllocation(n);
  if (void* p = std::malloc(n ? n : 1)) return p;
  throw std::bad_alloc();
}
void* operator new[](size_t n) { return ::operator new(n); }
void operator delete(void* p) noexcept { std::free(p); }
void operator delete(void* p, size_t) noexcept { std::free(p); }
void operator delete[](void* p) noexcept { std::free(p); }
void operator delete[](void* p, size_t) noexcept { std::free(p); }
void* operator new(size_t n, std::align_val_t alignment) {
  CountAllocation(n);
  if (tracking.load(std::memory_order_relaxed)) {
    aligned_allocations.fetch_add(1, std::memory_order_relaxed);
    aligned_bytes.fetch_add(n, std::memory_order_relaxed);
  }
  const size_t a = static_cast<size_t>(alignment);
  if (void* p = std::aligned_alloc(a, ((n ? n : 1) + a - 1) / a * a)) return p;
  throw std::bad_alloc();
}
void* operator new[](size_t n, std::align_val_t a) { return ::operator new(n, a); }
void operator delete(void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete(void* p, size_t, std::align_val_t) noexcept { std::free(p); }
void operator delete[](void* p, std::align_val_t) noexcept { std::free(p); }
void operator delete[](void* p, size_t, std::align_val_t) noexcept { std::free(p); }

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

namespace {
namespace la = microram::byteslice::levelarena;
namespace bs = microram::byteslice;
int failures = 0;
void Expect(bool condition, const char* message) {
  if (!condition) {
    std::fprintf(stderr, "test failed: %s\n", message);
    ++failures;
  }
}

void TestWarmedBatchAllocation() {
  for (bool parallel : {false, true}) {
    for (auto layout : {bs::BatchResultLayout::kRows,
                        bs::BatchResultLayout::kSlicedPlaceAtLane}) {
      la::LevelArenaEngine::Options o;
      o.geometry.branching = 2;
      o.geometry.levels = 2;
      o.geometry.top_digit = 2;
      o.geometry.prefix_flushes = 2;
      o.key_bytes = 8;
      o.value_bytes = 8;
      o.batch_lanes = 1;
      o.batch_participants = parallel ? 2 : 1;
      o.batch_execution = parallel ? la::BatchExecutionShape::kParallelTiles
                                  : la::BatchExecutionShape::kChunkedCascade;
      o.batch_result_layout = layout;
      la::LevelArenaEngine engine(o);
      bs::BatchRequest64 requests[2]{};
      uint64_t values[2] = {1, 2};
      for (unsigned i = 0; i < 2; ++i) {
        requests[i].key = i;
        requests[i].op = bs::BatchOp::kReadThenWrite;
        requests[i].value_in = reinterpret_cast<uint8_t*>(&values[i]);
      }
      engine.AccessBatch(2, requests, nullptr);
      const uint64_t flushes = engine.dense().flushes();
      allocations.store(0);
      tracking.store(true);
      engine.AccessBatch(2, requests, nullptr);
      tracking.store(false);
      Expect(allocations.load() == 0, "warmed batch phase allocated");
      Expect(engine.dense().flushes() == flushes,
             "allocation test unexpectedly triggered a flush");
    }
  }
}

// Independently count every C++ allocation made by a stack-owned job. This
// catches omitted vectors as well as payloads; no predictor feeds the census.
void TestJobBufferCensus() {
  for (unsigned branching : {2u, 4u, 8u}) {
    for (unsigned digit = 1; digit <= branching; digit *= 2) {
      la::LevelArenaGeometry::Params params;
      params.branching = branching;
      params.levels = 3;
      params.top_digit = digit;
      params.prefix_flushes = 2;
      const la::LevelArenaGeometry geometry(params);
      const la::LevelArenaStashSizing sizing(geometry, uint64_t{1} << 32);
      const bs::Layout layout = la::LevelArenaStoredLayout(8, 8, geometry);
      const auto& keys = bs::DefaultAesTagKeys();
      for (unsigned level = 1; level <= geometry.Levels(); ++level) {
        allocations.store(0);
        allocation_bytes.store(0);
        tracking.store(true);
        la::LevelMergeJob job(geometry, sizing, layout, level, keys);
        tracking.store(false);
        Expect(allocation_bytes.load() == job.bytes().requested(),
               "job buffer bill omitted an allocation");
        Expect(allocations.load() == job.bytes().allocated().allocations,
               "job buffer bill has an incorrect allocation count");
      }
    }
  }
}

// Count actual aligned payload allocations separately from metadata and
// geometry copies. The independent expected census is L main arenas + 1 pool.
void TestArenaPoolCensus() {
  const auto saved = bs::CurrentHugePagePolicy();
  for (auto policy : {bs::HugePagePolicy::kOff, bs::HugePagePolicy::kOn}) {
    bs::SetHugePagePolicy(policy);
    for (size_t value : {size_t{8}, size_t{48}}) {
      la::LevelArenaGeometry::Params p;
      p.branching = 8;
      p.levels = 3;
      p.top_digit = 8;
      p.tier_buckets = 3;
      p.level_tier_buckets = {1, 3, 2};
      const la::LevelArenaGeometry geometry(p);
      const auto layout = la::LevelArenaStoredLayout(8, value, geometry);
      size_t main_reserved = 0, tier_payload = 0;
      for (unsigned l = 1; l <= geometry.Levels(); ++l) {
        const auto& plan = geometry.storage().At(l);
        main_reserved += bs::Aligned64AllocationBytes(plan.arena_buckets * layout.BucketBytes());
        for (const auto& slot : plan.slots) {
          tier_payload += slot.tier_buckets * layout.BucketBytes();
        }
      }
      Expect(tier_payload < bs::kHugePageBytes, "census needs a small pool");
      aligned_allocations.store(0);
      aligned_bytes.store(0);
      tracking.store(true);
      la::LevelArenaSet arenas(geometry, layout);
      tracking.store(false);
      Expect(aligned_allocations.load() == geometry.Levels() + 1,
             "pool not allocated exactly once alongside unchanged main arenas");
      Expect(aligned_bytes.load() == main_reserved + tier_payload,
             "pool census differs or a small pool consumed a huge page");
      Expect(arenas.bytes().At(la::ByteRole::kTiers) == tier_payload &&
                 arenas.bytes().At(la::ByteRole::kRetainedTierHoles) == tier_payload,
             "census payload roles do not distinguish pool from retained holes");
    }
  }
  bs::SetHugePagePolicy(saved);
}

void TestFlushingBatchAllocation() {
  for (bool threaded : {false, true}) {
    for (unsigned digit : {1u, 2u, 4u, 8u}) {
      la::LevelArenaEngine::Options o;
      o.geometry.branching = digit == 1 ? 2 : 8;
      o.geometry.levels = 3;
      o.geometry.top_digit = digit;
      o.geometry.prefix_flushes = 2;
      o.key_bytes = 8;
      o.value_bytes = 8;
      o.owner_threads = threaded ? 2 : 0;
      o.batch_lanes = 2;
      o.batch_participants = threaded ? 2 : 1;
      o.batch_execution = threaded ? la::BatchExecutionShape::kParallelTiles
                                  : la::BatchExecutionShape::kChunkedCascade;
      la::LevelArenaEngine engine(o);
      bs::BatchRequest64 requests[4]{};
      uint64_t values[4] = {1, 2, 3, 4};
      for (unsigned i = 0; i < 4; ++i) {
        requests[i].key = i;
        requests[i].op = bs::BatchOp::kReadThenWrite;
        requests[i].value_in = reinterpret_cast<uint8_t*>(&values[i]);
      }
      // Include the first merge of every digit and repeated reuse. Helpers
      // and owners are counted too, and drain completes their pending work.
      allocations.store(0);
      tracking.store(true);
      for (unsigned i = 0; i < 4096; ++i)
        engine.AccessBatch(4, requests, nullptr);
      engine.Drain();
      tracking.store(false);
      Expect(allocations.load() == 0, "flush/merge execution allocated");
      Expect(engine.level(3).stats().merges > 1,
             "allocation test did not exercise repeated top compaction");
    }
  }
}

// A BACKPRESSURE WAIT LONGER THAN kLongWaitNanos records what every level
// waited on while it is still waiting, inside the access, and so into storage
// reserved at construction.  The owners of this deferred engine never start,
// so every write that would complete prefix 1 waits out its 50 ms limit and
// is refused.  The first kMaxLongWaits refusals record a long wait and the
// next one does not; both must allocate exactly what building the refusal's
// message allocates.
void TestLongWaitRecordDoesNotAllocate() {
  la::LevelArenaEngine::Options o;
  o.geometry.branching = 4;
  o.geometry.levels = 3;
  o.geometry.top_digit = 4;
  o.geometry.prefix_flushes = 2;
  o.geometry.stash_buckets = 1;
  o.geometry.dense_prefixes = 1;
  o.key_bytes = 8;
  o.value_bytes = 8;
  o.owner_threads = 1;
  o.defer_owner_start = true;
  o.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  o.wait_limit_millis = 50;
  la::LevelArenaEngine engine(o);
  const uint64_t value = 7;
  const uint8_t* bytes = reinterpret_cast<const uint8_t*>(&value);
  uint64_t key = 1;
  bool refused = false;
  for (; key <= 4096 && !refused; ++key) {
    try {
      engine.Write(key, bytes);
    } catch (const std::exception&) {
      refused = true;
    }
  }
  Expect(refused, "the requester never ran out of prefix slots");
  const auto refusal_allocations = [&] {
    allocations.store(0);
    tracking.store(true);
    try {
      engine.Write(key, bytes);
    } catch (const std::exception&) {
    }
    tracking.store(false);
    return allocations.load();
  };
  const size_t recorded = refusal_allocations();
  while (engine.long_waits().size() < la::LevelArenaEngine::kMaxLongWaits) {
    refusal_allocations();
  }
  const size_t unrecorded = refusal_allocations();
  Expect(engine.long_waits().size() == la::LevelArenaEngine::kMaxLongWaits,
         "the long waits were not recorded");
  Expect(recorded == unrecorded, "recording a long wait allocated");
}

void TestBorrowedPhaseAndExceptionJoin() {
  la::BatchWorkerPool::Config config;
  config.participants = 3;
  la::BatchWorkerPool pool(config);
  std::atomic<unsigned> completed{0};
  // Move-only, mutable callable: it cannot be stored in std::function. Each
  // participant touches a distinct element; a mutable callable is responsible
  // for synchronizing any shared captured state itself.
  auto phase = [values = std::make_unique<unsigned[]>(3)](unsigned t) mutable {
    values[t] = t + 1;
  };
  pool.RunPhase(3, phase);
  for (unsigned throwing : {0u, 1u, 2u}) {
    completed.store(0);
    bool caught = false;
    try {
      pool.RunPhase(3, [&](unsigned t) {
        completed.fetch_add(1);
        if (t == throwing) throw std::runtime_error("phase failure");
      });
    } catch (const std::runtime_error&) {
      caught = true;
    }
    Expect(caught && completed.load() == 3,
           "phase exception escaped before all participants retired");
    completed.store(0);
    const auto next = [&](unsigned) { completed.fetch_add(1); };
    pool.RunPhase(2, next);
    Expect(completed.load() == 2, "pool did not recover after a joined failure");
  }
}

void TestStuckInitialization() {
#if defined(__unix__)
  // Isolate the terminal policy in a child process.  SIGALRM bounds a pool
  // that would join unconditionally (and hang); the pool must reach its own
  // SIGABRT at the wait limit first.
  const pid_t child = fork();
  if (child == 0) {
    const rlimit no_core{0, 0};
    setrlimit(RLIMIT_CORE, &no_core);
    alarm(5);
    la::BatchWorkerPool::Config config;
    config.participants = 2;
    config.wait_limit = std::chrono::milliseconds(20);
    config.thread_init = [](unsigned) { for (;;) pause(); };
    la::BatchWorkerPool pool(config);
    _exit(1);
  }
  Expect(child >= 0, "could not fork the stuck-init test");
  if (child > 0) {
    int status = 0;
    Expect(waitpid(child, &status, 0) == child, "could not wait for stuck-init child");
    Expect(WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT,
           "stuck initialization did not terminate at its deadline");
  }
#endif
}
}

int main() {
  TestStuckInitialization();
  TestBorrowedPhaseAndExceptionJoin();
  TestWarmedBatchAllocation();
  TestJobBufferCensus();
  TestArenaPoolCensus();
  TestFlushingBatchAllocation();
  TestLongWaitRecordDoesNotAllocate();
  if (failures != 0) return 1;
  std::printf("level arena batch workers: allocation, join and startup contracts OK\n");
}
