// Single-core benchmark for the load-0.5 MergeSplit routing kernels
// (src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp), in isolation
// from the hierarchical ORAM driver.
//
// Every row routes a table of num_buckets 64-slot buckets filled to load 0.5
// (32 real entries per bucket) and reports the cost normalized per
// *MergeSplit byte line* -- the inner-loop unit: one MergeSplit touches
// entry_bytes lines, and one route of N buckets over L levels performs
// (N/2)*L MergeSplits.  That number is what the kernel optimizations move;
// ns/entry/level is the same quantity in ORAM terms.
//
// Phases:
//   grouped  - ButterflyRouteStash, group_levels=6 tiling (fused quads)
//   c-obliv  - ButterflyRouteStashCacheOblivious (what the ORAM uses)
//   radix-r  - one RadixPassStash over r * 2^block_bits buckets, per byte
//              line of one r-way MergeSplit.  The radix pass is the last
//              routing step, so it moves payload lines only; its ns/line is
//              normalized against the full entry width all the same.
//   fold     - MergeBucketIntoWithStash over the arena's bucket pairs (the
//              fixed-last-level rebuild's fold), per byte line of one merge.
//              Also payload-only: the butterfly has consumed every tag bit.
//
// Usage: cpu_byteslice_stash_rebuild_benchmark
//            [min_log2] [max_log2] [radix] [value_bytes] [stash_buckets]
// Defaults: 6 .. 20 in steps of 2, radix 3, value_bytes 16, stash_buckets 1.
//
// FLAG MODE (any argument beginning with "--") replaces the table above with
// one JSON object per line: routing-only rows (a whole network over one
// table) and isolated merge-split rows (one kernel call on one bucket pair).
// The positional mode above is the default.
//
//   Routing rows (one row per network, one shared input per invocation):
//     --network flat|grouped6|cache_oblivious|butterfly512[,..]  (repeatable;
//                        default: the first three; also grouped6_unfused and
//                        cache_oblivious_unfused for the fusion ablation)
//         flat            ButterflyRouteStash, group_levels=1: the standard
//                         stage-major, unfused 64-slot butterfly
//         grouped6        ButterflyRouteStash, group_levels=6
//         cache_oblivious ButterflyRouteStashCacheOblivious (the ORAM's)
//         butterfly512    the flat butterfly on 512-slot buckets (--live-entries
//                         / 256 of them), no stash: a surplus fails the row.
//                         Kernel: cpu_byteslice_slot512_kernel.hpp.  Rows carry
//                         bucket_slots; one thread.
//     --key-bytes 4|8    stored key width (4 for a K4/V8 map); default 8
//     --value-bytes N    logical value bytes (default 16)
//     --live-entries N   live entries in the table; buckets = N / 32 (load
//                        0.5), a power of two >= 2; default 2^20
//     --seed S           input seed: key offset, slot placement and tag nonce
//     --reps R           most timed repetitions (Measure: >= 2, then until
//                        0.3 s of work or R); default 200
//     --stash-buckets S  per-level residual capacity in buckets (default 1)
//     --threads T        cache_oblivious variants only; one network on T
//                        threads (the two top-level sub-network layers,
//                        barrier between)
//     --instances P      P INDEPENDENT routes at once instead: P threads, each
//                        routing its own table of --live-entries records (seed
//                        + i), started together -- P levels rebuilding at the
//                        same time, so the routes share the memory bandwidth.
//                        --reps is then the exact number of rounds; a round
//                        routes every instance once per network, the networks
//                        alternating their order round by round.  Each
//                        instance restores its table with streaming stores, so
//                        every route starts with its table in DRAM.  Not with
//                        --threads or butterfly512.
//     --cpus LIST        with --instances: pin instance i to the i-th CPU of
//                        LIST ("1-8", "1,3,5-7"); default unpinned
//     --check-overflow 0|1  checked kernels (default 1): a false return is
//                        the stash-overflow signal.  With 0 the unchecked
//                        kernels run and only the conservation check below
//                        can see an overflow.
//     --verify 0|1       post-route check outside the timer (default 1)
//     --max-bytes B      refuse rows whose data + pristine buffers exceed B
//                        (default 8 GiB); the row prints status
//                        "skipped_memory" and the exit status is nonzero
//   Outside the timer: input generation, ComputeRoutingTags, restoring the
//   pristine copy, stash reset, the shed count and the verification.  Inside:
//   the whole network, in-network stash emission included (and, for T > 1,
//   the hand-off to the worker threads).
//   Verification: every real table entry plus every stashed entry is one
//   input record, each exactly once (key bitmap, value bytes intact), and
//   every table entry sits in the bucket its tag selects.
//
//   Pair rows:
//     --pairs N          N independent merge-splits on two 64-slot buckets
//                        (load 0.5 each, random tag bit 0, bit = 0).  Takes
//                        --key-bytes, --value-bytes, --seed, --stash-buckets,
//                        --check-overflow, --max-bytes and
//     --arm A            current | compress_expand | bitonic | slot512 | all
//                        (default all).  current = MergeSplitPairStash;
//                        compress_expand = VPCOMPRESSB/VPEXPANDB merge-split;
//                        bitonic = the full 28-stage bitonic network over the
//                        pair's 128 slots (swap masks planned from the keys
//                        inside the timer, every stage applied to every
//                        routed line); slot512 = the same merge-split on a
//                        pair of 512-slot buckets (1024 slots, 8x the records
//                        per bucket, no stash: a surplus is an overflow, and
//                        --check-overflow does not apply).  The other arms
//                        share the generated records, the routing predicate,
//                        the shed/overflow contract and the post-run
//                        verification; slot512 has its own, of the same form.
//     Each arm runs on two pair pools sized in bytes of bucket data:
//     cache_resident = 2.5 MiB and dram_streaming = 40 MiB (pairs per pool =
//     floor(bytes / (2 * bucket_bytes)), at least 1), one JSON row per (arm,
//     pool).  The pool is restored from a pristine copy before every
//     pool-sized chunk and only the kernel loop is timed (restore total in
//     restore_ms_excluded).  --pool-bytes B replaces both with one "custom"
//     pool.  --load-per-bucket R (test only, default 32) fills R records per
//     bucket so that shedding to the stash actually happens.
//
// stash_buckets is the per-butterfly-level residual capacity in 64-slot
// buckets -- what PlanStashBuckets hands the engine, and what every MergeSplit
// kernel is TEMPLATED on.  It runs 1 .. kMaxResidualStashBuckets: the schedule
// reaches 3 at ~2^30 entries and 8 at ~2^34, so a benchmark that only ever
// measures 1 cannot see which of those depths still gets a specialized
// kernel.

#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"
#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "benchmarks/oram/cpu_byteslice_slot512_kernel.hpp"
#include "benchmarks/oram/cpu_byteslice_routing_comparator.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <memory>
#include <type_traits>
#include <string>
#include <thread>
#include <vector>

#include <pthread.h>
#include <sched.h>

namespace {

namespace bs = microram::byteslice;
using microram::byteslice::benchmark_support::Clock;
using microram::byteslice::benchmark_support::Measure;
using microram::byteslice::benchmark_support::PhaseTime;
using microram::byteslice::benchmark_support::SecondsSince;
using microram::byteslice::benchmark_support::SplitMix64;

// kStashTargetRealPerBucket entries at random slots in every bucket.
void GenerateInput(bs::TableView t, uint64_t seed) {
  std::memset(t.data, 0xA5, t.num_buckets * t.layout.BucketBytes());
  uint64_t rng = seed;
  uint64_t key_counter = 1;
  const size_t key_bytes = t.layout.key_bytes;
  for (size_t b = 0; b < t.num_buckets; ++b) {
    uint8_t* bucket = t.Bucket(b);
    uint8_t slots[bs::kBucketCapacity];
    for (size_t i = 0; i < bs::kBucketCapacity; ++i) {
      slots[i] = static_cast<uint8_t>(i);
    }
    uint64_t mask = 0;
    for (size_t i = 0; i < bs::kStashTargetRealPerBucket; ++i) {
      const size_t pick = i + SplitMix64(rng) % (bs::kBucketCapacity - i);
      std::swap(slots[i], slots[pick]);
      const size_t slot = slots[i];
      mask |= uint64_t{1} << slot;
      const uint64_t key = key_counter++ * 0x2545F4914F6CDD1Dull;
      for (size_t kb = 0; kb < key_bytes; ++kb) {
        bucket[kb * bs::kBucketCapacity + slot] =
            static_cast<uint8_t>(key >> (8 * kb));
      }
    }
    t.masks[b] = mask;
  }
}

// Owns num_slots stashes of stash_buckets buckets each.
struct StashSet {
  bs::Aligned64Ptr data;
  std::vector<bs::ResidualStash> stashes;

  StashSet(unsigned num_slots, size_t stash_buckets, const bs::Layout& layout) {
    const size_t bucket_bytes = layout.BucketBytes();
    data = bs::AllocateAligned64(num_slots * stash_buckets * bucket_bytes);
    std::memset(data.get(), 0, num_slots * stash_buckets * bucket_bytes);
    stashes.resize(num_slots);
    for (unsigned s = 0; s < num_slots; ++s) {
      stashes[s].data = data.get() + s * stash_buckets * bucket_bytes;
      stashes[s].num_buckets = stash_buckets;
      stashes[s].entry_bytes = layout.EntryBytes();
    }
  }

  void Reset() {
    for (auto& s : stashes) s.Reset();
  }
  size_t Count() const {
    size_t n = 0;
    for (const auto& s : stashes) n += s.Count();
    return n;
  }
};

int RunScale(unsigned log2_buckets, unsigned radix, size_t stash_buckets,
             const bs::StashLayout& stash_layout) {
  const bs::Layout layout = stash_layout.Base();
  const size_t num_buckets = size_t{1} << log2_buckets;
  const unsigned levels = log2_buckets;
  const size_t entry_bytes = layout.EntryBytes();
  const size_t data_bytes = num_buckets * layout.BucketBytes();
  const double merge_splits = double(num_buckets / 2) * levels;
  const double lines = merge_splits * double(entry_bytes);
  const size_t num_entries = num_buckets * bs::kStashTargetRealPerBucket;

  auto data = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> masks(num_buckets);
  bs::TableView t{layout, num_buckets, data.get(), masks.data()};
  GenerateInput(t, 0xC0FFEEull + log2_buckets);
  bs::ComputeRoutingTags(t, /*nonce_lo=*/42, /*nonce_hi=*/7);

  auto pristine = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> pristine_masks(num_buckets);
  std::memcpy(pristine.get(), data.get(), data_bytes);
  std::memcpy(pristine_masks.data(), masks.data(),
              num_buckets * sizeof(uint64_t));
  const auto restore = [&] {
    std::memcpy(data.get(), pristine.get(), data_bytes);
    std::memcpy(masks.data(), pristine_masks.data(),
                num_buckets * sizeof(uint64_t));
  };

  // One stash per butterfly bit-level, stash_buckets buckets each.
  StashSet stashes(levels + 1, stash_buckets, layout);

  const PhaseTime grouped = Measure(200, [&] {
    restore();
    stashes.Reset();
    const auto start = Clock::now();
    bs::ButterflyRouteStash(t, levels, stashes.stashes.data(), 6);
    return SecondsSince(start);
  });

  const PhaseTime cobliv = Measure(200, [&] {
    restore();
    stashes.Reset();
    const auto start = Clock::now();
    bs::ButterflyRouteStashCacheOblivious(t, levels, stashes.stashes.data());
    return SecondsSince(start);
  });
  const size_t shed = stashes.Count();

  std::printf(
      "%8zu %9.1f | %8.3f %6.3f | %8.3f %6.3f %6.2f | %5zu\n",
      num_buckets, data_bytes / (1024.0 * 1024.0),
      grouped.seconds_per_rep * 1e3, grouped.seconds_per_rep * 1e9 / lines,
      cobliv.seconds_per_rep * 1e3, cobliv.seconds_per_rep * 1e9 / lines,
      cobliv.seconds_per_rep * 1e9 / (double(num_entries) * levels), shed);
  std::fflush(stdout);

  // Radix pass over the largest r * 2^block_bits <= num_buckets sub-view, and
  // the fixed-rebuild fold (MergeBucketIntoWithStash over bucket pairs).
  if (radix >= 2 && size_t{radix} * 2 <= num_buckets) {
    unsigned block_bits = 0;
    while ((size_t{radix} << (block_bits + 1)) <= num_buckets) ++block_bits;
    const size_t radix_buckets = size_t{radix} << block_bits;
    bs::TableView rt{layout, radix_buckets, data.get(), masks.data()};
    // One r-way MergeSplit per stride tuple; normalize per byte line of one.
    const double radix_lines = double(size_t{1} << block_bits) * entry_bytes;
    const PhaseTime rp = Measure(200, [&] {
      restore();
      stashes.Reset();
      const auto start = Clock::now();
      bs::RadixPassStash(rt, block_bits, radix, stashes.stashes[0]);
      return SecondsSince(start);
    });
    const size_t half = num_buckets / 2;
    const double fold_lines = double(half) * entry_bytes;
    const PhaseTime fold = Measure(200, [&] {
      restore();
      stashes.Reset();
      const auto start = Clock::now();
      for (size_t p = 0; p < half; ++p) {
        // Payload lines only, as the fixed-level rebuild does: the butterfly
        // has already consumed every routing bit by the time the fold runs.
        bs::MergeBucketIntoWithStash(t.Bucket(half + p), t.Bucket(p),
                                     &masks[half + p], &masks[p],
                                     layout.PayloadLines(),
                                     stashes.stashes[0]);
      }
      return SecondsSince(start);
    });
    std::printf("%8s %9s | radix-%u %6.3f ns/line | fold %6.3f ns/line\n", "",
                "", radix, rp.seconds_per_rep * 1e9 / radix_lines,
                fold.seconds_per_rep * 1e9 / fold_lines);
    std::fflush(stdout);
  }
  return 0;
}


// ---------------------------------------------------------------------------
// Flag mode: routing-only rows and the isolated pair driver
// ---------------------------------------------------------------------------

struct Options {
  std::vector<std::string> networks;
  size_t key_bytes = 8;
  size_t value_bytes = 16;
  size_t live_entries = size_t{1} << 20;
  size_t stash_buckets = 1;
  size_t reps = 200;
  size_t pairs = 0;
  size_t pool_bytes = 0;  // 0: the two labelled pools
  size_t load_per_bucket = bs::kStashTargetRealPerBucket;  // test only
  std::string arm = "all";
  unsigned threads = 1;
  unsigned instances = 0;  // 0: one route at a time (RunRoutingRows)
  std::vector<int> cpus;   // --cpus, one per instance
  std::string cpus_text = "unpinned";
  uint64_t seed = 1;
  uint64_t max_bytes = uint64_t{8} << 30;
  bool check_overflow = true;
  bool verify = true;
};

// Unique keys of either width: key(i) = (i + offset) * odd mod 2^bits is a
// bijection on bits-wide integers, so records i = 1..live get distinct,
// nonzero stored keys, and Index() inverts it for the verification bitmap.
struct KeyGen {
  uint64_t mask = 0, mult = 0, inv = 0, offset = 0;
  KeyGen(size_t key_bytes, uint64_t seed, uint64_t live) {
    mask = key_bytes >= 8 ? ~uint64_t{0} : (uint64_t{1} << (8 * key_bytes)) - 1;
    mult = key_bytes >= 8 ? 0x2545F4914F6CDD1Dull : 0x9E3779B1ull;
    inv = mult;
    for (int i = 0; i < 6; ++i) inv *= 2 - mult * inv;  // Newton, mod 2^64
    uint64_t state = seed ^ 0x6A09E667F3BCC909ull;
    offset = SplitMix64(state) % (mask - live - 1);  // keys stay in [1, mask)
  }
  uint64_t Key(uint64_t i) const { return ((i + offset) * mult) & mask; }
  uint64_t Index(uint64_t key) const { return (key * inv - offset) & mask; }
};

// Value byte line j of the record with this key; lets the verification see a
// record's payload travel with its key.
inline uint8_t ValueByte(uint64_t key, size_t j) {
  return static_cast<uint8_t>(((key * 0x9E3779B97F4A7C15ull) >> (8 * (j & 7))) +
                              j * 131);
}

// `cap` is the bucket's slot count: a byte line is cap bytes (64 for every
// bucket but the slot512 arm's).
void WriteRecord(uint8_t* bucket, size_t slot, uint64_t key,
                 const bs::StashLayout& sl, size_t cap = bs::kBucketCapacity) {
  for (size_t kb = 0; kb < sl.key_bytes; ++kb) {
    bucket[kb * cap + slot] = static_cast<uint8_t>(key >> (8 * kb));
  }
  for (size_t j = 0; j < sl.value_bytes; ++j) {
    bucket[(sl.key_bytes + j) * cap + slot] = ValueByte(key, j);
  }
  bucket[sl.MetaOffset() * cap + slot] = 0;
}

uint64_t ReadKeyAt(const uint8_t* bucket, size_t slot, size_t key_bytes,
                   size_t cap = bs::kBucketCapacity) {
  uint64_t key = 0;
  for (size_t kb = 0; kb < key_bytes; ++kb) {
    key |= uint64_t{bucket[kb * cap + slot]} << (8 * kb);
  }
  return key;
}

bool ValueIntact(const uint8_t* bucket, size_t slot, uint64_t key,
                 const bs::StashLayout& sl, size_t cap = bs::kBucketCapacity) {
  for (size_t j = 0; j < sl.value_bytes; ++j) {
    if (bucket[(sl.key_bytes + j) * cap + slot] !=
        ValueByte(key, j)) {
      return false;
    }
  }
  return true;
}

// kStashTargetRealPerBucket records per bucket at random slots, ids 1..live.
// Dummy slots keep the 0xA5 fill of the positional generator.
void GenerateUnique(bs::TableView t, const bs::StashLayout& sl,
                    const KeyGen& keys, uint64_t seed) {
  std::memset(t.data, 0xA5, t.num_buckets * t.layout.BucketBytes());
  uint64_t rng = seed;
  uint64_t id = 1;
  for (size_t b = 0; b < t.num_buckets; ++b) {
    uint8_t slots[bs::kBucketCapacity];
    for (size_t i = 0; i < bs::kBucketCapacity; ++i) {
      slots[i] = static_cast<uint8_t>(i);
    }
    uint64_t mask = 0;
    for (size_t i = 0; i < bs::kStashTargetRealPerBucket; ++i) {
      const size_t pick = i + SplitMix64(rng) % (bs::kBucketCapacity - i);
      std::swap(slots[i], slots[pick]);
      mask |= uint64_t{1} << slots[i];
      WriteRecord(t.Bucket(b), slots[i], keys.Key(id++), sl);
    }
    t.masks[b] = mask;
  }
}

// Spins, yielding now and then so an oversubscribed run still finishes.
template <class Cond>
inline void SpinUntil(Cond&& cond) {
  for (unsigned i = 1; !cond(); ++i) {
    if ((i & 1023) == 0) std::this_thread::yield();
    else _mm_pause();
  }
}

// T-1 persistent workers plus the caller.  Run(f) executes f(tid) on all T
// threads and returns when every one is done; Barrier() is callable from f.
class RoutePool {
 public:
  explicit RoutePool(unsigned n) : n_(n) {
    for (unsigned t = 1; t < n_; ++t) workers_.emplace_back([this, t] { Loop(t); });
  }
  ~RoutePool() {
    stop_.store(true, std::memory_order_release);
    for (auto& w : workers_) w.join();
  }
  void Run(const std::function<void(unsigned)>& f) {
    job_ = &f;
    done_.store(0, std::memory_order_relaxed);
    gen_.fetch_add(1, std::memory_order_release);
    f(0);
    SpinUntil([&] { return done_.load(std::memory_order_acquire) == n_ - 1; });
  }
  void Barrier() {
    const uint64_t sense = sense_.load(std::memory_order_acquire);
    if (arrived_.fetch_add(1, std::memory_order_acq_rel) + 1 == n_) {
      arrived_.store(0, std::memory_order_relaxed);
      sense_.store(sense + 1, std::memory_order_release);
    } else {
      SpinUntil([&] { return sense_.load(std::memory_order_acquire) != sense; });
    }
  }

 private:
  void Loop(unsigned tid) {
    uint64_t seen = 0;
    for (;;) {
      SpinUntil([&] {
        return gen_.load(std::memory_order_acquire) != seen ||
               stop_.load(std::memory_order_acquire);
      });
      if (stop_.load(std::memory_order_acquire)) return;
      seen = gen_.load(std::memory_order_acquire);
      (*job_)(tid);
      done_.fetch_add(1, std::memory_order_acq_rel);
    }
  }
  unsigned n_;
  std::vector<std::thread> workers_;
  const std::function<void(unsigned)>* job_ = nullptr;
  std::atomic<uint64_t> gen_{0}, sense_{0};
  std::atomic<unsigned> done_{0}, arrived_{0};
  std::atomic<bool> stop_{false};
};

// ButterflyRouteStashCacheOblivious on T threads.  The recursion's first split
// (SplitSubnetwork) is 2^high independent sub-networks on bits [0, low), then
// 2^low independent stride-multiplied ones on bits [low, levels); each layer is
// divided into contiguous unit ranges, with a barrier between the layers.  The
// MergeSplit set and every MergeSplit's input are those of the serial order,
// so the table is byte-identical; only each shed lands in its thread's private
// stash set (a set either way).
template <bool Check, bool Unfused = false>
bool RouteParallel(RoutePool& pool, unsigned threads, bs::TableView t,
                   unsigned levels, std::vector<StashSet>& sets) {
  std::atomic<bool> ok{true};
  const bool leaf = bs::SubnetworkIsLeaf(levels, 0);
  const bs::SubnetworkSplit split = bs::SplitSubnetwork(levels);
  pool.Run([&](unsigned tid) {
    bs::ButterflyStashContext ctx;
    ctx.data = t.data;
    ctx.masks = t.masks;
    ctx.layout = t.layout;
    ctx.bucket_bytes = t.layout.BucketBytes();
    ctx.level_stashes = sets[tid].stashes.data();
    if (leaf) {
      if (tid == 0) {
        const bool routed = Unfused
            ? bs::benchmark_comparator::CacheObliviousUnfused<Check>(t, levels, ctx.level_stashes)
            : bs::ButterflyRouteStashCacheOblivious<Check>(t, levels, ctx.level_stashes);
        if (!routed) ok.store(false, std::memory_order_relaxed);
      }
      return;
    }
    const auto range = [&](size_t n, size_t* lo, size_t* hi) {
      *lo = n * tid / threads;
      *hi = n * (tid + 1) / threads;
    };
    size_t lo, hi;
    range(size_t{1} << split.high, &lo, &hi);
    for (size_t h = lo; h < hi; ++h) {
      const bool routed = Unfused
          ? bs::benchmark_comparator::SubnetworkUnfused<Check>(ctx, h << split.low, 0, split.low)
          : bs::RouteSubnetworkRecursive<Check>(ctx, h << split.low, 0, split.low);
      if (!routed) {
        ok.store(false, std::memory_order_relaxed);
      }
    }
    pool.Barrier();
    range(size_t{1} << split.low, &lo, &hi);
    for (size_t l = lo; l < hi; ++l) {
      const bool routed = Unfused
          ? bs::benchmark_comparator::SubnetworkUnfused<Check>(ctx, l, split.low, split.high)
          : bs::RouteSubnetworkRecursive<Check>(ctx, l, split.low, split.high);
      if (!routed) {
        ok.store(false, std::memory_order_relaxed);
      }
    }
  });
  return ok.load();
}

struct RowFields {
  const char* network;
  size_t key_bytes, value_bytes, entry_bytes, live, buckets, levels, reps;
  unsigned threads;
  uint64_t seed;
  size_t bucket_slots = bs::kBucketCapacity;  // 512 for the butterfly512 rows
};

void PrintRoutingRow(const RowFields& r, const char* status, bool timed,
                     double route_s, size_t shed, const char* note) {
  std::printf(
      "{\"network\":\"%s\",\"key_bytes\":%zu,\"value_bytes\":%zu,"
      "\"entry_bytes\":%zu,\"live_entries\":%zu,\"buckets\":%zu,"
      "\"slots\":%zu,\"bucket_slots\":%zu,\"levels\":%zu,\"reps\":%zu,",
      r.network, r.key_bytes, r.value_bytes, r.entry_bytes, r.live, r.buckets,
      r.buckets * r.bucket_slots, r.bucket_slots, r.levels, r.reps);
  if (timed) {
    std::printf(
        "\"route_ms\":%.6f,\"ns_per_record_per_stage\":%.6f,"
        "\"records_per_second\":%.1f,",
        route_s * 1e3, route_s * 1e9 / (double(r.live) * r.levels),
        double(r.live) / route_s);
  } else {
    std::printf(
        "\"route_ms\":null,\"ns_per_record_per_stage\":null,"
        "\"records_per_second\":null,");
  }
  std::printf("\"shed\":%zu,\"status\":\"%s\",\"seed\":%llu,\"threads\":%u",
              shed, status, static_cast<unsigned long long>(r.seed), r.threads);
  if (note[0] != 0) std::printf(",\"note\":\"%s\"", note);
  std::printf("}\n");
  std::fflush(stdout);
}

// Everything the routed table plus its stashes must satisfy; empty on success.
std::string VerifyRoute(bs::TableView t, const bs::StashLayout& sl,
                        const std::vector<StashSet>& sets, const KeyGen& keys,
                        size_t live, uint64_t nonce_lo, uint64_t nonce_hi) {
  std::vector<uint64_t> seen(live / 64 + 1, 0);
  size_t total = 0;
  std::string why;
  const auto visit = [&](const uint8_t* bucket, size_t slot) {
    const uint64_t key = ReadKeyAt(bucket, slot, sl.key_bytes);
    const uint64_t id = keys.Index(key);
    if (id < 1 || id > live) { why = "key is not an input record"; return false; }
    uint64_t& word = seen[id / 64];
    if ((word >> (id % 64)) & 1) { why = "record duplicated"; return false; }
    word |= uint64_t{1} << (id % 64);
    if (!ValueIntact(bucket, slot, key, sl)) { why = "value corrupted"; return false; }
    ++total;
    return true;
  };
  for (size_t b = 0; b < t.num_buckets; ++b) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      if (!((t.masks[b] >> slot) & 1)) continue;
      if (!visit(t.Bucket(b), slot)) return why;
      const uint64_t key = ReadKeyAt(t.Bucket(b), slot, sl.key_bytes);
      const uint64_t tag =
          microram::crypto::AesCtrTagU64WordsHost(nonce_lo, nonce_hi, key);
      if ((tag & (t.num_buckets - 1)) != b) return "entry in the wrong bucket";
    }
  }
  for (const StashSet& set : sets) {
    for (const bs::ResidualStash& st : set.stashes) {
      for (size_t b = 0; b < st.num_buckets; ++b) {
        for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
          if ((st.masks[b] >> slot) & 1) {
            if (!visit(st.Bucket(b), slot)) return why;
          }
        }
      }
    }
  }
  if (total != live) return "records lost (stash overflow or kernel bug)";
  return "";
}

// One 64-slot network on the calling thread.
template <bool Check>
bool RouteOne(const std::string& net, bs::TableView t, unsigned levels,
              bs::ResidualStash* stashes) {
  if (net == "flat") return bs::ButterflyRouteStash<Check>(t, levels, stashes, 1);
  if (net == "grouped6") return bs::ButterflyRouteStash<Check>(t, levels, stashes, 6);
  if (net == "grouped6_unfused") {
    return bs::benchmark_comparator::GroupedUnfused<Check>(t, levels, stashes, 6);
  }
  if (net == "cache_oblivious_unfused") {
    return bs::benchmark_comparator::CacheObliviousUnfused<Check>(t, levels, stashes);
  }
  return bs::ButterflyRouteStashCacheOblivious<Check>(t, levels, stashes);
}

int RunRoutingRows(const Options& o) {
  const size_t buckets = o.live_entries / bs::kStashTargetRealPerBucket;
  const unsigned levels = bs::Log2Exact(buckets);
  bs::StashLayout sl;
  sl.key_bytes = o.key_bytes;
  sl.value_bytes = o.value_bytes;
  const bs::Layout layout = sl.Base();
  const size_t data_bytes = buckets * layout.BucketBytes();
  int exit_code = 0;

  RowFields row{"", o.key_bytes, o.value_bytes, sl.EntryBytes(), o.live_entries,
                buckets, levels, 0, o.threads, o.seed};
  const uint64_t need = 2 * (uint64_t{data_bytes} + buckets * sizeof(uint64_t));
  if (need > o.max_bytes) {
    std::fprintf(stderr,
                 "skipped: data + pristine buffers need %.2f GiB > --max-bytes "
                 "%.2f GiB\n",
                 need / 1073741824.0, o.max_bytes / 1073741824.0);
    for (const std::string& net : o.networks) {
      row.network = net.c_str();
      PrintRoutingRow(row, "skipped_memory", false, 0, 0, "");
    }
    return 1;
  }

  const KeyGen keys(o.key_bytes, o.seed, o.live_entries);
  const uint64_t nonce_lo = 42 ^ o.seed, nonce_hi = 7;
  auto data = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> masks(buckets);
  bs::TableView t{layout, buckets, data.get(), masks.data()};
  GenerateUnique(t, sl, keys, o.seed);
  bs::ComputeRoutingTags(t, nonce_lo, nonce_hi);
  auto pristine = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> pristine_masks(masks);
  std::memcpy(pristine.get(), data.get(), data_bytes);
  const auto restore = [&] {
    std::memcpy(data.get(), pristine.get(), data_bytes);
    std::memcpy(masks.data(), pristine_masks.data(), buckets * sizeof(uint64_t));
  };

  std::vector<StashSet> sets;
  for (unsigned i = 0; i < o.threads; ++i) {
    sets.emplace_back(levels + 1, o.stash_buckets, layout);
  }
  std::unique_ptr<RoutePool> pool;
  if (o.threads > 1) pool = std::make_unique<RoutePool>(o.threads);

  for (const std::string& net : o.networks) {
    row.network = net.c_str();
    if (o.threads > 1 && net != "cache_oblivious" && net != "cache_oblivious_unfused") {
      PrintRoutingRow(row, "unsupported_threads", false, 0, 0,
                      "only cache_oblivious variants run on more than one thread");
      exit_code = 1;
      continue;
    }
    const auto route = [&]() -> bool {
      const auto go = [&](auto check) -> bool {
        constexpr bool kCheck = decltype(check)::value;
        if (o.threads > 1) {
          return net == "cache_oblivious_unfused"
              ? RouteParallel<kCheck, true>(*pool, o.threads, t, levels, sets)
              : RouteParallel<kCheck>(*pool, o.threads, t, levels, sets);
        }
        return RouteOne<kCheck>(net, t, levels, sets[0].stashes.data());
      };
      return o.check_overflow ? go(std::true_type{}) : go(std::false_type{});
    };

    bool overflowed = false;
    size_t shed = 0;
    const PhaseTime time = Measure(static_cast<int>(o.reps), [&] {
      restore();
      for (auto& s : sets) s.Reset();
      const auto start = Clock::now();
      const bool ok = route();
      const double seconds = SecondsSince(start);
      size_t count = 0;
      for (const auto& s : sets) count += s.Count();
      shed = count;
      overflowed |= !ok;
      return seconds;
    });
    row.reps = static_cast<size_t>(time.reps);
    if (overflowed) {
      PrintRoutingRow(row, "overflow", false, 0, shed, "");
      exit_code = 1;
      continue;
    }
    std::string why;
    if (o.verify) why = VerifyRoute(t, sl, sets, keys, o.live_entries, nonce_lo, nonce_hi);
    if (!why.empty()) {
      PrintRoutingRow(row, "verify_failed", false, 0, shed, why.c_str());
      exit_code = 1;
      continue;
    }
    PrintRoutingRow(row, "ok", true, time.seconds_per_rep, shed,
                    o.verify ? "" : "unverified");
  }
  return exit_code;
}

// ---------------------------------------------------------------------------
// Instance mode: P independent routes started together
// ---------------------------------------------------------------------------
//
// The ORAM rebuilds several levels at once, one thread each, so a route runs
// while other routes stream their own tables.  Alone, a 2^20-record table
// partly fits the L3; P of them at once do not, and they share the memory
// bandwidth.  These rows time that situation: P threads, each with its own
// table, input seed (seed + i) and stashes, start every route at a common
// barrier and meet at another after the slowest one, so a round never
// overlaps the next restore.  A round routes every instance once per network,
// the networks in alternating order (A/B order bias).  Before the timed
// rounds, one untimed round per network checks every instance's output
// (VerifyRoute).  Each instance restores its table with streaming stores: the
// lines leave the caches, as after the preparation copy's streaming stores,
// so every route starts with its table in DRAM.

// "1-8" or "1,3,5-7"; empty on a malformed list.
std::vector<int> ParseCpuList(const std::string& text) {
  std::vector<int> cpus;
  size_t pos = 0;
  while (pos < text.size()) {
    size_t comma = text.find(',', pos);
    if (comma == std::string::npos) comma = text.size();
    const std::string part = text.substr(pos, comma - pos);
    char* end = nullptr;
    const long lo = std::strtol(part.c_str(), &end, 10);
    long hi = lo;
    if (end != part.c_str() && *end == '-') {
      const char* rest = end + 1;
      hi = std::strtol(rest, &end, 10);
      if (end == rest) return {};
    }
    if (end == part.c_str() || *end != 0 || lo < 0 || hi < lo) return {};
    for (long c = lo; c <= hi; ++c) cpus.push_back(static_cast<int>(c));
    pos = comma + 1;
  }
  return cpus;
}

bool PinThisThread(int cpu) {
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(static_cast<unsigned>(cpu), &set);
  return pthread_setaffinity_np(pthread_self(), sizeof(set), &set) == 0;
}

// A copy with streaming stores: the destination lines end up in DRAM, not in
// a cache.  Both buffers 64-byte aligned, bytes a multiple of 64.
void StreamCopy(uint8_t* dst, const uint8_t* src, size_t bytes) {
  for (size_t i = 0; i < bytes; i += 64) {
    _mm512_stream_si512(reinterpret_cast<__m512i*>(dst + i),
                        _mm512_load_si512(reinterpret_cast<const void*>(src + i)));
  }
  _mm_sfence();
}

// Bytes of this process on transparent huge pages (the tables ask for them).
uint64_t AnonHugeBytes() {
  std::ifstream in("/proc/self/smaps_rollup");
  for (std::string line; std::getline(in, line);) {
    if (line.rfind("AnonHugePages:", 0) == 0) {
      return std::strtoull(line.c_str() + 14, nullptr, 10) << 10;
    }
  }
  return 0;
}

double Median(std::vector<double> v) {
  std::sort(v.begin(), v.end());
  const size_t n = v.size();
  return n % 2 ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

void PrintMsArray(const char* name, const std::vector<double>& seconds) {
  std::printf(",\"%s\":[", name);
  for (size_t i = 0; i < seconds.size(); ++i) {
    std::printf("%s%.4f", i ? "," : "", seconds[i] * 1e3);
  }
  std::printf("]");
}

int RunInstanceRows(const Options& o) {
  const size_t buckets = o.live_entries / bs::kStashTargetRealPerBucket;
  const unsigned levels = bs::Log2Exact(buckets);
  bs::StashLayout sl;
  sl.key_bytes = o.key_bytes;
  sl.value_bytes = o.value_bytes;
  const bs::Layout layout = sl.Base();
  const size_t data_bytes = buckets * layout.BucketBytes();
  const unsigned p = o.instances;
  const size_t nets = o.networks.size();
  const size_t rounds = o.reps;

  RowFields row{"", o.key_bytes, o.value_bytes, sl.EntryBytes(), o.live_entries,
                buckets, levels, rounds, 1, o.seed};
  const uint64_t need =
      uint64_t{p} * 2 * (uint64_t{data_bytes} + buckets * sizeof(uint64_t));
  if (need > o.max_bytes) {
    std::fprintf(stderr,
                 "skipped: %u instances' data + pristine buffers need %.2f GiB "
                 "> --max-bytes %.2f GiB\n",
                 p, need / 1073741824.0, o.max_bytes / 1073741824.0);
    for (const std::string& net : o.networks) {
      row.network = net.c_str();
      PrintRoutingRow(row, "skipped_memory", false, 0, 0, "");
    }
    return 1;
  }

  // Per (round, network, instance): seconds since `epoch` at the route's
  // start and end.
  const auto cell = [&](size_t r, size_t n, unsigned i) {
    return (r * nets + n) * p + i;
  };
  std::vector<double> begin(rounds * nets * p), end(rounds * nets * p);
  std::vector<uint8_t> overflowed(nets * p, 0);
  std::vector<std::string> why(nets * p);
  std::vector<size_t> shed(nets * p, 0);
  std::atomic<bool> pin_failed{false};
  uint64_t huge_bytes = 0;

  RoutePool pool(p);
  const Clock::time_point epoch = Clock::now();
  pool.Run([&](unsigned tid) {
    if (!o.cpus.empty() && !PinThisThread(o.cpus[tid])) {
      pin_failed.store(true, std::memory_order_relaxed);
    }
    // Every buffer is allocated and first touched by its own thread.
    const uint64_t seed = o.seed + tid;
    const KeyGen keys(o.key_bytes, seed, o.live_entries);
    const uint64_t nonce_lo = 42 ^ seed, nonce_hi = 7;
    auto data = bs::AllocateAligned64(data_bytes);
    std::vector<uint64_t> masks(buckets);
    const bs::TableView t{layout, buckets, data.get(), masks.data()};
    GenerateUnique(t, sl, keys, seed);
    bs::ComputeRoutingTags(t, nonce_lo, nonce_hi);
    auto pristine = bs::AllocateAligned64(data_bytes);
    std::memcpy(pristine.get(), data.get(), data_bytes);
    const std::vector<uint64_t> pristine_masks(masks);
    std::vector<StashSet> sets;
    sets.emplace_back(levels + 1, o.stash_buckets, layout);
    const auto restore = [&] {
      StreamCopy(data.get(), pristine.get(), data_bytes);
      std::memcpy(masks.data(), pristine_masks.data(), buckets * sizeof(uint64_t));
      sets[0].Reset();
    };
    const auto route = [&](const std::string& net) {
      return o.check_overflow
          ? RouteOne<true>(net, t, levels, sets[0].stashes.data())
          : RouteOne<false>(net, t, levels, sets[0].stashes.data());
    };
    pool.Barrier();
    if (pin_failed.load(std::memory_order_relaxed)) return;  // every thread sees it
    if (tid == 0) huge_bytes = AnonHugeBytes();

    for (size_t n = 0; n < nets; ++n) {
      restore();
      pool.Barrier();
      const bool ok = route(o.networks[n]);
      pool.Barrier();
      shed[n * p + tid] = sets[0].Count();
      if (!ok) {
        overflowed[n * p + tid] = 1;
      } else if (o.verify) {
        why[n * p + tid] =
            VerifyRoute(t, sl, sets, keys, o.live_entries, nonce_lo, nonce_hi);
      }
    }
    for (size_t r = 0; r < rounds; ++r) {
      for (size_t k = 0; k < nets; ++k) {
        const size_t n = (r & 1) ? nets - 1 - k : k;
        restore();
        pool.Barrier();
        const Clock::time_point start = Clock::now();
        const bool ok = route(o.networks[n]);
        const Clock::time_point stop = Clock::now();
        pool.Barrier();
        if (!ok) overflowed[n * p + tid] = 1;
        begin[cell(r, n, tid)] = std::chrono::duration<double>(start - epoch).count();
        end[cell(r, n, tid)] = std::chrono::duration<double>(stop - epoch).count();
      }
    }
  });
  if (pin_failed.load()) {
    std::fprintf(stderr, "could not pin to --cpus %s\n", o.cpus_text.c_str());
    return 1;
  }

  // Per network and round: the instances' mean route time, and the round's
  // wall time (first start to last end).
  int exit_code = 0;
  std::vector<std::vector<double>> mean_s(nets), wall_s(nets);
  std::vector<bool> ok(nets);
  for (size_t n = 0; n < nets; ++n) {
    row.network = o.networks[n].c_str();
    std::vector<double> instance_s(p, 0.0);
    double shortest = 1e300, longest = 0, total = 0;
    for (size_t r = 0; r < rounds; ++r) {
      double sum = 0, first = 1e300, last = 0;
      for (unsigned i = 0; i < p; ++i) {
        const double b = begin[cell(r, n, i)], e = end[cell(r, n, i)];
        sum += e - b;
        instance_s[i] += (e - b) / double(rounds);
        shortest = std::min(shortest, e - b);
        longest = std::max(longest, e - b);
        first = std::min(first, b);
        last = std::max(last, e);
      }
      mean_s[n].push_back(sum / p);
      wall_s[n].push_back(last - first);
      total += sum;
    }
    size_t shed_n = 0;
    bool overflow = false;
    std::string bad;
    for (unsigned i = 0; i < p; ++i) {
      shed_n += shed[n * p + i];
      overflow |= overflowed[n * p + i] != 0;
      if (bad.empty()) bad = why[n * p + i];
    }
    ok[n] = !overflow && bad.empty();
    if (!ok[n]) exit_code = 1;
    std::printf(
        "{\"mode\":\"instances\",\"network\":\"%s\",\"key_bytes\":%zu,"
        "\"value_bytes\":%zu,\"entry_bytes\":%zu,\"live_entries\":%zu,"
        "\"buckets\":%zu,\"levels\":%zu,\"table_bytes\":%zu,\"instances\":%u,"
        "\"cpus\":\"%s\",\"rounds\":%zu,",
        row.network, row.key_bytes, row.value_bytes, row.entry_bytes, row.live,
        row.buckets, row.levels, data_bytes, p, o.cpus_text.c_str(), rounds);
    if (ok[n]) {
      double wall_total = 0;
      for (double w : wall_s[n]) wall_total += w;
      const double route_s = total / (double(rounds) * p);
      const double wall_mean = wall_total / double(rounds);
      std::printf(
          "\"route_ms\":%.4f,\"route_ms_median\":%.4f,\"route_ms_min\":%.4f,"
          "\"route_ms_max\":%.4f,\"round_wall_ms\":%.4f,"
          "\"round_wall_ms_median\":%.4f,\"ns_per_record_per_stage\":%.4f,"
          "\"aggregate_records_per_second\":%.1f,",
          route_s * 1e3, Median(mean_s[n]) * 1e3, shortest * 1e3, longest * 1e3,
          wall_mean * 1e3, Median(wall_s[n]) * 1e3,
          route_s * 1e9 / (double(row.live) * row.levels),
          double(p) * double(row.live) / wall_mean);
    } else {
      std::printf("\"route_ms\":null,\"round_wall_ms\":null,");
    }
    std::printf(
        "\"shed\":%zu,\"status\":\"%s\",\"seed\":%llu,\"anon_huge_bytes\":%llu",
        shed_n, overflow ? "overflow" : ok[n] ? "ok" : "verify_failed",
        static_cast<unsigned long long>(o.seed),
        static_cast<unsigned long long>(huge_bytes));
    if (!bad.empty()) std::printf(",\"note\":\"%s\"", bad.c_str());
    if (!o.verify) std::printf(",\"note\":\"unverified\"");
    if (ok[n]) {
      PrintMsArray("round_mean_ms", mean_s[n]);
      PrintMsArray("round_wall_ms_all", wall_s[n]);
      PrintMsArray("instance_mean_ms", instance_s);
    }
    std::printf("}\n");
  }
  // Paired by round: the first network's time over each other network's.
  for (size_t n = 1; n < nets; ++n) {
    if (!ok[0] || !ok[n]) continue;
    std::vector<double> ratio, wall_ratio;
    double sum0 = 0, sum_n = 0;
    for (size_t r = 0; r < rounds; ++r) {
      ratio.push_back(mean_s[0][r] / mean_s[n][r]);
      wall_ratio.push_back(wall_s[0][r] / wall_s[n][r]);
      sum0 += mean_s[0][r];
      sum_n += mean_s[n][r];
    }
    std::printf(
        "{\"mode\":\"instances_ratio\",\"numerator\":\"%s\","
        "\"denominator\":\"%s\",\"key_bytes\":%zu,\"value_bytes\":%zu,"
        "\"live_entries\":%zu,\"instances\":%u,\"cpus\":\"%s\",\"rounds\":%zu,"
        "\"route_ratio_median\":%.4f,\"route_ratio_min\":%.4f,"
        "\"route_ratio_max\":%.4f,\"route_ratio_of_means\":%.4f,"
        "\"wall_ratio_median\":%.4f}\n",
        o.networks[0].c_str(), o.networks[n].c_str(), row.key_bytes,
        row.value_bytes, row.live, p, o.cpus_text.c_str(), rounds,
        Median(ratio), *std::min_element(ratio.begin(), ratio.end()),
        *std::max_element(ratio.begin(), ratio.end()), sum0 / sum_n,
        Median(wall_ratio));
  }
  return exit_code;
}

// ---------------------------------------------------------------------------
// Pair mode: three comparator kernels with MergeSplitPairStash's contract
// ---------------------------------------------------------------------------
//
// Contract shared by every arm (taken from MergeSplitPairStash): first's
// records stay on the side their tag bit selects; second's records of a
// direction fill that side's free slots in slot order; the surplus (a suffix
// of second's records of that direction, in slot order) is shed into the
// stash.  Checked mode returns false BEFORE touching anything if the stash
// cannot take the surplus.  Scalar mask arithmetic only (pdep, popcount,
// min): no branch or memory index depends on a tag or an occupancy bit.

enum class Arm { kCurrent, kCompressExpand, kBitonic };

const char* ArmName(Arm a) {
  switch (a) {
    case Arm::kCurrent: return "current";
    case Arm::kCompressExpand: return "compress_expand";
    case Arm::kBitonic: return "bitonic";
  }
  return "?";
}

struct PairMasks {
  uint64_t a0, a1;        // first's real slots by direction
  uint64_t src0, src1;    // second's slots that land on side 0 / side 1
  uint64_t used0, used1;  // the free slots of side 0 / 1 they land in
  uint64_t resid;         // second's slots that shed
  uint64_t new_a, new_b;  // output occupancy of the in-place merge
};

inline PairMasks PlanPairMasks(const uint8_t* first, const uint8_t* second,
                               uint64_t first_real, uint64_t second_real,
                               size_t tag_line) {
  const __m512i probe = _mm512_set1_epi8(1);
  const __m512i ft = _mm512_load_si512(
      reinterpret_cast<const void*>(first + tag_line * bs::kBucketCapacity));
  const __m512i st = _mm512_load_si512(
      reinterpret_cast<const void*>(second + tag_line * bs::kBucketCapacity));
  PairMasks m;
  m.a1 = microram::core::obliTestMask8(ft, probe) & first_real;
  const uint64_t b1 = microram::core::obliTestMask8(st, probe) & second_real;
  m.a0 = first_real & ~m.a1;
  const uint64_t b0 = second_real & ~b1;
  const unsigned alloc0 = std::min(bs::Popcount64(b0),
      static_cast<unsigned>(bs::kBucketCapacity) - bs::Popcount64(m.a0));
  const unsigned alloc1 = std::min(bs::Popcount64(b1),
      static_cast<unsigned>(bs::kBucketCapacity) - bs::Popcount64(m.a1));
  m.used0 = _pdep_u64(bs::LowMask64(alloc0), ~m.a0);
  m.used1 = _pdep_u64(bs::LowMask64(alloc1), ~m.a1);
  m.src0 = _pdep_u64(bs::LowMask64(alloc0), b0);
  m.src1 = _pdep_u64(bs::LowMask64(alloc1), b1);
  m.resid = (b0 & ~m.src0) | (b1 & ~m.src1);
  m.new_a = m.a0 | m.used0;
  m.new_b = m.a1 | m.used1;
  return m;
}

// Stash bookkeeping for the shed set: per stash bucket, which second-line
// slots go in (take_src) and which free stash slots receive them (dest).
struct ShedPlan {
  uint64_t take_src[bs::kMaxResidualStashBuckets];
  uint64_t dest[bs::kMaxResidualStashBuckets];
  size_t num_buckets = 0;
};

inline void PlanShed(bs::ResidualStash& stash, uint64_t resid, ShedPlan* p) {
  p->num_buckets = stash.num_buckets;
  uint64_t pending = resid;
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    const uint64_t old_mask = stash.masks[b];
    const unsigned free_slots =
        static_cast<unsigned>(bs::kBucketCapacity) - bs::Popcount64(old_mask);
    const unsigned take = std::min(bs::Popcount64(pending), free_slots);
    p->take_src[b] = _pdep_u64(bs::LowMask64(take), pending);
    p->dest[b] = _pdep_u64(bs::LowMask64(take), ~old_mask);
    stash.masks[b] = old_mask | p->dest[b];
    pending &= ~p->take_src[b];
  }
}

// One routed line's shed: compress the shed slots of `second_line`, expand
// them into the stash bucket's free slots (other slots keep their bytes).
template <int S>
inline void ShedLine(uint8_t* const* ptr, const ShedPlan& p, size_t off,
                     __m512i second_line) {
  if constexpr (S == bs::kDynamicStashBuckets) {
    for (size_t b = 0; b < p.num_buckets; ++b) {
      uint8_t* q = ptr[b] + off;
      const __m512i old = _mm512_load_si512(reinterpret_cast<const void*>(q));
      _mm512_store_si512(reinterpret_cast<void*>(q),
          _mm512_mask_expand_epi8(old, _cvtu64_mask64(p.dest[b]),
              _mm512_maskz_compress_epi8(_cvtu64_mask64(p.take_src[b]),
                                         second_line)));
    }
  } else {
    for (int b = 0; b < S; ++b) {
      uint8_t* q = ptr[b] + off;
      const __m512i old = _mm512_load_si512(reinterpret_cast<const void*>(q));
      _mm512_store_si512(reinterpret_cast<void*>(q),
          _mm512_mask_expand_epi8(old, _cvtu64_mask64(p.dest[b]),
              _mm512_maskz_compress_epi8(_cvtu64_mask64(p.take_src[b]),
                                         second_line)));
    }
  }
}

// Returns false (nothing modified) if checked and the stash cannot take the
// surplus; otherwise runs `lines` with the shed plan applied and the stash
// masks updated.  Dispatches the public stash depth to a compile-time one.
template <bool Check, class LinesFn>
inline bool PairDriver(const PairMasks& m, bs::ResidualStash& stash,
                       LinesFn&& lines_fn) {
  assert(Check || stash.num_buckets > 0);
  if constexpr (Check) {
    if (stash.Count() + bs::Popcount64(m.resid) > stash.Capacity()) {
      return false;
    }
  }
  ShedPlan shed;
  PlanShed(stash, m.resid, &shed);
  uint8_t* ptr[bs::kMaxResidualStashBuckets];
  for (size_t b = 0; b < stash.num_buckets; ++b) ptr[b] = stash.Bucket(b);
  bs::DispatchStashDepth<static_cast<int>(bs::kMaxResidualStashBuckets)>(
      shed.num_buckets,
      [&](auto depth) {
        lines_fn(depth, static_cast<const uint8_t* const*>(nullptr), shed, ptr);
        return true;
      },
      [&] {
        lines_fn(std::integral_constant<int, bs::kDynamicStashBuckets>{},
                 static_cast<const uint8_t* const*>(nullptr), shed, ptr);
        return true;
      });
  return true;
}

// ---- arm: compress_expand -------------------------------------------------
// Per routed line: VPCOMPRESSB each direction of second's records into a
// dense run, VPEXPANDB that run into the free slots of the side it belongs
// to (first's records already sit in their slots: a zero-masked copy of the
// first line is the expand's background).  The only plan is mask arithmetic.
template <bool Check>
bool PairCompressExpand(uint8_t* first, uint8_t* second, uint64_t* fm,
                        uint64_t* sm, size_t lines, size_t tag_line,
                        bs::ResidualStash& stash) {
  const PairMasks m = PlanPairMasks(first, second, *fm, *sm, tag_line);
  const bool ok = PairDriver<Check>(
      m, stash, [&](auto depth, const uint8_t* const*, const ShedPlan& shed,
                    uint8_t* const* sptr) {
        constexpr int S = decltype(depth)::value;
        const __mmask64 a0 = _cvtu64_mask64(m.a0), a1 = _cvtu64_mask64(m.a1);
        const __mmask64 s0 = _cvtu64_mask64(m.src0), s1 = _cvtu64_mask64(m.src1);
        const __mmask64 u0 = _cvtu64_mask64(m.used0), u1 = _cvtu64_mask64(m.used1);
        size_t off = 0;
        for (size_t line = 0; line < lines; ++line, off += bs::kBucketCapacity) {
          const __m512i f = _mm512_load_si512(
              reinterpret_cast<const void*>(first + off));
          const __m512i s = _mm512_load_si512(
              reinterpret_cast<const void*>(second + off));
          ShedLine<S>(sptr, shed, off, s);
          const __m512i c0 = _mm512_maskz_compress_epi8(s0, s);
          const __m512i c1 = _mm512_maskz_compress_epi8(s1, s);
          _mm512_store_si512(reinterpret_cast<void*>(first + off),
              _mm512_mask_expand_epi8(_mm512_maskz_mov_epi8(a0, f), u0, c0));
          _mm512_store_si512(reinterpret_cast<void*>(second + off),
              _mm512_mask_expand_epi8(_mm512_maskz_mov_epi8(a1, f), u1, c1));
        }
      });
  if (!ok) return false;
  *fm = m.new_a;
  *sm = m.new_b;
  return true;
}

// ---- arm: bitonic ---------------------------------------------------------
// The pair's 128 slots (first's 64 then second's 64) are sorted by a class
// key with the full bitonic network (7 phases, 28 compare-exchange stages):
//   0 = side-0 record, 1 = empty reserved for side 0, 2 = side-1 record,
//   3 = empty reserved for side 1.
// Shed records are classed as empties (their bytes were already compressed
// into the stash from the unsorted second line).  Side 0 has 64 - n0 reserved
// empties and side 1 has 64 - n1, so after the sort slots 0..63 are exactly
// side 0's bucket and 64..127 side 1's; output occupancy is the low n0 / n1
// slots.  PLAN (inside the timer): the keys are built from the masks, then
// every stage's swap mask is computed from the keys by permute + compares on
// the key vectors.  APPLY: every stage runs on every routed line as a
// VPERMB of the partner slots plus a masked blend (the j = 64 stage swaps
// between the two registers with blends only).
constexpr int kBitonicStages = 28;
struct BitonicTables {
  int j[kBitonicStages];
  uint64_t x[kBitonicStages][2];  // lower-position XOR descending, per half
  alignas(64) uint8_t partner[6][64];
  BitonicTables() {
    int st = 0;
    for (int k = 2; k <= 128; k *= 2) {
      for (int jj = k / 2; jj >= 1; jj /= 2, ++st) {
        j[st] = jj;
        for (int h = 0; h < 2; ++h) {
          uint64_t bits = 0;
          for (int s = 0; s < 64; ++s) {
            const int i = h * 64 + s;
            const bool lower = (i & jj) == 0;
            const bool desc = (i & k) != 0;
            if (lower != desc) bits |= uint64_t{1} << s;
          }
          x[st][h] = bits;
        }
      }
    }
    for (int l = 0; l < 6; ++l) {
      for (int s = 0; s < 64; ++s) partner[l][s] = static_cast<uint8_t>(s ^ (1 << l));
    }
  }
};
inline const BitonicTables& Tables() {
  static const BitonicTables t;
  return t;
}
inline int Log2Small(int v) { return __builtin_ctz(static_cast<unsigned>(v)); }

template <bool Check>
bool PairBitonic(uint8_t* first, uint8_t* second, uint64_t* fm, uint64_t* sm,
                 size_t lines, size_t tag_line, bs::ResidualStash& stash) {
  const BitonicTables& tb = Tables();
  const PairMasks m = PlanPairMasks(first, second, *fm, *sm, tag_line);
  const bool ok = PairDriver<Check>(
      m, stash, [&](auto depth, const uint8_t* const*, const ShedPlan& shed,
                    uint8_t* const* sptr) {
        constexpr int S = decltype(depth)::value;
        // Index plan: classes, then every stage's swap masks.
        const unsigned n0 = bs::Popcount64(m.new_a);
        const uint64_t empt_lo = ~(m.a0 | m.a1);
        const uint64_t empt_hi = ~(m.src0 | m.src1);
        const unsigned want0 = static_cast<unsigned>(bs::kBucketCapacity) - n0;
        const unsigned take_lo = std::min(want0, bs::Popcount64(empt_lo));
        const uint64_t e0_lo = _pdep_u64(bs::LowMask64(take_lo), empt_lo);
        const uint64_t e0_hi =
            _pdep_u64(bs::LowMask64(want0 - take_lo), empt_hi);
        __m512i key[2];
        key[0] = _mm512_set1_epi8(3);
        key[1] = _mm512_set1_epi8(3);
        const __m512i c0 = _mm512_setzero_si512(), c1 = _mm512_set1_epi8(1),
                      c2 = _mm512_set1_epi8(2);
        key[0] = _mm512_mask_mov_epi8(key[0], _cvtu64_mask64(m.a0), c0);
        key[0] = _mm512_mask_mov_epi8(key[0], _cvtu64_mask64(e0_lo), c1);
        key[0] = _mm512_mask_mov_epi8(key[0], _cvtu64_mask64(m.a1), c2);
        key[1] = _mm512_mask_mov_epi8(key[1], _cvtu64_mask64(m.src0), c0);
        key[1] = _mm512_mask_mov_epi8(key[1], _cvtu64_mask64(e0_hi), c1);
        key[1] = _mm512_mask_mov_epi8(key[1], _cvtu64_mask64(m.src1), c2);
        uint64_t swap[kBitonicStages][2];
        __m512i pidx[6];
        for (int l = 0; l < 6; ++l) {
          pidx[l] = _mm512_load_si512(reinterpret_cast<const void*>(tb.partner[l]));
        }
        for (int st = 0; st < kBitonicStages; ++st) {
          if (tb.j[st] == 64) {
            const __mmask64 g = _mm512_cmpgt_epu8_mask(key[0], key[1]);
            const __m512i k0 = _mm512_mask_blend_epi8(g, key[0], key[1]);
            key[1] = _mm512_mask_blend_epi8(g, key[1], key[0]);
            key[0] = k0;
            swap[st][0] = _cvtmask64_u64(g);
          } else {
            const __m512i pi = pidx[Log2Small(tb.j[st])];
            for (int h = 0; h < 2; ++h) {
              const __m512i kp = _mm512_permutexvar_epi8(pi, key[h]);
              const uint64_t gt =
                  _cvtmask64_u64(_mm512_cmpgt_epu8_mask(key[h], kp));
              const uint64_t lt =
                  _cvtmask64_u64(_mm512_cmplt_epu8_mask(key[h], kp));
              const uint64_t sw = (gt & tb.x[st][h]) | (lt & ~tb.x[st][h]);
              swap[st][h] = sw;
              key[h] = _mm512_mask_blend_epi8(_cvtu64_mask64(sw), key[h], kp);
            }
          }
        }
        // Apply every stage to every routed line.
        size_t off = 0;
        for (size_t line = 0; line < lines; ++line, off += bs::kBucketCapacity) {
          __m512i v0 = _mm512_load_si512(reinterpret_cast<const void*>(first + off));
          __m512i v1 = _mm512_load_si512(reinterpret_cast<const void*>(second + off));
          ShedLine<S>(sptr, shed, off, v1);
          for (int st = 0; st < kBitonicStages; ++st) {
            if (tb.j[st] == 64) {
              const __mmask64 g = _cvtu64_mask64(swap[st][0]);
              const __m512i n0v = _mm512_mask_blend_epi8(g, v0, v1);
              v1 = _mm512_mask_blend_epi8(g, v1, v0);
              v0 = n0v;
            } else {
              const __m512i pi = pidx[Log2Small(tb.j[st])];
              v0 = _mm512_mask_blend_epi8(_cvtu64_mask64(swap[st][0]), v0,
                                          _mm512_permutexvar_epi8(pi, v0));
              v1 = _mm512_mask_blend_epi8(_cvtu64_mask64(swap[st][1]), v1,
                                          _mm512_permutexvar_epi8(pi, v1));
            }
          }
          _mm512_store_si512(reinterpret_cast<void*>(first + off), v0);
          _mm512_store_si512(reinterpret_cast<void*>(second + off), v1);
        }
      });
  if (!ok) return false;
  *fm = bs::LowMask64(bs::Popcount64(m.new_a));
  *sm = bs::LowMask64(bs::Popcount64(m.new_b));
  return true;
}

template <bool Check>
struct KCurrent {
  bool operator()(uint8_t* a, uint8_t* b, uint64_t* ma, uint64_t* mb,
                  size_t lines, size_t tag_line, bs::ResidualStash& st) const {
    return bs::MergeSplitPairStash<Check>(a, b, ma, mb, lines, tag_line, 0, st);
  }
};
template <bool Check>
struct KCompressExpand {
  bool operator()(uint8_t* a, uint8_t* b, uint64_t* ma, uint64_t* mb,
                  size_t lines, size_t tag_line, bs::ResidualStash& st) const {
    return PairCompressExpand<Check>(a, b, ma, mb, lines, tag_line, st);
  }
};
template <bool Check>
struct KBitonic {
  bool operator()(uint8_t* a, uint8_t* b, uint64_t* ma, uint64_t* mb,
                  size_t lines, size_t tag_line, bs::ResidualStash& st) const {
    return PairBitonic<Check>(a, b, ma, mb, lines, tag_line, st);
  }
};

template <class F>
void WithKernel(Arm arm, bool check, F&& f) {
  if (check) {
    switch (arm) {
      case Arm::kCurrent: f(KCurrent<true>{}); break;
      case Arm::kCompressExpand: f(KCompressExpand<true>{}); break;
      default: f(KBitonic<true>{}); break;
    }
  } else {
    switch (arm) {
      case Arm::kCurrent: f(KCurrent<false>{}); break;
      case Arm::kCompressExpand: f(KCompressExpand<false>{}); break;
      default: f(KBitonic<false>{}); break;
    }
  }
}

// The verification every arm shares (first chunk): each of the chunk's
// records exactly once across both buckets of its pair and the stash, key and
// value intact, every table record on the side its tag bit selects (pairs
// whose checked call failed are left unmodified, so only their record
// accounting is checked), and no record lost.
std::string VerifyPairChunk(const bs::TableView& t, const bs::StashLayout& sl,
                            const KeyGen& keys, size_t n, size_t per_bucket,
                            size_t tag_line, const bs::ResidualStash& stash,
                            const std::vector<uint8_t>& pair_failed) {
  const uint64_t live = uint64_t{t.num_buckets} * per_bucket;
  std::vector<uint64_t> seen(live / 64 + 1, 0);
  size_t total = 0;
  const auto account = [&](const uint8_t* bucket, size_t slot) -> const char* {
    const uint64_t key = ReadKeyAt(bucket, slot, sl.key_bytes);
    const uint64_t id = keys.Index(key);
    if (id < 1 || id > live) return "key is not an input record";
    if ((seen[id / 64] >> (id % 64)) & 1) return "record duplicated";
    if (!ValueIntact(bucket, slot, key, sl)) return "value corrupted";
    seen[id / 64] |= uint64_t{1} << (id % 64);
    ++total;
    return nullptr;
  };
  for (size_t i = 0; i < n; ++i) {
    for (size_t k = 0; k < 2; ++k) {
      const size_t b = 2 * i + k;
      const uint8_t* bucket = t.Bucket(b);
      for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
        if (!((t.masks[b] >> slot) & 1)) continue;
        if (const char* e = account(bucket, slot)) return e;
        if (!pair_failed[i] &&
            (bucket[tag_line * bs::kBucketCapacity + slot] & 1) != k) {
          return "record in the wrong direction";
        }
      }
    }
  }
  for (size_t b = 0; b < stash.num_buckets; ++b) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      if (!((stash.masks[b] >> slot) & 1)) continue;
      if (const char* e = account(stash.Bucket(b), slot)) return e;
    }
  }
  if (total != n * 2 * per_bucket) return "records lost in a pair";
  return "";
}

int RunPairRows512(const Options& o);

// Public chunk sizes only. No timed interval may contain just one call.
bool PairPoolUsable(size_t pool, size_t pairs) {
  return pool >= 2 && pairs >= 2 && !(pool == 2 && (pairs & 1));
}

size_t PairChunkSize(size_t pool, size_t remaining) {
  size_t n = std::min(pool, remaining);
  if (remaining > n && remaining - n == 1) --n;  // leave two for the last chunk
  return n;
}

// N independent pair merge-splits (tag bit 0) on pairs of buckets, for each
// selected arm and each pool.
int RunPairRows(const Options& o) {
  bs::StashLayout sl;
  sl.key_bytes = o.key_bytes;
  sl.value_bytes = o.value_bytes;
  const bs::Layout layout = sl.Base();
  const size_t bucket_bytes = layout.BucketBytes();
  const size_t lines = layout.RoutedLines(0);
  const size_t tag_line = layout.TagLine(0);
  const size_t per_bucket = o.load_per_bucket;

  struct PoolSpec { const char* label; size_t bytes; };
  std::vector<PoolSpec> pools;
  if (o.pool_bytes > 0) {
    pools.push_back({"custom", o.pool_bytes});
  } else {
    pools.push_back({"cache_resident", size_t{2621440}});
    pools.push_back({"dram_streaming", size_t{41943040}});
  }
  std::vector<Arm> arms;
  const auto want = [&](const char* name) { return o.arm == "all" || o.arm == name; };
  if (want("current")) arms.push_back(Arm::kCurrent);
  if (want("compress_expand")) arms.push_back(Arm::kCompressExpand);
  if (want("bitonic")) arms.push_back(Arm::kBitonic);

  int exit_code = 0;
  for (const PoolSpec& ps : pools) {
    const size_t pool = std::min(
        std::max<size_t>(1, ps.bytes / (2 * bucket_bytes)), o.pairs);
    const size_t buckets = 2 * pool;
    const size_t pool_bytes = buckets * bucket_bytes;
    const uint64_t need = 2 * (uint64_t{buckets} * (bucket_bytes + 8));
    const auto head = [&](const Arm arm) {
      std::printf(
          "{\"mode\":\"pairs\",\"arm\":\"%s\",\"pool\":\"%s\","
          "\"pool_bytes\":%zu,\"requested_pool_bytes\":%zu,\"pool_pairs\":%zu,\"key_bytes\":%zu,"
          "\"value_bytes\":%zu,\"entry_bytes\":%zu,\"pairs\":%zu,"
          "\"slots_per_merge_split\":128,"
          "\"real_records_per_merge_split\":%zu,\"routed_lines\":%zu,",
          ArmName(arm), ps.label, pool_bytes, ps.bytes, pool, o.key_bytes, o.value_bytes,
          sl.EntryBytes(), o.pairs, 2 * per_bucket, lines);
    };
    if (!PairPoolUsable(pool, o.pairs)) {
      for (const Arm arm : arms) {
        head(arm);
        std::printf("\"status\":\"skipped_timing_granularity\",\"note\":\"pool/count cannot form chunks of at least two calls\"}\n");
      }
      exit_code = 1;
      continue;
    }
    if (need > o.max_bytes) {
      std::printf("{\"mode\":\"pairs\",\"pool\":\"%s\",\"status\":\"skipped_memory\"}\n",
                  ps.label);
      exit_code = 1;
      continue;
    }
    const size_t live = buckets * per_bucket;
    const KeyGen keys(o.key_bytes, o.seed, live);
    auto data = bs::AllocateAligned64(pool_bytes);
    std::vector<uint64_t> masks(buckets);
    bs::TableView t{layout, buckets, data.get(), masks.data()};
    {  // per_bucket records per bucket at random slots, ids 1..live
      std::memset(t.data, 0xA5, pool_bytes);
      uint64_t rng = o.seed;
      uint64_t id = 1;
      for (size_t b = 0; b < buckets; ++b) {
        uint8_t slots[bs::kBucketCapacity];
        for (size_t i = 0; i < bs::kBucketCapacity; ++i) slots[i] = static_cast<uint8_t>(i);
        uint64_t mask = 0;
        for (size_t i = 0; i < per_bucket; ++i) {
          const size_t pick = i + SplitMix64(rng) % (bs::kBucketCapacity - i);
          std::swap(slots[i], slots[pick]);
          mask |= uint64_t{1} << slots[i];
          WriteRecord(t.Bucket(b), slots[i], keys.Key(id++), sl);
        }
        t.masks[b] = mask;
      }
    }
    // Random routing tags: bit 0 picks the direction, the rest is filler.
    uint64_t rng = o.seed ^ 0xB5297A4D3F84D5B5ull;
    for (size_t b = 0; b < buckets; ++b) {
      for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
        uint8_t* line = t.Bucket(b) + (layout.TagOffset() + tb) * bs::kBucketCapacity;
        for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
          line[slot] = static_cast<uint8_t>(SplitMix64(rng));
        }
      }
    }
    auto pristine = bs::AllocateAligned64(pool_bytes);
    std::vector<uint64_t> pristine_masks(masks);
    std::memcpy(pristine.get(), data.get(), pool_bytes);
    const auto restore = [&] {
      std::memcpy(data.get(), pristine.get(), pool_bytes);
      std::memcpy(masks.data(), pristine_masks.data(), buckets * sizeof(uint64_t));
    };
    StashSet stash(1, o.stash_buckets, layout);

    for (const Arm arm : arms) {
      size_t failed = 0, shed = 0, remaining = o.pairs;
      double seconds = 0, restore_seconds = 0;
      std::string why;
      std::vector<uint8_t> pair_failed(pool, 0);
      WithKernel(arm, o.check_overflow, [&](auto kernel) {
        const auto chunk = [&](size_t n, size_t* nfailed, uint8_t* per_pair) {
          const auto start = Clock::now();
          for (size_t i = 0; i < n; ++i) {
            const bool ok = kernel(t.Bucket(2 * i), t.Bucket(2 * i + 1),
                                   &masks[2 * i], &masks[2 * i + 1], lines,
                                   tag_line, stash.stashes[0]);
            *nfailed += !ok;
            if (per_pair) per_pair[i] = !ok;
          }
          return SecondsSince(start);
        };
        restore();
        stash.Reset();
        chunk(pool, &failed, nullptr);  // warm-up chunk, untimed
        failed = 0;
        bool first = true;
        while (remaining > 0) {
          const size_t n = PairChunkSize(pool, remaining);
          const auto r0 = Clock::now();
          restore();
          restore_seconds += SecondsSince(r0);
          stash.Reset();
          seconds += chunk(n, &failed, first ? pair_failed.data() : nullptr);
          shed += stash.Count();
          if (first) {
            first = false;
            why = VerifyPairChunk(t, sl, keys, n, per_bucket, tag_line,
                                  stash.stashes[0], pair_failed);
          }
          remaining -= n;
        }
      });
      const char* status = failed ? "overflow" : why.empty() ? "ok" : "verify_failed";
      head(arm);
      if (failed == 0) {
        std::printf(
            "\"ns_per_merge_split\":%.4f,\"ns_per_input_record\":%.4f,"
            "\"merge_splits_per_second\":%.1f,",
            seconds * 1e9 / o.pairs, seconds * 1e9 / (o.pairs * 2.0 * per_bucket),
            o.pairs / seconds);
      }
      std::printf(
          "\"total_ms\":%.3f,\"restore_ms_excluded\":%.3f,\"shed\":%zu,"
          "\"overflow_calls\":%zu,\"status\":\"%s\",\"seed\":%llu,\"threads\":1",
          seconds * 1e3, restore_seconds * 1e3, shed, failed, status,
          static_cast<unsigned long long>(o.seed));
      if (!why.empty()) std::printf(",\"note\":\"%s\"", why.c_str());
      std::printf("}\n");
      if (!(status[0] == 'o' && status[1] == 'k')) exit_code = 1;
    }
  }
  // slot512 has its own buckets, pools and verification.
  if (want("slot512")) exit_code |= RunPairRows512(o);
  return exit_code;
}

// ---------------------------------------------------------------------------
// 512-slot rows: the slot512 pair arm and the butterfly512 network
// ---------------------------------------------------------------------------
//
// Buckets of 512 slots at load 0.5 (256 records), merge-split with
// benchmarks/oram/cpu_byteslice_slot512_kernel.hpp.  There is no residual
// stash at this size: a surplus is an overflow (the call fails before touching
// anything), so rows report "stash":"none" and shed 0.  The same entry layout
// (key, value, meta, tags), key generator, record check and tag source as the
// 64-slot rows; only the byte line is 512 bytes.

namespace s5 = microram::byteslice::slot512;

// `per` records at random slots of a 512-slot bucket, ids from *id.
void FillBucket512(uint8_t* bucket, uint64_t* mask, size_t per, uint64_t* id,
                   const KeyGen& keys, const bs::StashLayout& sl, uint64_t& rng) {
  std::vector<uint16_t> slots(s5::kSlots);
  for (size_t i = 0; i < s5::kSlots; ++i) slots[i] = static_cast<uint16_t>(i);
  std::memset(mask, 0, s5::kWords * sizeof(uint64_t));
  for (size_t i = 0; i < per; ++i) {
    std::swap(slots[i], slots[i + SplitMix64(rng) % (s5::kSlots - i)]);
    const size_t slot = slots[i];
    mask[slot / 64] |= uint64_t{1} << (slot % 64);
    WriteRecord(bucket, slot, keys.Key((*id)++), sl, s5::kSlots);
  }
}

// Verification of a group of 512-slot pairs after pair merge-splits (tag bit 0):
// every record exactly once, key and value intact, on the side its tag bit
// selects.  A failed (overflow) pair was left unmodified, so only its record
// accounting is checked.
std::string VerifyPairChunk512(const uint8_t* data, const uint64_t* masks,
                               size_t bucket_bytes, const bs::StashLayout& sl,
                               const KeyGen& keys, size_t pairs, size_t per_bucket,
                               size_t tag_line, const std::vector<uint8_t>& pair_failed) {
  const uint64_t live = uint64_t{pairs} * 2 * per_bucket;
  std::vector<uint64_t> seen(live / 64 + 1, 0);
  size_t total = 0;
  for (size_t i = 0; i < pairs; ++i) {
    for (size_t k = 0; k < 2; ++k) {
      const size_t b = 2 * i + k;
      const uint8_t* bucket = data + b * bucket_bytes;
      for (size_t slot = 0; slot < s5::kSlots; ++slot) {
        if (!((masks[b * s5::kWords + slot / 64] >> (slot % 64)) & 1)) continue;
        const uint64_t key = ReadKeyAt(bucket, slot, sl.key_bytes, s5::kSlots);
        const uint64_t id = keys.Index(key);
        if (id < 1 || id > live) return "key is not an input record";
        if ((seen[id / 64] >> (id % 64)) & 1) return "record duplicated";
        if (!ValueIntact(bucket, slot, key, sl, s5::kSlots)) return "value corrupted";
        seen[id / 64] |= uint64_t{1} << (id % 64);
        ++total;
        if (!pair_failed[i] &&
            (bucket[tag_line * s5::kSlots + slot] & 1) != k) {
          return "record in the wrong direction";
        }
      }
    }
  }
  if (total != live) return "records lost in a pair";
  return "";
}

// N independent 512-slot merge-splits (tag bit 0), on the two byte pools, in
// the pair rows' format.  load_per_bucket is per 64 slots, so a bucket holds
// 8x as many records (load 0.5 by default).
int RunPairRows512(const Options& o) {
  bs::StashLayout sl;
  sl.key_bytes = o.key_bytes;
  sl.value_bytes = o.value_bytes;
  const bs::Layout layout = sl.Base();
  const size_t bucket_bytes = layout.EntryBytes() * s5::kSlots;
  const size_t lines = layout.RoutedLines(0);
  const size_t tag_line = layout.TagLine(0);
  const size_t per_bucket = o.load_per_bucket * (s5::kSlots / bs::kBucketCapacity);

  struct PoolSpec { const char* label; size_t bytes; };
  std::vector<PoolSpec> pools;
  if (o.pool_bytes > 0) {
    pools.push_back({"custom", o.pool_bytes});
  } else {
    pools.push_back({"cache_resident", size_t{2621440}});
    pools.push_back({"dram_streaming", size_t{41943040}});
  }
  int exit_code = 0;
  for (const PoolSpec& ps : pools) {
    const size_t pool = std::min(
        std::max<size_t>(1, ps.bytes / (2 * bucket_bytes)), o.pairs);
    const size_t buckets = 2 * pool;
    const size_t pool_bytes = buckets * bucket_bytes;
    const uint64_t need = 2 * (uint64_t{pool_bytes} + buckets * s5::kWords * 8);
    const auto head = [&] {
      std::printf(
          "{\"mode\":\"pairs\",\"arm\":\"slot512\",\"pool\":\"%s\","
          "\"pool_bytes\":%zu,\"requested_pool_bytes\":%zu,\"pool_pairs\":%zu,\"key_bytes\":%zu,"
          "\"value_bytes\":%zu,\"entry_bytes\":%zu,\"pairs\":%zu,"
          "\"bucket_slots\":512,\"slots_per_merge_split\":1024,"
          "\"real_records_per_merge_split\":%zu,\"routed_lines\":%zu,"
          "\"stash\":\"none\",",
          ps.label, pool_bytes, ps.bytes, pool, o.key_bytes, o.value_bytes,
          layout.EntryBytes(), o.pairs, 2 * per_bucket, lines);
    };
    if (!PairPoolUsable(pool, o.pairs)) {
      head();
      std::printf("\"status\":\"skipped_timing_granularity\",\"note\":\"pool/count cannot form chunks of at least two calls\"}\n");
      exit_code = 1;
      continue;
    }
    if (need > o.max_bytes) {
      std::printf("{\"mode\":\"pairs\",\"arm\":\"slot512\",\"pool\":\"%s\","
                  "\"status\":\"skipped_memory\"}\n", ps.label);
      exit_code = 1;
      continue;
    }
    const uint64_t live = uint64_t{buckets} * per_bucket;
    const KeyGen keys(o.key_bytes, o.seed, live);
    auto data = bs::AllocateAligned64(pool_bytes);
    std::vector<uint64_t> masks(buckets * s5::kWords);
    std::memset(data.get(), 0xA5, pool_bytes);
    uint64_t rng = o.seed, id = 1;
    for (size_t b = 0; b < buckets; ++b) {
      FillBucket512(data.get() + b * bucket_bytes, &masks[b * s5::kWords],
                    per_bucket, &id, keys, sl, rng);
    }
    uint64_t trng = o.seed ^ 0xB5297A4D3F84D5B5ull;
    for (size_t b = 0; b < buckets; ++b) {
      for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
        uint8_t* line = data.get() + b * bucket_bytes +
                        (layout.TagOffset() + tb) * s5::kSlots;
        for (size_t slot = 0; slot < s5::kSlots; ++slot) {
          line[slot] = static_cast<uint8_t>(SplitMix64(trng));
        }
      }
    }
    auto pristine = bs::AllocateAligned64(pool_bytes);
    std::vector<uint64_t> pristine_masks(masks);
    std::memcpy(pristine.get(), data.get(), pool_bytes);
    const auto restore = [&] {
      std::memcpy(data.get(), pristine.get(), pool_bytes);
      std::memcpy(masks.data(), pristine_masks.data(), masks.size() * 8);
    };
    size_t failed = 0, remaining = o.pairs;
    double seconds = 0, restore_seconds = 0;
    std::string why;
    std::vector<uint8_t> pair_failed(pool, 0);
    const auto chunk = [&](size_t n, size_t* nfailed, uint8_t* per_pair) {
      const auto start = Clock::now();
      for (size_t i = 0; i < n; ++i) {
        const bool ok = s5::MergeSplit(
            data.get() + 2 * i * bucket_bytes, data.get() + (2 * i + 1) * bucket_bytes,
            &masks[2 * i * s5::kWords], &masks[(2 * i + 1) * s5::kWords], lines,
            tag_line, 0);
        *nfailed += !ok;
        if (per_pair) per_pair[i] = !ok;
      }
      return SecondsSince(start);
    };
    restore();
    chunk(pool, &failed, nullptr);  // warm-up chunk, untimed
    failed = 0;
    bool first = true;
    while (remaining > 0) {
      const size_t n = PairChunkSize(pool, remaining);
      const auto r0 = Clock::now();
      restore();
      restore_seconds += SecondsSince(r0);
      seconds += chunk(n, &failed, first ? pair_failed.data() : nullptr);
      if (first) {
        first = false;
        why = VerifyPairChunk512(data.get(), masks.data(), bucket_bytes, sl, keys, n,
                                 per_bucket, tag_line, pair_failed);
      }
      remaining -= n;
    }
    const char* status = failed ? "overflow" : why.empty() ? "ok" : "verify_failed";
    head();
    if (failed == 0) {
      std::printf(
          "\"ns_per_merge_split\":%.4f,\"ns_per_input_record\":%.4f,"
          "\"merge_splits_per_second\":%.1f,",
          seconds * 1e9 / o.pairs, seconds * 1e9 / (o.pairs * 2.0 * per_bucket),
          o.pairs / seconds);
    }
    std::printf(
        "\"total_ms\":%.3f,\"restore_ms_excluded\":%.3f,\"shed\":0,"
        "\"overflow_calls\":%zu,\"status\":\"%s\",\"seed\":%llu,\"threads\":1",
        seconds * 1e3, restore_seconds * 1e3, failed, status,
        static_cast<unsigned long long>(o.seed));
    if (!why.empty()) std::printf(",\"note\":\"%s\"", why.c_str());
    std::printf("}\n");
    if (!(status[0] == 'o' && status[1] == 'k')) exit_code = 1;
  }
  return exit_code;
}

// The standard stage-major butterfly (as `flat`) on 512-slot buckets: live/256
// buckets at load 0.5, one 512-slot merge-split per bucket pair per level, no
// stash, no deduplication, no residual handling: a surplus fails the row.  The
// tags are the same AES tags as the 64-slot rows, written outside the timer.
int RunButterfly512(const Options& o) {
  const size_t buckets = o.live_entries / (s5::kSlots / 2);
  const unsigned levels = bs::Log2Exact(buckets);
  bs::StashLayout sl;
  sl.key_bytes = o.key_bytes;
  sl.value_bytes = o.value_bytes;
  const bs::Layout layout = sl.Base();
  const size_t bucket_bytes = layout.EntryBytes() * s5::kSlots;
  const size_t data_bytes = buckets * bucket_bytes;
  RowFields row{"butterfly512", o.key_bytes, o.value_bytes, layout.EntryBytes(),
                o.live_entries, buckets, levels, 0, 1, o.seed, s5::kSlots};
  if (o.live_entries % (s5::kSlots / 2) != 0 || buckets < 2 ||
      (buckets & (buckets - 1)) != 0 || levels > 8 * layout.tag_bytes) {
    PrintRoutingRow(row, "unsupported_size", false, 0, 0,
                    "--live-entries must be 256 * a power of two >= 2");
    return 1;
  }
  if (o.threads > 1) {
    PrintRoutingRow(row, "unsupported_threads", false, 0, 0,
                    "butterfly512 runs on one thread");
    return 1;
  }
  const uint64_t need = 2 * (uint64_t{data_bytes} + buckets * s5::kWords * 8);
  if (need > o.max_bytes) {
    std::fprintf(stderr, "skipped: data + pristine buffers need %.2f GiB > --max-bytes %.2f GiB\n",
                 need / 1073741824.0, o.max_bytes / 1073741824.0);
    PrintRoutingRow(row, "skipped_memory", false, 0, 0, "");
    return 1;
  }
  const KeyGen keys(o.key_bytes, o.seed, o.live_entries);
  const uint64_t nonce_lo = 42 ^ o.seed, nonce_hi = 7;
  auto data = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> masks(buckets * s5::kWords);
  std::memset(data.get(), 0xA5, data_bytes);
  uint64_t rng = o.seed, id = 1;
  for (size_t b = 0; b < buckets; ++b) {
    FillBucket512(data.get() + b * bucket_bytes, &masks[b * s5::kWords],
                  s5::kSlots / 2, &id, keys, sl, rng);
  }
  // Routing tags: tag byte tb holds bits [8 tb, 8 tb + 8), stored at line
  // TagOffset + tag_bytes - 1 - tb (Layout::TagLine).
  for (size_t b = 0; b < buckets; ++b) {
    uint8_t* bucket = data.get() + b * bucket_bytes;
    for (size_t slot = 0; slot < s5::kSlots; ++slot) {
      if (!((masks[b * s5::kWords + slot / 64] >> (slot % 64)) & 1)) continue;
      const uint64_t key = ReadKeyAt(bucket, slot, sl.key_bytes, s5::kSlots);
      const uint64_t tag = microram::crypto::AesCtrTagU64WordsHost(nonce_lo, nonce_hi, key);
      for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
        bucket[(layout.TagOffset() + layout.tag_bytes - 1 - tb) * s5::kSlots + slot] =
            static_cast<uint8_t>(tag >> (8 * tb));
      }
    }
  }
  auto pristine = bs::AllocateAligned64(data_bytes);
  std::vector<uint64_t> pristine_masks(masks);
  std::memcpy(pristine.get(), data.get(), data_bytes);
  const auto restore = [&] {
    std::memcpy(data.get(), pristine.get(), data_bytes);
    std::memcpy(masks.data(), pristine_masks.data(), masks.size() * 8);
  };
  const auto route = [&]() -> bool {
    for (unsigned bit = 0; bit < levels; ++bit) {
      const size_t lines = layout.RoutedLines(bit);
      const size_t tag_line = layout.TagLine(bit);
      for (size_t i = 0; i < buckets; ++i) {
        if ((i >> bit) & 1) continue;
        const size_t j = i | (size_t{1} << bit);
        if (!s5::MergeSplit(data.get() + i * bucket_bytes, data.get() + j * bucket_bytes,
                            &masks[i * s5::kWords], &masks[j * s5::kWords], lines,
                            tag_line, bit)) {
          return false;
        }
      }
    }
    return true;
  };
  bool overflowed = false;
  const PhaseTime time = Measure(static_cast<int>(o.reps), [&] {
    restore();
    const auto start = Clock::now();
    const bool ok = route();
    const double seconds = SecondsSince(start);
    overflowed |= !ok;
    return seconds;
  });
  row.reps = static_cast<size_t>(time.reps);
  if (overflowed) {
    PrintRoutingRow(row, "overflow", false, 0, 0, "");
    return 1;
  }
  std::string why;
  if (o.verify) {
    std::vector<uint64_t> seen(o.live_entries / 64 + 1, 0);
    size_t total = 0;
    for (size_t b = 0; b < buckets && why.empty(); ++b) {
      const uint8_t* bucket = data.get() + b * bucket_bytes;
      for (size_t slot = 0; slot < s5::kSlots; ++slot) {
        if (!((masks[b * s5::kWords + slot / 64] >> (slot % 64)) & 1)) continue;
        const uint64_t key = ReadKeyAt(bucket, slot, sl.key_bytes, s5::kSlots);
        const uint64_t rid = keys.Index(key);
        if (rid < 1 || rid > o.live_entries) { why = "key is not an input record"; break; }
        if ((seen[rid / 64] >> (rid % 64)) & 1) { why = "record duplicated"; break; }
        seen[rid / 64] |= uint64_t{1} << (rid % 64);
        if (!ValueIntact(bucket, slot, key, sl, s5::kSlots)) { why = "value corrupted"; break; }
        const uint64_t tag = microram::crypto::AesCtrTagU64WordsHost(nonce_lo, nonce_hi, key);
        if ((tag & (buckets - 1)) != b) { why = "entry in the wrong bucket"; break; }
        ++total;
      }
    }
    if (why.empty() && total != o.live_entries) why = "records lost (kernel bug)";
  }
  if (!why.empty()) {
    PrintRoutingRow(row, "verify_failed", false, 0, 0, why.c_str());
    return 1;
  }
  PrintRoutingRow(row, "ok", true, time.seconds_per_rep, 0, o.verify ? "" : "unverified");
  return 0;
}

// Returns -1 on success, else the exit code.
int ParseFlags(int argc, char** argv, Options* o) {
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    std::string value;
    const size_t eq = arg.find('=');
    if (eq != std::string::npos) {
      value = arg.substr(eq + 1);
      arg.resize(eq);
    } else if (i + 1 < argc) {
      value = argv[i + 1];
    }
    const auto need_value = [&] {
      if (eq == std::string::npos) ++i;
    };
    const auto num = [&](const char* name) -> uint64_t {
      char* end = nullptr;
      const unsigned long long v = std::strtoull(value.c_str(), &end, 0);
      if (value.empty() || *end != 0) {
        std::fprintf(stderr, "bad value for %s: '%s'\n", name, value.c_str());
        std::exit(2);
      }
      return v;
    };
    if (arg == "--network") {
      need_value();
      size_t pos = 0;
      while (pos <= value.size()) {
        size_t comma = value.find(',', pos);
        if (comma == std::string::npos) comma = value.size();
        const std::string name = value.substr(pos, comma - pos);
        if (name != "flat" && name != "grouped6" && name != "cache_oblivious" &&
            name != "grouped6_unfused" && name != "cache_oblivious_unfused" &&
            name != "butterfly512") {
          std::fprintf(stderr, "unknown network '%s'\n", name.c_str());
          return 2;
        }
        o->networks.push_back(name);
        pos = comma + 1;
      }
    } else if (arg == "--key-bytes") { need_value(); o->key_bytes = num("--key-bytes");
    } else if (arg == "--value-bytes") { need_value(); o->value_bytes = num("--value-bytes");
    } else if (arg == "--live-entries") { need_value(); o->live_entries = num("--live-entries");
    } else if (arg == "--seed") { need_value(); o->seed = num("--seed");
    } else if (arg == "--reps") { need_value(); o->reps = num("--reps");
    } else if (arg == "--stash-buckets") { need_value(); o->stash_buckets = num("--stash-buckets");
    } else if (arg == "--threads") { need_value(); o->threads = static_cast<unsigned>(num("--threads"));
    } else if (arg == "--instances") { need_value(); o->instances = static_cast<unsigned>(num("--instances"));
    } else if (arg == "--cpus") {
      need_value();
      o->cpus = ParseCpuList(value);
      o->cpus_text = value;
      if (o->cpus.empty()) {
        std::fprintf(stderr, "bad --cpus list '%s'\n", value.c_str());
        return 2;
      }
    } else if (arg == "--pairs") { need_value(); o->pairs = num("--pairs");
    } else if (arg == "--pool-bytes") { need_value(); o->pool_bytes = num("--pool-bytes");
    } else if (arg == "--load-per-bucket") { need_value(); o->load_per_bucket = num("--load-per-bucket");
    } else if (arg == "--arm") { need_value(); o->arm = value;
    } else if (arg == "--max-bytes") { need_value(); o->max_bytes = num("--max-bytes");
    } else if (arg == "--check-overflow") { need_value(); o->check_overflow = num("--check-overflow") != 0;
    } else if (arg == "--verify") { need_value(); o->verify = num("--verify") != 0;
    } else {
      std::fprintf(stderr, "unknown flag '%s'\n", arg.c_str());
      return 2;
    }
  }
  if (o->networks.empty()) o->networks = {"flat", "grouped6", "cache_oblivious"};
  if (o->key_bytes != 4 && o->key_bytes != 8) {
    std::fprintf(stderr, "--key-bytes must be 4 or 8\n");
    return 2;
  }
  if (o->stash_buckets < 1 || o->stash_buckets > bs::kMaxResidualStashBuckets) {
    std::fprintf(stderr, "--stash-buckets must be in [1, %zu]\n",
                 bs::kMaxResidualStashBuckets);
    return 2;
  }
  if (o->threads < 1 || o->reps < 1) {
    std::fprintf(stderr, "--threads and --reps must be >= 1\n");
    return 2;
  }
  if (o->instances > 0) {
    if (o->threads > 1 || o->pairs > 0 ||
        std::find(o->networks.begin(), o->networks.end(), "butterfly512") !=
            o->networks.end()) {
      std::fprintf(stderr, "--instances takes neither --threads, --pairs nor butterfly512\n");
      return 2;
    }
    if (!o->cpus.empty() && o->cpus.size() < o->instances) {
      std::fprintf(stderr, "--cpus names fewer CPUs than --instances\n");
      return 2;
    }
  } else if (!o->cpus.empty()) {
    std::fprintf(stderr, "--cpus needs --instances\n");
    return 2;
  }
  if (o->arm != "all" && o->arm != "current" && o->arm != "compress_expand" &&
      o->arm != "bitonic" && o->arm != "slot512") {
    std::fprintf(stderr, "--arm must be current|compress_expand|bitonic|slot512|all\n");
    return 2;
  }
  if (o->load_per_bucket < 1 || o->load_per_bucket > bs::kBucketCapacity) {
    std::fprintf(stderr, "--load-per-bucket must be in [1, 64]\n");
    return 2;
  }
  if (o->pairs == 0) {
    const size_t buckets = o->live_entries / bs::kStashTargetRealPerBucket;
    if (o->live_entries % bs::kStashTargetRealPerBucket != 0 || buckets < 2 ||
        (buckets & (buckets - 1)) != 0 || bs::Log2Exact(buckets) > 32) {
      std::fprintf(stderr,
                   "--live-entries must be 32 * a power of two >= 2 (load "
                   "0.5), at most 32-level tags\n");
      return 2;
    }
  }
  if (o->live_entries >= 0xFFFFFFF0ull && o->key_bytes == 4) {
    std::fprintf(stderr, "K4 keys cannot be unique for >= 2^32 live entries\n");
    return 2;
  }
  return -1;
}

}  // namespace

int main(int argc, char** argv) {
  std::setvbuf(stdout, nullptr, _IOLBF, 0);  // retain completed rows on interruption
  bool flags = false;
  for (int i = 1; i < argc; ++i) flags |= std::strncmp(argv[i], "--", 2) == 0;
  if (flags) {
    Options o;
    const int rc = ParseFlags(argc, argv, &o);
    if (rc >= 0) return rc;
    if (o.pairs > 0) return RunPairRows(o);
    if (o.instances > 0) return RunInstanceRows(o);
    // butterfly512 has its own table (512-slot buckets); the rest share one.
    int rc512 = 0;
    const auto it = std::find(o.networks.begin(), o.networks.end(), "butterfly512");
    if (it != o.networks.end()) {
      o.networks.erase(it);
      rc512 = RunButterfly512(o);
    }
    return std::max(rc512, o.networks.empty() ? 0 : RunRoutingRows(o));
  }
  unsigned min_log2 = 6;
  unsigned max_log2 = 20;
  unsigned radix = 3;
  size_t stash_buckets = 1;
  bs::StashLayout layout;  // 8 key + 16 value + 1 meta + 4 tag = 29 B
  if (argc > 1) min_log2 = static_cast<unsigned>(std::atoi(argv[1]));
  if (argc > 2) max_log2 = static_cast<unsigned>(std::atoi(argv[2]));
  if (argc > 3) radix = static_cast<unsigned>(std::atoi(argv[3]));
  if (argc > 4) layout.value_bytes = static_cast<size_t>(std::atoi(argv[4]));
  if (argc > 5) stash_buckets = static_cast<size_t>(std::atoi(argv[5]));
  if (stash_buckets < 1 || stash_buckets > bs::kMaxResidualStashBuckets) {
    std::fprintf(stderr, "stash_buckets must be in [1, %zu]\n",
                 bs::kMaxResidualStashBuckets);
    return 1;
  }

  std::printf(
      "cpu_byteslice_stash_rebuild: %zuB entry (%zu byte lines), bucket=64, "
      "load=0.5, stash=%zu bucket(s)/level, single core\n",
      layout.EntryBytes(), layout.Base().EntryBytes(), stash_buckets);
  std::printf(
      "%8s %9s | %8s %6s | %8s %6s %6s | %5s\n"
      "%8s %9s | %8s %6s | %8s %6s %6s | %5s\n",
      "buckets", "MiB", "group ms", "ns/ln", "cobl ms", "ns/ln", "ns/e/l",
      "shed",
      "", "", "(g=6)", "", "(recurse)", "", "", "");
  for (unsigned lg = min_log2; lg <= max_log2; lg += 2) {
    if (RunScale(lg, radix, stash_buckets, layout) != 0) return 1;
  }
  return 0;
}
