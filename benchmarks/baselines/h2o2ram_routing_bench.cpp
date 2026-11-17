// A matched comparator for our stash rebuild's routing: H2O2RAM's bucket
// placement in isolation.
// Calls the released OHashBucket::build (two bitonic sorts over N + 64*B
// pairs) on a table of B = N/32 buckets of 64 slots (load 0.5), the shape of
// cpu_byteslice_stash_rebuild_benchmark's rows. Timer covers build() only
// (PRF tagging, dummy padding, sort, cap scan, sort, copy-out). Input and the
// post-build check (every id found in its bucket; shortfall = overflow loss)
// are outside the timer. One JSON line per invocation and instance.
//   h2o2ram_routing_bench --key-bytes 4|8 --value-bytes 8|16|48|64|256|1024|4096
//       --live-entries N --threads T --reps R --seed S --bucket-slots 64|128
//       [--merge 0|1] [--planned 0|1] [--cpu LIST]
// --merge 1 builds the table from two tables of N/2 records each, as
// H2O2RAM's rebuild does from its lower levels (oram.hpp): the timer also
// covers both halves' extract() (one bitonic sort each) and the copy into one
// input array; the halves' builds and that array's allocation are outside.
// Their ids are disjoint: H2O2RAM never merges copies of a key (an access
// turns the entry it finds into a dummy).
// --planned 1 (8-byte ids) builds what H2O2RAM's ORAM builds for a level of N
// blocks: ObliviousBin(N, N), whose table type (linear scan, bucket, cuckoo or
// two-tier) and shape come from H2O2RAM's planner cache, hash_map.bin<block
// bytes> beside this executable.  A missing entry is an error, never a
// planner run.  Rows name the cache line used.  Some builds shuffle their
// input, so each repetition builds from a copy.
// --cpu LIST runs one identical instance per listed CPU, side by side
// (benchmarks/support/parallel_instances.hpp); every timed build starts
// together, and instance 0's clock decides when to stop repeating.
// seed controls input values only: the released build resets its AES PRF
// with RAND_bytes inside the timer. No source patch changes that behavior.
#include <omp.h>
#include <tbb/global_control.h>
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#include "timer.hpp"  // ohash_bucket.hpp is not self-contained (Timer, osorter)
#include "oshuffle.hpp"
#include "ohash_bucket.hpp"
#include "ohash_bin.hpp"
#include "hash_planner.hpp"  // determine_hash: the planner cache
#include "benchmarks/support/parallel_instances.hpp"

using benchmark_support::ParallelInstances;

template <typename K, size_t V, class Table, class Make>
int Run(ParallelInstances& group, uint64_t n, unsigned reps, uint64_t seed, bool merge,
        const std::string& shape, Make make) {
  using Blk = ORAM::Block<K, sizeof(K) + V>;
  std::vector<Blk> data(n);
  uint64_t x = seed * 0x9E3779B97F4A7C15ull + 1;
  for (uint64_t i = 0; i < n; ++i) {  // distinct ids, value bytes random
    data[i].id = static_cast<K>(i);
    for (size_t j = 0; j < V; ++j) { x = x * 6364136223846793005ull + 1442695040888963407ull; data[i].value[j] = x >> 56; }
  }
  std::vector<Blk> work(n);   // a build's input, which it may permute
  std::vector<Blk> input(merge ? n : 0);  // the halves' records, one array
  std::vector<double> ms;
  uint64_t lost = 0;
  const auto t_end = std::chrono::steady_clock::now() + std::chrono::milliseconds(300);
  for (unsigned r = 0; group.Sync(r < reps && (r < 2 || std::chrono::steady_clock::now() < t_end)); ++r) {
    std::unique_ptr<Table> table = make(n);
    std::unique_ptr<Table> halves[2];
    work = data;
    for (int h = 0; merge && h < 2; ++h) {
      halves[h] = make(n / 2);
      halves[h]->build(work.data() + h * (n / 2));
    }
    group.Sync();
    auto t0 = std::chrono::steady_clock::now();
    if (merge) {
      for (int h = 0; h < 2; ++h) {
        auto& records = halves[h]->extract();
        std::copy(records.begin(), records.end(), input.begin() + h * (n / 2));
      }
      table->build(input.data());
    } else {
      table->build(work.data());
    }
    ms.push_back(std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count());
    if (r == 0) {  // outside the timer: every id must be found with its value
      uint64_t found = 0, bad = 0;
      for (uint64_t i = 0; i < n; ++i) {
        Blk b = (*table)[static_cast<K>(i)];
        if (b.id == static_cast<K>(i)) { ++found; bad += std::memcmp(b.value, data[i].value, V) != 0; }
      }
      lost = n - found;
      if (bad) { std::fprintf(stderr, "value mismatch %lu\n", (unsigned long)bad); return 2; }
    }
  }
  std::string samples;  // in run order, before sorting
  for (size_t i = 0; i < ms.size(); ++i) samples += (i ? "," : "") + std::to_string(ms[i]);
  std::sort(ms.begin(), ms.end());
  group.InTurn([&] {
    std::printf("{\"driver\":\"h2o2ram_ohashbucket_build\",\"mode\":\"%s\",\"key_bytes\":%zu,\"value_bytes\":%zu,\"live\":%lu,"
                "%s,\"block_bytes\":%zu,\"threads\":%d,\"instance\":%u,\"instances\":%u,"
                "\"cpu\":%d,\"reps\":%zu,\"median_ms\":%.4f,\"min_ms\":%.4f,\"max_ms\":%.4f,\"samples_ms\":[%s],\"ns_per_live\":%.2f,"
                "\"lost_to_overflow\":%lu,\"input_seed\":%lu,\"routing_seed\":\"openssl_random\","
                "\"includes_tagging\":true,\"includes_extract\":%s}\n",
                merge ? "merge" : "build", sizeof(K), V, (unsigned long)n, shape.c_str(), sizeof(Blk),
                omp_get_max_threads(), group.index(), group.count(),
                group.cpu(), ms.size(), ms[ms.size() / 2], ms[0], ms.back(), samples.c_str(), ms[ms.size() / 2] * 1e6 / n,
                (unsigned long)lost, (unsigned long)seed, merge ? "true" : "false");
  });
  return lost ? 3 : 0;
}

// The planner cache's line for a level of `entries` blocks ("bucket 6622 301"),
// or "missing".
template <size_t kBlock>
std::string PlannedLine(uint64_t entries) {
  std::ifstream cache(ORAM::getExecutablePath() + CONFIG_FILE + std::to_string(kBlock));
  std::string line;
  while (std::getline(cache, line)) {
    std::istringstream in(line);
    uint64_t n = 0, ops = 0, delta = 0;
    std::string rest;
    if (in >> n >> ops >> delta && n == entries && ops == entries && delta == DELTA_INV_LOG2) {
      std::getline(in >> std::ws, rest);
      return rest;
    }
  }
  return "missing";
}

template <typename K, size_t V>
int RunWidth(ParallelInstances& group, uint64_t n, unsigned reps, uint64_t seed, size_t slots, bool merge,
             bool planned) {
  constexpr size_t kBlock = sizeof(K) + V;
  if (planned) {
    if constexpr (sizeof(K) == 8) {  // H2O2RAM's ORAM indexes blocks by 64-bit ids
      using Table = ORAM::ObliviousBin<K, kBlock>;
      std::string shape = "\"table\":\"planned\",\"planned\":\"" + PlannedLine<kBlock>(n) + "\"";
      if (merge) shape += ",\"halves_planned\":\"" + PlannedLine<kBlock>(n / 2) + "\"";
      return Run<K, V, Table>(group, n, reps, seed, merge, shape, [](uint64_t entries) {
        return std::make_unique<Table>(K(entries), K(entries), K(DELTA_INV_LOG2));
      });
    }
    std::fprintf(stderr, "--planned takes --key-bytes 8 (H2O2RAM's 64-bit block ids)\n");
    return 2;
  }
  using Table = ORAM::OHashBucket<K, kBlock>;
  return Run<K, V, Table>(group, n, reps, seed, merge,
                          "\"table\":\"bucket\",\"buckets\":" + std::to_string(n / 32) + ",\"slots\":" +
                              std::to_string(slots) + ",\"stash\":\"none\"",
                          [slots](uint64_t entries) {
                            return std::make_unique<Table>(K(entries), K(entries / 32), K(slots));
                          });
}

int main(int argc, char** argv) {
  size_t kb = 8, vb = 16, threads = 1, reps = 200, slots = 64;
  uint64_t n = 1u << 20, seed = 1;
  bool merge = false, planned = false;
  std::string cpus;
  if (argc % 2 != 1) { std::fprintf(stderr, "each option needs a value\n"); return 2; }
  for (int i = 1; i + 1 < argc; i += 2) {
    const std::string a = argv[i];
    const uint64_t v = std::strtoull(argv[i + 1], nullptr, 10);
    if (a == "--key-bytes") kb = v; else if (a == "--value-bytes") vb = v; else if (a == "--live-entries") n = v;
    else if (a == "--threads") threads = v; else if (a == "--reps") reps = v; else if (a == "--seed") seed = v;
    else if (a == "--bucket-slots") slots = v; else if (a == "--merge") merge = v != 0;
    else if (a == "--planned") planned = v != 0;
    else if (a == "--cpu") cpus = argv[i + 1];
    else { std::fprintf(stderr, "unknown %s\n", a.c_str()); return 1; }
  }
  if (n < 64 || (n & (n - 1)) || (kb == 4 && n >= (uint64_t{1} << 31))) {
    std::fprintf(stderr, "live-entries: power of two >= 64; K4 ids must leave the dummy bit clear\n"); return 2;
  }
  if (!threads || !reps || (slots != 64 && slots != 128)) {
    std::fprintf(stderr, "threads/reps must be positive; bucket-slots must be 64 or 128\n"); return 2;
  }
  // Each instance starts its own TBB and OpenMP runtimes after the fork.
  return ParallelInstances::Run(ParallelInstances::ParseCpus(cpus), [&](ParallelInstances& group) {
    tbb::global_control control(tbb::global_control::max_allowed_parallelism, threads);
    omp_set_num_threads(static_cast<int>(threads));
#define ROUTING_WIDTH(K, V) if (kb == sizeof(K) && vb == V) return RunWidth<K, V>(group, n, reps, seed, slots, merge, planned)
    ROUTING_WIDTH(uint32_t, 8); ROUTING_WIDTH(uint32_t, 16);
    ROUTING_WIDTH(uint32_t, 48); ROUTING_WIDTH(uint32_t, 64);
    ROUTING_WIDTH(uint32_t, 256); ROUTING_WIDTH(uint32_t, 1024); ROUTING_WIDTH(uint32_t, 4096);
    ROUTING_WIDTH(uint64_t, 8); ROUTING_WIDTH(uint64_t, 16);
    ROUTING_WIDTH(uint64_t, 48); ROUTING_WIDTH(uint64_t, 64);
    ROUTING_WIDTH(uint64_t, 256); ROUTING_WIDTH(uint64_t, 1024); ROUTING_WIDTH(uint64_t, 4096);
#undef ROUTING_WIDTH
    std::fprintf(stderr, "unsupported width\n");
    return 1;
  });
}
