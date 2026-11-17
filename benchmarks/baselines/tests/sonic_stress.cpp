// A long-running stress driver for the SONIC adapter (diagnosis of the data
// race on ZingORAM's per-tree PRNG that patch P-S1 fixes: unpatched, long runs
// can die in `EVP_EncryptInit_ex`, and ThreadSanitizer reports the race in
// `buffered_prng::random_bytes`). It builds the recursive map exactly as oram_baseline_sonic does for
// Ser (scalar) or Par8 (batch 8) rows, at a small N, then runs random windows
// for a given time, checking every read against a plain copy of the data.
// Build it plain, with -fsanitize=address or with -fsanitize=thread.
//
//   sonic_stress LOG2_N scalar|batch8 SECONDS [SEED]
#include "benchmarks/baselines/sonic_map.hpp"
#include "sonic/threads/platform/pthread_thread_pool.hpp"
#include "sonic/util/log.hpp"

#include <chrono>
#include <cstdio>
#include <cstring>
#include <random>
#include <string>

namespace {
namespace sm = oram_bench::sonic;
constexpr size_t kBytes = 8;

void Check(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error(message);
}

template <size_t W>
std::unique_ptr<sm::Tree> Tree(uint64_t blocks, const sm::TreeParams& p, uint32_t routing, unsigned access,
                               sn::threads::thread_pool& eviction, unsigned eviction_threads) {
  const auto geometry = sm::TreeGeometry(blocks, p, routing, W);
  const unsigned team = std::min<unsigned>(eviction_threads, 1u << geometry.routing);
  return std::make_unique<sm::ZingTree<W>>(blocks, p, routing, access, sn::threads::thread_team(eviction, team),
                                           sm::kMaxLanes);
}
}  // namespace

int main(int argc, char** argv) {
  if (argc < 4) {
    std::fprintf(stderr, "usage: %s LOG2_N scalar|batch8 SECONDS [SEED]\n", argv[0]);
    return 2;
  }
  sn::util::log::global_logger().set_verbosity(sn::util::log::level::critical);
  const uint64_t n = uint64_t{1} << std::stoul(argv[1]);
  const bool batch = std::string(argv[2]) == "batch8";
  const double seconds = std::stod(argv[3]);
  std::mt19937_64 rng(argc > 4 ? std::stoull(argv[4]) : 1);
  // The worker's presets: Ser (Z=8, S=12, E=1, T=1) and Par8 (Z=16, S=16, E=2, T=8); R=3, 2^R eviction threads,
  // map trees with the data tree's parameters, b=16, C=2048.
  const sm::TreeParams params = batch ? sm::TreeParams{16, 16, 0, 2} : sm::TreeParams{8, 12, 0, 1};
  const unsigned access_threads = batch ? 8 : 1, eviction_threads = 8;
  const uint32_t routing = 3;
  const unsigned branching = 16;
  const uint64_t top = 2048;
  try {
    sn::threads::thread_policy policy{};
    policy.affinity = sn::threads::thread_affinity::inherit;
    sn::threads::thread_context context(policy);
    sn::threads::pthread_thread_pool access_pool(context, access_threads - 1, "access");
    sn::threads::pthread_thread_pool eviction_pool(context, eviction_threads - 1, "evict");
    sn::threads::thread_team access(access_pool.pool(), access_threads);
    std::vector<std::unique_ptr<sm::Tree>> maps;
    uint64_t blocks = n;
    const unsigned levels = sm::MapLevels(n, branching, top);
    for (unsigned level = 1; level <= levels; ++level) {
      blocks = (blocks + branching - 1) / branching;
      maps.push_back(Tree<4 * branching>(blocks, params, routing, access_threads, eviction_pool.pool(),
                                         eviction_threads));
    }
    sm::EngineConfig config{n, kBytes, true, branching, top};
    sm::Engine engine(config, Tree<kBytes>(n, params, routing, access_threads, eviction_pool.pool(), eviction_threads),
                      std::move(maps), access_threads > 1 ? &access : nullptr);
    std::vector<uint64_t> reference(n, 0);
    alignas(64) uint8_t values[sm::kMaxLanes * kBytes] = {}, results[sm::kMaxLanes * kBytes] = {};
    const auto begin = std::chrono::steady_clock::now();
    auto elapsed = [&] { return std::chrono::duration<double>(std::chrono::steady_clock::now() - begin).count(); };
    // Fill in key order, as the worker does.
    for (uint64_t id = 0; id < n;) {
      sm::Window window;
      window.lanes = static_cast<unsigned>(std::min<uint64_t>(access_threads, n - id));
      for (unsigned w = 0; w < window.lanes; ++w, ++id) {
        window.key[w] = id;
        window.write[w] = true;
        const uint64_t v = id * 2 + 1;
        std::memcpy(values + w * kBytes, &v, kBytes);
        reference[id] = v;
      }
      engine.Run(window, values, results);
    }
    std::printf("filled %llu entries (%s) in %.0f s\n", (unsigned long long)n, argv[2], elapsed());
    std::fflush(stdout);
    // Random windows; a key at most once per window keeps the check simple.
    uint64_t accesses = 0, next_report = 60;
    while (elapsed() < seconds) {
      sm::Window window;
      window.lanes = access_threads;
      uint64_t expected[sm::kMaxLanes];
      for (unsigned w = 0; w < window.lanes; ++w) {
        uint64_t key;
        bool fresh;
        do {
          key = rng() % n;
          fresh = true;
          for (unsigned v = 0; v < w; ++v) fresh &= window.key[v] != key;
        } while (!fresh);
        window.key[w] = key;
        window.write[w] = (rng() % 20) == 0;
        const uint64_t value = rng() | 1;
        std::memcpy(values + w * kBytes, &value, kBytes);
        expected[w] = reference[key];
        if (window.write[w]) reference[key] = value;
      }
      engine.Run(window, values, results);
      for (unsigned w = 0; w < window.lanes; ++w) {
        uint64_t got;
        std::memcpy(&got, results + w * kBytes, kBytes);
        Check(got == expected[w], "key " + std::to_string(window.key[w]) + " returned " + std::to_string(got) +
                                      ", expected " + std::to_string(expected[w]) + " after " +
                                      std::to_string(accesses) + " accesses");
      }
      accesses += window.lanes;
      if (elapsed() >= next_report) {
        std::printf("%.0f s: %llu accesses, all reads correct\n", elapsed(), (unsigned long long)accesses);
        std::fflush(stdout);
        next_report += 60;
      }
    }
    std::printf("DONE %llu accesses in %.0f s, all reads correct\n", (unsigned long long)accesses, elapsed());
    return 0;
  } catch (const std::exception& error) {
    std::printf("FAILED: %s\n", error.what());
    return 1;
  }
}
