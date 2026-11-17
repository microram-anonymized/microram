// The SONIC adapter's map (sonic_map.hpp; README.md in the parent directory), on small real
// ZingORAM trees: the recursive position map and the one outside against a
// reference map, with random windows and adversarial ones; the map mutator;
// and the data round against the batch contract.
#include "benchmarks/baselines/sonic_map.hpp"
#include "sonic/threads/platform/pthread_thread_pool.hpp"
#include "sonic/util/log.hpp"

#include <iostream>
#include <numeric>
#include <random>

namespace {
namespace sm = oram_bench::sonic;
void Check(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error(message);
}

constexpr size_t kBytes = 8;
uint64_t Word(const uint8_t* bytes) { uint64_t w; std::memcpy(&w, bytes, 8); return w; }
void Put(uint8_t* bytes, uint64_t w) { std::memcpy(bytes, &w, 8); }

// Small trees: Z=8, S=12, R=2, four eviction threads, b = 16.
class Fixture {
 public:
  Fixture(uint64_t entries, bool recursive, unsigned threads, uint64_t top)
      : threads_(threads), access_pool_(threads - 1), eviction_pool_(3), access_(access_pool_.pool(), threads) {
    const sm::TreeParams params{8, 12, 0, 1};
    auto tree = [&](uint64_t blocks, auto bytes_tag) -> std::unique_ptr<sm::Tree> {
      constexpr size_t bytes = decltype(bytes_tag)::value;
      const auto g = sm::TreeGeometry(blocks, params, 2, bytes);
      return std::make_unique<sm::ZingTree<bytes>>(blocks, params, 2, threads,
          sn::threads::thread_team(eviction_pool_.pool(), std::min<unsigned>(4, 1u << g.routing)), sm::kMaxLanes);
    };
    sm::EngineConfig config{entries, kBytes, recursive, 16, top};
    std::vector<std::unique_ptr<sm::Tree>> maps;
    uint64_t blocks = entries;
    if (recursive)
      for (unsigned level = 0; level < sm::MapLevels(entries, 16, top); ++level) {
        blocks = (blocks + 15) / 16;
        maps.push_back(tree(blocks, std::integral_constant<size_t, 64>{}));
      }
    engine_ = std::make_unique<sm::Engine>(config, tree(entries, std::integral_constant<size_t, kBytes>{}),
                                           std::move(maps), threads > 1 ? &access_ : nullptr);
    reference_.assign(entries, 0);
  }
  unsigned threads() const { return threads_; }
  const sm::Engine& engine() const { return *engine_; }
  // One window against the reference: request order within the window.
  void Run(const std::vector<uint64_t>& keys, const std::vector<bool>& writes, std::mt19937_64& rng) {
    sm::Window window;
    window.lanes = static_cast<unsigned>(keys.size());
    alignas(64) uint8_t values[sm::kMaxLanes * kBytes] = {}, results[sm::kMaxLanes * kBytes] = {};
    std::vector<uint64_t> expected(keys.size());
    for (unsigned w = 0; w < window.lanes; ++w) {
      window.key[w] = keys[w];
      window.write[w] = writes[w];
      const uint64_t value = rng() | 1;
      Put(values + w * kBytes, value);
      expected[w] = reference_[keys[w]];
      if (writes[w]) reference_[keys[w]] = value;
    }
    engine_->Run(window, values, results);
    for (unsigned w = 0; w < window.lanes; ++w)
      Check(Word(results + w * kBytes) == expected[w],
            "lane " + std::to_string(w) + " of key " + std::to_string(keys[w]) + ": got " +
                std::to_string(Word(results + w * kBytes)) + ", expected " + std::to_string(expected[w]));
  }
  void Fill(std::mt19937_64& rng) {
    for (uint64_t id = 0; id < reference_.size();) {
      std::vector<uint64_t> keys;
      for (unsigned w = 0; w < threads_ && id < reference_.size(); ++w) keys.push_back(id++);
      Run(keys, std::vector<bool>(keys.size(), true), rng);
    }
  }
  uint64_t entries() const { return reference_.size(); }
 private:
  unsigned threads_;
  sn::threads::pthread_thread_pool access_pool_, eviction_pool_;
  sn::threads::thread_team access_;
  std::unique_ptr<sm::Engine> engine_;
  std::vector<uint64_t> reference_;
};

void TestAgainstReference(bool recursive, unsigned threads) {
  // 2^12 entries with C = 16: two map levels (256 then 16 blocks) under the top.
  Fixture f(4096, recursive, threads, 16);
  Check(!recursive || f.engine().levels() == 2, "fixture should have two map levels");
  std::mt19937_64 rng(recursive * 10 + threads);
  f.Fill(rng);
  auto random_window = [&](unsigned lanes, auto key) {
    std::vector<uint64_t> keys;
    std::vector<bool> writes;
    for (unsigned w = 0; w < lanes; ++w) { keys.push_back(key(w)); writes.push_back(rng() % 3 == 0); }
    f.Run(keys, writes, rng);
  };
  const unsigned t = f.threads();
  for (int i = 0; i < 1500; ++i)  // random keys, full and partial windows
    random_window(1 + rng() % t, [&](unsigned) { return rng() % f.entries(); });
  for (int i = 0; i < 200; ++i) {  // every lane the same key
    const uint64_t key = rng() % f.entries();
    random_window(t, [&](unsigned) { return key; });
  }
  for (int i = 0; i < 200; ++i) {  // every lane in one level-1 block, on distinct keys
    const uint64_t block = rng() % (f.entries() / 16);
    std::vector<uint64_t> offsets(16);
    std::iota(offsets.begin(), offsets.end(), 0);
    std::shuffle(offsets.begin(), offsets.end(), rng);
    random_window(t, [&](unsigned w) { return block * 16 + offsets[w]; });
  }
  const uint64_t few[3] = {7, 8, 4095};
  for (int i = 0; i < 200; ++i) {  // alternating reads and writes on a few keys
    std::vector<uint64_t> keys;
    std::vector<bool> writes;
    for (unsigned w = 0; w < t; ++w) { keys.push_back(few[(i + w) % 3]); writes.push_back((i + w) % 2); }
    f.Run(keys, writes, rng);
  }
  for (int i = 0; i < 300; ++i)  // a partial window
    random_window(t > 1 ? t - 1 : 1, [&](unsigned) { return rng() % 64; });
}

// The map mutator changes exactly one entry per child new to its run and
// leaves every other entry as it was; a dummy or another block changes nothing.
void TestMapMutator() {
  std::mt19937_64 rng(5);
  sm::Window window;
  window.lanes = 5;
  sm::MapRound round;
  round.window = &window;
  const uint64_t blocks[5] = {7, 7, 9, 7, 7}, entries[5] = {3, 3, 5, 10, 20};
  const bool child_rep[5] = {true, false, true, true, true};  // lane 1 shares lane 0's child
  for (unsigned w = 0; w < 5; ++w) {
    round.block[w] = blocks[w];
    round.entry[w] = entries[w];
    round.child_rep[w] = child_rep[w];
    round.child_next[w] = static_cast<uint32_t>(rng());
  }
  uint32_t block[64], before[64];
  for (auto& e : block) e = static_cast<uint32_t>(rng());
  std::memcpy(before, block, sizeof(block));
  sm::MapMutate(block, 64, true, 7, round, 0);
  for (unsigned w = 0; w < 5; ++w) {
    const bool in_run = blocks[w] == 7;
    Check(round.valid[0][w] == in_run, "run membership");
    if (in_run) Check(round.out[0][w] == before[entries[w]], "a lane did not get its child's old label");
  }
  for (size_t j = 0; j < 64; ++j) {
    const uint32_t expected = j == 3 ? round.child_next[0] : j == 10 ? round.child_next[3]
                              : j == 20 ? round.child_next[4] : before[j];
    Check(block[j] == expected, "entry " + std::to_string(j) + " changed wrongly");
  }
  std::memcpy(before, block, sizeof(block));
  sm::MapRound dummy = round;
  sm::MapMutate(block, 64, false, -1, dummy, 1);
  sm::MapMutate(block, 64, true, 8, dummy, 2);
  Check(std::equal(block, block + 64, before), "a dummy or unwanted block changed an entry");
  for (unsigned w = 0; w < 5; ++w) Check(!dummy.valid[1][w] && !dummy.valid[2][w], "a dummy served a lane");
}

// The data round: a read returns the latest earlier write of its run or the
// value before the window; a write returns the value before it; the block
// keeps the last write; other keys' lanes are not served.
void TestDataRound() {
  sm::Window window;
  window.lanes = 5;
  const uint64_t keys[5] = {5, 5, 6, 5, 5};
  const bool writes[5] = {false, true, false, true, false};
  alignas(64) uint8_t values[sm::kMaxLanes * kBytes] = {}, rows[sm::kMaxLanes * sm::kMaxLanes * kBytes] = {};
  for (unsigned w = 0; w < 5; ++w) {
    window.key[w] = keys[w];
    window.write[w] = writes[w];
    Put(values + w * kBytes, 100 + w);
  }
  sm::DataRound round;
  round.window = &window;
  round.block_bytes = kBytes;
  round.values = values;
  round.rows = rows;
  alignas(64) uint8_t data[kBytes];
  Put(data, 42);
  sm::DataMutate<kBytes>(data, true, 5, round, 3);
  const uint64_t expected[5] = {42, 42, 0, 101, 103};
  for (unsigned w = 0; w < 5; ++w) {
    Check(round.valid[3][w] == (keys[w] == 5), "data run membership");
    if (keys[w] == 5) Check(Word(rows + (3 * sm::kMaxLanes + w) * kBytes) == expected[w], "batch contract");
  }
  Check(Word(data) == 103, "the block should keep the run's last write");
  sm::DataMutate<kBytes>(data, false, -1, round, 4);
  Check(Word(data) == 103, "a dummy changed the block");
}
}  // namespace

int main() {
  sn::util::log::global_logger().set_verbosity(sn::util::log::level::critical);
  try {
    TestMapMutator();
    TestDataRound();
    for (const bool recursive : {false, true})
      for (const unsigned threads : {1u, 4u}) {
        TestAgainstReference(recursive, threads);
        std::cout << (recursive ? "recursive" : "outside") << " map, " << threads << " lanes: matches the reference\n";
      }
    std::cout << "sonic map tests passed\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
