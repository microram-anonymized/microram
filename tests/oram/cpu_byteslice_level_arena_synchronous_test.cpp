// The synchronous storage mode (cpu_byteslice_level_arena_synchronous.hpp)
// against the arena engine's inline executor and a scalar map.
//
// THE CLAIM UNDER TEST is that the mode runs the arena's jobs, so it is
// checked against the arena itself: two engines with one secret, one settling
// every flush in the arena's buffers and one merging in place, must give the
// same answer to every operation AND hold the same entries in the same slots
// of every live table.  A scalar map checks both against the semantics.

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <string>
#include <tuple>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

int failures = 0;

void Expect(bool ok, const std::string& what) {
  if (!ok) {
    std::fprintf(stderr, "FAILED: %s\n", what.c_str());
    ++failures;
  }
}

template <class F>
bool Throws(F&& f) {
  try {
    f();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

struct Shape {
  const char* name;
  unsigned branching;
  unsigned levels;
  unsigned top_digit;
  unsigned prefix_flushes;
  size_t stash_buckets;
  std::vector<unsigned> fanouts;  // empty: uniform
};

la::LevelArenaEngine::Options MakeOptions(const Shape& shape,
                                          bool synchronous) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = shape.branching;
  options.geometry.levels = shape.levels;
  options.geometry.top_digit = shape.top_digit;
  options.geometry.prefix_flushes = shape.prefix_flushes;
  options.geometry.stash_buckets = shape.stash_buckets;
  options.geometry.level_fanouts = shape.fanouts;
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.max_accesses = kMaxAccesses;
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kSettle;
  options.synchronous = synchronous;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(
      0x5C0C ^ (31 * shape.branching + 7 * shape.levels + shape.top_digit));
  return options;
}

const std::vector<Shape>& Shapes() {
  static const std::vector<Shape> shapes = {
      {"B=2 L=6 D=2", 2, 6, 2, 2, 1, {}},
      {"B=4 L=4 D=4", 4, 4, 4, 2, 1, {}},
      {"B=8 L=3 D=8", 8, 3, 8, 2, 1, {}},
      {"B=8 L=4 D=8 half-fanout 4,4,8", 8, 4, 8, 2, 1, {4, 4, 8}},
      {"B=8 L=3 D=4 r0=4 s=2", 8, 3, 4, 4, 2, {}},
  };
  return shapes;
}

// Occupied entries of one table or tier, by slot: (bucket, slot) -> bytes.
using Entries = std::map<std::pair<size_t, unsigned>, std::vector<uint8_t>>;

// The key, value and meta lines only: a residual sweep moves payload lines
// and leaves an entry's tag lines as the destination held them, so those are
// the previous occupant's, which differs between the two layouts.
Entries OccupiedEntries(const uint8_t* data, const uint64_t* masks,
                        size_t buckets, const bs::Layout& layout) {
  Entries out;
  const size_t entry = layout.TagOffset();
  for (size_t b = 0; b < buckets; ++b) {
    for (unsigned s = 0; s < 64; ++s) {
      if (((masks[b] >> s) & 1) == 0) continue;
      std::vector<uint8_t> bytes(entry);
      for (size_t line = 0; line < entry; ++line) {
        bytes[line] = data[b * layout.BucketBytes() + line * 64 + s];
      }
      out[{b, s}] = std::move(bytes);
    }
  }
  return out;
}

// Every live hashed table of the two engines, matched by window and family,
// holds the same entries in the same slots, and so does its tier.  Bytes of
// empty slots are not compared: they are whatever the buffer held before.
size_t CompareLiveTables(const la::LevelArenaEngine& a,
                         const la::LevelArenaEngine& b) {
  auto key = [](const la::PublishedTable& t) {
    return std::make_tuple(t.window_begin, t.window_end, t.family_id);
  };
  auto sorted = [&](std::vector<la::PublishedTable> tables) {
    std::sort(tables.begin(), tables.end(),
              [&](const la::PublishedTable& x, const la::PublishedTable& y) {
                return key(x) < key(y);
              });
    return tables;
  };
  const auto ta = sorted(a.publisher().LiveTables());
  const auto tb = sorted(b.publisher().LiveTables());
  if (ta.size() != tb.size()) return 1;
  size_t mismatches = 0;
  for (size_t i = 0; i < ta.size(); ++i) {
    const la::PublishedTable& x = ta[i];
    const la::PublishedTable& y = tb[i];
    if (key(x) != key(y) || x.main_buckets != y.main_buckets ||
        x.tier_buckets != y.tier_buckets || x.index_bits != y.index_bits ||
        x.radix != y.radix) {
      ++mismatches;
      continue;
    }
    if (OccupiedEntries(x.data, x.masks, x.main_buckets, a.layout()) !=
            OccupiedEntries(y.data, y.masks, y.main_buckets, b.layout()) ||
        OccupiedEntries(x.tier_data, x.tier_masks, x.tier_buckets,
                        a.layout()) !=
            OccupiedEntries(y.tier_data, y.tier_masks, y.tier_buckets,
                            b.layout())) {
      ++mismatches;
    }
  }
  return mismatches;
}

void MakeValue(uint64_t key, uint64_t gen, std::vector<uint8_t>* value) {
  for (size_t b = 0; b < value->size(); ++b) {
    (*value)[b] = static_cast<uint8_t>(key * 131 + gen * 17 + b);
  }
}

// Reads, writes, erases and exchanges over a quarter of the capacity's keys,
// absent ones included, on both engines and the map.
void RunLockstep(la::LevelArenaEngine& arena, la::LevelArenaEngine& sync,
                 std::map<uint64_t, std::vector<uint8_t>>& model,
                 uint64_t seed, size_t operations, const std::string& where) {
  const size_t value_bytes = arena.ValueBytes();
  std::vector<uint8_t> value(value_bytes), a_out(value_bytes),
      s_out(value_bytes);
  std::mt19937_64 rng(seed);
  const uint64_t keys = arena.Capacity() / 4 + 1;
  size_t disagreements = 0;
  size_t table_mismatches = 0;
  for (size_t i = 0; i < operations; ++i) {
    const uint64_t key = rng() % keys + 1;
    const auto it = model.find(key);
    const bool present = it != model.end();
    switch (rng() % 8) {
      case 0: case 1: case 2:
        MakeValue(key, i, &value);
        arena.Write(key, value.data());
        sync.Write(key, value.data());
        model[key] = value;
        break;
      case 3: case 4: case 5: {
        const bool a = arena.Read(key, a_out.data());
        const bool s = sync.Read(key, s_out.data());
        if (a != present || s != present ||
            (present && (a_out != it->second || s_out != it->second))) {
          ++disagreements;
        }
        break;
      }
      case 6: {
        const bool a = arena.Erase(key, a_out.data());
        const bool s = sync.Erase(key, s_out.data());
        if (a != present || s != present ||
            (present && (a_out != it->second || s_out != it->second))) {
          ++disagreements;
        }
        model.erase(key);
        break;
      }
      default: {
        MakeValue(key, i + 3, &value);
        const bool insert = (rng() & 1) != 0;
        const bool a = arena.Exchange(key, value.data(), a_out.data(), insert);
        const bool s = sync.Exchange(key, value.data(), s_out.data(), insert);
        if (a != s || (a && a_out != s_out)) ++disagreements;
        if (present || insert) model[key] = value;
        break;
      }
    }
    if (i % 997 == 0) table_mismatches += CompareLiveTables(arena, sync);
  }
  table_mismatches += CompareLiveTables(arena, sync);
  Expect(disagreements == 0,
         where + ": " + std::to_string(disagreements) +
             " operations disagreed with the map");
  Expect(table_mismatches == 0,
         where + ": the synchronous tables differ from the arena's in " +
             std::to_string(table_mismatches) + " comparisons");
  Expect(arena.ProbeAuditViolations() == 0 && sync.ProbeAuditViolations() == 0,
         where + ": a key was really probed twice under one nonce family");
}

void TestLockstep() {
  for (const Shape& shape : Shapes()) {
    la::LevelArenaEngine arena(MakeOptions(shape, false));
    la::LevelArenaEngine sync(MakeOptions(shape, true));
    Expect(sync.synchronous() && sync.synchronous_levels() != nullptr,
           std::string(shape.name) + ": not in the synchronous mode");
    std::map<uint64_t, std::vector<uint8_t>> model;
    // Several top compactions' worth, so every digit of every level and the
    // top's in-place compaction run more than once.
    const size_t operations =
        static_cast<size_t>(std::min<uint64_t>(6 * arena.Capacity(), 200000));
    RunLockstep(arena, sync, model, 0x51C0 + shape.levels, operations,
                shape.name);
    Expect(sync.synchronous_levels()->merges() > 0,
           std::string(shape.name) + ": no merge ran");
    Expect(sync.synchronous_levels()->ordinal(shape.levels) > 1,
           std::string(shape.name) + ": the top never compacted");
  }
}

class Records {
 public:
  explicit Records(uint64_t first_key) : key_(first_key) {}
  bs::InitializationEntry operator*() {
    std::memcpy(key_bytes_, &key_, sizeof(key_));
    for (size_t b = 0; b < sizeof(value_); ++b) {
      value_[b] = static_cast<uint8_t>(key_ * 7 + b);
    }
    return bs::InitializationEntry{key_bytes_, value_};
  }
  Records& operator++() {
    ++key_;
    return *this;
  }

 private:
  uint64_t key_;
  uint8_t key_bytes_[8] = {};
  uint8_t value_[8] = {};
};

void TestInitialization() {
  for (const Shape& shape : Shapes()) {
    la::LevelArenaEngine arena(MakeOptions(shape, false));
    la::LevelArenaEngine sync(MakeOptions(shape, true));
    const size_t count = static_cast<size_t>(arena.Capacity() / 2);
    arena.Initialize(Records(1), count);
    sync.Initialize(Records(1), count);
    Expect(CompareLiveTables(arena, sync) == 0,
           std::string(shape.name) + ": initialized tops differ");
    Expect(Throws([&] { sync.Initialize(Records(1), 1); }),
           std::string(shape.name) + ": a second initialization was accepted");
    std::map<uint64_t, std::vector<uint8_t>> model;
    for (uint64_t k = 1; k <= count; ++k) {
      std::vector<uint8_t> v(8);
      for (size_t b = 0; b < 8; ++b) v[b] = static_cast<uint8_t>(k * 7 + b);
      model[k] = v;
    }
    RunLockstep(arena, sync, model, 0x1717 + shape.levels,
                static_cast<size_t>(
                    std::min<uint64_t>(3 * arena.Capacity(), 30000)),
                std::string(shape.name) + " after initialization");
  }
}

// A throwing input leaves the empty top, and the engine usable.
void TestInitializationRollback() {
  const Shape& shape = Shapes()[1];
  la::LevelArenaEngine sync(MakeOptions(shape, true));
  struct Throwing {
    uint64_t key = 1;
    size_t left = 5;
    uint8_t bytes[8] = {};
    uint8_t value[8] = {};
    bs::InitializationEntry operator*() {
      if (left == 0) throw std::runtime_error("the input failed");
      std::memcpy(bytes, &key, 8);
      return bs::InitializationEntry{bytes, value};
    }
    Throwing& operator++() {
      ++key;
      --left;
      return *this;
    }
  };
  Expect(Throws([&] { sync.Initialize(Throwing{}, 16); }),
         "a throwing initialization input did not throw");
  sync.Initialize(Records(100), 16);
  uint8_t out[8];
  Expect(!sync.Read(uint64_t{2}, out),
         "a failed initialization left a record behind");
  Expect(sync.Read(uint64_t{101}, out),
         "the retried initialization lost a key");
}

// The storage the header promises: T + sum(l=2..L) U_l mains, about 47 % of
// the arena's at B = D = 8, and the bill the planner prices.
void TestStorage() {
  for (const Shape& shape : Shapes()) {
    la::LevelArenaEngine arena(MakeOptions(shape, false));
    la::LevelArenaEngine sync(MakeOptions(shape, true));
    const la::LevelArenaGeometry& g = sync.geometry();
    size_t mains = g.TopBuckets();
    for (unsigned l = 2; l <= g.Levels(); ++l) mains += g.CarryBuckets(l);
    Expect(la::SynchronousLevels::MainBuckets(g) == mains,
           std::string(shape.name) + ": mains are not T + sum U_l");
    const auto role = [](const la::LevelArenaEngine& e, la::ByteRole r) {
      return e.ByteBill().At(r);
    };
    Expect(role(sync, la::ByteRole::kMains) <
               role(arena, la::ByteRole::kMains) * 3 / 5,
           std::string(shape.name) +
               ": the synchronous mains are not well below the arena's");
    Expect(sync.ByteBill().requested() < arena.ByteBill().requested(),
           std::string(shape.name) + ": the synchronous bill is not smaller");
  }
  // The closed form at B = D = 8: M/T = 1 + 8/56 (1 - 8^-(L-1)).
  const Shape uniform{"B=8 L=4 D=8", 8, 4, 8, 2, 1, {}};
  la::LevelArenaEngine sync(MakeOptions(uniform, true));
  const la::LevelArenaGeometry& g = sync.geometry();
  const double ratio =
      static_cast<double>(la::SynchronousLevels::MainBuckets(g)) /
      static_cast<double>(g.TopBuckets());
  const double want = 1.0 + 8.0 / 56.0 * (1.0 - 1.0 / 512.0);
  Expect(ratio > want - 1e-9 && ratio < want + 1e-9,
         "the B = D = 8 mains are not 1 + B/((B-1)D)(1 - B^-(L-1)) top tables");

  // The planner prices the same bill.
  la::LevelArenaCapacityRequest request;
  request.entries = uint64_t{1} << 20;
  request.synchronous = true;
  const la::LevelArenaCapacityChoice planned =
      la::PlanLevelArenaCapacity(request);
  la::LevelArenaEngine::Options options;
  options.geometry = planned.geometry;
  options.key_bytes = request.key_bytes;
  options.value_bytes = request.value_bytes;
  options.synchronous = true;
  la::LevelArenaEngine built(options);
  Expect(built.ByteBill().requested() == planned.bill.requested(),
         "the planner's synchronous bill is not the built engine's");
  request.synchronous = false;
  Expect(la::PlanLevelArenaCapacity(request).bill.requested() >
             planned.bill.requested(),
         "the planner priced the synchronous mode no smaller");
}

void TestRefusals() {
  const Shape& shape = Shapes()[1];
  auto options = MakeOptions(shape, true);
  options.owner_threads = 1;
  Expect(Throws([&] { la::LevelArenaEngine e(options); }),
         "a synchronous engine accepted an owner thread");
  options = MakeOptions(shape, true);
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  Expect(Throws([&] { la::LevelArenaEngine e(options); }),
         "a synchronous engine accepted kHandOver");
  options = MakeOptions(shape, true);
  options.lanes.lanes = 2;
  Expect(Throws([&] { la::LevelArenaEngine e(options); }),
         "a synchronous engine accepted lanes");
  la::LevelArenaEngine sync(MakeOptions(shape, true));
  Expect(Throws([&] { (void)sync.level(1); }),
         "a synchronous engine handed out a level state machine");
}

// The batch path is the engine's; it must agree with serial accesses here
// too, across the merges its flushes trigger.
void TestBatch() {
  const Shape& shape = Shapes()[2];
  la::LevelArenaEngine serial(MakeOptions(shape, true));
  la::LevelArenaEngine batched(MakeOptions(shape, true));
  std::mt19937_64 rng(0xBA7C4);
  const uint64_t keys = serial.Capacity() / 4 + 1;
  constexpr size_t kLanes = 40;
  size_t mismatches = 0;
  std::vector<uint64_t> lane_keys(kLanes);
  std::vector<std::vector<uint8_t>> in(kLanes, std::vector<uint8_t>(8)),
      out(kLanes, std::vector<uint8_t>(8)), want(kLanes, std::vector<uint8_t>(8));
  std::vector<bs::BatchRequest64> requests(kLanes);
  std::vector<uint8_t> found(kLanes);
  for (size_t round = 0; round < 400; ++round) {
    for (size_t j = 0; j < kLanes; ++j) {
      lane_keys[j] = rng() % keys + 1;
      MakeValue(lane_keys[j], round * kLanes + j, &in[j]);
      requests[j].op = (rng() & 1) ? bs::BatchOp::kWrite : bs::BatchOp::kRead;
      requests[j].key = lane_keys[j];
      requests[j].value_in = in[j].data();
      requests[j].value_out = out[j].data();
    }
    batched.AccessBatch(kLanes, requests.data(), found.data());
    for (size_t j = 0; j < kLanes; ++j) {
      bool f = false;
      if (requests[j].op == bs::BatchOp::kWrite) {
        f = serial.Read(lane_keys[j], want[j].data());
        serial.Write(lane_keys[j], in[j].data());
      } else {
        f = serial.Read(lane_keys[j], want[j].data());
      }
      if (static_cast<bool>(found[j]) != f || (f && out[j] != want[j])) {
        ++mismatches;
      }
    }
  }
  Expect(mismatches == 0, "a synchronous batch disagreed with serial accesses "
                          "on " + std::to_string(mismatches) + " lanes");
}

}  // namespace

int main() {
  TestRefusals();
  TestStorage();
  TestLockstep();
  TestInitialization();
  TestInitializationRollback();
  TestBatch();
  if (failures != 0) {
    std::fprintf(stderr, "%d synchronous-mode checks failed\n", failures);
    return 1;
  }
  std::printf("level-arena synchronous-mode tests passed\n");
  return 0;
}
