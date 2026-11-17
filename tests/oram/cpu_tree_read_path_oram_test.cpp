// The tree ORAM engine (cpu_tree_read_path_oram.hpp):
//
//   * against a model map -- reads, contains, misses, updates, inserts,
//     exchanges and erases, with every value checked -- on one-tile and
//     two-tile paths, both stash widths (A = 3, 4) and folded roots,
//     synchronous and with payload workers;
//   * against the stash simulator's in-place plan
//     (benchmarks/oram/cpu_tree_stash_sim.hpp), slot for slot and stash lane
//     for stash lane, which is what ties the engine to the stash measurement
//     -- including runs that crowd the stash into its last register, so
//     every stash register holds live entries that are routed, gathered and
//     landed;
//   * the threaded engine's planes, reassembled, against a synchronous twin
//     fed the same requests, byte for byte;
//   * the storage invariant: every live entry is exactly once on its path or
//     in the stash;
//   * the failure event: an overflowing pass throws and writes nothing, on
//     the synchronous and on the threaded engine;
//   * the configuration boundary: hand-built geometries the engine refuses
//     before it reserves an arena;
//   * the payload worker pool: the slice layout, lifetime, a worker's
//     failure at each stage, a failing init hook or thread creation, a
//     lagging worker, and an access that waits for every worker's slice of
//     the value, on the ordinary and on the staged pass;
//   * through CpuTreeMap: misses read fresh random paths, and the bucket
//     offset helpers agree with the addressing every pass uses.

#include "benchmarks/oram/cpu_tree_stash_sim.hpp"
#include "src/oram/tree/cpu_tree_map.hpp"
#include "src/oram/tree/cpu_tree_read_path_oram.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <mutex>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

namespace {

namespace tr = microram::tree;
namespace sim = microram::tree::stash_sim;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrowsAs;
using microram::byteslice::test_support::WideKey;

struct Config {
  const char* name;
  size_t capacity;
  size_t value_bytes;
  unsigned stash_registers;
  unsigned leaf_scale = 0;
  unsigned workers = 0;
  // Nonzero: while the stash holds fewer than `crowd` entries, fresh leaves
  // come from this many fixed leaves, so their paths fill and the rest piles
  // up in the stash -- into its last register.
  unsigned hot_leaves = 0;
  unsigned crowd = 0;
  // A fold past 1 puts its levels' slots in the stash.
  unsigned fold = 1;
};

tr::TreeShape ShapeFor(const Config& c) {
  tr::TreeShape shape;
  shape.stash_registers = c.stash_registers;
  return shape;
}

tr::TreeKnobs KnobsFor(const Config& c) {
  tr::TreeKnobs k;
  k.fold = c.fold;
  k.leaf_scale = c.leaf_scale;
  k.shape = ShapeFor(c);
  k.payload_spin_micros = 50;
  return k;
}

tr::TreeGeometry GeometryFor(const Config& c) {
  return tr::TreeGeometry::ForCapacity(c.capacity, c.fold, c.value_bytes,
                                       c.leaf_scale, ShapeFor(c));
}

// Every stored slot and stash lane of the metadata plane -- the whole entry
// on the synchronous engine -- as (real, uid, leaf), by a callback.  Drained
// first: a threaded engine's write-back may still be running.
template <class F>
void ForEachSlot(tr::CpuReadPathOram& oram, F&& f) {
  oram.Drain();
  const tr::TreeStorage& st = oram.StorageForTest();
  const tr::TreeGeometry& g = st.geometry;
  const unsigned Z = tr::kBucketSlots;
  for (unsigned level = g.fold; level <= g.tree_levels; ++level) {
    for (uint64_t b = 0; b < g.buckets_at(level); ++b) {
      const uint8_t* bucket = st.BucketAt(g.level_offset_bytes(level) +
                                          g.stored_slot(level, b) * g.bucket_stride());
      for (unsigned t = 0; t < Z; ++t) {
        const uint64_t uid = tr::ReadBucketU64(bucket, t, tr::kUidOffset);
        const uint64_t pos = tr::ReadBucketU64(bucket, t, tr::kPositionOffset);
        f(false, level, b, t, tr::StoredPositionIsReal(pos), uid,
          tr::StoredPositionLeaf(pos));
      }
    }
  }
  for (unsigned lane = 0; lane < oram.StashCapacity(); ++lane) {
    const uint64_t uid = tr::ReadStashU64(st, lane, tr::kUidOffset);
    const uint64_t pos = tr::ReadStashU64(st, lane, tr::kPositionOffset);
    f(true, 0u, uint64_t{lane}, 0u, tr::StoredPositionIsReal(pos), uid,
      tr::StoredPositionLeaf(pos));
  }
}

// Every live uid exactly once, on its own path or in the stash, and nothing
// else real.
void ExpectInvariant(tr::CpuReadPathOram& oram,
                     const std::unordered_map<uint64_t, uint64_t>& leaf_of,
                     const std::string& where) {
  const tr::TreeGeometry& g = oram.geometry();
  std::unordered_map<uint64_t, unsigned> seen;
  ForEachSlot(oram, [&](bool stash, unsigned level, uint64_t b, unsigned,
                        bool real, uint64_t uid, uint64_t leaf) {
    if (!real) return;
    ++seen[uid];
    const auto it = leaf_of.find(uid);
    Expect(it != leaf_of.end(), (where + ": a real entry that is not live").c_str());
    Expect(it->second == leaf, (where + ": an entry carries a stale leaf").c_str());
    if (!stash) {
      Expect((leaf >> (g.leaf_bits - level)) == b,
             (where + ": an entry off its path").c_str());
    }
  });
  Expect(seen.size() == leaf_of.size(), (where + ": a live entry is missing").c_str());
  for (const auto& kv : seen) {
    Expect(kv.second == 1, (where + ": an entry is stored twice").c_str());
  }
}

void ExpectSameAsSim(tr::CpuReadPathOram& oram, const sim::TreeSim& s,
                     const std::string& where) {
  ForEachSlot(oram, [&](bool stash, unsigned level, uint64_t b, unsigned t,
                        bool real, uint64_t uid, uint64_t leaf) {
    sim::Slot want;
    if (stash) {
      if (b < s.StashLanes()) want = s.StashLane(static_cast<unsigned>(b));
    } else {
      want = s.TreeSlot(level, b, t);
    }
    char msg[256];
    std::snprintf(msg, sizeof(msg),
                  "%s: %s %u/%llu slot %u: engine %s(uid %llu, leaf %llu), "
                  "sim %s(block %d, leaf %u)",
                  where.c_str(), stash ? "stash lane" : "level", level,
                  (unsigned long long)b, t, real ? "real" : "dummy",
                  (unsigned long long)uid, (unsigned long long)leaf,
                  want.block >= 0 ? "real" : "dummy", want.block, want.pos);
    Expect(real == (want.block >= 0), msg);
    if (real) {
      Expect(uid == static_cast<uint64_t>(want.block), msg);
      Expect(leaf == want.pos, msg);
    }
  });
}

// The threaded engine's planes, reassembled, against the synchronous twin's
// whole storage (cpu_tree_layout.hpp's SlicedStorageEquals).
void ExpectSameAsTwin(tr::CpuReadPathOram& threaded, tr::CpuReadPathOram& twin,
                      const std::string& where) {
  threaded.Drain();
  std::vector<const tr::TreeStorage*> planes;
  for (size_t i = 0; i < threaded.PlaneCount(); ++i) {
    planes.push_back(&threaded.plane(i).StorageForTest());
  }
  std::string what;
  const bool same = tr::SlicedStorageEquals(planes, twin.StorageForTest(), &what);
  Expect(same, (where + ": planes differ from the synchronous engine: " + what).c_str());
}

std::vector<uint8_t> ValueFor(uint64_t uid, uint64_t version, size_t n) {
  std::vector<uint8_t> v(n);
  uint64_t x = uid * 0x9E3779B97F4A7C15ull + version * 0xD1B54A32D192ED03ull;
  for (size_t i = 0; i < n; ++i) {
    x ^= x >> 29;
    x *= 0xBF58476D1CE4E5B9ull;
    v[i] = static_cast<uint8_t>(x >> 56);
  }
  return v;
}

// The model test, with the simulator alongside when `with_sim`, and a
// synchronous twin when the engine under test has workers.
void RunModel(const Config& c, uint64_t ops, bool with_sim) {
  const tr::TreeGeometry g = GeometryFor(c);
  tr::CpuReadPathOram oram(g, KnobsFor(c), c.workers);
  Expect(oram.Threaded() == (c.workers > 0), "the worker count was not honoured");
  std::unique_ptr<tr::CpuReadPathOram> twin;
  if (c.workers > 0) twin = std::make_unique<tr::CpuReadPathOram>(g, KnobsFor(c), 0);
  sim::TreeSim s(sim::MakeGeometry(g.leaf_bits, g.fold, g.shape.stash_registers),
                 c.capacity, 1);

  std::mt19937_64 rng(c.capacity * 31 + c.value_bytes + c.workers);
  const uint64_t leaf_mask = (uint64_t{1} << g.leaf_bits) - 1;
  std::vector<uint64_t> hot;
  for (unsigned i = 0; i < c.hot_leaves; ++i) hot.push_back(rng() & leaf_mask);
  const size_t V = c.value_bytes;
  std::unordered_map<uint64_t, uint64_t> leaf_of;      // live uid -> leaf
  std::unordered_map<uint64_t, uint64_t> version_of;   // live uid -> version
  std::vector<uint64_t> live;
  std::vector<uint8_t> in(V), out(V), twin_out(V);
  uint64_t next_uid = 0, version = 0;
  unsigned contains = 0;
  for (uint64_t op = 0; op < ops; ++op) {
    const unsigned kind = static_cast<unsigned>(rng() % 100);
    const bool fill = live.size() < c.capacity / 2;
    const bool crowding = !hot.empty() && oram.StashOccupancy() < c.crowd;
    const uint64_t fresh = crowding ? hot[rng() % hot.size()] : rng() & leaf_mask;
    tr::TreeAccessRequest req;
    req.position_new = fresh;
    const uint8_t* value_in = nullptr;
    uint8_t* value_out = out.data();
    std::memset(out.data(), 0xA5, V);
    int32_t sim_target = -1, sim_lane0 = -1;
    uint64_t uid = 0;
    bool expect_found = false;
    std::vector<uint8_t> expect_value(V, 0);
    enum { kRead, kContains, kMiss, kUpdate, kInsert, kErase, kExchange } what;
    if (live.empty() || (fill && kind < 50) ||
        (kind >= 85 && kind < 95 && live.size() < c.capacity)) {
      what = kInsert;
    } else if (kind < 40) {
      what = kRead;
    } else if (kind < 50) {
      what = kMiss;
    } else if (kind < 70) {
      what = kUpdate;
    } else if (kind < 80) {
      what = kErase;
    } else if (kind >= 95) {
      what = kContains;  // past the band a fill turns into inserts
    } else {
      what = kExchange;
    }
    if (what == kInsert) {
      uid = next_uid++;
      req.uid_old = uid;
      req.position_read = rng() & leaf_mask;
      req.uid_new = uid;
      req.create = true;
      req.write = true;
      in = ValueFor(uid, ++version, V);
      value_in = in.data();
      sim_lane0 = static_cast<int32_t>(uid);
    } else if (what == kMiss) {
      uid = (uint64_t{1} << 40) + op;  // never live
      req.uid_old = uid;
      req.position_read = rng() & leaf_mask;
      req.uid_new = uid;
    } else {
      const size_t idx = rng() % live.size();
      uid = live[idx];
      req.uid_old = uid;
      req.position_read = leaf_of[uid];
      req.uid_new = uid;
      expect_found = true;
      expect_value = ValueFor(uid, version_of[uid], V);
      sim_target = static_cast<int32_t>(uid);
      if (what == kErase) {
        req.erase = true;
        live[idx] = live.back();
        live.pop_back();
      } else {
        sim_lane0 = static_cast<int32_t>(uid);
        if (what == kContains) value_out = nullptr;
        if (what == kUpdate || what == kExchange) {
          req.write = true;
          in = ValueFor(uid, ++version, V);
          value_in = in.data();
          if (what == kUpdate) value_out = nullptr;
        }
      }
    }
    if (with_sim) {
      s.Access(req.position_read, sim_target, sim_lane0,
               static_cast<uint32_t>(fresh));
    }
    const bool found = oram.Access(req, value_in, value_out);
    Expect(found == expect_found, "found disagrees with the model");
    if (value_out != nullptr) {
      Expect(std::memcmp(out.data(), expect_value.data(), V) == 0,
             "value_out disagrees with the model");
    }
    if (twin != nullptr) {
      Expect(twin->Access(req, value_in, value_out ? twin_out.data() : nullptr) ==
                 found,
             "the synchronous twin disagrees on found");
    }
    contains += what == kContains;
    if (what == kErase) {
      leaf_of.erase(uid);
      version_of.erase(uid);
    } else if (what == kInsert) {
      leaf_of[uid] = fresh;
      version_of[uid] = version;
      live.push_back(uid);
    } else if (what != kMiss) {
      leaf_of[uid] = fresh;
      if (req.write) version_of[uid] = version;
    }
    // A scan reads every slot of the tree, so the big trees scan less often.
    const uint64_t period = g.slots() > (size_t{1} << 18) ? 2003 : 97;
    if (op < 64 || op % period == 0 || op + 1 == ops) {
      const std::string where =
          std::string(c.name) + " op " + std::to_string(op);
      ExpectInvariant(oram, leaf_of, where);
      if (with_sim) ExpectSameAsSim(oram, s, where);
      if (twin != nullptr) ExpectSameAsTwin(oram, *twin, where);
    }
  }
  Expect(contains > 0, "no contains ran");
  if (c.crowd != 0) {
    Expect(oram.MaxStashOccupancy() > 64 * (c.stash_registers - 1),
           "the crowded run never reached the last stash register");
  }
  std::printf("  %-36s N %-6zu V %-4zu A %u K %-2u lambda %2u P %2u  %llu ops "
              "(%s%s), stash peak %3u of %u\n",
              c.name, c.capacity, V, c.stash_registers, oram.PayloadPlanes(),
              g.leaf_bits, g.path_buckets(), (unsigned long long)ops,
              with_sim ? "model + simulator" : "model",
              twin != nullptr ? " + twin" : "", oram.MaxStashOccupancy(),
              oram.StashCapacity());
}

// Fill the stash past its lanes: the pass that would overflow throws, and it
// has written nothing -- not a bucket and not a stash line of any plane.
void TestOverflowWritesNothing(unsigned workers) {
  Config c{"overflow", 1024, 100, 3, 0, workers};
  tr::TreeGeometry g = GeometryFor(c);
  tr::CpuReadPathOram oram(g, KnobsFor(c), workers);
  std::mt19937_64 rng(5);
  const uint64_t leaf_mask = (uint64_t{1} << g.leaf_bits) - 1;
  std::vector<uint8_t> value(100, 7);
  bool threw = false;
  // Every entry on ONE leaf: the path holds 4 P of them, the rest pile up.
  const uint64_t leaf = rng() & leaf_mask;
  const auto snapshot = [&] {
    oram.Drain();
    std::vector<std::vector<uint8_t>> bytes;
    for (size_t i = 0; i < oram.PlaneCount(); ++i) {
      const tr::TreeStorage& st = oram.plane(i).StorageForTest();
      bytes.emplace_back(st.buckets.get(),
                         st.buckets.get() + st.geometry.bucket_bytes_total());
      bytes.emplace_back(st.stash.get(),
                         st.stash.get() + st.geometry.stash_bytes());
    }
    return bytes;
  };
  for (uint64_t uid = 0; uid < 4096 && !threw; ++uid) {
    const auto before = snapshot();
    tr::TreeAccessRequest req;
    req.uid_old = uid;
    req.position_read = rng() & leaf_mask;
    req.uid_new = uid;
    req.position_new = leaf;
    req.create = true;
    req.write = true;
    try {
      oram.Access(req, value.data(), nullptr);
    } catch (const tr::StashOverflowError&) {
      threw = true;
      Expect(snapshot() == before, "an overflowing pass wrote something");
      Expect(oram.Overflows() == 1, "the overflow was not counted");
    }
  }
  Expect(threw, "the stash never overflowed");
  std::printf("  overflow, K %u: thrown at %u of %u stash lanes, nothing written\n",
              oram.PayloadPlanes(), oram.MaxStashOccupancy(),
              oram.StashCapacity());
}

void TestArguments() {
  Config c{"arguments", 1024, 8, 3};
  const tr::TreeGeometry g = GeometryFor(c);
  // Knobs that disagree with the geometry they are handed.
  bool threw = false;
  try {
    tr::TreeKnobs k = KnobsFor(c);
    k.shape.stash_registers = 4;
    tr::CpuReadPathOram oram(g, k);
  } catch (const std::invalid_argument&) {
    threw = true;
  }
  Expect(threw, "a stash width the geometry was not built with was accepted");
  // THE CONFIGURATION BOUNDARY: hand-built geometries the engine refuses
  // before it reserves an arena, each with knobs that agree with it, so that
  // the geometry itself is what is refused.
  const auto knobs_of = [](const tr::TreeGeometry& geometry) {
    tr::TreeKnobs k;
    k.fold = geometry.fold;
    k.leaf_scale = geometry.leaf_scale;
    k.shape = geometry.shape;
    return k;
  };
  struct Refused {
    const char* what;
    tr::TreeGeometry geometry;
    bool length_error;  // else std::invalid_argument
  };
  const tr::TreeGeometry base = tr::TreeGeometry::ForCapacity(1 << 12, 1, 16);
  std::vector<Refused> refused;
  {
    tr::TreeGeometry g = base;
    g.leaf_bits = 33;
    g.DeriveShape();
    refused.push_back({"a 33-bucket path was accepted", g, false});
  }
  {
    tr::TreeGeometry g = base;
    g.value_bytes = SIZE_MAX - 15;
    refused.push_back({"a value width that wraps the entry was accepted", g, true});
  }
  {
    tr::TreeGeometry g = base;
    g.tree_levels = ~0u;
    refused.push_back({"a tree depth past the level tables was accepted", g, false});
  }
  {
    tr::TreeGeometry g = base;
    g.path_match_bits[0] = 0;
    refused.push_back({"path tables that disagree with the shape were accepted", g, false});
  }
  refused.push_back({"a slice of the entry was accepted as a whole tree",
                     tr::TreeGeometry::ForCapacity(128, 1, 64).ForSlice(1, 1), false});
  {
    tr::TreeGeometry g = base;
    g.fold = 6;
    g.DeriveShape();
    refused.push_back({"fold 6 was accepted", g, false});
  }
  for (unsigned a : {0u, 5u}) {
    tr::TreeGeometry g = base;
    g.shape.stash_registers = a;
    refused.push_back({"a built stash width other than 3 or 4 was accepted", g, false});
  }
  {
    tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1 << 14, 4, 64);
    g.shape.max_folded_slots = 29;
    refused.push_back({"a fold past its lane budget was accepted", g, false});
  }
  {
    tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1 << 14, 5, 64);
    g.shape.stash_registers = 3;
    refused.push_back({"fold 5 with three stash registers was accepted", g, false});
  }
  // Fold 5 behind a two-register path (21 leaf bits, P = 17).
  refused.push_back({"fold 5 behind a two-register path was accepted",
                     tr::TreeGeometry::ForCapacity(size_t{1} << 23, 5, 64), false});
  {
    // 25 leaf bits (2^27 entries) take four; refused before the arena.
    tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(size_t{1} << 27, 1, 64);
    g.shape.stash_registers = 3;
    refused.push_back({"25 leaf bits with three stash registers was accepted", g, false});
  }
  for (const Refused& r : refused) {
    const auto build = [&] { tr::CpuReadPathOram oram(r.geometry, knobs_of(r.geometry)); };
    if (r.length_error) {
      ExpectThrowsAs<std::length_error>(build, r.what);
    } else {
      ExpectThrowsAs<std::invalid_argument>(build, r.what);
    }
  }
  // Fold 5 asks for four stash registers, and the geometry refuses three.
  ExpectThrowsAs<std::invalid_argument>(
      [] {
        tr::TreeShape three;
        three.stash_registers = 3;
        (void)tr::TreeGeometry::ForCapacity(1 << 14, 5, 64, 0, three);
      },
      "ForCapacity accepted fold 5 with three stash registers");
  // The worker policy: one per started 32 value bytes.
  tr::TreeKnobs k = KnobsFor(c);
  k.payload_max_threads = 64;
  Expect(tr::PayloadThreadCount(256, k) == 8, "256 B is 8 workers");
  Expect(tr::PayloadThreadCount(257, k) == 9, "257 B is 9 workers");
  Expect(tr::PayloadThreadCount(32, k) == 1, "32 B is 1 worker");
  Expect(tr::PayloadThreadCount(31, k) == 0, "31 B has none");
  k.payload_max_threads = 3;
  Expect(tr::PayloadThreadCount(1024, k) == 3, "the cap binds");
  std::printf("  arguments: working sets and worker counts as specified\n");
}

std::vector<uint8_t> PoolValue(uint64_t uid, uint64_t version, size_t bytes) {
  std::vector<uint8_t> v(bytes);
  uint64_t state = uid * 0x9E3779B97F4A7C15ull + version * 0xD1B54A32D192ED03ull + 1;
  for (auto& b : v) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    b = static_cast<uint8_t>(state >> 40);
  }
  return v;
}

// A write of uid `i + 1`, landing on leaf `(i * mul + add) mod leaves`.
tr::TreeAccessRequest WriteRequest(const tr::TreeGeometry& g, unsigned i,
                                   uint64_t mul, uint64_t add) {
  tr::TreeAccessRequest req;
  req.uid_old = i + 1;
  req.uid_new = i + 1;
  req.create = true;
  req.write = true;
  req.position_read = i % g.leaves();
  req.position_new = (i * mul + add) % g.leaves();
  return req;
}

void TestSliceLayout() {
  // The metadata plane is chunk 0; the payload chunks divide into contiguous
  // ranges with at most one chunk of difference.
  const tr::SliceLayout a = tr::SliceLayout::For(/*chunks=*/17, /*workers=*/4);
  Expect(a.ranges.size() == 5, "17 chunks / 4 workers is five planes");
  Expect(a.payload_planes() == 4, "four payload planes");
  Expect(a.ranges[0].begin == 0 && a.ranges[0].count == 1, "chunk 0 is meta");
  size_t at = 1;
  for (size_t i = 1; i < a.ranges.size(); ++i) {
    Expect(a.ranges[i].begin == at, "ranges are contiguous");
    at += a.ranges[i].count;
  }
  Expect(at == 17, "the ranges tile the entry");
  // A non-divisor still gets the selected count: 16 over 5 is 4,3,3,3,3.
  const tr::SliceLayout b = tr::SliceLayout::For(17, 5);
  Expect(b.payload_planes() == 5, "rounding must preserve selected workers");
  size_t total = 0;
  for (const auto& r : b.ranges) {
    Expect(r.count > 0, "no empty plane");
    total += r.count;
  }
  Expect(total == 17, "the ranges tile the entry (K = 5)");
  // More workers than payload chunks: clamped.
  const tr::SliceLayout c = tr::SliceLayout::For(3, 8);
  Expect(c.payload_planes() == 2, "two payload chunks, two planes");
  // No payload chunks at all: one plane holding everything.
  const tr::SliceLayout d = tr::SliceLayout::For(1, 4);
  Expect(d.ranges.size() == 1 && d.ranges[0].count == 1,
         "V <= 16 has no payload planes");
  std::printf("  slice layout: contiguous, balanced, clamped\n");
}

// Destruction while the workers are still on the write-back of the last
// access: the pool finishes the accepted job and joins.
void TestDestructionWithWorkPending() {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, 1024);
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 1000;
  auto oram = std::make_unique<tr::CpuReadPathOram>(g, tr::TreeKnobs{}, 4, wk);
  const std::vector<uint8_t> value(1024, 0x77);
  std::vector<uint8_t> out(1024);
  for (unsigned i = 0; i < 64; ++i) {
    (void)oram->Access(WriteRequest(g, i, 7, 1), value.data(), out.data());
  }
  oram.reset();  // returns only when every worker has retired its job
}

// No caller memory is referenced after an access returns: the value goes in
// as a copy and comes out before VALUE_READY, so a buffer freed on return is
// never touched again.  Meaningful under ASan, harmless without it.
void TestCallerBufferIsNotTouchedAfterReturn() {
  const size_t V = 512;
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 2000;
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, wk);
  for (unsigned i = 0; i < 64; ++i) {
    // Both buffers are freed the instant the access returns, while the
    // workers are still on the write-back of the job.
    auto value_in = std::make_unique<uint8_t[]>(V);
    auto value_out = std::make_unique<uint8_t[]>(V);
    for (size_t b = 0; b < V; ++b) value_in[b] = static_cast<uint8_t>(i + b);
    (void)oram.Access(WriteRequest(g, i, 13, 5), value_in.get(), value_out.get());
  }
  oram.Drain();
}

// A worker that throws stops: the pool latches the failure, the waits give
// up instead of spinning on a word that will never advance, and the next
// access is refused rather than hanging.  Nothing in the kernel throws, so
// the hook is how the state is reached at all.
void TestWorkerFailureIsRefusedNotHung() {
  const size_t V = 512;
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 0;
  wk.stage_observer = [](unsigned w, uint64_t job, tr::PayloadStage st) {
    if (w == 1 && job == 2 && st == tr::PayloadStage::kPlanReceived) {
      throw std::runtime_error("a worker failed");
    }
  };
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, wk);
  const std::vector<uint8_t> value(V, 0x21);
  std::vector<uint8_t> out(V);
  auto access = [&](unsigned i) {
    return oram.Access(WriteRequest(g, i, 5, 1), value.data(), out.data());
  };
  (void)access(0);           // job 1 is fine
  bool threw = false;
  try {
    (void)access(1);         // job 2: worker 1 throws before its pass
  } catch (const std::runtime_error&) {
    threw = true;
  }
  Expect(threw, "a worker's exception must reach the caller");
  bool refused = false;
  try {
    (void)access(2);         // and the instance is done
  } catch (const std::runtime_error&) {
    refused = true;
  }
  Expect(refused, "a failed pool must refuse further accesses");
}

// A WORKER THAT FAILS AFTER ITS VALUE IS READY MUST NOT HANG THE NEXT ACCESS.
//
// A worker that fails after publishing `value_ready(t)` lets access t return
// normally; if the main thread's `Failed()` check for access t+1 runs before
// the flag is visible, job t+1 goes to a thread that will never answer it.
// The worker's catch retires EVERY job (the words are monotone and every
// wait is `>= want`), so the next access throws instead of hanging.
//
// Deterministic: worker 1 is HELD at the end of job 1 (its pass done, `done`
// not yet published) until the main thread has published job 2 -- which
// worker 0's receipt of job 2's leaf reports -- and is then released with a
// throw.
void TestWorkerFailureAfterValueReadyDoesNotHang() {
  constexpr size_t V = 512;
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  std::mutex m;
  std::condition_variable cv;
  bool job2_published = false;
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 0;
  wk.stage_observer = [&](unsigned w, uint64_t job, tr::PayloadStage st) {
    if (w == 0 && job == 2 && st == tr::PayloadStage::kLeavesReceived) {
      std::lock_guard<std::mutex> lk(m);
      job2_published = true;
      cv.notify_all();
    }
    if (w == 1 && job == 1 && st == tr::PayloadStage::kJobDone) {
      std::unique_lock<std::mutex> lk(m);
      cv.wait(lk, [&] { return job2_published; });
      throw std::runtime_error("worker 1 failed after job 1's value was ready");
    }
  };
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, wk);
  const std::vector<uint8_t> value(V, 0x37);
  std::vector<uint8_t> out(V);
  auto access = [&](unsigned i) {
    return oram.Access(WriteRequest(g, i, 7, 3), value.data(), out.data());
  };
  (void)access(0);  // job 1: returns on value_ready; worker 1 then holds at kJobDone
  bool threw = false;
  try {
    (void)access(1);  // job 2: published before worker 1's failure is visible
  } catch (const std::runtime_error&) {
    threw = true;
  }
  Expect(threw, "the access after a late worker failure must throw, not hang");
  bool refused = false;
  try {
    (void)access(2);
  } catch (const std::runtime_error&) {
    refused = true;
  }
  Expect(refused, "a failed pool must refuse further accesses");
  // And the wait for the write-back must not hang either: `Drain` waits on
  // `done`, which the retire-all answers for every job number.  It then
  // reports the latched failure, exactly as any other wait does, so the
  // throw is the pass condition and hanging is the failure.
  bool drained = false;
  try {
    oram.Drain();
    drained = true;
  } catch (const std::runtime_error&) {
    drained = true;  // reported, not hung
  }
  Expect(drained, "Drain neither returned nor reported after a worker failed");
}

// A WORKER'S FAILURE MUST NOT HAND THE CALLER ITS BUFFER BACK EARLY.
//
// `value_out` belongs to the caller and the workers write their slices of it
// directly, so the whole contract is that `Access` does not return -- by
// value OR by exception -- until every worker has finished writing.  A wait
// released pool-wide by one worker's failure would hand the caller its
// buffer while the survivors were still storing into it.
//
// The check is direct rather than timing-based: hold a SURVIVING worker
// before its pass, fail another, and see whether `value_out` changes after
// the exception has been caught.  It must not.
void TestWorkerFailureDoesNotReleaseTheBufferEarly(size_t V, unsigned workers) {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 2000;
  // Worker 1 throws on job 2.  Worker 0 is held long enough that, if the
  // wait is released early, the caller sees its buffer back before worker 0
  // has written a byte of it.
  static constexpr auto kHold = std::chrono::milliseconds(50);
  wk.stage_observer = [](unsigned w, uint64_t job, tr::PayloadStage st) {
    if (job != 2) return;
    if (w == 1 && st == tr::PayloadStage::kPlanReceived) {
      throw std::runtime_error("a worker failed");
    }
    if (w == 0 && st == tr::PayloadStage::kPlanReceived) {
      std::this_thread::sleep_for(kHold);
    }
  };
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, workers, wk);
  const std::vector<uint8_t> value(V, 0x21);
  std::vector<uint8_t> out(V, 0xEE);
  auto access = [&](unsigned i) {
    return oram.Access(WriteRequest(g, i, 5, 1), value.data(), out.data());
  };
  (void)access(0);  // job 1 is fine

  std::fill(out.begin(), out.end(), 0xEE);
  bool threw = false;
  try {
    (void)access(1);  // job 2: worker 1 throws, worker 0 is held
  } catch (const std::runtime_error&) {
    threw = true;
  }
  Expect(threw, "a worker's exception must reach the caller");
  // Whatever the buffer holds now is what it must still hold: no worker may
  // write to it after the access has returned.
  const std::vector<uint8_t> snapshot = out;
  std::this_thread::sleep_for(kHold * 4);
  Expect(out == snapshot,
         "a worker wrote the caller's value_out after the access threw");
}

void TestInitHookFailureFailsConstruction() {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(512, 1, 512);
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 0;
  wk.init = [](unsigned k) {
    if (k == 1) throw std::runtime_error("pinning failed");
  };
  bool threw = false;
  try {
    tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, wk);
  } catch (const std::runtime_error&) {
    threw = true;
  }
  Expect(threw, "a failing init hook must fail construction");
}

// PARTIAL THREAD STARTUP.  A thread constructor that throws -- an OS thread
// limit is the ordinary cause -- must not leave the workers already created
// joinable while the pool's constructor unwinds: destroying a joinable
// `std::thread` member calls `std::terminate`, and the caller's catch would
// never run.  The injection knob makes the k-th creation fail on demand.
void TestPartialThreadStartupIsCleanedUp() {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(512, 1, 512);
  for (unsigned at = 1; at <= 3; ++at) {
    tr::PayloadWorkerKnobs wk;
    wk.spin_micros = 0;
    wk.fail_thread_creation_at = at;
    unsigned started = 0;
    std::mutex m;
    wk.init = [&](unsigned) {
      std::lock_guard<std::mutex> lk(m);
      ++started;
    };
    bool threw = false;
    try {
      tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, wk);
    } catch (const std::runtime_error&) {
      threw = true;  // the ORIGINAL exception, catchable, process alive
    }
    Expect(threw, "a failing thread creation must throw, not terminate");
    // Every worker that WAS created ran its hook and was then joined: the
    // count cannot move again, so reading it here is not a race.
    Expect(started == at - 1, "the workers created before the failure ran");
  }
  // And the pool still builds when nothing is injected.
  tr::PayloadWorkerKnobs ok;
  ok.spin_micros = 0;
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, 3, ok);
  Expect(oram.Threaded(), "the uninjected pool did not build");
}

// Holds one worker at one stage of one job until released.
class StageGate {
 public:
  void ArmAt(unsigned worker, uint64_t job, tr::PayloadStage stage) {
    std::lock_guard<std::mutex> lk(m_);
    worker_ = worker;
    job_ = job;
    stage_ = stage;
    armed_ = true;
    reached_ = false;
    released_ = false;
  }
  // Installed as the pool's stage observer.
  void operator()(unsigned worker, uint64_t job, tr::PayloadStage stage) {
    std::unique_lock<std::mutex> lk(m_);
    if (!armed_ || worker != worker_ || job != job_ || stage != stage_) return;
    reached_ = true;
    cv_.notify_all();
    cv_.wait(lk, [&] { return released_; });
    armed_ = false;
  }
  void WaitUntilReached() {
    std::unique_lock<std::mutex> lk(m_);
    cv_.wait(lk, [&] { return reached_; });
  }
  void Release() {
    {
      std::lock_guard<std::mutex> lk(m_);
      released_ = true;
    }
    cv_.notify_all();
  }

 private:
  std::mutex m_;
  std::condition_variable cv_;
  unsigned worker_ = 0;
  uint64_t job_ = 0;
  tr::PayloadStage stage_ = tr::PayloadStage::kLeavesReceived;
  bool armed_ = false;
  bool reached_ = false;
  bool released_ = false;
};

// An access does not return while any worker's slice of the value is
// outstanding, and the value is right once it is released.
void TestAccessWaitsForEveryWorkersValue(size_t V, unsigned workers) {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  StageGate gate;
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 0;
  wk.stage_observer = [&gate](unsigned w, uint64_t j, tr::PayloadStage st) {
    gate(w, j, st);
  };
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, workers, wk);
  const std::vector<uint8_t> value = PoolValue(1, 1, V);
  std::vector<uint8_t> out(V, 0);

  tr::TreeAccessRequest w;
  w.uid_old = 1; w.uid_new = 1; w.create = true; w.write = true;
  w.position_read = 5; w.position_new = 9;
  (void)oram.Access(w, value.data(), out.data());
  oram.Drain();

  // Job 2: a read of the same entry, with worker 1 held before its pass.
  gate.ArmAt(/*worker=*/1, /*job=*/2, tr::PayloadStage::kPlanReceived);
  tr::TreeAccessRequest r;
  r.uid_old = 1; r.uid_new = 1;
  r.position_read = 9; r.position_new = 13;
  std::vector<uint8_t> got(V, 0xEE);
  std::atomic<bool> returned{false};
  std::thread caller([&] {
    (void)oram.Access(r, nullptr, got.data());
    returned.store(true, std::memory_order_release);
  });
  gate.WaitUntilReached();
  // The held worker's slice of the value cannot be in place, so the access
  // must still be inside WaitValueReady.
  std::this_thread::sleep_for(std::chrono::milliseconds(20));
  Expect(!returned.load(std::memory_order_acquire),
         "an access must not return while a worker's value slice is "
         "outstanding");
  gate.Release();
  caller.join();
  Expect(std::memcmp(got.data(), value.data(), V) == 0,
         "the value is complete once every worker has published it");
}

// A LAGGING WORKER.  Worker 0 is held at `stage` of job 10 while the caller
// runs jobs 9-12 -- job 12 reuses job 10's slot -- and then released.  No
// access past the held job returns while it is held, and the values and the
// reassembled planes match a synchronous twin fed the same requests.
void TestLaggingWorker(size_t V, unsigned workers, tr::PayloadStage stage) {
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, V);
  StageGate gate;
  tr::PayloadWorkerKnobs wk;
  wk.spin_micros = 0;
  wk.stage_observer = [&gate](unsigned w, uint64_t j, tr::PayloadStage st) {
    gate(w, j, st);
  };
  tr::CpuReadPathOram oram(g, tr::TreeKnobs{}, workers, wk);
  tr::CpuReadPathOram twin(g, tr::TreeKnobs{}, 0);
  // Jobs 1-8 write uids 1-8; uid 1 lands on leaf 3.
  std::vector<uint8_t> out(V), twin_out(V);
  for (unsigned i = 0; i < 8; ++i) {
    const tr::TreeAccessRequest req = WriteRequest(g, i, 7, 3);
    const std::vector<uint8_t> value = PoolValue(i + 1, 0, V);
    (void)oram.Access(req, value.data(), out.data());
    (void)twin.Access(req, value.data(), twin_out.data());
  }
  oram.Drain();
  // Jobs 9-12 exchange uid 1: each reads the value the one before wrote.
  gate.ArmAt(/*worker=*/0, /*job=*/10, stage);
  std::atomic<unsigned> returned{0};
  std::thread caller([&] {
    uint64_t leaf = 3;
    std::vector<uint8_t> want = PoolValue(1, 0, V);
    for (unsigned i = 1; i <= 4; ++i) {
      tr::TreeAccessRequest req;
      req.uid_old = 1;
      req.uid_new = 1;
      req.create = true;
      req.write = true;
      req.position_read = leaf;
      leaf = (leaf * 5 + 1) % g.leaves();
      req.position_new = leaf;
      const std::vector<uint8_t> value = PoolValue(1, i, V);
      std::fill(out.begin(), out.end(), 0xEE);
      Expect(oram.Access(req, value.data(), out.data()), "uid 1 was not found");
      returned.fetch_add(1, std::memory_order_release);
      Expect(twin.Access(req, value.data(), twin_out.data()),
             "the twin did not find uid 1");
      Expect(out == want && twin_out == want,
             "an exchange did not read the value the one before wrote");
      want = value;
    }
  });
  gate.WaitUntilReached();
  std::this_thread::sleep_for(std::chrono::milliseconds(20));
  // Job 10 returns once worker 0 has published its value, which it has at
  // kJobDone and has not at kPlanReceived; job 11 waits for it either way.
  const unsigned bound = stage == tr::PayloadStage::kJobDone ? 2 : 1;
  Expect(returned.load(std::memory_order_acquire) <= bound,
         "an access returned past a worker that has not published its value");
  gate.Release();
  caller.join();
  ExpectSameAsTwin(oram, twin, "lagging worker");
}

void TestWorkerPool() {
  TestSliceLayout();
  TestPartialThreadStartupIsCleanedUp();
  TestInitHookFailureFailsConstruction();
  TestDestructionWithWorkPending();
  TestCallerBufferIsNotTouchedAfterReturn();
  TestWorkerFailureIsRefusedNotHung();
  TestWorkerFailureAfterValueReadyDoesNotHang();
  // 512 B runs the ordinary pass; 96 B over three workers and 100 B over two
  // stage their slices and gather first (ReadPathStagesSlice).
  const struct {
    size_t value_bytes;
    unsigned workers;
  } shapes[] = {{512, 3}, {96, 3}, {100, 2}};
  for (const auto& shape : shapes) {
    TestWorkerFailureDoesNotReleaseTheBufferEarly(shape.value_bytes, shape.workers);
    TestAccessWaitsForEveryWorkersValue(shape.value_bytes, shape.workers);
  }
  TestLaggingWorker(512, 3, tr::PayloadStage::kJobDone);
  TestLaggingWorker(96, 3, tr::PayloadStage::kJobDone);
  TestLaggingWorker(96, 3, tr::PayloadStage::kPlanReceived);
  std::printf("  worker pool: lifetime, failures, lagging workers and value hand-off\n");
}

// A miss reads a fresh random path, never the zeros an absent key comes back
// with, so repeated misses do not repeat an address (cpu_tree_map.hpp).
void TestMissesReadDistinctPaths() {
  using TestMap = tr::CpuTreeMap<tr::UnorderedPositionMap>;
  tr::TreeKnobs knobs;
  TestMap map(tr::TreeGeometry::ForCapacity(1 << 12, 0, 16), 8, knobs,
              tr::UnorderedPositionMap(1 << 12, 8),
              microram::crypto::SecretKeySeed::Fixed(5));
  std::set<uint64_t> paths;
  std::vector<uint8_t> out(16);
  for (uint64_t k = 1; k <= 200; ++k) {
    const std::vector<uint8_t> key = WideKey(900000 + k, 8);
    Expect(!map.Read(key.data(), out.data()), "a never-written key was found");
    paths.insert(map.LastPositionRead());
  }
  // 200 draws from 2^10 leaves: ~19 collisions expected, never 100.
  Expect(paths.size() > 150, "misses did not read fresh random paths");
  std::printf("  misses: %zu distinct paths of 200\n", paths.size());
}

// THE OFFSET HELPERS AGREE WITH PRODUCTION ADDRESSING.  `bucket_offset` is
// what reference scans walk the tree with, and PathAddressing is what every
// pass uses; this checks every leaf of a few geometries, folded and not.
void TestBucketOffsetMatchesPathAddressing() {
  struct Case {
    size_t capacity, value_bytes;
    unsigned fold;
  };
  const Case cases[] = {{257, 16, 1}, {512, 64, 1}, {1024, 100, 2},
                        {4096, 7, 3}, {3000, 64, 0}, {1u << 14, 40, 5}};
  for (const Case& c : cases) {
    const tr::TreeGeometry g =
        tr::TreeGeometry::ForCapacity(c.capacity, c.fold, c.value_bytes);
    tr::TreeStorage storage = tr::TreeStorage::Create(g);
    tr::PathAddressing addr;
    addr.Init(storage);
    const uint8_t* arena = storage.buckets.get();
    uint8_t* buckets[tr::kMaxPathLevels];
    for (uint64_t leaf = 0; leaf < g.leaves(); ++leaf) {
      addr.Buckets(leaf, buckets);
      for (unsigned i = 0; i < g.path_levels(); ++i) {
        Expect(static_cast<size_t>(buckets[i] - arena) ==
                   g.bucket_offset(g.fold + i, leaf),
               "bucket_offset disagrees with a path bucket");
      }
    }
  }
  std::printf("  bucket offsets: agree with PathAddressing at every leaf\n");
}

}  // namespace

int main() {
  std::printf("cpu_tree_read_path_oram_test\n");
  TestArguments();
  TestWorkerPool();
  TestMissesReadDistinctPaths();
  TestBucketOffsetMatchesPathAddressing();
  TestOverflowWritesNothing(0);
  TestOverflowWritesNothing(3);
  // One tile (P <= 16), two tiles (leaf_scale 4 deepens a small tree past
  // 16 levels), partial last chunks, both stash widths; synchronous, then
  // with workers.
  RunModel({"one tile, A=3, V=8", 1024, 8, 3}, 20000, true);
  RunModel({"one tile, A=4, V=1", 4096, 1, 4}, 20000, true);
  RunModel({"one tile, A=3, V=1024", 1u << 12, 1024, 3}, 5000, true);
  RunModel({"two tiles, A=3, V=24", 1u << 15, 24, 3, 4}, 30000, true);
  RunModel({"two tiles, A=3, V=100", 1u << 15, 100, 3, 4}, 10000, true);
  RunModel({"two tiles, A=4, V=24", 1u << 15, 24, 4, 4}, 30000, true);
  RunModel({"two tiles, A=4, V=100", 1u << 15, 100, 4, 4}, 10000, true);
  // The stash crowded into its last register.
  RunModel({"crowded, one tile, A=3, V=20", 2048, 20, 3, 0, 0, 3, 150},
           20000, true);
  RunModel({"crowded, one tile, A=4, V=72", 2048, 72, 4, 0, 0, 3, 200},
           20000, true);
  RunModel({"crowded, two tiles, A=3, V=50", 1u << 15, 50, 3, 4, 0, 4, 150},
           20000, true);
  RunModel({"crowded, two tiles, A=4, V=50", 1u << 15, 50, 4, 4, 0, 4, 220},
           20000, true);
  // Payload workers: every plane against the synchronous twin.
  RunModel({"workers, one tile, A=3, V=100", 1024, 100, 3, 0, 2}, 10000, true);
  RunModel({"workers, one tile, A=4, V=1024", 1u << 12, 1024, 4, 0, 5}, 4000,
           true);
  RunModel({"workers, crowded, two tiles, A=3, V=200", 1u << 15, 200, 3, 4, 4,
            4, 150}, 10000, true);
  RunModel({"workers, crowded, two tiles, A=4, V=200", 1u << 15, 200, 4, 4, 4,
            4, 220}, 10000, true);
  RunModel({"workers, one tile, A=3, V=1000", 512, 1000, 3, 0, 8}, 4000, false);
  // Folded roots behind a one-register path, at the stash widths the default
  // rule gives them.
  RunModel({"fold 4, A=3, V=100", 4096, 100, 3, 0, 0, 0, 0, 4}, 20000, true);
  RunModel({"fold 5, crowded, A=4, V=40", 1u << 14, 40, 4, 0, 0, 3, 196, 5},
           20000, true);
  RunModel({"fold 5, workers, A=4, V=200", 1u << 15, 200, 4, 0, 4, 0, 0, 5},
           10000, true);
  std::printf("cpu_tree_read_path_oram_test: PASS\n");
  return 0;
}
