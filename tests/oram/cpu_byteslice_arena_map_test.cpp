// The per-level arena byte map, `cpu_byteslice_oram::ByteMap<true>` (the
// hierarchical ORAM in its incremental, deamortized storage mode), checked
// against an equal-capacity scalar std::map model driven with the same
// arguments.  `ByteMap<false>` is the same engine in its synchronous storage
// mode, so it is not an independent reference and is not used as one.  Every
// answer -- what an absent read, an erase of a missing key or an
// exchange-without-insert MEANS -- is compared against the model.
//
// Four fixtures cover four phases: initialization, fill, steady state, and
// every public operation including the ones with unusual answers.  What this
// file covers that cpu_byteslice_oram_map_test.cpp does not is the BATCH
// surface, the packed conveniences and the result layouts, driven in lockstep
// against the model's lane-by-lane definition of a batch.

#include <cpu_byteslice_oram/oram.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;

int failures = 0;

void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

constexpr size_t kKeyBytes = 8;
constexpr size_t kValueBytes = 16;

using Key = std::array<uint8_t, kKeyBytes>;
using Value = std::array<uint8_t, kValueBytes>;

Key KeyOf(uint64_t i) {
  Key k{};
  std::memcpy(k.data(), &i, sizeof(i));
  return k;
}

Value ValueOf(uint64_t i) {
  Value v{};
  for (size_t b = 0; b < kValueBytes; ++b) {
    i = i * 6364136223846793005ull + 1442695040888963407ull;
    v[b] = static_cast<uint8_t>(i >> 33);
  }
  return v;
}

// The arena map at a shape small enough to exercise the whole ladder in a
// test: B = 4 keeps the cascade short and the arena small, and the owner
// threads stay off so that the comparison is of ANSWERS and not of schedules
// (the threaded shape is what cpu_byteslice_level_arena_threads_test pins).
//
// THE BATCH CONFIGURATION the map is built with, when a fixture wants one.
struct BatchArms {
  unsigned lanes = 1;
  unsigned participants = 1;
  bool parallel = false;
  // WHERE A LANE'S PROBE RESULT LANDS.  Public and fixed per instance; it
  // changes instruction streams, never trace shape and never answers, which is
  // exactly the claim the lockstep below is able to make.
  oram::BatchResultLayout layout =
      oram::BatchResultLayout::kSlicedPlaceAtLane;
  bool on() const { return lanes > 1 || participants > 1 || parallel; }
};

oram::Options ArenaOptions(BatchArms batch = {}) {
  oram::Options options;
  options.deamortized_batch_lanes = batch.lanes;
  options.deamortized_batch_participants = batch.participants;
  options.deamortized_batch_execution =
      batch.parallel ? oram::BatchExecutionShape::kParallelTiles
                     : oram::BatchExecutionShape::kChunkedCascade;
  options.deamortized_batch_result_layout = batch.layout;
  options.deamortized_branching_factor = 4;
  options.deamortized_online_stash_entries = 64;
  // The deterministic inline executor: the request thread drives every level
  // at its own flush, so the comparison is of ANSWERS and not of schedules.
  options.deamortized_owner_threads = 0;
  options.max_accesses = uint64_t{1} << 32;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0xA5E4A);
  return options;
}

// ---------------------------------------------------------------------------
// The input iterator the map is initialized from
// ---------------------------------------------------------------------------

class Records {
 public:
  explicit Records(uint64_t first = 0) : next_(first) {}

  oram::InitializationEntry operator*() {
    key_ = KeyOf(next_);
    value_ = ValueOf(next_);
    return oram::InitializationEntry{key_.data(), value_.data()};
  }
  Records& operator++() {
    ++next_;
    return *this;
  }

 private:
  uint64_t next_;
  Key key_{};
  Value value_{};
};

// ---------------------------------------------------------------------------
// One workload, run against the map and a std::map model
// ---------------------------------------------------------------------------

// Every public operation, on the map and the model, with the same argument,
// and every answer compared.  Returns as soon as something disagrees, because
// after a divergence the two are answering different questions and every
// later mismatch is the same failure reported again.
class Lockstep {
 public:
  explicit Lockstep(size_t requested_capacity, BatchArms batch = {})
      : arena_(requested_capacity, kKeyBytes, kValueBytes,
               ArenaOptions(batch)) {}

  // The map bulk-loaded from the records, and the model told what was loaded
  // -- `initialize` does not go through Insert below, so without this the
  // model would be empty and every later comparison vacuous.
  void Load(size_t count) {
    arena_.initialize(Records(0), count);
    for (uint64_t k = 0; k < count; ++k) model_[k] = ValueOf(k);
  }

  oram::ByteMap<true>& arena() { return arena_; }
  const std::map<uint64_t, Value>& model() const { return model_; }

  bool Find(uint64_t key, const std::string& where) {
    Value got{};
    const bool a = arena_.find(KeyOf(key).data(), got.data());
    const auto at = model_.find(key);
    return Agree(a == (at != model_.end()), where,
                 "find disagreed with the model") &&
           Agree(!a || got == at->second, where,
                 "find returned a value the model does not hold");
  }

  bool Insert(uint64_t key, const Value& value) {
    arena_.insert_or_assign(KeyOf(key).data(), value.data());
    model_[key] = value;
    return true;
  }

  bool Erase(uint64_t key, const std::string& where) {
    Value old{};
    const bool a = arena_.erase(KeyOf(key).data(), old.data());
    const auto at = model_.find(key);
    const bool held = at != model_.end();
    const bool ok =
        Agree(a == held, where, "erase disagreed with the model") &&
        Agree(!a || old == at->second, where, "erase returned other bytes");
    if (held) model_.erase(at);
    return ok;
  }

  bool Exchange(uint64_t key, const Value& value, bool insert,
                const std::string& where) {
    Value old{};
    const bool a =
        arena_.exchange(KeyOf(key).data(), value.data(), old.data(), insert);
    const auto at = model_.find(key);
    const bool held = at != model_.end();
    const bool ok =
        Agree(a == held, where, "exchange disagreed with the model") &&
        Agree(!a || old == at->second, where, "exchange returned other bytes");
    if (held || insert) model_[key] = value;
    return ok;
  }

  bool Contains(uint64_t key, const std::string& where) {
    const bool a = arena_.contains(KeyOf(key).data());
    return Agree(a == (model_.count(key) != 0), where,
                 "contains disagreed with the model");
  }

  // ONE BATCH THROUGH `access_batch`.  Every lane's `found` and previous value
  // is compared against the model, which is advanced lane by lane, in lane
  // order, because that is the order a batch's effects are defined in.
  struct Lane {
    oram::BatchOp op = oram::BatchOp::kRead;
    bool insert = false;
    uint64_t key = 0;
    Value value_in{};
  };

  bool Batch(const std::vector<Lane>& lanes, const std::string& where) {
    const size_t n = lanes.size();
    std::vector<Key> keys(n);
    std::vector<Value> out(n);
    std::vector<oram::BatchRequest> requests(n);
    for (size_t j = 0; j < n; ++j) {
      keys[j] = KeyOf(lanes[j].key);
      out[j].fill(0xA5);
      requests[j] = oram::BatchRequest{lanes[j].op, lanes[j].insert,
                                       keys[j].data(),
                                       lanes[j].value_in.data(), out[j].data()};
    }
    std::vector<uint8_t> found(n, 0);
    arena_.access_batch(n, requests.data(), found.data());
    for (size_t j = 0; j < n; ++j) {
      const auto at = model_.find(lanes[j].key);
      const bool held = at != model_.end();
      if (!Agree((found[j] != 0) == held, where,
                 "a batch lane disagreed with the model about presence") ||
          !Agree(!held || out[j] == at->second, where,
                 "a batch lane returned a value the model does not hold")) {
        return false;
      }
      switch (lanes[j].op) {
        case oram::BatchOp::kRead:
          break;
        case oram::BatchOp::kWrite:
          model_[lanes[j].key] = lanes[j].value_in;
          break;
        case oram::BatchOp::kErase:
          model_.erase(lanes[j].key);
          break;
        case oram::BatchOp::kExchange:
          if (held || lanes[j].insert) model_[lanes[j].key] = lanes[j].value_in;
          break;
      }
    }
    return true;
  }

  // Every key the model holds, and a band of keys it does not.
  bool Verify(uint64_t absent_from, const std::string& where) {
    for (const auto& entry : model_) {
      if (!Find(entry.first, where)) return false;
    }
    for (uint64_t k = absent_from; k < absent_from + 16; ++k) {
      if (model_.count(k) != 0) continue;
      if (!Find(k, where)) return false;
    }
    return true;
  }

  void Drain() { arena_.drain_rebuilds(); }

 private:
  bool Agree(bool ok, const std::string& where, const char* what) {
    if (ok) return true;
    Expect(false, where + ": " + what);
    return false;
  }

  oram::ByteMap<true> arena_;
  std::map<uint64_t, Value> model_;
};

// ---------------------------------------------------------------------------

// The capacity contract: the ladder covers the request, and the map reports
// the COMPLETE bill rather than its arenas.
void TestCapacityContract() {
  for (size_t requested : {size_t{100}, size_t{1000}, size_t{1} << 14}) {
    oram::ByteMap<true> map(requested, kKeyBytes, kValueBytes, ArenaOptions());
    Expect(map.requested_capacity() == requested,
           "the requested capacity was not kept");
    Expect(map.capacity() >= requested,
           "the rounded capacity does not cover the request");
    Expect(map.key_bytes() == kKeyBytes && map.value_bytes() == kValueBytes,
           "the public widths are not the ones asked for");
    // arena_bytes() is the COMPLETE bill, which is strictly more than the
    // level arenas: the contract is not to report the one as the other.
    Expect(map.arena_bytes() > map.main_arena_bytes(),
           "arena_bytes() is not the complete bill");
    Expect(map.byte_bill().requested() == map.arena_bytes(),
           "the bill and arena_bytes() disagree");
    Expect(map.byte_bill().reserved() >= map.byte_bill().requested(),
           "reserved bytes are below requested bytes");
    // The chosen geometry is public and is the one the engine was built at.
    Expect(map.geometry_choice().capacity == map.capacity(),
           "the ladder's capacity is not the engine's");
    Expect(map.geometry_choice().geometry.branching ==
               ArenaOptions().deamortized_branching_factor,
           "the ladder moved B, which is the caller's");
  }
  // The knobs that are refused rather than rounded.
  Expect(Throws([] {
           oram::ByteMap<true> m(0, kKeyBytes, kValueBytes, ArenaOptions());
         }),
         "a capacity of zero was accepted");
  Expect(Throws([] {
           oram::Options o = ArenaOptions();
           // not a whole number of buckets
           o.deamortized_online_stash_entries = 100;
           oram::ByteMap<true> m(1000, kKeyBytes, kValueBytes, o);
         }),
         "an insertion unit that is not a multiple of 64 was accepted");
  Expect(Throws([] {
           oram::Options o = ArenaOptions();
           o.max_accesses = 0;
           oram::ByteMap<true> m(1000, kKeyBytes, kValueBytes, o);
         }),
         "a zero request horizon was accepted");
  std::printf("  map: capacity, widths and the complete bill\n");
}

// Initialization: the map bulk-loaded from the records, then compared key by
// key against the model AND against the records that went in.
void TestInitialization() {
  constexpr size_t kRequested = 1 << 12;
  Lockstep pair(kRequested);
  const size_t count = kRequested / 2;
  pair.Load(count);
  // Every loaded key, with its value; and a band above the input that is not
  // held.
  if (!pair.Verify(count, "initialized")) return;
  // ...and the values are the ones the ITERATOR produced, read back directly
  // rather than through the model the load seeded.
  Value got{};
  for (uint64_t k = 0; k < count; k += 7) {
    Expect(pair.arena().find(KeyOf(k).data(), got.data()) && got == ValueOf(k),
           "an initialized key came back wrong at " + std::to_string(k));
    if (failures != 0) return;
  }
  // An initialized map keeps serving: the accesses after the load walk the
  // same hierarchy the load seeded.
  pair.Insert(count + 1, ValueOf(7));
  if (!pair.Verify(count + 2, "initialized, then written")) return;
  pair.Drain();
  if (!pair.Verify(count + 2, "initialized, written and drained")) return;
  std::printf("  map: %zu records initialized and read back in lockstep\n",
              count);
}

// Fill: write the map up to its requested capacity one access at a time and
// read everything back, then drain and read again.
void TestFill() {
  constexpr size_t kRequested = 1 << 11;
  Lockstep pair(kRequested);
  for (uint64_t k = 0; k < kRequested; ++k) {
    pair.Insert(k, ValueOf(k));
  }
  if (!pair.Verify(kRequested, "filled")) return;
  // A drain is a barrier, not a change of contents: the same answers before
  // and after is what makes it usable as one in a benchmark.
  pair.Drain();
  if (!pair.Verify(kRequested, "filled, drained")) return;
  std::printf("  map: %zu writes filled and verified, before and after a "
              "drain\n", size_t{kRequested});
}

// Steady state: a long mixed workload well past one capacity cycle, so that
// the top compacts several times and every level rebuilds under traffic.
void TestSteadyState() {
  constexpr size_t kRequested = 1 << 10;
  Lockstep pair(kRequested);
  for (uint64_t k = 0; k < kRequested / 2; ++k) pair.Insert(k, ValueOf(k));
  if (!pair.Verify(kRequested, "warmed")) return;

  std::mt19937_64 rng(0x5EED);
  const uint64_t span = kRequested;
  for (uint64_t i = 0; i < 6 * kRequested; ++i) {
    const uint64_t key = rng() % span;
    const std::string where = "steady state at access " + std::to_string(i);
    bool ok = true;
    switch (rng() % 5) {
      case 0: ok = pair.Find(key, where); break;
      case 1: ok = pair.Contains(key, where); break;
      case 2: ok = pair.Insert(key, ValueOf(rng())); break;
      case 3: ok = pair.Erase(key, where); break;
      default:
        ok = pair.Exchange(key, ValueOf(rng()), (i & 1) != 0, where);
        break;
    }
    if (!ok) return;
  }
  pair.Drain();
  if (!pair.Verify(span, "steady state, drained")) return;
  std::printf("  map: %zu mixed accesses over %zu keys, in lockstep\n",
              size_t{6 * kRequested}, size_t{span});
}

// The operations whose answers are easy to get subtly wrong, each exercised
// in both the present and the absent case.
void TestEveryOperation() {
  constexpr size_t kRequested = 1 << 10;
  Lockstep pair(kRequested);
  const uint64_t present = 11;
  const uint64_t absent = 999999;
  pair.Insert(present, ValueOf(present));

  // find, contains: present and absent.
  if (!pair.Find(present, "find present")) return;
  if (!pair.Find(absent, "find absent")) return;
  if (!pair.Contains(present, "contains present")) return;
  if (!pair.Contains(absent, "contains absent")) return;

  // exchange without insert on an absent key leaves it absent, and returns
  // false -- the one operation that reads and then deliberately does NOT
  // write.
  if (!pair.Exchange(absent, ValueOf(1), /*insert=*/false,
                     "exchange absent, no insert")) {
    return;
  }
  if (!pair.Find(absent, "after exchange without insert")) return;
  // ...with insert it becomes present.
  if (!pair.Exchange(absent, ValueOf(2), /*insert=*/true,
                     "exchange absent, insert")) {
    return;
  }
  if (!pair.Find(absent, "after exchange with insert")) return;
  // ...and on a present key it replaces and returns the old value.
  if (!pair.Exchange(present, ValueOf(3), /*insert=*/false,
                     "exchange present")) {
    return;
  }

  // erase: present, then the same key again.
  if (!pair.Erase(present, "erase present")) return;
  if (!pair.Erase(present, "erase the same key twice")) return;
  if (!pair.Find(present, "after erase")) return;

  // insert_without_probe skips the cascade, so it is checked by a subsequent
  // ordinary read.
  const uint64_t fresh = 4242;
  const Value value = ValueOf(fresh);
  pair.arena().insert_without_probe(KeyOf(fresh).data(), value.data());
  Value got{};
  Expect(pair.arena().find(KeyOf(fresh).data(), got.data()) && got == value,
         "an unprobed insert did not become visible");

  // The null-pointer refusals, which are the interface's own and not the
  // engine's.
  Expect(Throws([&] { pair.arena().find(nullptr, got.data()); }),
         "a null key was accepted");
  Expect(Throws([&] { pair.arena().find(KeyOf(1).data(), nullptr); }),
         "a null value_out was accepted");
  Expect(Throws([&] {
           pair.arena().insert_or_assign(KeyOf(1).data(), nullptr);
         }),
         "a null value was accepted");
  std::printf("  map: every public operation, present and absent\n");
}

// A drain does not wait for a carry that has not happened, and it keeps a
// speculatively prepared job rather than cancelling it (the drain contract).
void TestDrainContract() {
  constexpr size_t kRequested = 1 << 12;
  oram::ByteMap<true> map(kRequested, kKeyBytes, kValueBytes, ArenaOptions());
  for (uint64_t k = 0; k < kRequested / 4; ++k) {
    map.insert_or_assign(KeyOf(k).data(), ValueOf(k).data());
  }
  map.drain_rebuilds();
  // A second drain finds nothing to do: the first one completed every
  // accepted carry, so quiescence is a fixed point rather than a state the
  // hierarchy drifts out of on its own.
  const uint64_t sweeps = map.engine().sweeps();
  map.drain_rebuilds();
  Expect(map.engine().sweeps() <= sweeps + 1,
         "a second drain had work to do, so the first did not finish");

  // A DRAIN DOES NOT EMPTY THE HIERARCHY, and it is not supposed to: a
  // half-full level is waiting for carries only future accesses can produce.
  size_t with_partials = 0;
  size_t prepared = 0;
  for (unsigned l = 1; l <= map.engine().geometry().Levels(); ++l) {
    if (map.engine().level(l).has_partial()) ++with_partials;
    if (map.engine().level(l).prepared()) ++prepared;
  }
  Expect(with_partials > 0,
         "a drained hierarchy holds no partial table at all, so this workload "
         "did not reach the state the drain contract is about");
  // ...and where a level got ahead of its carry, the prepared job SURVIVES
  // the drain.  That is the half of the contract with a cost attached: the
  // alternative is cancelling it and re-routing the same older half at the
  // next carry.
  // Whether a level is prepared at this instant depends on where the workload
  // stopped, so what is pinned is the implication and not the count: nothing
  // drops a prepared job, and a prepared job still holds its destination.
  for (unsigned l = 1; l <= map.engine().geometry().Levels(); ++l) {
    if (!map.engine().level(l).prepared()) continue;
    Expect(map.engine().level(l).has_pending_job(),
           "a prepared level lost the job the preparation belongs to");
  }
  // The accesses after the drain use it and keep answering correctly, which
  // is what "retain that valid prepared job" has to mean in practice.
  for (uint64_t k = 0; k < kRequested / 4; ++k) {
    Value got{};
    Expect(map.find(KeyOf(k).data(), got.data()) && got == ValueOf(k),
           "a key was lost across a drain at " + std::to_string(k));
    if (failures != 0) return;
  }
  std::printf("  map: drain completes accepted work, keeps %zu prepared jobs "
              "and %zu partials\n", prepared, with_partials);
}

// ---------------------------------------------------------------------------

// THE BATCH SURFACE, in lockstep with the model's serial definition of
// the same interface.  The point of running it here rather than only in the
// engine's own fixture is that the public map must agree about what a BATCH
// means -- lane order, a write visible to a later lane's read, the previous
// value a write reports -- and not only about what a scalar operation means.
// The map carries the lane width and the participant count; the model runs
// the same lanes in order, which is precisely the definition it is held to.
void TestBatchSurface() {
  constexpr size_t kRequested = 1 << 11;
  // Chunked and parallel, and both result layouts the engine implements --
  // `kRows` is the reference and `kSlicedPlaceAtLane` is the default, so
  // running both against one oracle is what makes "it changes instruction
  // streams, never answers" a tested claim rather than a comment.
  for (BatchArms arms :
       {BatchArms{16, 1, false, oram::BatchResultLayout::kSlicedPlaceAtLane},
        BatchArms{16, 1, false, oram::BatchResultLayout::kRows},
        BatchArms{8, 3, true, oram::BatchResultLayout::kSlicedPlaceAtLane},
        BatchArms{8, 3, true, oram::BatchResultLayout::kRows}}) {
    Lockstep pair(kRequested, arms);
    Expect(pair.arena().batch_lanes() == arms.lanes,
           "the map did not take the lane width");
    Expect(pair.arena().batch_participants() == arms.participants,
           "the map did not take the participant count");
    for (uint64_t k = 0; k < kRequested / 2; ++k) pair.Insert(k, ValueOf(k));
    if (!pair.Verify(kRequested, "warmed")) return;

    // A mixed stream over a SMALL key span, so a chunk usually holds several
    // lanes of one key and the forwarding chain is exercised rather than
    // merely present.
    std::mt19937_64 rng(0xBA7C4 + arms.lanes);
    const uint64_t span = 64;
    for (unsigned round = 0; round < 24; ++round) {
      std::vector<Lockstep::Lane> lanes(37);
      for (size_t j = 0; j < lanes.size(); ++j) {
        const unsigned pick = static_cast<unsigned>(rng() % 10);
        lanes[j].op = pick < 4   ? oram::BatchOp::kRead
                      : pick < 7 ? oram::BatchOp::kWrite
                      : pick < 8 ? oram::BatchOp::kErase
                                 : oram::BatchOp::kExchange;
        lanes[j].insert = (rng() & 1) != 0;
        lanes[j].key = rng() % span;
        lanes[j].value_in = ValueOf(lanes[j].key * 131 + round);
      }
      if (!pair.Batch(lanes, "mixed batch")) return;
    }
    if (!pair.Verify(kRequested, "batched")) return;
    pair.Drain();
    if (!pair.Verify(kRequested, "batched, drained")) return;

    // The packed conveniences, which are the surface a caller actually uses.
    std::vector<uint8_t> keys(8 * kKeyBytes), values(8 * kValueBytes);
    std::vector<uint8_t> got(8 * kValueBytes), found(8, 0);
    for (uint64_t i = 0; i < 8; ++i) {
      const Key key = KeyOf(5000 + i);
      const Value value = ValueOf(5000 + i);
      std::memcpy(keys.data() + i * kKeyBytes, key.data(), kKeyBytes);
      std::memcpy(values.data() + i * kValueBytes, value.data(), kValueBytes);
    }
    pair.arena().insert_or_assign_batch(8, keys.data(), values.data());
    pair.arena().find_batch(8, keys.data(), got.data(), found.data());
    Expect(got == values, "find_batch did not return what insert_batch wrote");
    for (uint8_t f : found) Expect(f == 1, "find_batch missed a written key");
    pair.arena().erase_batch(8, keys.data(), found.data());
    for (uint8_t f : found) Expect(f == 1, "erase_batch missed a written key");
    pair.arena().find_batch(8, keys.data(), got.data(), found.data());
    for (uint8_t f : found) Expect(f == 0, "a key survived erase_batch");
    if (failures != 0) return;
  }
  std::printf("  map: the batch surface, chunked and parallel, both result "
              "layouts, in lockstep with the model\n");
}

// THE LADDER PRICED WHAT THE MAP BUILT.  The choice a caller can read back
// carries a bill, and the engine carries the bill its components actually
// allocated; if the two ever disagreed, every capacity report would be about
// a geometry nobody built.  The near/far boundary is the axis that could
// break it -- it changes the DIVISION of the levels, and the transient range
// scratch is sized per group -- so it is swept here rather than assumed.
void TestLadderPricesWhatItBuilds() {
  for (unsigned boundary : {0u, 1u, 2u, oram::kLevelArenaNearMaxLevelAuto}) {
    for (unsigned owners : {0u, 2u}) {
      oram::Options options = ArenaOptions(BatchArms{16, 3, true});
      options.deamortized_batch_bucket_scan = true;
      options.deamortized_near_max_level = boundary;
      options.deamortized_owner_threads = owners;
      oram::ByteMap<true> map(1 << 14, kKeyBytes, kValueBytes, options);
      Expect(map.geometry_choice().bill == map.byte_bill(),
             "the capacity ladder priced a different engine from the one it "
             "built");
      Expect(map.geometry_choice().candidates != 0,
             "the ladder compared no candidates, so the agreement above is "
             "vacuous");
      if (boundary == oram::kLevelArenaNearMaxLevelAuto) {
        Expect(map.geometry_choice().resolved_near_max_level >= 1,
               "the automatic boundary did not resolve to a level");
      }
      if (failures != 0) return;
    }
  }
  std::printf("  map: the ladder's bill is the engine's, at every near/far "
              "boundary\n");
}

// A THREAD BUDGET (deamortized_rebuild_threads): the map divides it with the
// heuristic on the geometry it chose, prices exactly what it builds, and
// refuses being handed the answer twice.  An explicit division
// (deamortized_level_groups) is built as given.
void TestRebuildBudget() {
  namespace la = microram::byteslice::levelarena;
  for (unsigned threads : {1u, 3u, 5u}) {
    oram::Options options = ArenaOptions();
    options.deamortized_branching_factor = 8;
    options.deamortized_rebuild_threads = threads;
    oram::ByteMap<true> map(1 << 16, kKeyBytes, kValueBytes, options);
    const la::LevelArenaCapacityChoice& choice = map.geometry_choice();
    const la::LevelArenaRebuildParams expected = la::HeuristicRebuildParams(
        la::LevelArenaGeometry(choice.geometry), choice.layout, {threads}, {},
        la::LevelResidualInputs{options.max_accesses});
    const la::LevelArenaEngine& engine = map.engine();
    const std::string where = std::to_string(threads) + " rebuild threads";
    Expect(engine.owner_groups() == expected.groups.size(),
           where + ": the map built another number of groups");
    for (size_t g = 0; g < expected.groups.size() && g < engine.owner_groups();
         ++g) {
      Expect(engine.owner_group(g).first == expected.groups[g].first &&
                 engine.owner_group(g).last == expected.groups[g].last,
             where + ": the map built another division");
    }
    Expect(engine.lane_config().lanes == expected.lanes.lanes,
           where + ": the map built other lanes");
    Expect(choice.bill == map.byte_bill(),
           where + ": the ladder priced another engine than it built");
    for (uint64_t i = 0; i < 3000; ++i) {
      const auto key = KeyOf(i % 211);
      const auto value = ValueOf(i % 211);
      map.insert_or_assign(key.data(), value.data());
    }
    map.drain_rebuilds();
    for (uint64_t i = 0; i < 211; ++i) {
      const auto key = KeyOf(i);
      Value got{};
      Expect(map.find(key.data(), got.data()) && got == ValueOf(i),
             where + ": a value was lost");
    }
    if (failures != 0) return;
  }
  Expect(Throws([] {
           oram::Options o = ArenaOptions();
           o.deamortized_rebuild_threads = 2;
           o.deamortized_top_helpers = 1;
           oram::ByteMap<true> m(1 << 12, kKeyBytes, kValueBytes, o);
         }),
         "a thread budget and explicit helpers were both accepted");
  // An explicit division: the top alone, everything else together -- the
  // simple top-down division, the natural comparison point for the
  // heuristic.
  oram::Options options = ArenaOptions();
  options.deamortized_owner_threads = 2;
  const unsigned levels =
      oram::ByteMap<true>::plan_geometry(1 << 14, kKeyBytes, kValueBytes,
                                         options)
          .geometry.levels;
  options.deamortized_level_groups = {la::LevelGroupPlan{levels, levels},
                                      la::LevelGroupPlan{1, levels - 1}};
  {
    oram::ByteMap<true> map(1 << 14, kKeyBytes, kValueBytes, options);
    Expect(map.engine().owner_group(0).first == levels &&
               map.engine().owner_group(1).last == levels - 1,
           "the map did not build the division it was given");
  }
  options.deamortized_owner_threads = 3;
  Expect(Throws([&] {
           oram::ByteMap<true> m(1 << 14, kKeyBytes, kValueBytes, options);
         }),
         "a division of the wrong size was accepted");
  std::printf("  map: a thread budget divided by the heuristic, an explicit "
              "division built as given\n");
}

// NO MORE THREADS THAN PHYSICAL CORES: the map cuts the top's helpers to the
// cores its caller, batch participants and owners leave, and keeps those.
void TestHelpersFitThePhysicalCores() {
  namespace mb = microram::byteslice;
  const unsigned cores = mb::HostPhysicalCores();
  Expect(cores >= 1 && cores <= std::max(1u, std::thread::hardware_concurrency()),
         "the physical core count is outside [1, logical CPUs]");
  Expect(mb::HelpersThatFit(5, 3, 16) == 5 && mb::HelpersThatFit(20, 3, 16) == 13 &&
             mb::HelpersThatFit(4, 16, 16) == 0 && mb::HelpersThatFit(4, 20, 16) == 0,
         "helpers must take exactly the cores the others leave");
  oram::Options options = ArenaOptions();
  options.deamortized_branching_factor = 8;
  options.deamortized_owner_threads = 2;
  options.deamortized_rebuild_lanes = 8;
  for (unsigned asked : {0u, 1u, cores + 5}) {
    options.deamortized_top_helpers = asked;
    const auto choice = oram::ByteMap<true>::plan_geometry(1 << 16, kKeyBytes,
                                                           kValueBytes, options);
    const auto engine = oram::detail::ArenaEngineOptions(choice, kKeyBytes,
                                                         kValueBytes, options);
    Expect(engine.owner_threads == 2 && engine.batch_participants == 1,
           "the cap moved the owners or the participants");
    Expect(engine.top_helpers == mb::HelpersThatFit(asked, 1 + 2, cores),
           "the top's helpers were not cut to the cores left");
    Expect(1 + engine.owner_threads + engine.top_helpers <=
               std::max(cores, 1u + engine.owner_threads),
           "the map would start more threads than physical cores");
  }
  std::printf("  map: top helpers cut to %u physical cores\n", cores);
}

void TestBinaryArena() {
  {
    for (unsigned owners : {0u, 2u}) {
      auto options = ArenaOptions();
      options.deamortized_branching_factor = 2;
      options.deamortized_owner_threads = owners;
      options.deamortized_top_digit = 2;
      options.deamortized_prefix_flushes = 2;
      oram::ByteMap<true> map(1 << 12, kKeyBytes, kValueBytes, options);
      const auto& choice = map.geometry_choice();
      Expect(choice.geometry.levels > 2,
             "the capacity search must build a binary hierarchy");
      Expect(choice.bill == map.byte_bill(),
             "the binary layout must price the actual allocations");
      for (uint64_t i = 0; i < 2200; ++i) {
        const auto key = KeyOf(i % 97);
        const auto value = ValueOf(i % 97);
        map.insert_or_assign(key.data(), value.data());
      }
      map.drain_rebuilds();
      for (uint64_t i = 0; i < 97; ++i) {
        const auto key = KeyOf(i);
        Value got{};
        Expect(map.find(key.data(), got.data()) && got == ValueOf(i),
               "the binary layout preserves values across threaded rebuilds");
      }
    }
  }
}

}  // namespace

int main() {
  std::printf("level arena: ByteMap<true>, the arena byte map\n");
  TestCapacityContract();
  TestHelpersFitThePhysicalCores();
  TestBinaryArena();
  TestInitialization();
  TestFill();
  TestSteadyState();
  TestEveryOperation();
  TestDrainContract();
  TestBatchSurface();
  TestLadderPricesWhatItBuilds();
  TestRebuildBudget();
  if (failures != 0) {
    std::fprintf(stderr, "%d arena map checks failed\n", failures);
    return 1;
  }
  std::printf("arena 11.6 map: OK\n");
  return 0;
}
