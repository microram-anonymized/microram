// Direct initialization of the level-arena engine (`Initialize`): build the
// top out of a batch of records instead of one online write per record, seed
// every other level's counters to the state an ordinary run would have
// reached, and carry on with no special case anywhere.
//
// THE REQUIREMENTS, and where each is checked:
//
//   - "initialized contents match ordinary insertion" -- TestMatchesOrdinary
//     compares an initialized engine against one filled by writes, by LOGICAL
//     VALUE and by WINDOW, never by nonce-dependent byte layout (the two are
//     under different families by construction, so their bytes cannot agree);
//   - "and remain correct through several subsequent carry boundaries" --
//     TestSurvivesCarryBoundaries keeps going for several top compactions'
//     worth of traffic, in lockstep with a std::map model;
//   - "validate the ladder against independent enumeration" --
//     TestSeedsAreReachable rebuilds the seeded state by RUNNING an ordinary
//     engine to the same point and compares every counter, rather than
//     comparing the seed formula with itself;
//   - "publish nothing until all records and metadata are valid; preserve
//     initialization rollback behavior" -- TestRollback throws from the
//     iterator at several points and checks the engine is untouched and a
//     retry works;
//   - "verify several carries after initialization to detect nonce reuse and
//     window-offset errors" -- every case here runs with the PROBE AUDIT
//     live, which is what turns a reused family into a failure rather than
//     into a plausible-looking trace.
//
// AND ONE LIMITATION: only kDistinct is implemented, which is
// the caller's promise that no stored key repeats.  TestRefusals pins that the
// other two policies are refused rather than quietly treated as distinct --
// a duplicate under kDistinct does not fail, it publishes the key twice.

#define MICRORAM_BYTESLICE_PROBE_AUDIT 1

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

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

constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;
constexpr size_t kValueBytes = 8;

la::LevelArenaEngine::Options MakeOptions(
    unsigned branching, unsigned levels, unsigned top_digit,
    unsigned prefix_flushes = 2,
    const std::vector<unsigned>& level_fanouts = {}) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = branching;
  options.geometry.levels = levels;
  options.geometry.top_digit = top_digit;
  options.geometry.prefix_flushes = prefix_flushes;
  options.geometry.level_fanouts = level_fanouts;
  options.geometry.stash_buckets = 1;
  options.geometry.dense_prefixes = 2;
  options.key_bytes = 8;
  options.value_bytes = kValueBytes;
  options.max_accesses = kMaxAccesses;
  // THE SETTLING EXECUTOR: every flush settles, so the hierarchy a fixture inspects
  // after an access is the one that access left, not a share of the way
  // there.  The default inline executor runs shares instead, and the
  // threads suite's agreement fixture holds it to the same drained state.
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kSettle;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(
      0x1417u + 31 * branching + 7 * levels + top_digit);
  return options;
}

// ---------------------------------------------------------------------------
// The input
// ---------------------------------------------------------------------------

// Key i has value f(i), in both engines, so "the same records" is one rule.
void ValueOf(uint64_t key, uint8_t* out) {
  uint64_t v = key * 0x9E3779B97F4A7C15ull + 0x1234567;
  std::memcpy(out, &v, kValueBytes);
}

// A single-pass input iterator over keys [0, count), exactly the contract
// Initialize states: dereference yields a record whose storage survives only
// until the increment, and nothing is replayed.
//
// `throw_at` is what TestRollback uses: the iterator raises at a chosen
// record, in the middle of the scatter, with the destination bank half
// written.
class Records {
 public:
  explicit Records(uint64_t first_key, size_t throw_at = ~size_t{0})
      : key_(first_key), throw_at_(throw_at) {}

  bs::InitializationEntry operator*() {
    if (index_ == throw_at_) throw std::runtime_error("the input failed");
    std::memcpy(key_bytes_, &key_, sizeof(key_));
    ValueOf(key_, value_bytes_);
    return bs::InitializationEntry{key_bytes_, value_bytes_};
  }
  Records& operator++() {
    ++key_;
    ++index_;
    return *this;
  }

 private:
  uint64_t key_;
  size_t index_ = 0;
  size_t throw_at_;
  uint8_t key_bytes_[8] = {};
  uint8_t value_bytes_[kValueBytes] = {};
};

// Every key the initialization wrote is present, with its value, and nothing
// else is.
void ExpectHolds(la::LevelArenaEngine& engine, uint64_t count,
                 uint64_t absent_from, const std::string& where) {
  uint8_t got[kValueBytes] = {};
  uint8_t want[kValueBytes] = {};
  for (uint64_t k = 0; k < count; ++k) {
    const bool found = engine.Read(k, got);
    ValueOf(k, want);
    if (!found || std::memcmp(got, want, kValueBytes) != 0) {
      Expect(false, where + ": key " + std::to_string(k) +
                        (found ? " has the wrong value" : " is missing"));
      return;
    }
  }
  for (uint64_t k = absent_from; k < absent_from + 32; ++k) {
    if (engine.Read(k, got)) {
      Expect(false, where + ": key " + std::to_string(k) +
                        " is present and was never written");
      return;
    }
  }
}

// ---------------------------------------------------------------------------

// The contents an initialization publishes are the contents ordinary writes
// would have left, and the cascade sees them in the same PLACE in probe order.
void TestMatchesOrdinary() {
  const la::LevelArenaEngine::Options options = MakeOptions(4, 3, 4);
  la::LevelArenaEngine initialized(options);
  const uint64_t count = initialized.Capacity() / 2;
  initialized.Initialize(Records(0), static_cast<size_t>(count));
  // AND THE INITIALIZED COUNTERS DO NOT DEPEND ON `count`.  The top is
  // published at its full digit whatever the input length is, so the state it
  // stands for is a WHOLE capacity cycle -- H prefixes -- and not `count`
  // writes.  That is deliberate: the arena shape after an initialization then
  // reveals only the record count the caller already knew.  Read BEFORE the
  // lookups below, which are themselves accesses and move the counter.
  const la::InitialSeed seed =
      la::DirectInitializationSeed(initialized.geometry());
  Expect(initialized.dense().positions() == seed.access_offset,
         "an initialized engine's access offset is not a whole cycle's");
  Expect(initialized.dense().flushes() == seed.stash_flushes,
         "an initialized engine's flush count is not a whole cycle's");
  ExpectHolds(initialized, count, count, "initialized");

  // The same records, written one access at a time into an engine of the same
  // shape.  Its byte layout differs -- the two are under different nonce
  // families by construction -- so what is compared is the LOGICAL answer and
  // the probe order, which is what the requirement asks for.
  la::LevelArenaEngine written(options);
  uint8_t value[kValueBytes] = {};
  for (uint64_t k = 0; k < count; ++k) {
    ValueOf(k, value);
    written.Write(k, value);
  }
  written.Drain();
  ExpectHolds(written, count, count, "written");

  // The top holds everything in both, so both cascades are the top plus the
  // dense prefix the requester is assembling -- the initialized one having
  // reached it in one step.
  Expect(initialized.publisher().live_count() == 1,
         "an initialized engine publishes the top and nothing else");
  Expect(seed.access_offset > count,
         "a half-full initialization did not jump the counters past the "
         "writes that would have filled the same keys one at a time");
  std::printf("  initialization: %llu records match ordinary insertion\n",
              static_cast<unsigned long long>(count));
}

// The seeded counters are the ones an ordinary run reaches, checked by RUNNING
// one there rather than by re-deriving the formula.
void TestSeedsAreReachable() {
  // THE MIXED LADDERS ARE HERE AND NOT ONLY IN THE GEOMETRY TEST, because
  // this is the fixture that compares the seed against a real run: H is
  // D * prod(b_l) and level l's seeded carry count is H / prod(b_j, j < l),
  // so a ladder whose fanouts differ is the only shape in which a `B` left
  // where a `b_l` belongs produces a seed that is merely WRONG rather than
  // obviously wrong.  A run that then disagrees is the check.
  struct Shape {
    unsigned branching, levels;
    std::vector<unsigned> fanouts;
  };
  const Shape shapes[] = {
      {2, 3, {}}, {4, 3, {}}, {4, 3, {2, 4}}, {4, 4, {4, 2, 4}},
  };
  for (const Shape& shape : shapes) {
    const unsigned branching = shape.branching;
    for (unsigned digit : {1u, 2u, 4u}) {
      if (digit > branching) continue;  // the top is no wider than B
      const la::LevelArenaEngine::Options options =
          MakeOptions(branching, shape.levels, digit, 2, shape.fanouts);
      la::LevelArenaEngine engine(options);
      const la::InitialSeed seed =
          la::DirectInitializationSeed(engine.geometry());

      // The run: fill the engine exactly once, which is 32T entries, i.e.
      // H complete prefixes.  Its counters are what the seed claims.
      la::LevelArenaEngine run(options);
      uint8_t value[kValueBytes] = {};
      for (uint64_t k = 0; k < run.Capacity(); ++k) {
        ValueOf(k, value);
        run.WriteWithoutProbe(k, value);
      }
      run.Drain();
      Expect(run.dense().flushes() == seed.stash_flushes,
             "the seeded flush count is not the one a full cycle reaches");
      Expect(run.dense().positions() == seed.access_offset,
             "the seeded access offset is not the one a full cycle reaches");
      for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
        Expect(run.level(l).ordinal() == seed.level_carries[l],
               "level " + std::to_string(l) +
                   "'s seeded carry count is not the one a full cycle reaches");
      }

      // ...and an initialization puts the engine there in one step.
      engine.Initialize(Records(0), 1);
      Expect(engine.dense().flushes() == seed.stash_flushes,
             "initialization did not seed the flush count");
      Expect(engine.dense().positions() == seed.access_offset,
             "initialization did not seed the access offset");
      for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
        Expect(engine.level(l).ordinal() == seed.level_carries[l],
               "initialization did not seed level " + std::to_string(l));
        // Every non-top level holds no partial, which is what "all non-top
        // digits are zero" means in storage rather than in arithmetic.
        Expect(l == engine.geometry().Levels() ||
                   !engine.level(l).has_partial(),
               "a seeded non-top level holds a partial table");
      }
      Expect(engine.level(engine.geometry().TopLevel()).ordinal() ==
                 engine.geometry().TopDigit(),
             "the initialized top has not accepted D carries");
    }
  }
  std::printf("  initialization: every seeded counter is one a run reaches\n");
}

// Several carry boundaries past the initialization, in lockstep with a
// std::map model of the contents.  This is where a reused nonce family or a window off by one
// prefix shows up: the audit fires, or the cascade starts answering with the
// wrong copy of a key.
void TestSurvivesCarryBoundaries() {
  const la::LevelArenaEngine::Options options = MakeOptions(4, 3, 2);
  la::LevelArenaEngine engine(options);
  const uint64_t count = engine.Capacity() / 4;
  engine.Initialize(Records(0), static_cast<size_t>(count));

  // The oracle starts where the initialization left the engine, by ordinary
  // writes: it is a model of the CONTENTS, not of the schedule.
  std::map<uint64_t, std::vector<uint8_t>> model;
  uint8_t value[kValueBytes] = {};
  for (uint64_t k = 0; k < count; ++k) {
    ValueOf(k, value);
    model[k].assign(value, value + kValueBytes);
  }

  // Enough traffic to carry into the top several times: one top compaction is
  // Capacity() / D accesses.
  const uint64_t top_period = engine.Capacity() / options.geometry.top_digit;
  const uint64_t accesses = 3 * top_period;
  std::mt19937_64 rng(0xB0A7);
  const int before = failures;  // this loop's own, not the suite's so far
  const uint64_t span = count * 2;
  uint8_t got[kValueBytes] = {};
  for (uint64_t i = 0; i < accesses; ++i) {
    const uint64_t key = rng() % span;
    switch (rng() % 4) {
      case 0: {
        const bool found = engine.Read(key, got);
        const auto at = model.find(key);
        Expect(found == (at != model.end()),
               "a read disagreed with the model at access " +
                   std::to_string(i));
        if (found && at != model.end()) {
          Expect(std::memcmp(got, at->second.data(), kValueBytes) == 0,
                 "a read returned the wrong value at access " +
                     std::to_string(i));
        }
        break;
      }
      case 1:
      case 2: {
        uint64_t v = rng();
        std::memcpy(value, &v, kValueBytes);
        engine.Write(key, value);
        model[key].assign(value, value + kValueBytes);
        break;
      }
      default: {
        const bool erased = engine.Erase(key);
        Expect(erased == (model.erase(key) != 0),
               "an erase disagreed with the model at access " +
                   std::to_string(i));
        break;
      }
    }
    if (failures != before) break;
  }
  engine.Drain();
  Expect(engine.ProbeAuditViolations() == 0,
         "the probe audit saw a family probed twice for one key after an "
         "initialization");
  Expect(engine.level(engine.geometry().TopLevel()).ordinal() >
             options.geometry.top_digit,
         "the run did not reach a top compaction past the initialized one");
  std::printf("  initialization: correct through %llu accesses and %llu top "
              "carries\n",
              static_cast<unsigned long long>(accesses),
              static_cast<unsigned long long>(
                  engine.level(engine.geometry().TopLevel()).ordinal()));
}

// An iterator that throws leaves nothing published and a retry works.
void TestRollback() {
  const la::LevelArenaEngine::Options options = MakeOptions(4, 3, 2);
  const uint64_t probe_count = la::LevelArenaEngine(options).Capacity() / 2;
  for (size_t throw_at : {size_t{0}, size_t{1},
                          static_cast<size_t>(probe_count / 2)}) {
    la::LevelArenaEngine engine(options);
    const size_t count = static_cast<size_t>(engine.Capacity() / 2);
    Expect(Throws([&] { engine.Initialize(Records(0, throw_at), count); }),
           "an iterator that threw was swallowed");
    // Untouched: the empty top is still the only live table, and nothing has
    // been counted.
    Expect(engine.publisher().live_count() == 1,
           "a failed initialization published something");
    Expect(engine.dense().positions() == 0 && engine.dense().flushes() == 0,
           "a failed initialization moved the requester's counters");
    for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
      Expect(engine.level(l).ordinal() == 0,
             "a failed initialization seeded a level");
    }
    // ...and a retry is legal and correct, which is the point of the
    // rollback: a caller whose input stream hiccuped has not lost the engine.
    engine.Initialize(Records(0), count);
    ExpectHolds(engine, count, count, "after a rolled-back attempt");
  }
  std::printf("  initialization: a throwing input rolls back and a retry "
              "works\n");
}

// The refusals, each of which is a state where the seeded counters would be a
// lie rather than a reachable state.
void TestRefusals() {
  const la::LevelArenaEngine::Options options = MakeOptions(4, 3, 2);
  {
    la::LevelArenaEngine engine(options);
    Expect(Throws([&] {
             engine.Initialize(Records(0), 8,
                               bs::InitializationPolicy::kFirstWins);
           }),
           "a duplicate-resolving policy was accepted");
    Expect(Throws([&] {
             engine.Initialize(Records(0), 8,
                               bs::InitializationPolicy::kLastWins);
           }),
           "a duplicate-resolving policy was accepted");
    Expect(Throws([&] {
             engine.Initialize(Records(0),
                               static_cast<size_t>(engine.Capacity() + 1));
           }),
           "a count above Capacity() was accepted");
    // Refused, and the refusals left the engine initializable.
    engine.Initialize(Records(0), 64);
    Expect(Throws([&] { engine.Initialize(Records(0), 64); }),
           "a second initialization was accepted");
  }
  {
    // After an access, the counters an initialization would seed are no
    // longer the ones the run has reached.
    la::LevelArenaEngine engine(options);
    uint8_t value[kValueBytes] = {};
    ValueOf(1, value);
    engine.Write(1, value);
    Expect(Throws([&] { engine.Initialize(Records(0), 64); }),
           "an initialization after an access was accepted");
  }
  {
    // Empty input is a no-op, and the engine stays initializable.
    la::LevelArenaEngine engine(options);
    engine.Initialize(Records(0), 0);
    Expect(engine.dense().positions() == 0 && engine.dense().flushes() == 0,
           "an empty initialization moved the counters");
    engine.Initialize(Records(0), 64);
    ExpectHolds(engine, 64, 64, "after an empty initialization");
  }
  {
    // With owner threads: refused, because "this engine is untouched" is not
    // a property one thread can establish about storage several are driving.
    la::LevelArenaEngine::Options threaded = options;
    threaded.owner_threads = 2;
    la::LevelArenaEngine engine(threaded);
    Expect(Throws([&] { engine.Initialize(Records(0), 64); }),
           "an initialization with owner threads was accepted");
  }
  std::printf("  initialization: policy, count, repeat, lateness and threads "
              "are refused\n");
}

// A full table, at several shapes: the load the scatter writes at is the one
// the top routes at, so `count == Capacity()` has to fit exactly.
void TestFullAndEdgeShapes() {
  for (unsigned branching : {2u, 4u, 8u}) {
    for (unsigned digit : {1u, 2u, 4u}) {
      if (digit > branching) continue;  // the top is no wider than B
      const la::LevelArenaEngine::Options options =
          MakeOptions(branching, 3, digit, 2,
                      branching == 2 ? std::vector<unsigned>{}
                                     : std::vector<unsigned>{2, branching});
      la::LevelArenaEngine engine(options);
      const size_t count = static_cast<size_t>(engine.Capacity());
      engine.Initialize(Records(0), count);
      ExpectHolds(engine, count, count, "a full initialized table");
      Expect(engine.ProbeAuditViolations() == 0,
             "the probe audit fired on a full initialized table");
      if (failures != 0) return;
    }
  }
  std::printf("  initialization: full tables at B in {2,4,8}, D in "
              "{1,2,4} up to B, trimmed bottom where B > 2\n");
}

// The top preparation's one-page DFS distributor through direct publication,
// at B = 8 where its pool routes, then read across online carry boundaries.
// Include empty, partial and full input.
void TestDfsInitialization() {
  for (unsigned digit : {1u, 2u, 4u, 8u}) {
    for (unsigned load : {0u, 1u, 2u}) {
      const auto options = MakeOptions(8, 3, digit, 2);
      la::LevelArenaEngine engine(options);
      const size_t count = load * engine.Capacity() / 2;
      engine.Initialize(Records(0), count);
      ExpectHolds(engine, count, count, "DFS initialization");
      Expect(engine.ProbeAuditViolations() == 0, "DFS initialization placement");
    }
  }
}

// The absent older tier still participates as a zero-masked source. Its
// borrowed backing must cover the maximum tier on the smallest top shape.
void TestWideTierInitialization() {
  auto options = MakeOptions(2, 2, 1, 2);
  options.geometry.tier_buckets = bs::kMaxResidualStashBuckets;
  la::LevelArenaEngine engine(options);
  const size_t count = static_cast<size_t>(engine.Capacity());
  engine.Initialize(Records(0), count);
  ExpectHolds(engine, count, count, "wide-tier initialization");
}

}  // namespace

int main() {
  std::printf("level arena: direct initialization\n");
  TestMatchesOrdinary();
  TestSeedsAreReachable();
  TestSurvivesCarryBoundaries();
  TestRollback();
  TestRefusals();
  TestFullAndEdgeShapes();
  TestWideTierInitialization();
  TestDfsInitialization();
  if (failures != 0) {
    std::fprintf(stderr, "%d initialization checks failed\n", failures);
    return 1;
  }
  std::printf("level arena 11.6 initialization: OK\n");
  return 0;
}
