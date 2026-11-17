// The publication layer and the deterministic all-level executor of the
// level-arena engine (src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp):
// an engine that probes, inserts and drives every level itself, with one
// immutable probe PLAN (the ordered list of published tables a request
// probes) swapped atomically under a reader EPOCH protocol: a request holds
// the epoch while it reads the plan, and storage a publication retired is
// reclaimed only after every reader that could still name it has left.  The
// vocabulary -- prefix, carry, digit, adoption, inbox, lease, bank, tier,
// nonce family -- is defined in src/oram/levelarena/DESIGN.md.
//
// WHAT THE OTHER FIXTURES ESTABLISH, and therefore what this one does not
// repeat.  cpu_byteslice_level_arena_job_test and _top_test drive one merge
// at a time over real arena slots and compare its output, main plus tier,
// against a key/value model; _lifecycle_test drives the slot lifecycle and
// the boundary rings on two threads.  What none of them has is an ENGINE:
// composing a probe plan, retiring a source against a reader epoch, adopting
// a carry in place, or answering a request.  That is this file.
//
// THE CLAIMS:
//
//   - a publication is one transaction over the LATEST live set, so two
//     independently completed deltas both land, a same-family removal and
//     addition cross in one swap, and a removal of something that is not live
//     is refused rather than silently dropped;
//   - the plan-record pool is bounded, exhaustion REFUSES rather than
//     overwriting a plan a reader is inside, and reclamation recovers it;
//   - the dense ring assembles units into prefixes, keeps at most q of them
//     outstanding, and hands a consumed one back only when the REQUESTER says
//     its readers are gone;
//   - a level adopts or installs digit 1 according to its arena policy,
//     merges other digits, and reports what it is blocked on;
//   - a held reader pins what a publication retired: the bytes are unchanged,
//     the slots stay unreclaimed, and releasing the reader recovers them;
//   - and the whole thing answers Read/Write/Erase/Exchange, present and
//     absent, exactly as a std::map model does;
//   - a level-1 step that throws after taking its prefix merges THAT prefix
//     when it runs again, and the inline executor latches the failure, so no
//     later access answers from the state it left;
//   - every table built in a forwarding lease starts from an empty tier, even
//     though one lease holds P_2, P_4, ... in turn, so a forced leftover of an
//     earlier partial never reappears as a stale value or an erased key;
//   - every level's next-job deadline follows the buffer protocol at every
//     ordinal, and the top's is never a middle level's short window,
//     whatever D is;
//   - the cascade's main/tier groups answer and find tombstones as a std::map
//     model and the planted flags say, access for access, over seeded tiers,
//     with and without value workers; and a tier hit turns the tables below
//     it dummy without keeping its own family real once a fresher copy
//     exists.
//
// EVERY CASE RUNS WITH THE PROBE AUDIT LIVE, so "at most one real probe per
// (nonce family, key)" is checked over every handoff these runs perform.
// That is the obliviousness invariant: a nonce family (the tables hashed
// under one nonce, which spans a producer's publication, its consumer's
// adoption and that consumer's own full table) must never be probed for real
// twice for one key, or two accesses to the same key would touch the same
// bucket and reveal the repetition.

#define MICRORAM_BYTESLICE_PROBE_AUDIT 1
// For the fault injection of a failing step alone: the hook stays null
// otherwise.
#define MICRORAM_BYTESLICE_LEVEL_ARENA_PAUSE 1

#include <immintrin.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
namespace ts = microram::byteslice::test_support;

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

// The request horizon every geometry here is certified for.
constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

la::LevelArenaEngine::Options MakeOptions(unsigned branching, unsigned levels,
                                          unsigned top_digit,
                                          unsigned prefix_flushes = 2,
                                          size_t stash_buckets = 1,
                                          unsigned dense_prefixes = 2) {
  la::LevelArenaEngine::Options options;
  options.geometry.branching = branching;
  options.geometry.levels = levels;
  options.geometry.top_digit = top_digit;
  options.geometry.prefix_flushes = prefix_flushes;
  options.geometry.stash_buckets = stash_buckets;
  options.geometry.dense_prefixes = dense_prefixes;
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.max_accesses = kMaxAccesses;
  // THE SETTLING EXECUTOR: every flush settles, so the hierarchy a fixture inspects
  // after an access is the one that access left, not a share of the way
  // there.  The default inline executor runs shares instead, and the
  // threads suite's agreement fixture holds it to the same drained state.
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kSettle;
  // Fixed, so that a failure is reproducible: the tag PRF's key is the
  // per-ORAM secret and every bucket an entry lands in is a function of it.
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(
      0x1E5E10ull + 31 * branching + 7 * levels + top_digit);
  return options;
}

// A cheap digest of a table's bytes and masks: what a publication retired
// must still read the same to a reader that is inside the plan naming it.
uint64_t DigestTable(const la::PublishedTable& t, const bs::Layout& layout) {
  uint64_t h = ts::DigestBytes(t.data, t.main_buckets * layout.BucketBytes());
  for (size_t b = 0; b < t.main_buckets; ++b) {
    h = (h ^ t.masks[b]) * 0x100000001b3ull;
  }
  h ^= ts::DigestBytes(t.tier_data, t.tier_buckets * layout.BucketBytes());
  for (size_t b = 0; b < t.tier_buckets; ++b) {
    h = (h ^ t.tier_masks[b]) * 0x100000001b3ull;
  }
  return h;
}

// ---------------------------------------------------------------------------
// The publisher on its own
// ---------------------------------------------------------------------------
//
// A hand-built live set, so that a delta can be exhibited rather than
// provoked: the engine has no way to publish a malformed plan, which is
// exactly why the refusals need a fixture that can.

struct FakeStorage {
  std::vector<uint8_t> main;
  std::vector<uint64_t> masks;
  std::vector<uint8_t> tier;
  std::vector<uint64_t> tier_masks;
};

class PublisherFixture {
 public:
  explicit PublisherFixture(size_t prefix_slots = 4, size_t arena_slots = 8,
                            size_t dense_slots = 3) {
    la::LevelArenaPublisher::Config config;
    config.prefix_slots = prefix_slots;
    config.arena_slots = arena_slots;
    config.dense_slots = dense_slots;
    config.owner_threads = 1;
    publisher_ = std::make_unique<la::LevelArenaPublisher>(config);
  }

  la::LevelArenaPublisher& publisher() { return *publisher_; }

  // A well-formed table of `buckets` buckets owning [begin, end), in family
  // (level, ordinal).  The storage is the fixture's; nothing probes it.
  la::PublishedTable Make(unsigned level, uint64_t ordinal, uint64_t begin,
                          uint64_t end, unsigned slot, size_t buckets = 2,
                          unsigned index_bits = 1, unsigned radix = 1) {
    storage_.push_back(std::make_unique<FakeStorage>());
    FakeStorage& s = *storage_.back();
    s.main.assign(buckets * 64, 0);
    s.masks.assign(buckets, 0);
    s.tier.assign(64, 0);
    s.tier_masks.assign(1, 0);
    la::PublishedTable table;
    publisher_->AllocateTableIds(&table.table_id, &table.tier_table_id);
    table.family = la::Family{level, ordinal};
    table.family_id = la::FamilyId(table.family);
    table.nonce = la::FamilyNonce(table.family);
    table.window_begin = begin;
    table.window_end = end;
    table.owner = level;
    table.slot = slot;
    table.generation = 1;
    table.main_buckets = buckets;
    table.index_bits = index_bits;
    table.radix = radix;
    table.data = s.main.data();
    table.masks = s.masks.data();
    table.tier_data = s.tier.data();
    table.tier_masks = s.tier_masks.data();
    table.tier_buckets = 1;
    return table;
  }

 private:
  std::unique_ptr<la::LevelArenaPublisher> publisher_;
  std::vector<std::unique_ptr<FakeStorage>> storage_;
};

void TestPublicationTransactions() {
  PublisherFixture fixture;
  la::LevelArenaPublisher& publisher = fixture.publisher();

  // The floor: one table whose window begins at 0, which every laminar plan
  // needs (PlanWindowsLaminar's last condition).
  const la::PublishedTable floor = fixture.Make(3, 1, 0, 1, 0);
  {
    la::PublicationDelta delta;
    delta.Add(floor);
    publisher.Publish(delta);
  }
  Expect(publisher.live_count() == 1,
         "the first publication did not install its table");
  Expect(publisher.CurrentPlan() != nullptr,
         "no plan was installed");

  // ONLY THE FIRST publication may add without removing: the plan-record bound
  // rests on every later one retiring a slot with the same threshold as the
  // plan it replaces.
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 1, 8, 16, 1));
    Expect(Throws([&] { publisher.Publish(delta); }),
           "an add-only publication after the first was accepted, which the "
           "pool bound does not cover");
  }

  // Two tables at level 1, published one after the other, each removing the
  // previous: this is the ordinary shape.
  la::PublishedTable a = fixture.Make(1, 1, 0, 8, 1);
  {
    la::PublicationDelta delta;
    delta.Add(a);
    delta.ConsumePrefixes(1);
    publisher.Publish(delta);
  }
  la::PublishedTable b = fixture.Make(1, 2, 8, 16, 2);
  {
    la::PublicationDelta delta;
    delta.Add(b);
    delta.ConsumePrefixes(2);
    publisher.Publish(delta);
  }
  Expect(publisher.live_count() == 3,
         "two level-1 tables and the floor should be live");

  // TWO INDEPENDENTLY COMPLETED DELTAS against ONE latest plan.  The second is
  // composed from a snapshot taken BEFORE the first landed and still resolves,
  // because a removal names an immutable identity rather than a position.
  const std::vector<la::PublishedTable> before = publisher.LiveTables();
  la::PublishedTable c = fixture.Make(1, 3, 16, 24, 3);
  {
    la::PublicationDelta first;
    first.Add(c);
    first.Remove(a.table_id);
    first.ConsumePrefixes(3);
    publisher.Publish(first);
  }
  la::PublishedTable d = fixture.Make(2, 1, 8, 24, 4, 4, 2);
  {
    la::PublicationDelta second;  // planned against `before`
    second.Add(d);
    second.Remove(b.table_id);
    second.Remove(c.table_id);
    publisher.Publish(second);
  }
  Expect(publisher.IsLive(d.table_id) && !publisher.IsLive(b.table_id) &&
             !publisher.IsLive(c.table_id) && !publisher.IsLive(a.table_id),
         "two independently completed deltas did not both land against the "
         "latest live set");

  // A removal the latest plan does not hold is refused, and the live set is
  // left as it was.
  {
    const size_t live = publisher.live_count();
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 4, 24, 32, 5));
    delta.Remove(b.table_id);  // already gone
    Expect(Throws([&] { publisher.Publish(delta); }),
           "a removal of a table that is not live was accepted");
    Expect(publisher.live_count() == live,
           "a refused publication changed the live set");
  }

  // SAME-FAMILY REMOVAL AND ADDITION: a merge at digit B removes the
  // fresh carry and exposes its same-family output in one swap, so the plan
  // never holds two members of one family and the audit's history is never
  // dropped.  A plan that held both is refused.
  {
    const la::PublishedTable same = fixture.Make(2, 1, 8, 24, 6, 4, 2);
    la::PublicationDelta delta;
    delta.Add(same);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "two members of one nonce family were published together");
    la::PublicationDelta swap;
    swap.Add(same);
    swap.Remove(d.table_id);
    swap.ConsumePrefixes(4);
    swap.prefixes_consumed = 4;
    swap.consume_prefixes = true;
    publisher.Publish(swap);
    Expect(publisher.IsLive(same.table_id) && !publisher.IsLive(d.table_id),
           "a same-family removal and addition did not cross in one swap");
  }

  // A crossing window is refused: there is then no order in which "the first
  // table that has the key has the freshest copy" holds.
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 9, 12, 20, 7));  // crosses [8, 24)
    delta.Remove(floor.table_id);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "a crossing window was published");
  }
  // And a mixed-radix table whose public shape is not r << index_bits.
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 10, 24, 32, 7, /*buckets=*/5, /*index_bits=*/1,
                           /*radix=*/3));
    delta.Remove(floor.table_id);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "a mixed-radix table with an inconsistent public shape was "
           "published");
  }
  // AN EMPTY OR INVERTED WINDOW, INCLUDING THE ONES THAT END AT ZERO.  [0, 0)
  // is the window an empty top would have and [b, 0) is a transposed pair.
  // PlanWindowsLaminar downstream would also refuse them, but only
  // incidentally: its loop stops one entry short of the end, so what rejects
  // an empty LAST window there is only that a main is always followed by its
  // own tier.  These cases pin the refusal to the publication's own addition
  // check, so that the laminar predicate's gap is never load bearing.
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 11, 0, 0, 7));
    delta.Remove(floor.table_id);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "an empty window [0, 0) was published");
  }
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 12, 40, 0, 7));
    delta.Remove(floor.table_id);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "an inverted window ending at zero was published");
  }
  {
    la::PublicationDelta delta;
    delta.Add(fixture.Make(1, 13, 40, 40, 7));
    delta.Remove(floor.table_id);
    Expect(Throws([&] { publisher.Publish(delta); }),
           "an empty window was published");
  }
  Expect(publisher.IsLive(floor.table_id),
         "a refused publication took the floor out of the live set");
}

// BOUNDED PLAN EXHAUSTION AND RECOVERY.  With a reader inside, nothing
// retires, so the pool drains one record per publication; the publisher must
// REFUSE rather than overwrite a plan the reader may be probing, and the
// records must come back once the reader leaves.
void TestPlanPoolExhaustionAndRecovery() {
  PublisherFixture fixture(/*prefix_slots=*/4, /*arena_slots=*/4,
                           /*dense_slots=*/2);
  la::LevelArenaPublisher& publisher = fixture.publisher();
  const size_t pool = publisher.pool_slots();
  Expect(pool == 4 + 2 + 1 + 1,
         "the pool is slots + dense slots + current + one staging record");

  la::PublishedTable live = fixture.Make(3, 1, 0, 1, 0);
  {
    la::PublicationDelta delta;
    delta.Add(live);
    publisher.Publish(delta);
  }

  size_t published = 1;
  const bs::Layout layout;
  {
    la::ReaderEpoch::Guard guard(publisher.epoch());
    const microram::byteslice::ProbePlan* held = publisher.CurrentPlan();
    const size_t held_tables = held->tables.size();
    uint64_t ordinal = 2;
    while (publisher.CanPublish()) {
      la::PublishedTable next = fixture.Make(3, ordinal, 0, 1, 0);
      la::PublicationDelta delta;
      delta.Add(next);
      delta.Remove(live.table_id);
      publisher.Publish(delta);
      live = next;
      ++ordinal;
      ++published;
      // Reclamation cannot help while this reader is inside: the threshold on
      // everything retired is e + 1 and the observed epoch is e.
      publisher.ReclaimPlans(publisher.epoch().Observed());
    }
    Expect(published > 1 && published <= pool,
           "the pool drained in a number of publications outside its own "
           "bound");
    la::PublicationDelta over;
    over.Add(fixture.Make(3, ordinal, 0, 1, 0));
    over.Remove(live.table_id);
    Expect(Throws([&] { publisher.Publish(over); }),
           "an exhausted plan pool did not refuse; a record a reader is inside "
           "would have been reused");
    // The plan this reader holds is intact, which is the whole point of
    // refusing.
    Expect(held->tables.size() == held_tables &&
               publisher.CurrentPlan() != held,
           "the held plan was recycled under its reader");
    (void)layout;
  }
  Expect(publisher.ReclaimPlans(publisher.epoch().Observed()) > 0,
         "the pool did not recover once the reader left");
  Expect(publisher.CanPublish(),
         "the publisher could not publish again after reclamation");
}

// ---------------------------------------------------------------------------
// The dense prefix ring on its own
// ---------------------------------------------------------------------------

void TestDensePrefixRing() {
  la::LevelArenaGeometry::Params params;
  params.branching = 2;
  params.levels = 2;
  params.top_digit = 1;
  params.prefix_flushes = 2;  // r0
  params.stash_buckets = 1;   // s
  params.dense_prefixes = 2;  // q
  const la::LevelArenaGeometry geometry(params);
  const bs::Layout layout;
  la::DensePrefixRing ring(geometry, layout);

  Expect(ring.plan_prefix_slots() == params.dense_prefixes + 2,
         "the plan reserves the current unit, the frozen part of the prefix "
         "being assembled, and q complete prefixes");
  Expect(ring.ring_slots() == params.dense_prefixes + 1,
         "the ring is q complete prefixes plus the one being assembled");

  std::vector<uint8_t> value(layout.value_bytes - 1, 7);
  const auto fill_unit = [&](uint64_t first_key) {
    for (size_t i = 0; i < ring.unit_entries(); ++i) {
      ring.Insert(bs::KeyWords{first_key + i}, value.data(), true, false,
                  false);
    }
  };

  // q complete prefixes and one being assembled is exactly the ring; the next
  // unit that would complete a prefix is refused until one is reclaimed.
  uint64_t key = 1;
  for (unsigned p = 0; p < params.dense_prefixes; ++p) {
    for (unsigned u = 0; u < params.prefix_flushes; ++u) {
      Expect(ring.CanFreezeUnit(), "a unit inside the ring's bound was refused");
      fill_unit(key);
      key += ring.unit_entries();
      ring.FreezeUnit();
    }
  }
  Expect(ring.complete_prefixes() == params.dense_prefixes,
         "the ring did not complete q prefixes");
  fill_unit(key);
  key += ring.unit_entries();
  Expect(ring.CanFreezeUnit(),
         "a unit that does not complete a prefix needs no new slot");
  ring.FreezeUnit();
  fill_unit(key);
  Expect(!ring.CanFreezeUnit(),
         "the ring accepted a (q+1)-th complete prefix");

  // Level 1 takes prefixes in order; taking one does NOT free its slot.
  uint64_t prefix = 0, generation = 0;
  Expect(ring.PrefixReady(), "a complete prefix was not offered to level 1");
  const bs::TableView view = ring.TakePrefix(&prefix, &generation);
  Expect(prefix == 0 && generation == 1 &&
             view.num_buckets == geometry.DensePrefixBuckets(),
         "the taken prefix is not prefix 0 at its first occupancy, Z/2 buckets "
         "wide");
  Expect(!ring.CanFreezeUnit(),
         "taking a prefix freed its slot, though only the publication that "
         "replaces it and its readers can");

  // The publication: the mark takes it out of the cascade, the notification
  // takes it out of the ring -- and only once the requester observes an epoch
  // that has reached the threshold.
  ring.NoteConsumed(1);
  Expect(ring.SendRetirement(la::PrefixRetirement{0, generation, 4}),
         "the retirement ring refused a notification");
  Expect(ring.ReclaimPrefixes(3) == 0,
         "a prefix was reclaimed before its threshold was observed");
  Expect(!ring.CanFreezeUnit(),
         "an unreclaimed prefix stopped counting against q");
  Expect(ring.ReclaimPrefixes(4) == 1,
         "the prefix was not reclaimed once its threshold was reached");
  Expect(ring.CanFreezeUnit(), "the reclaimed slot did not come back");

  // A notification for an occupancy that has ended is rejected, not acted on.
  const uint64_t rejected = ring.rejected();
  ring.SendRetirement(la::PrefixRetirement{0, generation, 4});
  ring.ReclaimPrefixes(~uint64_t{0});
  Expect(ring.rejected() == rejected + 1,
         "a stale prefix retirement was not rejected");

  // The plan's dense half, in probe order: the current unit first, then the
  // frozen part of the prefix being assembled, then complete prefixes newest
  // first.
  microram::byteslice::ProbePlan plan;
  microram::byteslice::TableEntry placeholder;
  placeholder.kind = microram::byteslice::TableKind::kDense;
  plan.prefix_slots = ring.plan_prefix_slots();
  plan.tables.assign(plan.prefix_slots, placeholder);
  plan.heads_consumed = 1;
  ring.FillDensePrefix(&plan);
  const size_t live = plan.prefix_slots - plan.first_live;
  Expect(live == 1 + 1 + (ring.complete_prefixes() - 1),
         "the dense prefix does not list the current unit, the frozen part and "
         "every unconsumed complete prefix");
  Expect(plan.tables[plan.first_live].removable,
         "the current unit is the one removable dense source");
  for (size_t i = plan.first_live; i + 1 < plan.prefix_slots; ++i) {
    Expect(plan.tables[i].window_end > plan.tables[i + 1].window_end &&
               plan.tables[i].window_begin >= plan.tables[i + 1].window_end,
           "the dense prefix is not in descending, disjoint window order");
  }
  Expect(!plan.tables[plan.first_live + 1].removable,
         "a frozen unit is a rebuild source and may not be cleared by a probe");

  // A FULL UNIT REFUSES ANOTHER ENTRY.  The engine freezes the moment a unit
  // fills, but its flush has a real failure mode (no free prefix slot and no
  // level able to progress), and an unguarded Insert after one would write at
  // the first bucket of the NEXT ring slot -- one past the allocation when
  // this is the last one.
  {
    la::DensePrefixRing full(geometry, layout);
    for (size_t i = 0; i < full.unit_entries(); ++i) {
      full.Insert(bs::KeyWords{i + 1}, value.data(), true, false, false);
    }
    Expect(full.UnitFull(), "the unit did not fill");
    Expect(Throws([&] {
             full.Insert(bs::KeyWords{999}, value.data(), true, false, false);
           }),
           "an entry was inserted into a unit that was already full");
  }
}

// A PREFIX WITH NO RETIREMENT THRESHOLD RECORDED IS NOT RECLAIMABLE.
//
// The reclaim scan walks prefixes in order and stops at the first one whose
// threshold the observed epoch has not reached.  If "no threshold yet" read
// as zero, which every epoch has reached, a gap in the notification stream --
// prefix p + 1's arriving while p's had not -- would free p's ring slot while
// readers were still inside the plan that named it, and free it silently.
// One SPSC producer publishing in order cannot open that gap; this pins the
// behaviour so that nothing which does can open it quietly.
void TestPrefixRetirementGapIsNotReclaimed() {
  la::LevelArenaGeometry::Params params;
  params.branching = 2;
  params.levels = 2;
  params.top_digit = 1;
  params.prefix_flushes = 2;
  params.stash_buckets = 1;
  params.dense_prefixes = 2;
  const la::LevelArenaGeometry geometry(params);
  const bs::Layout layout;
  la::DensePrefixRing ring(geometry, layout);
  std::vector<uint8_t> value(layout.value_bytes - 1, 7);

  uint64_t key = 1;
  for (unsigned p = 0; p < 2; ++p) {
    for (unsigned u = 0; u < params.prefix_flushes; ++u) {
      for (size_t i = 0; i < ring.unit_entries(); ++i) {
        ring.Insert(bs::KeyWords{key++}, value.data(), true, false, false);
      }
      ring.FreezeUnit();
    }
  }
  Expect(ring.complete_prefixes() == 2, "the ring did not complete two");

  uint64_t p0 = 0, g0 = 0, p1 = 0, g1 = 0;
  ring.TakePrefix(&p0, &g0);
  ring.TakePrefix(&p1, &g1);
  ring.NoteConsumed(2);

  // Prefix 1's notification alone: prefix 0's slot is still pinned.
  Expect(ring.SendRetirement(la::PrefixRetirement{p1, g1, 4}),
         "the retirement ring refused a notification");
  Expect(ring.ReclaimPrefixes(10) == 0,
         "a prefix whose retirement threshold was never recorded was "
         "reclaimed, so a slot a reader may be inside came free");
  Expect(ring.reclaimed() == 0, "the reclaim mark moved with nothing to move");

  // And once it arrives, both go, in order.
  Expect(ring.SendRetirement(la::PrefixRetirement{p0, g0, 4}),
         "the retirement ring refused a notification");
  Expect(ring.ReclaimPrefixes(10) == 2,
         "the two prefixes were not reclaimed once both thresholds were "
         "recorded and observed");
  Expect(ring.reclaimed() == 2, "the reclaim mark did not reach both");
}

// ---------------------------------------------------------------------------
// The engine
// ---------------------------------------------------------------------------

// A value that is a function of the key and a generation counter, so that a
// wrong value is caught rather than a missing one.
void MakeValue(uint64_t key, uint64_t gen, std::vector<uint8_t>* value) {
  for (size_t b = 0; b < value->size(); ++b) {
    (*value)[b] = static_cast<uint8_t>(key * 131 + gen * 17 + b);
  }
}

struct RunReport {
  size_t mismatches = 0;
  size_t model_size = 0;
  uint64_t top_compactions = 0;
  uint64_t adoptions = 0;
  uint64_t forwards = 0;
};

// One mixed workload against a std::map model.  Every operation the engine
// exposes, including absent reads and erases of keys that were never written.
RunReport RunWorkload(la::LevelArenaEngine* engine, size_t operations,
                      uint64_t seed, const std::string& name) {
  const size_t value_bytes = engine->ValueBytes();
  std::vector<uint8_t> value(value_bytes), got(value_bytes);
  std::map<uint64_t, std::vector<uint8_t>> model;
  std::mt19937_64 rng(seed);
  // A quarter of capacity: every access spends a slot whatever it found, so a
  // workload that touched capacity keys would overflow on tombstones alone.
  const uint64_t keys = engine->Capacity() / 4 + 1;
  RunReport report;
  for (size_t i = 0; i < operations; ++i) {
    const uint64_t key = rng() % keys + 1;
    const auto it = model.find(key);
    const bool present = it != model.end();
    switch (rng() % 10) {
      case 0: case 1: case 2: case 3: {
        MakeValue(key, i, &value);
        engine->ReadThenWrite(key, value.data());
        model[key] = value;
        break;
      }
      case 4: case 5: case 6: {
        const bool found = engine->Read(key, got.data());
        if (found != present || (present && got != it->second)) {
          if (report.mismatches < 4) {
            std::fprintf(stderr, "%s: read of %llu: found=%d want=%d\n",
                         name.c_str(), static_cast<unsigned long long>(key),
                         static_cast<int>(found), static_cast<int>(present));
          }
          ++report.mismatches;
        }
        break;
      }
      case 7: {
        const bool erased = engine->Erase(key, got.data());
        if (erased != present || (present && got != it->second)) {
          ++report.mismatches;
        }
        model.erase(key);
        break;
      }
      case 8: {
        MakeValue(key, i + 1, &value);
        const bool insert = (rng() & 1) != 0;
        const bool was = engine->Exchange(key, value.data(), got.data(), insert);
        if (was != present || (present && got != it->second)) {
          ++report.mismatches;
        }
        if (present || insert) model[key] = value;
        break;
      }
      default: {
        // An unprobed write, the one path that does not consult the cascade.
        MakeValue(key, i + 2, &value);
        engine->WriteWithoutProbe(key, value.data());
        model[key] = value;
        break;
      }
    }
  }
  for (const auto& entry : model) {
    if (!engine->Read(entry.first, got.data()) || got != entry.second) {
      if (report.mismatches < 4) {
        std::fprintf(stderr, "%s: final read of %llu disagrees\n", name.c_str(),
                     static_cast<unsigned long long>(entry.first));
      }
      ++report.mismatches;
    }
  }
  report.model_size = model.size();
  for (unsigned l = 1; l <= engine->geometry().Levels(); ++l) {
    report.adoptions += engine->level(l).stats().adoptions;
    report.forwards += engine->level(l).stats().forwards;
  }
  report.top_compactions =
      engine->level(engine->geometry().TopLevel()).stats().merges;
  return report;
}

// MULTIPLE FULL-TO-FULL CHAINS AND CYCLES.  A level's digit odometer has to
// run round more than once, its full table has to be forwarded into the level
// above, and the top has to compact several times -- otherwise the family
// coordinate, the bank parity and the two-inbox handoff are each exercised
// exactly once and their second cycle is untested.
void TestChainsAndCycles() {
  struct Case {
    const char* name;
    unsigned branching, levels, top_digit, prefix_flushes;
    size_t stash_buckets;
    unsigned dense_prefixes;
    size_t operations;
    size_t tier_buckets;
    // Empty is the uniform ladder, exactly as the geometry reads it.
    std::vector<unsigned> fanouts;
    // A pinned per-level tier profile (Params::level_tier_buckets); empty is
    // the shared `tier_buckets`.
    std::vector<size_t> tier_profile;
  };
  const Case cases[] = {
      {"B=2 L=3 D=1", 2, 3, 1, 2, 1, 2, 12000, 1, {}},
      {"B=2 L=4 D=2", 2, 4, 2, 4, 1, 2, 16000, 1, {}},
      {"B=4 L=3 D=4", 4, 3, 4, 2, 1, 2, 20000, 1, {}},
      {"B=4 L=3 D=2 r0=4", 4, 3, 2, 4, 2, 3, 20000, 1, {}},
      {"B=8 L=3 D=4", 8, 3, 4, 2, 1, 2, 24000, 1, {}},
      {"B=8 L=2 D=4 r0=8", 8, 2, 4, 8, 1, 2, 16000, 1, {}},
      // THE BINARY TOP at its widest: D = 8 routes A
      // with K + 3 butterfly levels and no radix pass, and the sweep splits
      // each carry bucket eight ways on raw tag bits.  The D = 2 cases above
      // are the same path at e = 1.
      {"B=8 L=2 D=8", 8, 2, 8, 2, 1, 2, 16000, 1, {}},
      {"B=8 L=3 D=8", 8, 3, 8, 2, 1, 2, 40000, 1, {}},
      // A wide online stash (s = 4, so a flush is 256 entries and a prefix is
      // eight dense buckets, which is a run scan eight deep) and a two-bucket
      // tier, the one geometry knob that changes what a published table's
      // second half is.
      {"B=4 L=3 D=2 wide", 4, 3, 2, 2, 4, 2, 40000, 2, {}},
      // MIXED LADDERS.  What these exercise that no uniform one can: a level
      // whose fanout differs from the level ABOVE it, which is the seam every
      // per-level substitution has to get right -- the digit odometer, the
      // forward announce's `ordinal / b_l`, the carry extent the receiver
      // validates, and the family the two of them have to agree on without
      // talking.  The first is the ladder's own shape (a trimmed bottom under
      // a uniform B); the second puts a two-way level in the MIDDLE, which
      // exercises binary bank installation between larger fanouts.
      {"B=8 L=4 trimmed bottom", 8, 4, 4, 2, 1, 2, 70000, 1, {2, 8, 8}},
      {"B=4 L=4 two-way middle", 4, 4, 4, 2, 1, 2, 24000, 1, {4, 2, 4}},
      // PER-LEVEL TIER PROFILES, pinned wider than the horizon needs so that
      // every seam changes width: a level's carry arrives at the level
      // below's width and its adopted first carry stays there, its own
      // partials and the next level's inbox take its own, and a top narrower
      // than its inbox reads B's tier wider than it writes C's.  The two-way
      // middle level installs its carry's tier into a wider bank.
      {"B=8 L=4 tier profile", 8, 4, 4, 2, 1, 2, 70000, 0, {4, 8, 8},
       {1, 2, 3, 2}},
      {"B=4 L=4 two-way middle, tier profile", 4, 4, 4, 2, 1, 2, 24000, 0,
       {4, 2, 4}, {1, 2, 2, 1}},
      {"B=8 L=3 D=8 tier profile", 8, 3, 8, 2, 1, 2, 40000, 0, {},
       {2, 3, 1}},
  };
  // Every case also runs with each level's cycle STARTING IN ITS IDLE ODD
  // BANK (the bank-first run), where a fanout leaves room for a run: the run's
  // partials beside the live one in one bank, and the lease taken later.
  //
  for (la::BankFirst mode : {la::BankFirst::kOff, la::BankFirst::kNoClone}) {
  for (const Case& case_template : cases) {
    if (mode != la::BankFirst::kOff && case_template.branching < 4) continue;
    const std::string name_storage =
        std::string(case_template.name) +
        (mode == la::BankFirst::kOff
             ? std::string()
             : std::string(", bank-first ") + la::BankFirstName(mode));
    Case c = case_template;
    c.name = name_storage.c_str();
    la::LevelArenaEngine::Options options =
        MakeOptions(c.branching, c.levels, c.top_digit, c.prefix_flushes,
                    c.stash_buckets, c.dense_prefixes);
    options.geometry.tier_buckets = c.tier_buckets;
    options.geometry.level_fanouts = c.fanouts;
    if (!c.tier_profile.empty()) {
      options.geometry.level_tier_buckets = c.tier_profile;
      options.geometry.tier_buckets = *std::max_element(
          c.tier_profile.begin(), c.tier_profile.end());
    }
    options.geometry.bank_first = mode;
    la::LevelArenaEngine engine(options);
    const auto fanout_of = [&](unsigned level) {
      return c.fanouts.empty() ? c.branching : c.fanouts[level - 1];
    };
    const RunReport report =
        RunWorkload(&engine, c.operations, 0xC0FFEEull + c.branching, c.name);
    Expect(report.mismatches == 0,
           std::string(c.name) + ": " + std::to_string(report.mismatches) +
               " operations disagreed with the model");
    Expect(engine.ProbeAuditViolations() == 0,
           std::string(c.name) + ": a key was really probed twice under one "
                                 "nonce family");
    Expect(engine.RealProbes() > 0,
           std::string(c.name) + ": no real probe was audited at all, so the "
                                 "audit proves nothing");
    // Every level must have cycled its odometer more than once, and the top
    // must have compacted more than once.
    for (unsigned l = 1; l < c.levels; ++l) {
      Expect(engine.level(l).ordinal() > 2 * fanout_of(l),
             std::string(c.name) + ": level " + std::to_string(l) +
                 " did not run its digit odometer round twice");
    }
    Expect(report.top_compactions >= 2,
           std::string(c.name) + ": the top compacted " +
               std::to_string(report.top_compactions) + " times");
    if (c.levels > 2 && c.branching > 2) {
      Expect(report.adoptions > 0,
             std::string(c.name) + ": no carry was ever adopted in place");
    }
    Expect(report.forwards > 0,
           std::string(c.name) + ": no full table was ever forwarded");
    Expect(engine.dense().reclaimed() > 0,
           std::string(c.name) + ": no dense prefix slot was ever returned");
    // THE POOL BOUND, empirically: a run in which nothing is ever pinned must
    // never exhaust the plan records, or the bound is not a bound but a hope.
    for (unsigned l = 1; l <= c.levels; ++l) {
      Expect(engine.level(l).stats().blocked_on(la::LevelBlock::kPlanRecords) ==
                 0,
             std::string(c.name) + ": level " + std::to_string(l) +
                 " ran out of plan records with no reader pinning anything");
    }
    Expect(engine.publisher().free_records() > 0,
           std::string(c.name) + ": the plan pool ended empty");
  }
  }
}

// THE TWO-INBOX CASE.  A level with fanout above two adopts at digit 1, so its
// adopted P_1 holds one inbox until digit 2 replaces it -- and the carry that
// replaces it has to be built in the other.  With one inbox the hierarchy
// would deadlock, which is why every level keeps two inboxes; this is the run
// that would stop if it were wrong.
void TestTwoInboxProgress() {
  auto options = MakeOptions(4, 3, 1);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0xA5);
  size_t both_occupied = 0;
  size_t adopted_held = 0;
  size_t adopted_in_use_beside_a_ready_carry = 0;
  const unsigned level = 2;
  const la::LevelPlan& plan = engine.geometry().storage().At(level);
  for (size_t i = 0; i < 6000; ++i) {
    engine.Write(i % 97 + 1, value.data());
    const la::SlotState first = engine.arenas().At(level).State(plan.inbox[0]);
    const la::SlotState second = engine.arenas().At(level).State(plan.inbox[1]);
    if (first != la::SlotState::kFree && second != la::SlotState::kFree) {
      ++both_occupied;
    }
    // THE ADOPTED TABLE KEEPS ITS INBOX.  While it is level 2's partial
    // it is the level's own immutable table living in an inbox slot, so that
    // slot must read kInUse -- not ready, not free -- and the carry that will
    // replace it has to be built in the other one.
    // Only P_1 is adopted; later partials live in banks or a lease above.
    if (!engine.level(level).has_partial() ||
        engine.geometry().CarryDigit(level, engine.level(level).ordinal()) !=
            1) {
      continue;
    }
    const unsigned slot = engine.level(level).partial().slot;
    if (slot != plan.inbox[0] && slot != plan.inbox[1]) continue;
    ++adopted_held;
    const la::SlotState state = engine.arenas().At(level).State(slot);
    Expect(state == la::SlotState::kInUse,
           std::string("an adopted inbox table's slot reads ") +
               la::SlotStateName(state) + " rather than in-use");
    const unsigned other = slot == plan.inbox[0] ? plan.inbox[1] : plan.inbox[0];
    const la::SlotState other_state = engine.arenas().At(level).State(other);
    if (other_state == la::SlotState::kInUse ||
        other_state == la::SlotState::kReady ||
        other_state == la::SlotState::kWriting) {
      ++adopted_in_use_beside_a_ready_carry;
    }
  }
  Expect(both_occupied > 0,
         "level 2's two inboxes were never occupied at once, so the run never "
         "reached the state two of them exist for");
  Expect(adopted_held > 0,
         "level 2 never held an adopted table in an inbox");
  Expect(adopted_in_use_beside_a_ready_carry > 0,
         "the carry that replaces an adopted P_1 was never being built or "
         "waiting in the other inbox, which is the progress guarantee two of "
         "them exist for");
  Expect(engine.level(2).stats().adoptions > 1 &&
             engine.level(2).stats().forwards > 1,
         "level 2 did not adopt and forward repeatedly at B = 4");
  Expect(engine.ProbeAuditViolations() == 0,
         "B = 4: a key was really probed twice under one nonce family");
}

// PARTIAL-PREFIX VISIBILITY.  A prefix is r0 units and level 1 takes
// only COMPLETE ones, so between two prefix boundaries the cascade has to see
// three different dense things: the unit being written, the frozen units of
// the prefix being assembled, and every complete prefix whose hashed
// replacement is not yet published.  A key written into any of them must be
// readable at every point in between.
void TestPartialPrefixVisibility() {
  // The owners are NOT driven at the flush here, so complete prefixes pile up
  // to q and the cascade has to carry all three dense shapes at once.  It is
  // also the backpressure path: the requester drives the levels only
  // when there is no free prefix slot left.
  la::LevelArenaEngine::Options options =
      MakeOptions(2, 3, 1, /*prefix_flushes=*/4);
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes), got(value_bytes);
  const size_t unit = engine.dense().unit_entries();
  std::map<uint64_t, std::vector<uint8_t>> planted;
  size_t saw_partial = 0;
  size_t saw_complete = 0;
  size_t saw_runs = 0;
  uint64_t key = 1;
  // One planted key per unit, over enough units to fill q prefixes and start
  // the next, with every planted key re-read after each unit.
  const unsigned units =
      engine.geometry().PrefixFlushes() *
          (engine.geometry().DensePrefixes() + 2) + 1;
  for (unsigned u = 0; u < units; ++u) {
    const uint64_t planted_key = key++;
    MakeValue(planted_key, u, &value);
    engine.Write(planted_key, value.data());
    planted[planted_key] = value;
    // The rest of this unit moves the cursor without disturbing the planted
    // keys; every access spends a slot, so they have to be keys of their own.
    for (size_t i = 1; i < unit; ++i) {
      MakeValue(key, 0, &value);
      engine.Write(key, value.data());
      ++key;
    }
    if (engine.dense().flushes() % engine.geometry().PrefixFlushes() != 0) {
      ++saw_partial;
    }
    if (engine.dense().complete_prefixes() > engine.dense().consumed()) {
      ++saw_complete;
    }
    const bs::ProbePlanSnapshot snapshot = engine.PlanSnapshot();
    for (const uint32_t i : snapshot.dense) {
      if (snapshot.tables[i].num_buckets > 1) ++saw_runs;
    }
    for (const auto& entry : planted) {
      const bool found = engine.Read(entry.first, got.data());
      Expect(found && got == entry.second,
             "a key planted in an earlier unit is no longer readable at its "
             "own value");
      // A read re-inserts what it found, so the model's copy stays current.
    }
  }
  Expect(saw_partial > 0,
         "the run never observed a partially assembled prefix");
  Expect(saw_complete > 0,
         "the run never observed a complete but unconsumed prefix, which is "
         "the state q counts");
  Expect(saw_runs > 0,
         "the cascade never carried a multi-bucket dense run, so the run scan "
         "was never exercised");
  Expect(engine.dense().taken() > 0,
         "the backpressure path never drove level 1 at all");
  Expect(engine.ProbeAuditViolations() == 0,
         "partial prefixes: a key was really probed twice under one family");
}

// A HELD READER ACROSS PUBLICATIONS.  An owner may publish
// while a request is inside an old plan; what it may NOT do is reuse the
// buffers that plan names.  So: hold the epoch open, step the owners, and
// check that what they retired is still byte for byte what it was and that its
// slot has not come back.
void TestHeldReaderAcrossPublication() {
  // Work has to be OUTSTANDING when the reader is taken, or the owners have
  // nothing to publish while it is held.
  // q = 3 at B = 2 on purpose: the requester drives the levels only when it
  // runs out of prefix slots, so it drives them q prefixes at a time -- and a
  // count that is a multiple of B would leave level 1 at the same digit every
  // time, which at B = 2 is the one digit that forwards and keeps no partial.
  la::LevelArenaEngine::Options options =
      MakeOptions(2, 3, 1, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/3);
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x5A);
  // Enough traffic that several tables are live, and then enough OUTSTANDING
  // prefixes that the owners have several merges to run while the reader is
  // held -- including one at a digit above 1, which is what retires a source.
  for (size_t i = 0; i < 3000; ++i) engine.Write(i % 211 + 1, value.data());
  // ...and stop at a state where the next merge is GUARANTEED to retire
  // something that is live now: level 1 holding a partial means its next digit
  // is above 1, and a merge at a digit above 1 absorbs that partial.
  const auto ready = [&] {
    return engine.level(1).has_partial() &&
           engine.dense().complete_prefixes() - engine.dense().consumed() >= 2;
  };
  for (size_t i = 0; i < 40000 && !ready(); ++i) {
    engine.Write(i % 211 + 1, value.data());
  }
  Expect(ready(),
         "the fixture never reached a state with an absorbable partial and "
         "outstanding prefixes");

  const uint64_t publications_before = engine.publisher().publications();
  std::vector<la::PublishedTable> pinned = engine.publisher().LiveTables();
  std::map<uint64_t, uint64_t> digests;
  for (const la::PublishedTable& t : pinned) {
    digests[t.table_id] = DigestTable(t, engine.layout());
  }
  size_t retired_while_held = 0;
  size_t free_slots_while_held = 0;
  {
    // The reader is inside from here.  Everything the owners retire below
    // gets the threshold e + 1, and the observed epoch is e.
    la::ReaderEpoch::Guard guard(engine.publisher().epoch());
    for (int i = 0; i < 256 && engine.StepOnce(); ++i) {
    }
    // Whatever left the plan is still in storage, unchanged.
    for (const la::PublishedTable& t : pinned) {
      if (engine.publisher().IsLive(t.table_id)) continue;
      ++retired_while_held;
      Expect(DigestTable(t, engine.layout()) == digests[t.table_id],
             "a table a held reader could still be probing was overwritten "
             "after it left the plan");
      Expect(engine.arenas().At(t.owner).State(t.slot) ==
                 la::SlotState::kRetired,
             "a slot a held reader pins came back to free");
      if (engine.arenas().At(t.owner).State(t.slot) == la::SlotState::kFree) {
        ++free_slots_while_held;
      }
    }
  }
  Expect(engine.publisher().publications() > publications_before,
         "the owners published nothing while the reader was held, so the "
         "pinning was never exercised");
  Expect(retired_while_held > 0,
         "nothing was retired while the reader was held");
  Expect(free_slots_while_held == 0,
         "a pinned slot was reclaimed under a live reader");
  // Releasing the reader releases the slots, and the engine keeps running.
  engine.RunOwners();
  size_t still_retired = 0;
  for (const la::PublishedTable& t : pinned) {
    if (engine.publisher().IsLive(t.table_id)) continue;
    if (engine.arenas().At(t.owner).State(t.slot) == la::SlotState::kRetired) {
      ++still_retired;
    }
  }
  Expect(still_retired == 0,
         "slots stayed pinned after their reader left");
  std::vector<uint8_t> got(value_bytes);
  for (size_t i = 0; i < 400; ++i) engine.Write(i % 211 + 1, value.data());
  Expect(engine.Read(uint64_t{1}, got.data()),
         "the engine stopped answering after a held reader was released");
}

// TWO CONCURRENT READERS ARE REFUSED.  The reused odd/even word
// describes one active snapshot; a second one would drive it even between the
// two entries and let an owner reclaim underneath both.
void TestOverlappingRequestsRefused() {
  la::LevelArenaEngine engine(MakeOptions(2, 2, 1));
  la::ReaderEpoch::Guard guard(engine.publisher().epoch());
  Expect(Throws([&] {
           la::ReaderEpoch::Guard second(engine.publisher().epoch());
         }),
         "a second overlapping reader epoch was allowed");
}

// ADOPTION CHANGES NO PLAN.  At digit 1 the receiving level takes the
// ready inbox table as its own P_1: same identity, same family, same window,
// same bytes -- so the publication count does not move and the entry the
// cascade probes is the same entry it was probing a moment before.
void TestAdoptionPublishesNothing() {
  la::LevelArenaEngine engine(MakeOptions(4, 3, 4));
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x33);
  uint64_t key = 1;
  size_t observed = 0;
  for (size_t i = 0; i < 20000 && observed < 3; ++i) {
    const uint64_t adoptions = engine.level(2).stats().adoptions;
    const uint64_t publications = engine.publisher().publications();
    const uint64_t ordinal_before = engine.level(2).ordinal();
    // A table that is about to be adopted is the one ready carry at level 2.
    std::set<uint64_t> live_before;
    for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
      live_before.insert(t.table_id);
    }
    engine.Write(key++ % 4096 + 1, value.data());
    if (engine.level(2).stats().adoptions == adoptions) continue;
    ++observed;
    // Adoption itself publishes nothing; the SAME flush may also have made
    // level 1 publish, so what is checked is that the adopted table is still
    // live under its own identity and that level 2's ordinal advanced.
    Expect(engine.level(2).ordinal() > ordinal_before,
           "an adoption did not advance the level's ordinal");
    std::set<uint64_t> live_after;
    for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
      live_after.insert(t.table_id);
    }
    size_t survivors = 0;
    for (const uint64_t id : live_before) survivors += live_after.count(id);
    Expect(survivors > 0,
           "every table left the plan across an adoption, which copies and "
           "swaps nothing");
    (void)publications;
  }
  Expect(observed >= 3, "level 2 never adopted a carry");
  Expect(engine.ProbeAuditViolations() == 0,
         "adoption: a key was really probed twice under one nonce family");
}

// Check public answers against selected deterministic inputs after preparations
// overlap carries; the merge fixture separately checks the phased routing.
void TestSpeculativePreparationValues() {
  la::LevelArenaEngine engine(MakeOptions(4, 3, 4));
  std::vector<std::vector<uint8_t>> expected(257,
      std::vector<uint8_t>(engine.ValueBytes()));
  for (size_t i = 0; i < 8000; ++i) {
    const uint64_t key = (i * 73) % 257;
    MakeValue(key, i, &expected[key]);
    engine.Write(key, expected[key].data());
  }
  Expect(engine.level(2).stats().preparations > 0,
         "speculative preparation was not exercised");
  std::vector<uint8_t> actual(engine.ValueBytes());
  for (uint64_t key = 0; key < expected.size(); ++key) {
    Expect(engine.Read(key, actual.data()), "prepared merge lost a key");
    Expect(actual == expected[key], "prepared merge returned a stale value");
  }
  Expect(!engine.Read(100000, actual.data()), "prepared merge invented a key");
}

// THE IN-LEASE RETIREMENT WAIT IS REPORTED UNDER THE INBOX'S NAME.  Drive
// level 1 until its published partial is P_2 -- an even partial inside its
// lease on level 2's inbox -- with a prefix waiting for digit 3; then hold a
// reader.  P_3's publication removes P_2 while the reader is inside, so the
// lease is pinned under that publication's threshold, and the next write into
// it -- digit 4, the full table -- must wait and say kInboxRetirement.  When
// the reader leaves, it goes through.
void TestInboxRetirementIsAttributed() {
  la::LevelArenaEngine::Options options =
      MakeOptions(4, 3, 4, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/4);
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x22);
  const auto outstanding = [&] {
    return engine.dense().complete_prefixes() - engine.dense().consumed();
  };
  uint64_t key = 0;
  bool positioned = false;
  for (size_t i = 0; i < 400000 && !positioned; ++i) {
    if (engine.level(1).next_digit() == 3 &&
        engine.level(1).stats().inbox_partials > 0 && outstanding() >= 2) {
      positioned = true;
      break;
    }
    if (outstanding() < 2) {
      engine.Write(key++ % 251 + 1, value.data());
    } else {
      engine.StepOnce();
    }
  }
  Expect(positioned,
         "level 1 never stood at digit 3 over an even partial in its lease "
         "with a prefix waiting");
  const uint64_t forwards_before = engine.level(1).stats().forwards;
  const uint64_t inbox_before =
      engine.level(1).stats().blocked_on(la::LevelBlock::kInboxRetirement);
  {
    la::ReaderEpoch::Guard guard(engine.publisher().epoch());
    for (int i = 0; i < 64; ++i) engine.StepOnce();
    Expect(engine.level(1).stats().blocked_on(la::LevelBlock::kInboxRetirement) >
               inbox_before,
           "level 1 did not report waiting on its lease's pinned partial "
           "under a held reader");
    Expect(engine.level(1).stats().forwards == forwards_before,
           "level 1 forwarded over a partial a reader was still inside");
  }
  for (int i = 0; i < 64 && engine.level(1).stats().forwards == forwards_before;
       ++i) {
    engine.StepOnce();
  }
  Expect(engine.level(1).stats().forwards > forwards_before,
         "level 1 did not forward once the reader left");
}

// Wide keys and a wide value through the byte API: user keys of 16 bytes or
// more normalize to 16 stored bytes, narrower ones are stored verbatim at
// their own width; both words are compared exactly.  Groups of four keys share
// their low eight bytes and differ only in byte 8, so a comparison that
// dropped the high word would merge them.
void TestWideKeysAndValues(size_t user_key_bytes) {
  la::LevelArenaEngine::Options options = MakeOptions(4, 3, 2);
  options.key_bytes = user_key_bytes;
  options.value_bytes = 40;
  la::LevelArenaEngine engine(options);
  Expect(engine.RehashesKeys() == (user_key_bytes >= 16),
         "only user keys of 16 bytes or more should be rehashed");
  const size_t key_bytes = engine.UserKeyBytes();
  const size_t value_bytes = engine.ValueBytes();
  std::map<std::vector<uint8_t>, std::vector<uint8_t>> model;
  std::vector<uint8_t> key(key_bytes), value(value_bytes), got(value_bytes);
  std::mt19937_64 rng(0xFEEDull);
  size_t bad = 0;
  for (size_t i = 0; i < 4000; ++i) {
    const uint64_t id = rng() % 512 + 1;
    for (size_t b = 0; b < key_bytes; ++b) {
      key[b] = static_cast<uint8_t>((b < 8 ? id / 4 : id) * 7 + b * 29);
    }
    key[8] = static_cast<uint8_t>(id % 4);
    if ((rng() & 1) != 0) {
      for (size_t b = 0; b < value_bytes; ++b) {
        value[b] = static_cast<uint8_t>(id + b + i);
      }
      engine.Write(key.data(), value.data());
      model[key] = value;
    } else {
      const bool found = engine.Read(key.data(), got.data());
      const auto it = model.find(key);
      const bool present = it != model.end();
      if (found != present || (present && got != it->second)) ++bad;
    }
  }
  for (const auto& entry : model) {
    if (!engine.Read(entry.first.data(), got.data()) ||
        got != entry.second) {
      ++bad;
    }
  }
  Expect(bad == 0, "wide keys and values: " + std::to_string(bad) +
                       " operations disagreed with the model");
  Expect(engine.ProbeAuditViolations() == 0,
         "wide keys: a key was really probed twice under one nonce family");
}

// THE AUDIT'S OWN REFCOUNT.  A family outlives any one of its tables, so a
// same-family swap must not pass through a count of zero and forget what has
// been probed.  Stated here directly, because the engine has no way to reach
// that state on purpose.
void TestFamilyHistorySurvivesASwap() {
  la::ProbeFamilyAudit audit;
  Expect(audit.Enabled(), "this fixture must run with the probe audit live");
  const uint64_t family = 12345;
  audit.AddMember(family);
  audit.RecordRealProbe(family, bs::KeyWords{7});
  Expect(audit.violations() == 0, "the first real probe was a violation");
  // The swap: the new member is counted before the old one is dropped.
  audit.AddMember(family);
  audit.DropMember(family);
  audit.RecordRealProbe(family, bs::KeyWords{7});
  Expect(audit.violations() == 1,
         "the family's history did not survive a same-family swap, so a "
         "repeated real probe went unnoticed");
  // The last member's retirement clears it.
  audit.DropMember(family);
  audit.RecordRealProbe(family, bs::KeyWords{7});
  Expect(audit.violations() == 1,
         "the family's history outlived its last member");
}

// FIFO CARRY VALIDATION.  A receiving level derives its digit, its family, its
// nonce and its window from the ORDINAL of the carry it is accepting, so a
// carry taken out of order would be merged under another carry's hash.  With
// one producer per boundary the engine cannot produce one, which is exactly
// why the refusal needs a fixture that can: this one wires a level up by hand
// and pushes it a Ready that lies.
class LevelFixture {
 public:
  explicit LevelFixture(unsigned branching = 4)
      : geometry_(Params(branching)),
        sizing_(geometry_, kMaxAccesses),
        arenas_(geometry_, layout_),
        publisher_(PublisherConfig()),
        aes_keys_(bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
            microram::crypto::SecretKeySeed::Fixed(7)))),
        inbox_(arenas_.At(2)),
        receiver_(inbox_),
        producer_(inbox_),
        above_(arenas_.At(3)),
        up_(above_),
        scratch_(layout_, la::MaxLevelMergeRangeBuckets(geometry_, sizing_, 2),
                 la::MaxLevelDfsAllocation(geometry_, sizing_, 2)) {
    la::LevelState::Wiring wiring;
    wiring.geometry = &geometry_;
    wiring.sizing = &sizing_;
    wiring.publisher = &publisher_;
    wiring.arena = &arenas_.At(2);
    wiring.receiver = &receiver_;
    wiring.producer = &up_;
    wiring.dense = nullptr;
    wiring.scratch = &scratch_;
    wiring.aes_keys = aes_keys_.get();
    wiring.layout = layout_;
    level_ = std::make_unique<la::LevelState>(2, wiring);
  }

  la::LevelState& level() { return *level_; }

  // Announce a carry into level 2's inbox under the descriptor given, which is
  // the producer's half of the boundary and the only thing a receiver sees.
  // `per_bucket` real entries in every bucket, under keys no other carry
  // uses and at whatever bucket the fixture put them: nothing here checks
  // their placement, but an empty table routes to all-zero bytes, and a
  // check that a table's bytes did not change needs some to change.
  void Announce(uint64_t ordinal, la::Family family, uint64_t window_begin,
                uint64_t window_end, bool publish = false,
                size_t per_bucket = 0) {
    if (!producer_.TryAcquire()) {
      throw std::logic_error("the fixture could not lease an inbox");
    }
    const size_t buckets = geometry_.CarryBuckets(2);
    bs::TableView main = producer_.WritableMain(buckets);
    std::memset(main.data, 0, buckets * layout_.BucketBytes());
    std::fill_n(main.masks, buckets, uint64_t{0});
    for (size_t b = 0; b < buckets && per_bucket != 0; ++b) {
      for (size_t slot = 0; slot < per_bucket; ++slot) {
        ts::PlantEntry(layout_, main.data + b * layout_.BucketBytes(), slot,
                       bs::KeyWords{++planted_key_}, 1);
      }
      main.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
    }
    la::ReadyMessage message;
    message.ordinal = ordinal;
    message.table_id = ++table_id_;
    message.family = family;
    message.window_begin = window_begin;
    message.window_end = window_end;
    message.main_buckets = buckets;
    message.tier_buckets = geometry_.TierBuckets();
    if (publish) {
      la::PublishedTable table;
      publisher_.AllocateTableIds(&table.table_id, &table.tier_table_id);
      message.table_id = table.table_id;
      table.family = family;
      table.family_id = la::FamilyId(family);
      table.nonce = la::FamilyNonce(family);
      table.window_begin = window_begin;
      table.window_end = window_end;
      table.owner = 2;
      table.slot = producer_.lease().slot;
      table.generation = producer_.lease().generation;
      table.main_buckets = buckets;
      table.index_bits = la::Log2Checked(buckets, "fixture carry");
      table.radix = 1;
      table.data = main.data;
      table.masks = main.masks;
      const auto* tier = producer_.WritableTier();
      table.tier_data = tier->data;
      table.tier_masks = const_cast<uint64_t*>(tier->masks);
      table.tier_buckets = tier->num_buckets;
      la::PublicationDelta delta;
      delta.Add(table);
      delta.ConsumePrefixes(ordinal * geometry_.Fanout(1));
      publisher_.Publish(delta);
    }
    producer_.PrepareReady(message);
    producer_.CommitReady();
  }

  la::ReaderEpoch& epoch() { return publisher_.epoch(); }
  size_t Reclaim() { return receiver_.ReclaimAndCredit(epoch().Observed()); }
  const la::LevelArena& arena() const { return arenas_.At(2); }
  const la::LevelArenaGeometry& geometry() const { return geometry_; }
  const la::LevelArenaPublisher& publisher() const { return publisher_; }
  // Level 3's end of its boundary, which is what issues the credits level 2
  // leases its forwarding inbox with.  Absent until opened, so a fixture can
  // hold level 2 on kNoOutputCredit for as long as it likes.
  void OpenAbove() {
    if (up_receiver_ == nullptr) {
      up_receiver_ = std::make_unique<la::BoundaryReceiver>(above_);
    }
  }

  uint64_t CarryPositions() const {
    return geometry_.Branching() * geometry_.PrefixPositions();
  }

 private:
  static la::LevelArenaGeometry::Params Params(unsigned branching) {
    la::LevelArenaGeometry::Params params;
    params.branching = branching;
    params.bank_first = la::BankFirst::kOff;
    params.levels = 3;
    params.top_digit = 2;
    params.prefix_flushes = 2;
    params.stash_buckets = 1;
    params.dense_prefixes = 2;
    return params;
  }

  la::LevelArenaPublisher::Config PublisherConfig() const {
    la::LevelArenaPublisher::Config config;
    config.prefix_slots = geometry_.DensePrefixes() + 2;
    size_t slots = 0;
    for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
      slots += geometry_.storage().At(l).slots.size();
    }
    config.arena_slots = slots;
    config.dense_slots = geometry_.DensePrefixes() + 1;
    return config;
  }

  bs::Layout layout_;
  la::LevelArenaGeometry geometry_;
  la::LevelArenaStashSizing sizing_;
  la::LevelArenaSet arenas_;
  la::LevelArenaPublisher publisher_;
  std::unique_ptr<bs::AesTagKeys> aes_keys_;
  la::LevelBoundary inbox_;
  la::BoundaryReceiver receiver_;
  la::BoundaryProducer producer_;   // level 1's end of level 2's inbox
  la::LevelBoundary above_;
  la::BoundaryProducer up_;         // level 2's end of level 3's inbox
  std::unique_ptr<la::BoundaryReceiver> up_receiver_;  // OpenAbove
  la::LevelMergeScratch scratch_;
  std::unique_ptr<la::LevelState> level_;
  uint64_t table_id_ = 100;
  uint64_t planted_key_ = 1u << 20;
};

// Pause the consumer with P_1 live. The binary layout can accept the next two
// carries. No timing assumptions.
void TestBinaryBufferSlack() {
  {
    LevelFixture fixture(2);
    const auto& plan = fixture.arena().plan();
    const uint64_t positions = fixture.CarryPositions();
    fixture.Announce(1, la::Family{2, 1}, 0, positions, true);
    {
      la::ReaderEpoch::Guard held(fixture.epoch());
      Expect(fixture.level().Step().progressed, "binary first carry progresses");
      const unsigned partial = fixture.level().partial().slot;
      Expect(partial == plan.odd_bank, "binary P_1 must live in the odd bank");
      Expect(fixture.Reclaim() == 0,
             "installation must not release an inbox while a reader pins it");
    }
    Expect(fixture.Reclaim() == 1u,
           "the binary layout returns P_1's inbox after reader retirement");
    fixture.Announce(2, la::Family{3, 1}, positions, 2 * positions, true);
    const bool blocked = Throws([&] {
      fixture.Announce(3, la::Family{2, 3}, 2 * positions, 3 * positions, true);
    });
    Expect(!blocked, "the binary layout accepts the second waiting carry");
  }
}

void TestCarryValidation() {
  const la::Family first{2, 1};
  {
    LevelFixture fixture;
    const uint64_t positions = fixture.CarryPositions();
    // Out of order: the level's next ordinal is 1.
    fixture.Announce(3, la::Family{2, 3}, 2 * positions, 3 * positions);
    Expect(Throws([&] { fixture.level().Step(); }),
           "a carry that skipped two ordinals was accepted");
  }
  {
    LevelFixture fixture;
    const uint64_t positions = fixture.CarryPositions();
    // The right ordinal under another family's nonce, which is the failure
    // that would otherwise be silent: the merge would re-tag under a hash the
    // carry was never placed by and simply stop deduplicating.
    fixture.Announce(1, la::Family{2, 9}, 0, positions);
    Expect(Throws([&] { fixture.level().Step(); }),
           "a carry whose family is not the one its ordinal names was "
           "accepted");
  }
  {
    LevelFixture fixture;
    const uint64_t positions = fixture.CarryPositions();
    fixture.Announce(1, first, 0, positions + 1);
    Expect(Throws([&] { fixture.level().Step(); }),
           "a carry whose window is not its ordinal's was accepted");
  }
  {
    LevelFixture fixture;
    const uint64_t positions = fixture.CarryPositions();
    fixture.Announce(1, first, 0, positions);
    la::LevelStepResult result = fixture.level().Step();
    Expect(result.progressed && fixture.level().ordinal() == 1 &&
               fixture.level().has_partial(),
           "a well-formed first carry was not adopted at digit 1");
  }
}

// BLOCKED REASONS ARE REPORTED, not collapsed.  Hold a reader so that
// nothing can be reclaimed, then step until every level stops, and check that
// what they stopped on is a retirement rather than an unattributed silence.
void TestBlockedReasonsAreAttributed() {
  la::LevelArenaEngine::Options options =
      MakeOptions(2, 3, 1, /*prefix_flushes=*/2, /*stash_buckets=*/1,
                  /*dense_prefixes=*/4);
  options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes, 0x11);
  for (size_t i = 0; i < 4000; ++i) engine.Write(i % 251 + 1, value.data());
  for (size_t i = 0; i < 20000 && engine.dense().complete_prefixes() -
                                          engine.dense().consumed() < 3;
       ++i) {
    engine.Write(i % 251 + 1, value.data());
  }
  uint64_t retirement_blocks = 0;
  {
    la::ReaderEpoch::Guard guard(engine.publisher().epoch());
    for (int i = 0; i < 256 && engine.StepOnce(); ++i) {
    }
    for (unsigned l = 1; l <= engine.geometry().Levels(); ++l) {
      const la::LevelStats& stats = engine.level(l).stats();
      retirement_blocks += stats.blocked_on(la::LevelBlock::kBankRetirement) +
                           stats.blocked_on(la::LevelBlock::kInboxRetirement) +
                           stats.blocked_on(la::LevelBlock::kNoOutputCredit);
    }
  }
  Expect(retirement_blocks > 0,
         "no level reported waiting on a retirement while a reader pinned "
         "every retired slot in the hierarchy");
  Expect(!engine.BlockedDiagnosis().empty(),
         "the blocked diagnosis is empty");
}

// ---------------------------------------------------------------------------
// A step that throws
// ---------------------------------------------------------------------------
//
// A publication failed BEFORE its install is the one failure a fixture can
// inject without corrupting anything: nothing is committed, and the level is
// left holding its carry, its destination and a finished job.  The pause hook
// is the injector.  Everything here runs on one thread.

constexpr const char* kInjectedFailure =
    "level arena test: a publication was failed on purpose";

struct InjectedThrow {
  la::ArenaPause point = la::ArenaPause::kBeforePlanInstall;
  unsigned who = 0;
  int remaining = 0;
};
InjectedThrow injected_throw;

void ThrowAtArmedPoint(la::ArenaPause point, unsigned who) {
  if (injected_throw.remaining > 0 && point == injected_throw.point &&
      who == injected_throw.who) {
    --injected_throw.remaining;
    throw std::runtime_error(kInjectedFailure);
  }
}

// Throws `times` times at (point, who), then passes; uninstalled on scope exit.
class ScopedThrow {
 public:
  ScopedThrow(la::ArenaPause point, unsigned who, int times) {
    injected_throw = InjectedThrow{point, who, times};
    la::SetArenaPauseHook(&ThrowAtArmedPoint);
  }
  ~ScopedThrow() {
    la::SetArenaPauseHook(nullptr);
    injected_throw = InjectedThrow{};
  }
  int remaining() const { return injected_throw.remaining; }
};

// LEVEL 1 WIRED BY HAND over a dense ring the fixture fills itself, so that a
// step can fail and then be stepped again -- which the engine, rightly, does
// not allow (see TestInlineStepFailureIsLatched).  Level 2's boundary is
// real, so the level has somewhere to forward.
class Level1Fixture {
 public:
  Level1Fixture()
      : geometry_(Params()),
        sizing_(geometry_, kMaxAccesses),
        arenas_(geometry_, layout_),
        dense_(geometry_, layout_),
        publisher_(PublisherConfig()),
        aes_keys_(bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
            microram::crypto::SecretKeySeed::Fixed(11)))),
        inbox_(arenas_.At(2)),
        receiver_(inbox_),
        producer_(inbox_),
        scratch_(layout_, la::MaxLevelMergeRangeBuckets(geometry_, sizing_, 1),
                 la::MaxLevelDfsAllocation(geometry_, sizing_, 1)) {
    la::LevelState::Wiring wiring;
    wiring.geometry = &geometry_;
    wiring.sizing = &sizing_;
    wiring.publisher = &publisher_;
    wiring.arena = &arenas_.At(1);
    wiring.receiver = nullptr;
    wiring.producer = &producer_;
    wiring.dense = &dense_;
    wiring.scratch = &scratch_;
    wiring.aes_keys = aes_keys_.get();
    wiring.layout = layout_;
    level_ = std::make_unique<la::LevelState>(1, wiring);
  }

  la::LevelState& level() { return *level_; }
  la::DensePrefixRing& dense() { return dense_; }

  // One more complete prefix of distinct live keys, as the requester would
  // assemble it, and the requester's reclamation of anything level 1 retired.
  void CompletePrefix() {
    dense_.ReclaimPrefixes(publisher_.epoch().Observed());
    std::vector<uint8_t> value(layout_.value_bytes, 0);
    const uint64_t target = dense_.complete_prefixes() + 1;
    while (dense_.complete_prefixes() < target) {
      const uint64_t key = ++next_key_;
      std::memcpy(value.data(), &key, std::min(value.size(), sizeof(key)));
      dense_.Insert(bs::KeyWords{key}, value.data(), /*real=*/true,
                    /*erased=*/false, /*unshadowed=*/false);
      if (dense_.UnitFull()) dense_.FreezeUnit();
    }
  }

 private:
  static la::LevelArenaGeometry::Params Params() {
    la::LevelArenaGeometry::Params params;
    params.branching = 4;
    params.levels = 3;
    params.top_digit = 2;
    params.prefix_flushes = 2;
    params.stash_buckets = 1;
    params.dense_prefixes = 2;
    return params;
  }

  la::LevelArenaPublisher::Config PublisherConfig() const {
    la::LevelArenaPublisher::Config config;
    config.prefix_slots = geometry_.DensePrefixes() + 2;
    size_t slots = 0;
    for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
      slots += geometry_.storage().At(l).slots.size();
    }
    config.arena_slots = slots;
    config.dense_slots = geometry_.DensePrefixes() + 1;
    return config;
  }

  bs::Layout layout_;
  la::LevelArenaGeometry geometry_;
  la::LevelArenaStashSizing sizing_;
  la::LevelArenaSet arenas_;
  la::DensePrefixRing dense_;
  la::LevelArenaPublisher publisher_;
  std::unique_ptr<bs::AesTagKeys> aes_keys_;
  la::LevelBoundary inbox_;
  la::BoundaryReceiver receiver_;
  la::BoundaryProducer producer_;  // level 1's end of level 2's inbox
  la::LevelMergeScratch scratch_;
  std::unique_ptr<la::LevelState> level_;
  uint64_t next_key_ = 0;
};

// THE TAKEN PREFIX IS KEPT ACROSS A FAILED STEP.  With one prefix complete, a
// retake would find nothing ready and wait for the next one; with two, it
// would merge the second under the first one's ordinal and consume both --
// prefix 0 would leave the cascade unmerged.  Both are checked: the retry runs
// with one prefix, and a second is added only afterwards.
void TestFailedStepKeepsItsPrefix() {
  Level1Fixture fixture;
  la::LevelState& level = fixture.level();
  la::DensePrefixRing& dense = fixture.dense();
  fixture.CompletePrefix();
  {
    ScopedThrow inject(la::ArenaPause::kBeforePlanInstall, /*who=*/1, 1);
    Expect(Throws([&] { level.Step(); }),
           "the injected publication failure did not reach the step");
    Expect(inject.remaining() == 0, "the injection point was never reached");
  }
  Expect(dense.taken() == 1 && dense.consumed() == 0 && level.ordinal() == 0,
         "a failed level-1 step did not leave exactly its prefix taken");

  const la::LevelStepResult retry = level.Step();
  Expect(retry.progressed && retry.block == la::LevelBlock::kNone,
         "a level holding a taken prefix did not retry its merge: it waited "
         "for another prefix instead");
  Expect(dense.taken() == 1,
         "the retry took a second prefix instead of the one it held");
  Expect(dense.consumed() == 1 && level.ordinal() == 1,
         "the retry did not publish the prefix it held under ordinal 1");

  fixture.CompletePrefix();
  for (int i = 0; i < 8 && dense.consumed() < 2; ++i) level.Step();
  Expect(dense.taken() == 2 && dense.consumed() == 2 && level.ordinal() == 2,
         "the prefix after the failed one was not merged in turn");
  level.Cancel();
}

// THE INLINE EXECUTOR LATCHES A FAILED STEP, as an owner thread's failure is
// latched with threads.  The scenario: B=4, L=3, D=4, r0=2, q=2, inline and
// kAuto, one throw injected at level 1's pre-install point, caught by the
// caller, who carries on.  An engine that did not latch would go on to answer
// some reads wrongly without an exception.  Latched, every later call
// re-raises the original failure, so nothing is answered from that state at
// all.
void TestInlineStepFailureIsLatched() {
  la::LevelArenaEngine::Options options = MakeOptions(4, 3, 4, 2, 1, 2);
  la::LevelArenaEngine engine(options);
  const size_t value_bytes = engine.ValueBytes();
  std::vector<uint8_t> value(value_bytes), got(value_bytes);
  for (uint64_t i = 0; i < 1500; ++i) {
    MakeValue(i % 300 + 1, i, &value);
    engine.Write(i % 300 + 1, value.data());
  }
  Expect(engine.first_failure().empty(), "a healthy engine reports a failure");
  std::string what;
  {
    ScopedThrow inject(la::ArenaPause::kBeforePlanInstall, /*who=*/1, 1);
    for (uint64_t i = 0; i < 4000 && what.empty(); ++i) {
      MakeValue(i % 300 + 1, i + 7, &value);
      try {
        engine.Write(i % 300 + 1, value.data());
      } catch (const std::exception& error) {
        what = error.what();
      }
    }
  }
  Expect(what == kInjectedFailure,
         "the injected failure was not what the access raised: " + what);
  Expect(engine.first_failure() == kInjectedFailure,
         "the inline executor did not latch the failed step: '" +
             engine.first_failure() + "'");
  // Every entry point re-raises it, with the original message, rather than a
  // secondary symptom such as "already took its carry" or "no free dense
  // prefix slot".
  const auto raises_original = [&](auto&& call) {
    try {
      call();
    } catch (const std::exception& error) {
      return std::string(error.what()) == kInjectedFailure;
    }
    return false;
  };
  size_t answered = 0;
  for (uint64_t key = 1; key <= 300; ++key) {
    if (!raises_original([&] { engine.Read(key, got.data()); })) ++answered;
  }
  Expect(answered == 0, std::to_string(answered) +
                            " reads were answered by an engine whose level 1 "
                            "had failed");
  Expect(raises_original([&] { engine.ReadThenWrite(uint64_t{1}, value.data()); }),
         "a probed write after the failure was not refused with it");
  Expect(raises_original(
             [&] { engine.WriteWithoutProbe(uint64_t{1}, value.data()); }),
         "an unprobed write after the failure was not refused with it");
  Expect(raises_original([&] { engine.Erase(uint64_t{1}); }),
         "an erase after the failure was not refused with it");
  Expect(raises_original([&] { engine.Drain(); }),
         "a drain after the failure was not refused with it");
  Expect(raises_original([&] { engine.StepOnce(); }),
         "a sweep after the failure was not refused with it");
  bs::BatchRequest64 lane;
  lane.op = bs::BatchOp::kRead;
  lane.key = 1;
  lane.value_out = got.data();
  Expect(raises_original([&] { engine.AccessBatch(1, &lane, nullptr); }),
         "a batch after the failure was not refused with it");
}

// ---------------------------------------------------------------------------
// One forwarding lease, several tables
// ---------------------------------------------------------------------------
//
// A level of fanout four builds P_2 and then P_4 inside ONE lease on an inbox
// of the level above.  A slot's tier is emptied when an occupancy begins
// (LevelArena::TryLease), which here is only at P_2; so unless each merge
// empties its destination tier itself, P_4 is published with P_2's leftovers
// still in it -- stale copies of keys P_4 also holds fresh.  Through the plan
// they are shadowed, but a merge that consumes P_4 as its carry ranks the
// carry's tier freshest, and the stale copy wins there: old values come back,
// and so do erased keys.
//
// At load one half nothing is left over by chance, so the fixture FORCES it:
// 72 keys whose tag under P_o's nonce names bucket 0 of its eight, split over
// the two prefixes P_o merges, with every other key of those prefixes steered
// away from bucket 0.  Sixty-four fit; eight are left over.  The next prefix
// rewrites (or erases) all 72, and then P_(o+2) is built in the same lease.


// Keys held twice in one live table, main and tier together.  A published
// table holds each key at most once (the carry's kNoDedup rests on it).
size_t KeysHeldTwice(const la::LevelArenaEngine& engine) {
  const bs::Layout& layout = engine.layout();
  size_t twice = 0;
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    std::map<uint64_t, int> count;
    const auto scan = [&](const uint8_t* data, const uint64_t* masks,
                          size_t buckets) {
      for (size_t b = 0; b < buckets; ++b) {
        const uint8_t* bucket = data + b * layout.BucketBytes();
        for (uint64_t m = masks[b]; m != 0; m &= m - 1) {
          const size_t slot = static_cast<size_t>(_tzcnt_u64(m));
          ++count[bs::ReadSlotKey(bucket, slot, layout.key_bytes).w0];
        }
      }
    };
    scan(t.data, t.masks, t.main_buckets);
    scan(t.tier_data, t.tier_masks, t.tier_buckets);
    for (const auto& entry : count) twice += entry.second > 1 ? 1 : 0;
  }
  return twice;
}

// Live entries in the tiers of the live tables of `family`.
size_t TierEntriesOf(const la::LevelArenaEngine& engine,
                     const la::Family& family) {
  size_t entries = 0;
  for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
    if (!(t.family == family)) continue;
    for (size_t b = 0; b < t.tier_buckets; ++b) {
      entries += static_cast<size_t>(_mm_popcnt_u64(t.tier_masks[b]));
    }
  }
  return entries;
}

void TestLeaseTierIsEmptiedPerTable() {
  struct Case {
    const char* name;
    unsigned levels;
    unsigned o;  // level 1's forced even partial, digit 2 of its cycle
    unsigned prefixes;
  };
  const Case cases[] = {
      // P_4 is level 1's full table, and the top's carry.
      {"L=2, P_2 into the top's carry", 2, 2, 6},
      // P_4 is adopted by level 2 as its P_1: a duplicate, read correctly.
      {"L=3, P_2 into level 2's adopted P_1", 3, 2, 12},
      // P_8 is level 2's second carry, merged at its digit 2.
      {"L=3, P_6 into level 2's second carry", 3, 6, 12},
  };
  for (const Case& c : cases) {
    for (bool erase : {false, true}) {
      const std::string name =
          std::string(c.name) + (erase ? ", erased" : ", rewritten");
      la::LevelArenaEngine::Options options =
          MakeOptions(4, c.levels, /*top_digit=*/2);
      options.geometry.bank_first = la::BankFirst::kOff;
      la::LevelArenaEngine engine(options);
      const la::LevelArenaGeometry& g = engine.geometry();
      const bs::Layout& layout = engine.layout();
      const std::unique_ptr<bs::AesTagKeys> aes = bs::MakeAesTagKeys(
          microram::crypto::DeriveRoutingAesRoundKeys(*options.secret_seed));
      // P_o's hash: level 1's family for ordinal o, and an unrouted index of
      // log2(2 U_1) bits -- the shape of every digit-2 merge at level 1.
      const la::Family family = la::CanonicalFamily(g, 1, c.o);
      const bs::RebuildNonce nonce = la::FamilyNonce(family);
      const unsigned bits =
          la::MakeMergeShape(g.CarryBuckets(1), 2, 1).block_bits;
      const auto bucket_of = [&](uint64_t key) {
        bs::Table probe = ts::ZeroedTable(1, layout);
        probe.masks[0] = 1;
        ts::PlantEntry(layout, probe.Bucket(0), 0, bs::KeyWords{key}, 0);
        bs::TableView view = bs::View(probe);
        bs::ComputeRoutingTags(view, nonce.real_lo, nonce.real_hi,
                               bs::RoutingIndexMap{}, bits, *aes);
        return ts::SlotTagBitsOf(layout, probe.Bucket(0), 0, bits);
      };
      uint64_t next_key = 1000;
      std::vector<uint64_t> forced;
      for (const bs::KeyWords& key : ts::KeysAtTagIndex(
               layout, nonce.real_lo, nonce.real_hi, bs::RoutingIndexMap{},
               bits, bits, /*target=*/0, 72, &next_key, *aes)) {
        forced.push_back(key.w0);
      }
      const std::set<uint64_t> forced_set(forced.begin(), forced.end());
      std::set<uint64_t> used = forced_set;
      uint64_t next_filler = uint64_t{1} << 30;
      const auto filler = [&](bool avoid_bucket_0) {
        for (;;) {
          const uint64_t key = next_filler++;
          if (used.count(key) != 0) continue;
          if (avoid_bucket_0 && bucket_of(key) == 0) continue;
          used.insert(key);
          return key;
        }
      };

      std::map<uint64_t, std::vector<uint8_t>> model;
      std::set<uint64_t> erased;
      std::vector<uint8_t> value(engine.ValueBytes()), got(engine.ValueBytes());
      const size_t positions = static_cast<size_t>(g.PrefixPositions());
      size_t left_over = 0, twice = 0;
      for (unsigned p = 1; p <= c.prefixes; ++p) {
        std::vector<uint64_t> keys;
        if (p == c.o - 1 || p == c.o) {
          const size_t base = p == c.o - 1 ? 0 : 36;
          keys.assign(forced.begin() + base, forced.begin() + base + 36);
        } else if (p == c.o + 1) {
          keys = forced;
        }
        const bool steer = p == c.o - 1 || p == c.o;
        while (keys.size() < positions) keys.push_back(filler(steer));
        for (uint64_t key : keys) {
          if (erase && p == c.o + 1 && forced_set.count(key) != 0) {
            engine.Erase(key);
            model.erase(key);
            erased.insert(key);
          } else {
            MakeValue(key, p, &value);
            engine.Write(key, value.data());
            model[key] = value;
          }
        }
        if (p == c.o) left_over = TierEntriesOf(engine, family);
        if (p >= c.o) twice = std::max(twice, KeysHeldTwice(engine));
      }
      Expect(left_over > 0, name + ": nothing was left over in P_o's tier, "
                                   "so the case tests nothing");
      Expect(twice == 0, name + ": " + std::to_string(twice) +
                             " keys were held twice in one live table");
      size_t wrong = 0;
      for (const auto& entry : model) {
        if (!engine.Read(entry.first, got.data()) || got != entry.second) {
          ++wrong;
        }
      }
      size_t resurrected = 0;
      for (uint64_t key : erased) {
        if (engine.Read(key, got.data())) ++resurrected;
      }
      Expect(wrong == 0, name + ": " + std::to_string(wrong) +
                             " keys read back a stale or missing value");
      Expect(resurrected == 0, name + ": " + std::to_string(resurrected) +
                                   " erased keys read back as present");
      Expect(engine.ProbeAuditViolations() == 0,
             name + ": a key was really probed twice under one family");
    }
  }
}

// A HELD READER ACROSS THE BANK-FIRST RUN.  The run puts
// two lifecycles over one bank, and neither's slot machine knows the other
// shares its buckets, so what keeps a reader's table intact is the level's
// own rule: a lease on one waits while the other is retired.  Hold a reader
// with level 1 at P_1 and prefixes outstanding, let the level run as far as
// it can -- P_2 into the run bank, and then the digit that would write over
// it -- and check
// that every table the reader could still reach kept its bytes.  The level
// must stop on the bank, not on anything else.
void TestBankFirstHeldReader() {
  struct Case {
    unsigned branching;
    la::BankFirst mode;
  };
  for (const Case& c : {Case{8, la::BankFirst::kNoClone}}) {
    const std::string name = "held reader, B=" + std::to_string(c.branching) +
                             " bank-first " + la::BankFirstName(c.mode);
    la::LevelArenaEngine::Options options =
        MakeOptions(c.branching, 3, 2, /*prefix_flushes=*/2,
                    /*stash_buckets=*/1, /*dense_prefixes=*/c.branching + 1);
    options.geometry.bank_first = c.mode;
    options.flush_policy = la::LevelArenaEngine::FlushPolicy::kHandOver;
    la::LevelArenaEngine engine(options);
    const la::LevelArenaGeometry& g = engine.geometry();
    std::vector<uint8_t> value(engine.ValueBytes(), 0x3C);
    std::map<uint64_t, std::vector<uint8_t>> model;
    uint64_t op = 0;
    const auto write = [&](uint64_t key) {
      MakeValue(key, op++, &value);
      engine.Write(key, value.data());
      model[key] = value;
    };
    // Past a whole level-1 cycle, so that the run bank has been used and
    // retired once, and then to a state with level 1 at P_1 of a cycle and
    // enough complete prefixes waiting for it to run its whole run.
    for (size_t i = 0; i < 4000; ++i) write(i % 199 + 1);
    const auto ready = [&] {
      return engine.level(1).ordinal() % c.branching == 1 &&
             engine.dense().complete_prefixes() - engine.dense().consumed() >=
                 g.ForwardingLeaseDigit(1);
    };
    for (size_t i = 0; i < 200000 && !ready(); ++i) write(i % 199 + 1);
    Expect(ready(), name + ": never reached P_1 with the run outstanding");
    if (!ready()) continue;
    const uint64_t ordinal_before = engine.level(1).ordinal();
    size_t retired_while_held = 0;
    {
      la::ReaderEpoch::Guard guard(engine.publisher().epoch());
      const std::vector<la::PublishedTable> pinned =
          engine.publisher().LiveTables();
      std::map<uint64_t, uint64_t> digests;
      for (const la::PublishedTable& t : pinned) {
        digests[t.table_id] = DigestTable(t, engine.layout());
      }
      for (int i = 0; i < 512 && engine.StepOnce(); ++i) {
      }
      for (const la::PublishedTable& t : pinned) {
        if (engine.publisher().IsLive(t.table_id)) continue;
        ++retired_while_held;
        Expect(DigestTable(t, engine.layout()) == digests[t.table_id],
               name + ": a table a held reader could still probe was "
                      "overwritten after it left the plan");
      }
      // Every table published while the reader was held that has already
      // left the plan again -- P_2 of the run -- is pinned by the same
      // reader, and so is its storage.
      Expect(engine.level(1).last_block() == la::LevelBlock::kBankRetirement,
             name + ": level 1 stopped on " +
                 la::LevelBlockName(engine.level(1).last_block()) +
                 ", not on its bank");
    }
    Expect(engine.level(1).ordinal() == ordinal_before + 1,
           name + ": level 1 went past P_2 of its run, or not as far, with "
                  "a reader pinning P_1 (" +
               std::to_string(engine.level(1).ordinal() - ordinal_before) +
               " digits)");
    Expect(retired_while_held > 0,
           name + ": nothing left the plan while the reader was held");
    // Released, the run completes, and every key reads back.
    engine.RunOwners();
    std::vector<uint8_t> got(engine.ValueBytes());
    size_t wrong = 0;
    for (const auto& entry : model) {
      if (!engine.Read(entry.first, got.data()) || got != entry.second) {
        ++wrong;
      }
    }
    Expect(wrong == 0, name + ": " + std::to_string(wrong) +
                           " keys read back wrong after the reader left");
    Expect(engine.ProbeAuditViolations() == 0,
           name + ": a key was really probed twice under one family");
  }
}

}  // namespace

// ---------------------------------------------------------------------------
// Job deadlines
// ---------------------------------------------------------------------------
//
// A level's next-job deadline (LevelState::NextJobDeadline) is the dense
// prefix count by which that job must publish or the requester waits.  Carry v
// arrives at v P(l), and the level below next needs the inbox it occupies
// either s P(l-1) later -- a middle level at digit 1 or 2, whose other inbox
// holds the adopted P_1 -- or (b + s) P(l-1) later, s being the digit at which
// the level below first takes the forwarding lease.  The top keeps its table
// in a bank and has both inboxes for carries, so it is ALWAYS the long case,
// whatever D is; a rule that tested the digit alone would give D = 1 and 2
// the short one.
//
// Walked over real ordinals and not only the first: every flush settles, and
// after each access every level's deadline is checked against the rule, until
// the top has taken three carries and level 2 has been through every digit.
void TestJobDeadlines() {
  // A worked example, as a literal: B = 8, L = 3, D = 2.
  // The first carry reaches the top at prefix 64, the second can take its
  // other inbox at 128, and the producer next needs the first at 160.
  {
    la::LevelArenaEngine::Options options = MakeOptions(8, 3, 2);
    options.geometry.bank_first = la::BankFirst::kNoClone;
    la::LevelArenaEngine engine(options);
    Expect(engine.level(3).NextJobDeadline() == 160,
           "B=8 L=3 D=2 no-clone: the top's first deadline is " +
               std::to_string(engine.level(3).NextJobDeadline()) +
               ", not 160");
  }
  for (unsigned branching : {4u, 8u}) {
    for (la::BankFirst mode : {la::BankFirst::kOff, la::BankFirst::kNoClone}) {
      uint64_t first_top_deadline = 0;
      for (unsigned top_digit : {1u, 2u, 4u, 8u}) {
        if (top_digit > branching) continue;
        la::LevelArenaEngine::Options options =
            MakeOptions(branching, 3, top_digit);
        options.geometry.bank_first = mode;
        la::LevelArenaEngine engine(options);
        const la::LevelArenaGeometry& g = engine.geometry();
        const unsigned top = g.TopLevel();
        const std::string name = "deadlines, B=" + std::to_string(branching) +
                                 " D=" + std::to_string(top_digit) + " " +
                                 la::BankFirstName(mode);
        const auto window = [&](unsigned l, bool short_window) {
          const uint64_t lease = g.ForwardingLeaseDigit(l - 1);
          return (short_window ? lease : g.Fanout(l - 1) + lease) *
                 g.PrefixProduct(l - 1);
        };
        const auto expected = [&](unsigned l) {
          const uint64_t v = engine.level(l).ordinal() + 1;
          if (l == 1) return v + g.DensePrefixes();
          const bool short_window = l != top && g.CarryDigit(l, v) <= 2;
          return v * g.PrefixProduct(l) + window(l, short_window);
        };
        // Nothing in the top's deadline depends on D.
        if (first_top_deadline == 0) {
          first_top_deadline = engine.level(top).NextJobDeadline();
        }
        Expect(engine.level(top).NextJobDeadline() == first_top_deadline,
               name + ": the top's first deadline depends on D");
        // The slice window is the same rule's tightest case at each level.
        Expect(la::LevelTightestWindowPrefixes(g, top) == window(top, false),
               name + ": the top's slice window is not its deadline window");
        Expect(la::LevelTightestWindowPrefixes(g, 2) == window(2, true),
               name + ": level 2's slice window is not its digit-2 window");

        std::vector<uint8_t> value(engine.ValueBytes(), 0x5A);
        std::set<unsigned> digits;
        size_t mismatches = 0;
        const uint64_t keys = engine.Capacity() / 4 + 1;
        const uint64_t bound =
            4 * 3 * g.PrefixProduct(top) * g.PrefixPositions();
        for (uint64_t i = 0; i < bound && engine.level(top).ordinal() < 3;
             ++i) {
          for (unsigned l = 1; l <= top; ++l) {
            if (engine.level(l).NextJobDeadline() == expected(l)) continue;
            if (mismatches++ < 4) {
              std::fprintf(stderr, "%s: level %u at ordinal %llu: %llu, not %llu\n",
                           name.c_str(), l,
                           static_cast<unsigned long long>(
                               engine.level(l).ordinal()),
                           static_cast<unsigned long long>(
                               engine.level(l).NextJobDeadline()),
                           static_cast<unsigned long long>(expected(l)));
            }
          }
          digits.insert(g.CarryDigit(2, engine.level(2).ordinal() + 1));
          engine.Write(i % keys + 1, value.data());
        }
        Expect(mismatches == 0, name + ": " + std::to_string(mismatches) +
                                    " deadlines broke the rule");
        Expect(engine.level(top).ordinal() >= 3,
               name + ": the top took fewer than three carries");
        Expect(digits.size() == branching,
               name + ": level 2 went through " +
                   std::to_string(digits.size()) + " digits, not all of them");
      }
    }
  }
  std::printf("  job deadlines follow the buffer protocol; the top's never "
              "takes the short window\n");
}

// AN UNSET SEED IS DRAWN PER ENGINE.  If two engines built from one Options
// object shared a seed drawn when the object was made, equal keys would land
// in equal buckets of equally scheduled tables in both -- a correlation an
// observer of both instances could read off the trace.
// The schedule is public and the same here, so every published table's
// OCCUPANCY is the only thing that can tell the keys apart, and it must
// differ; with the seed pinned it must not.
void TestUnsetSeedIsDrawnPerEngine() {
  auto occupancy = [](la::LevelArenaEngine& engine) {
    std::vector<uint64_t> words;
    for (const la::PublishedTable& t : engine.publisher().LiveTables()) {
      for (size_t b = 0; b < t.main_buckets; ++b) words.push_back(t.masks[b]);
    }
    return words;
  };
  auto run = [&](const la::LevelArenaEngine::Options& options) {
    la::LevelArenaEngine a(options), b(options);
    std::vector<uint8_t> value(a.ValueBytes(), 0x5A);
    for (uint64_t key = 1; key <= 3000; ++key) {
      a.Write(key, value.data());
      b.Write(key, value.data());
    }
    const std::vector<uint64_t> in_a = occupancy(a), in_b = occupancy(b);
    Expect(!in_a.empty() && in_a.size() == in_b.size(),
           "two engines on one schedule published different table shapes");
    return in_a == in_b;
  };
  la::LevelArenaEngine::Options options = MakeOptions(4, 3, 4);
  Expect(run(options), "two engines with one PINNED seed placed one key "
                       "sequence differently");
  options.secret_seed.reset();
  Expect(!run(options), "two engines built from one Options without a seed "
                        "placed every key identically, so they share it");
}

// ---------------------------------------------------------------------------
// The cascade's main/tier groups over seeded tiers
// ---------------------------------------------------------------------------
//
// The cascade folds a hashed main and its tier into one step.  After EVERY
// access it must agree with a std::map model on the answer -- the hit flag
// and the value written out -- with the probe audit clean, and a read of a
// seed must find the seed's tombstone flags, read back from the meta byte of
// the entry the access inserted (`erased`, and the unshadowed qualifier it
// inherits).
//
// At the design load no tier holds anything, so the tiers are SEEDED after
// each phase of the workload: live entries and
// tombstones of keys nothing else holds, and -- where an older, disjoint
// table holds a key nothing newer does -- a live entry and a tombstone
// SHADOWING that copy, which must win.  Seeds go round a multi-bucket tier's
// buckets, because the winner's bucket is part of what the workers are told.
// Rebuilds later consume the seeded tiers, which recompute every tag, so a
// planted entry needs only its key, value and meta byte.

// A stored key of the engine's stored width, from an index; the fixtures use
// the *Stored entry points, so a 16-byte key exercises both words.
bs::KeyWords JointKey(uint64_t n, size_t stored_key_bytes) {
  if (stored_key_bytes == 4) return bs::KeyWords{n & 0x7fffffffull};
  if (stored_key_bytes == 16) {
    return bs::KeyWords{n, n * 0x9E3779B97F4A7C15ull + 1};
  }
  return bs::KeyWords{n};
}

// The composed plan, between accesses: an inline engine runs nothing in the
// background, so the plan named here is the one the next access probes.
const bs::ProbePlan& ComposedPlanOf(la::LevelArenaEngine& engine) {
  engine.ProbeListLength();  // composes the dense prefix
  return *engine.publisher().CurrentPlan();
}

// The cascade position (in the live half) of the NEWEST table holding each
// live key: the copy a probe answers from.
std::map<std::pair<uint64_t, uint64_t>, size_t> NewestHolders(
    la::LevelArenaEngine& engine) {
  const bs::ProbePlan& plan = ComposedPlanOf(engine);
  const bs::Layout& layout = engine.layout();
  std::map<std::pair<uint64_t, uint64_t>, size_t> newest;
  // Oldest first, so a newer copy overwrites.
  for (size_t i = plan.tables.size(); i-- > plan.first_live;) {
    const bs::TableEntry& t = plan.tables[i];
    for (size_t b = 0; b < t.num_buckets; ++b) {
      const uint8_t* bucket = t.data + b * layout.BucketBytes();
      for (uint64_t m = t.masks[b]; m != 0; m &= m - 1) {
        const bs::KeyWords k = bs::ReadSlotKey(
            bucket, static_cast<size_t>(_tzcnt_u64(m)), layout.key_bytes);
        newest[{k.w0, k.w1}] = i - plan.first_live;
      }
    }
  }
  return newest;
}

// The width of the tier holding a live slot of `key` in the composed plan,
// and the bucket it is in; 0 if no tier holds it.  Tiers are a few buckets,
// so this is cheap where NewestHolders is not.
size_t TierHolding(la::LevelArenaEngine& engine, bs::KeyWords key,
                   size_t* bucket_out) {
  const bs::ProbePlan& plan = ComposedPlanOf(engine);
  const bs::Layout& layout = engine.layout();
  for (size_t i = plan.first_live; i < plan.tables.size(); ++i) {
    const bs::TableEntry& t = plan.tables[i];
    if (t.tier != 1) continue;
    for (size_t b = 0; b < t.num_buckets; ++b) {
      const uint8_t* bucket = t.data + b * layout.BucketBytes();
      for (uint64_t m = t.masks[b]; m != 0; m &= m - 1) {
        if (bs::ReadSlotKey(bucket, static_cast<size_t>(_tzcnt_u64(m)),
                            layout.key_bytes) == key) {
          *bucket_out = b;
          return t.num_buckets;
        }
      }
    }
  }
  return 0;
}

// A seed the fixture planted and no access has read yet.
struct PlantedSeed {
  uint64_t index = 0;
  std::vector<uint8_t> bytes;  // the value, for a live seed
  uint8_t meta = 0;
};
using SeedKey = std::pair<uint64_t, uint64_t>;

// THE SEEDS A REBUILD NEVER SAW.  A level binds its next merge -- and
// snapshots the older operand's tier masks -- as soon as it publishes the
// partial (speculative preparation), because a published tier is immutable.
// A seed planted after that binding is visible to probes until the merge runs
// and is absent from its output, which no real run can produce.  Such seeds
// are moved to `lost`: the newest copy of each pending key is compared with
// what was planted, and a key whose planted copy is gone or superseded is
// indeterminate for the model.  The two engines still have to agree on it.
void DropLostSeeds(la::LevelArenaEngine& engine,
                   std::map<SeedKey, PlantedSeed>* pending,
                   std::vector<uint64_t>* lost) {
  if (pending->empty()) return;
  const bs::ProbePlan& plan = ComposedPlanOf(engine);
  const bs::Layout& layout = engine.layout();
  const uint8_t flags = bs::kMetaErased | bs::kMetaUnshadowed;
  std::set<SeedKey> seen, superseded;
  for (size_t i = plan.first_live; i < plan.tables.size(); ++i) {
    const bs::TableEntry& t = plan.tables[i];
    // Newest first: tables in probe order, a run's buckets from its last.
    for (size_t b = t.num_buckets; b-- > 0;) {
      const uint8_t* bucket = t.data + b * layout.BucketBytes();
      for (uint64_t m = t.masks[b]; m != 0; m &= m - 1) {
        const size_t slot = static_cast<size_t>(_tzcnt_u64(m));
        const bs::KeyWords k = bs::ReadSlotKey(bucket, slot, layout.key_bytes);
        const SeedKey sk{k.w0, k.w1};
        const auto it = pending->find(sk);
        if (it == pending->end() || !seen.insert(sk).second) continue;
        const uint8_t meta =
            bucket[layout.MetaLine() * bs::kBucketCapacity + slot] & flags;
        bool same = meta == it->second.meta;
        if (same && (meta & bs::kMetaErased) == 0) {
          for (size_t v = 0; v < it->second.bytes.size(); ++v) {
            same &= bucket[(layout.key_bytes + v) * bs::kBucketCapacity +
                           slot] == it->second.bytes[v];
          }
        }
        if (!same) superseded.insert(sk);
      }
    }
  }
  for (auto it = pending->begin(); it != pending->end();) {
    if (seen.count(it->first) == 0 || superseded.count(it->first) != 0) {
      lost->push_back(it->second.index);
      it = pending->erase(it);
    } else {
      ++it;
    }
  }
}

// Public plan shapes the joint step has to get right, for the tallies.
struct JointPlanShape {
  size_t groups = 0;
  bool multi_bucket_tier = false;
  // A tier between two hashed tables of NESTED windows: a group followed by
  // a hashed table whose window lies inside the group's (a chain temporary
  // probed ahead of the source it consumed chunks of).
  bool nested = false;
  // The value-worker boundary falls between a main and its tier.
  bool split = false;
};

JointPlanShape ShapeOf(la::LevelArenaEngine& engine, unsigned value_tail) {
  const bs::ProbePlan& plan = ComposedPlanOf(engine);
  const bs::TableEntry* t = plan.tables.data() + plan.first_live;
  const size_t n = plan.tables.size() - plan.first_live;
  JointPlanShape shape;
  for (size_t i = 0; i + 1 < n; ++i) {
    if (t[i].kind != bs::TableKind::kHashed || t[i + 1].tier != 1) continue;
    ++shape.groups;
    shape.multi_bucket_tier |= t[i + 1].num_buckets > 1;
    if (i + 2 < n && t[i + 2].kind == bs::TableKind::kHashed &&
        t[i + 2].window_end > t[i].window_begin) {
      shape.nested = true;
    }
  }
  if (engine.ValueWorkers() != 0) {
    const size_t boundary =
        n - std::min<size_t>(value_tail, n - 1);
    shape.split = boundary < n && boundary >= 1 && t[boundary].tier == 1 &&
                  t[boundary - 1].kind == bs::TableKind::kHashed;
  }
  return shape;
}

struct JointCase {
  const char* name;
  unsigned branching, levels, top_digit;
  size_t tier_buckets;
  size_t key_bytes, value_bytes;  // user widths
  unsigned value_workers, value_tail;
  bool value_serial;
  unsigned rounds;
};

struct JointTally {
  size_t cases = 0, accesses = 0, tiers_seeded = 0, seeds = 0, shadowing = 0;
  size_t tier_hits = 0, tier_tombstones = 0;
  size_t multi_bucket_tier_hits = 0, bucket_beyond_first_hits = 0;
  size_t split_accesses = 0, nested_accesses = 0;
  size_t lost_seeds = 0;
  bool residual_case = false;
};

void TestTierGroupsAgreeWithModel(const JointCase& c, JointTally* tally) {
  const std::string name = std::string("tier groups ") + c.name;
  la::LevelArenaEngine::Options options =
      MakeOptions(c.branching, c.levels, c.top_digit);
  options.geometry.tier_buckets = c.tier_buckets;
  options.key_bytes = c.key_bytes;
  options.value_bytes = c.value_bytes;
  options.value_workers = c.value_workers;
  options.value_tail = c.value_tail;
  options.value_serial = c.value_serial;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(
      0x0DEA0510ull + 131 * c.branching + 17 * c.levels + c.key_bytes);
  la::LevelArenaEngine engine(options);
  Expect(engine.ValueWorkers() == c.value_workers,
         name + ": the value workers are not running under the audit");

  const bs::Layout& layout = engine.layout();
  const size_t kb = layout.key_bytes;
  const size_t vb = engine.ValueBytes();
  std::map<uint64_t, std::vector<uint8_t>> model;  // absent unless here
  std::vector<uint8_t> value(vb), got(vb);
  uint8_t found_flags = 0;  // the meta flags of the last access's insertion
  std::mt19937_64 rng(0x7131 + 7 * c.branching + c.value_tail);
  JointPlanShape shape = ShapeOf(engine, c.value_tail);
  uint64_t shape_flushes = engine.FlushCount();
  size_t mismatches = 0;
  std::map<std::string, size_t> kinds;
  const auto fail = [&](const std::string& what, uint64_t index) {
    ++kinds[what];
    if (mismatches++ < 6) {
      std::fprintf(stderr, "%s: %s (key index %llu, access %zu)\n",
                   name.c_str(), what.c_str(),
                   static_cast<unsigned long long>(index), tally->accesses);
    }
  };

  enum Op { kRead, kWrite, kErase, kExchange, kExchangeInsert, kUnprobed };
  // Seeds planted and not yet read (DropLostSeeds), and keys whose state the
  // model cannot know because a rebuild never saw their seed.  An access to
  // an indeterminate key makes it definite again: whatever it found, the
  // access re-inserted it at the top.
  std::map<SeedKey, PlantedSeed> pending;
  std::set<uint64_t> indeterminate;
  size_t lost_seeds = 0;
  // One access, checked.  Returns the hit flag the public call reports.
  const auto access = [&](Op op, uint64_t index, uint64_t gen) {
    if (engine.FlushCount() != shape_flushes) {
      std::vector<uint64_t> lost;
      DropLostSeeds(engine, &pending, &lost);
      for (uint64_t l : lost) {
        indeterminate.insert(l);
        model.erase(l);
      }
      lost_seeds += lost.size();
      shape = ShapeOf(engine, c.value_tail);
      shape_flushes = engine.FlushCount();
    }
    const bool definite = indeterminate.count(index) == 0;
    pending.erase({JointKey(index, kb).w0, JointKey(index, kb).w1});
    tally->split_accesses += shape.split && op != kUnprobed;
    tally->nested_accesses += shape.nested && op != kUnprobed;
    const bs::KeyWords key = JointKey(index, kb);
    uint8_t* const insert = engine.dense().NextInsertBucket();
    const size_t slot = engine.dense().NextInsertSlot();
    MakeValue(index, gen, &value);
    std::fill(got.begin(), got.end(), 0xEE);
    const auto it = model.find(index);
    const bool present = it != model.end();
    const std::vector<uint8_t> before =
        present ? it->second : std::vector<uint8_t>(vb, 0);
    bool rs = true;
    switch (op) {
      case kRead:
        rs = engine.ReadStored(key, got.data());
        if (definite && (rs != present || (present && got != before))) {
          fail("a read disagrees with the model", index);
        }
        if (rs) {
          model[index] = got;
        } else {
          model.erase(index);
        }
        break;
      case kWrite:
        engine.ReadThenWriteStored(key, value.data());
        model[index] = value;
        break;
      case kErase:
        rs = engine.EraseStored(key, got.data());
        if (definite && (rs != present || got != before)) {
          fail("an erase disagrees with the model", index);
        }
        model.erase(index);
        break;
      case kExchange:
      case kExchangeInsert: {
        const bool insert_new = op == kExchangeInsert;
        rs = engine.ExchangeStored(key, value.data(), got.data(), insert_new);
        if (definite && (rs != present || got != before)) {
          fail("an exchange disagrees with the model", index);
        }
        if (rs || insert_new) {
          model[index] = value;
        } else {
          model.erase(index);
        }
        break;
      }
      case kUnprobed:
        engine.WriteWithoutProbeStored(key, value.data());
        model[index] = value;
        break;
    }
    indeterminate.erase(index);
    ++tally->accesses;
    const uint8_t flags = bs::kMetaErased | bs::kMetaUnshadowed;
    found_flags =
        insert[layout.MetaLine() * bs::kBucketCapacity + slot] & flags;
    if (op == kRead && ((found_flags & bs::kMetaErased) != 0) == rs) {
      fail("a read's insertion is not a tombstone exactly on a miss", index);
    }
    if (engine.ProbeAuditViolations() != 0) {
      fail("the cascade real-probed one family twice for one key", index);
    }
    return rs;
  };

  // The ordinary key space: written once up front, then the workload's.  The
  // CANDIDATES are written up front and never touched again until a round
  // seeds a shadowing copy of one, so their newest copy is wherever the
  // rebuilds put it.  Fresh keys are never written at all.
  const uint64_t ordinary = std::max<uint64_t>(64, engine.Capacity() / 8);
  const uint64_t candidate_base = 1u << 20, fresh_base = 1u << 24;
  const uint64_t absent_base = 1u << 28;
  const uint64_t candidate_count = std::max<uint64_t>(64, engine.Capacity() / 16);
  std::vector<uint64_t> candidates;
  for (uint64_t k = 0; k < candidate_count; ++k) {
    access(kWrite, candidate_base + k, 1);
    candidates.push_back(candidate_base + k);
  }
  for (uint64_t k = 0; k < ordinary; ++k) access(kWrite, k + 1, 1);
  uint64_t fresh = fresh_base;
  std::vector<uint64_t> seeded;  // every key index any round planted
  const auto random_op = [&](uint64_t gen) {
    const unsigned r = static_cast<unsigned>(rng() % 16);
    uint64_t index;
    if (r < 3 && !seeded.empty()) {
      index = seeded[rng() % seeded.size()];
    } else if (r < 5) {
      index = absent_base + rng() % 256;  // absent, or made present below
    } else {
      index = rng() % ordinary + 1;
    }
    const Op op = r < 7 ? kRead
                  : r < 10 ? kWrite
                  : r < 12 ? kErase
                  : r < 13 ? kExchange
                  : r < 14 ? kExchangeInsert
                  : r < 15 ? kRead
                           : kUnprobed;
    access(op, index, gen);
  };

  for (unsigned round = 0; round < c.rounds; ++round) {
    // Advance the hierarchy: new publications, chain temporaries, new tiers.
    const size_t advance = static_cast<size_t>(engine.Capacity() / 3);
    for (size_t s = 0; s < advance; ++s) random_op(1000 + round * 100000 + s);

    // Seed every tier of the composed plan.
    const auto holders = NewestHolders(engine);
    const bs::ProbePlan& ps = ComposedPlanOf(engine);
    const size_t first = ps.first_live, n = ps.tables.size() - first;
    std::vector<uint64_t> round_live, round_tomb, round_shadow;
    for (size_t i = 0; i + 1 < n; ++i) {
      const bs::TableEntry& main = ps.tables[first + i];
      const bs::TableEntry& tier = ps.tables[first + i + 1];
      if (main.kind != bs::TableKind::kHashed || tier.tier != 1) continue;
      ++tally->tiers_seeded;
      size_t planted = 0;
      // The next free slot of bucket `planted mod width`.
      const auto plant = [&](uint64_t index, const std::vector<uint8_t>* bytes,
                             uint8_t meta) {
        const size_t bk = planted % tier.num_buckets;
        const uint64_t used = tier.masks[bk];
        if (~used == 0) return false;
        const size_t slot = static_cast<size_t>(_tzcnt_u64(~used));
        uint8_t* bucket = tier.data + bk * layout.BucketBytes();
        bs::WriteSlotKey(bucket, slot, kb, JointKey(index, kb));
        for (size_t v = 0; v < vb; ++v) {
          bucket[(kb + v) * bs::kBucketCapacity + slot] =
              bytes != nullptr ? (*bytes)[v] : 0;
        }
        bucket[layout.MetaLine() * bs::kBucketCapacity + slot] = meta;
        tier.masks[bk] |= uint64_t{1} << slot;
        ++planted;
        ++tally->seeds;
        const bs::KeyWords key = JointKey(index, kb);
        PlantedSeed& seed = pending[{key.w0, key.w1}];
        seed.index = index;
        seed.meta = meta & (bs::kMetaErased | bs::kMetaUnshadowed);
        seed.bytes = bytes != nullptr ? *bytes : std::vector<uint8_t>();
        return true;
      };
      // Fresh keys: three live entries and an unshadowed tombstone.
      for (int s = 0; s < 3; ++s) {
        const uint64_t index = fresh++;
        MakeValue(index, 9, &value);
        if (plant(index, &value, 0)) {
          model[index] = value;
          round_live.push_back(index);
        }
      }
      {
        const uint64_t index = fresh++;
        if (plant(index, nullptr, bs::kMetaErased | bs::kMetaUnshadowed)) {
          model.erase(index);
          round_tomb.push_back(index);
        }
      }
      // Shadowing copies: a candidate whose newest copy is in an OLDER,
      // DISJOINT table, so this tier's copy is the freshest.
      for (int s = 0; s < 2; ++s) {
        for (size_t k = 0; k < candidates.size(); ++k) {
          const uint64_t index = candidates[k];
          const bs::KeyWords key = JointKey(index, kb);
          const auto h = holders.find({key.w0, key.w1});
          if (h == holders.end() || h->second <= i + 1 ||
              ps.tables[first + h->second].window_end > main.window_begin) {
            continue;
          }
          candidates.erase(candidates.begin() + static_cast<ptrdiff_t>(k));
          if (s == 0) {
            MakeValue(index, 77 + round, &value);
            if (plant(index, &value, 0)) {
              model[index] = value;
              round_live.push_back(index);
              ++tally->shadowing;
            }
          } else if (plant(index, nullptr, bs::kMetaErased)) {
            model.erase(index);
            round_tomb.push_back(index);
            round_shadow.push_back(index);
            ++tally->shadowing;
          }
          break;
        }
      }
    }
    // Every seed read once, untouched, in a shared random order, between
    // ordinary accesses: each is a tier hit (a value or a tombstone).
    std::vector<uint64_t> order = round_live;
    order.insert(order.end(), round_tomb.begin(), round_tomb.end());
    std::shuffle(order.begin(), order.end(), rng);
    for (size_t r = 0; r < order.size(); ++r) {
      // An ordinary access between two seed reads, flushes included.
      if (r != 0) random_op(500000 + r);
      const uint64_t index = order[r];
      const bool tomb = std::find(round_tomb.begin(), round_tomb.end(),
                                  index) != round_tomb.end();
      // The tier holding it (a rebuild may have consumed the one it was
      // planted in), before the read re-inserts it at the top.
      size_t bucket_in_tier = 0;
      const size_t tier_width =
          TierHolding(engine, JointKey(index, kb), &bucket_in_tier);
      const bool definite = indeterminate.count(index) == 0;
      const bool found = access(kRead, index, 0);
      if (!definite) continue;
      if (found == tomb) {
        fail(tomb ? "a tier tombstone did not read as absent"
                  : "a tier entry was not found",
             index);
      }
      if (tier_width != 0) {
        // The newest copy is the planted one (it is definite), so the flags
        // found are the ones planted.
        const bool shadowing = std::find(round_shadow.begin(),
                                         round_shadow.end(), index) !=
                               round_shadow.end();
        const uint8_t planted_flags =
            !tomb ? 0
                  : shadowing ? bs::kMetaErased
                              : bs::kMetaErased | bs::kMetaUnshadowed;
        if (found_flags != planted_flags) {
          fail("a tier seed's tombstone flags were not the ones found",
               index);
        }
      }
      if (tier_width != 0) {
        tally->tier_hits += !tomb;
        tally->tier_tombstones += tomb;
        tally->multi_bucket_tier_hits += tier_width > 1;
        tally->bucket_beyond_first_hits += bucket_in_tier > 0;
      }
    }
    seeded.insert(seeded.end(), order.begin(), order.end());
  }

  // Quiesced: every modelled key and every seeded key, once more.
  engine.Drain();
  std::vector<uint64_t> modelled;
  for (const auto& entry : model) modelled.push_back(entry.first);
  for (uint64_t index : modelled) access(kRead, index, 0);
  for (uint64_t index : seeded) access(kRead, index, 0);
  ++tally->cases;
  tally->lost_seeds += lost_seeds;
  std::string summary;
  for (const auto& kind : kinds) {
    summary += "; " + kind.first + " x" + std::to_string(kind.second);
  }
  Expect(mismatches == 0, name + ": " + std::to_string(mismatches) +
                              " disagreements" + summary);
  Expect(engine.RealProbes() > 0, name + ": the audit counted nothing");
}

// The cases: B = 2/4/8, stored keys of 4/8/16 bytes, values of 8/16/48/64,
// one- to three-bucket tiers, no workers and serial or threaded workers with
// every tail from 0 to 3.  Tails 1 and 3 put the boundary between the top's
// main and tier, or between the next group's; the tallies require that some
// access ran each such split, and a nested window.
void TestTierGroupsAgreeWithModel() {
  const JointCase cases[] = {
      {"B=2 L=3", 2, 3, 1, 1, 8, 16, 0, 0, false, 3},
      {"B=2 L=4 4-byte keys", 2, 4, 2, 1, 4, 8, 0, 0, false, 3},
      {"B=4 L=3 two-bucket tiers", 4, 3, 4, 2, 8, 16, 0, 0, false, 3},
      {"B=8 L=2", 8, 2, 4, 1, 16, 64, 0, 0, false, 3},
      {"B=8 L=3 three-bucket tiers", 8, 3, 4, 3, 8, 48, 0, 0, false, 3},
      {"B=4 L=3 16-byte keys", 4, 3, 2, 1, 16, 8, 0, 0, false, 3},
      // Value workers, each tail.
      {"B=2 L=3 W=2 k=0", 2, 3, 1, 1, 8, 16, 2, 0, true, 3},
      {"B=2 L=3 W=2 k=1", 2, 3, 1, 1, 8, 16, 2, 1, true, 3},
      {"B=4 L=3 W=3 k=2 two-bucket", 4, 3, 4, 2, 8, 48, 3, 2, false, 3},
      {"B=4 L=3 W=3 k=3", 4, 3, 2, 1, 16, 64, 3, 3, true, 3},
      {"B=8 L=3 W=2 k=1 three-bucket", 8, 3, 4, 3, 8, 64, 2, 1, false, 3},
      {"B=8 L=3 W=4 k=3 4-byte keys", 8, 3, 4, 1, 4, 16, 4, 3, true, 3},
      {"B=8 L=2 W=1 k=1", 8, 2, 4, 2, 8, 8, 1, 1, true, 3},
  };
  JointTally tally;
  for (const JointCase& c : cases) TestTierGroupsAgreeWithModel(c, &tally);
  Expect(tally.tier_hits > 0 && tally.tier_tombstones > 0,
         "tier groups: no tier hit or tier tombstone was exercised");
  Expect(tally.shadowing > 0,
         "tier groups: no tier copy shadowed a deeper one");
  Expect(tally.multi_bucket_tier_hits > 0,
         "tier groups: no multi-bucket tier was hit");
  Expect(tally.split_accesses > 0,
         "tier groups: no access split a main from its tier at the "
         "value-worker boundary");
  Expect(tally.nested_accesses > 0,
         "tier groups: no plan put a tier between hashed tables of "
         "nested windows");
  std::printf("  tier groups: %zu cases, %zu accesses checked; %zu "
              "tiers seeded with %zu entries (%zu shadowing a deeper copy); "
              "%zu tier hits and %zu tier tombstones (%zu in multi-bucket "
              "tiers); %zu accesses with a split group, %zu with nested "
              "windows; %zu seeds planted after "
              "a merge had bound their tier\n",
              tally.cases, tally.accesses, tally.tiers_seeded, tally.seeds,
              tally.shadowing, tally.tier_hits, tally.tier_tombstones,
              tally.multi_bucket_tier_hits, tally.split_accesses,
              tally.nested_accesses, tally.lost_seeds);
}

// A TIER HIT MUST NOT TURN LATER PROBES REAL, and a fresher copy must silence
// the tier's family -- a residual-tier counterexample to naive gating, on
// this engine's tiers.
//   1. a key sits ONLY in the tier of a hashed table T with a hashed table
//      below it;
//   2. its first read real-probes every hashed table down to and including
//      T's main -- whose address was chosen before anything matched -- and
//      dummies every table below,
//      because the tier's hit gates them;
//   3. the read re-inserts it at the top, so the second read finds it in the
//      current stash and real-probes NOTHING: the old tier entry, still live
//      and still matching, must not keep T's family real.
void TestResidualHitDoesNotForceLaterRealProbes(unsigned branching,
                                                unsigned value_workers) {
  const std::string name = "residual gate B=" + std::to_string(branching) +
                           " W=" + std::to_string(value_workers);
  la::LevelArenaEngine::Options options =
      MakeOptions(branching, branching == 2 ? 5 : 3, 2);
  options.geometry.tier_buckets = 2;
  options.value_bytes = 16;
  options.value_workers = value_workers;
  options.value_tail = 1;
  options.value_serial = true;
  la::LevelArenaEngine engine(options);
  const bs::Layout& layout = engine.layout();
  std::vector<uint8_t> value(engine.ValueBytes()), out(engine.ValueBytes());
  const uint64_t keys = engine.Capacity() / 4;
  std::mt19937_64 rng(0x5EEE + branching);
  for (uint64_t k = 1; k <= keys; ++k) {
    MakeValue(k, 1, &value);
    engine.Write(k, value.data());
  }
  // Until a group has a hashed table below it, and the next insertion leaves
  // the current unit open (a flush would carry the re-inserted copy into a
  // hashed table before the second read).
  size_t group = 0, below = 0, expected_real = 0;
  for (size_t tries = 0;; ++tries) {
    if (tries > 4 * engine.Capacity()) {
      Expect(false, name + ": no group ever had a hashed table below it");
      return;
    }
    const bs::ProbePlan& plan = ComposedPlanOf(engine);
    const bs::TableEntry* t = plan.tables.data() + plan.first_live;
    const size_t n = plan.tables.size() - plan.first_live;
    // The DEEPEST group with a hashed table below it, so that the first
    // read's real probes are as many as the plan allows.
    group = n;
    for (size_t i = 0; i + 2 < n; ++i) {
      if (t[i].kind != bs::TableKind::kHashed || t[i + 1].tier != 1) continue;
      for (size_t j = i + 2; j < n; ++j) {
        if (t[j].kind == bs::TableKind::kHashed) {
          group = i;
          break;
        }
      }
    }
    const bool room = engine.dense().NextInsertSlot() + 2 <
                      bs::kBucketCapacity;
    expected_real = below = 0;
    for (size_t i = 0; i < n && group != n; ++i) {
      if (t[i].kind != bs::TableKind::kHashed) continue;
      (i <= group ? expected_real : below) += 1;
    }
    // Two real probes at least: a hashed table above the group's own main.
    if (group != n && room && expected_real >= 2) {
      // Plant a key nothing else holds in the group's tier.
      const bs::TableEntry& tier = t[group + 1];
      const size_t bk = tier.num_buckets - 1;  // the run's newest bucket
      const size_t slot = static_cast<size_t>(_tzcnt_u64(~tier.masks[bk]));
      uint8_t* bucket = tier.data + bk * layout.BucketBytes();
      bs::WriteSlotKey(bucket, slot, layout.key_bytes, bs::KeyWords{900000});
      MakeValue(900000, 5, &value);
      for (size_t v = 0; v < value.size(); ++v) {
        bucket[(layout.key_bytes + v) * bs::kBucketCapacity + slot] = value[v];
      }
      bucket[layout.MetaLine() * bs::kBucketCapacity + slot] = 0;
      tier.masks[bk] |= uint64_t{1} << slot;
      break;
    }
    engine.Read(rng() % keys + 1, out.data());
  }
  Expect(below > 0, name + ": nothing hashed below the seeded group");
  const uint64_t before = engine.RealProbes();
  Expect(engine.Read(900000, out.data()) && out == value,
         name + ": the tier entry was not found");
  Expect(engine.RealProbes() - before == expected_real,
         name + ": the first read real-probed " +
             std::to_string(engine.RealProbes() - before) + " tables, not " +
             "the " + std::to_string(expected_real) +
             " down to the tier's own main");
  const uint64_t after_first = engine.RealProbes();
  Expect(engine.Read(900000, out.data()) && out == value,
         name + ": the re-inserted copy was not found");
  Expect(engine.RealProbes() == after_first,
         name + ": a read that found its key in the current stash "
                "real-probed a table; the old tier entry kept its family real");
  Expect(engine.ProbeAuditViolations() == 0,
         name + ": the residual scenario real-probed a family twice");
  std::printf("  %s: first read %zu real probes (%zu hashed tables dummy "
              "below), second read 0\n",
              name.c_str(), expected_real, below);
}

int main() {
  TestUnsetSeedIsDrawnPerEngine();
  TestSpeculativePreparationValues();
  TestPublicationTransactions();
  TestPlanPoolExhaustionAndRecovery();
  TestDensePrefixRing();
  TestPrefixRetirementGapIsNotReclaimed();
  TestFamilyHistorySurvivesASwap();
  TestOverlappingRequestsRefused();
  TestAdoptionPublishesNothing();
  TestTwoInboxProgress();
  TestBinaryBufferSlack();
  TestPartialPrefixVisibility();
  TestHeldReaderAcrossPublication();
  TestCarryValidation();
  TestBlockedReasonsAreAttributed();
  TestFailedStepKeepsItsPrefix();
  TestInlineStepFailureIsLatched();
  TestLeaseTierIsEmptiedPerTable();
  TestBankFirstHeldReader();
  TestInboxRetirementIsAttributed();
  TestWideKeysAndValues(20);
  TestWideKeysAndValues(12);
  TestChainsAndCycles();
  TestJobDeadlines();
  TestTierGroupsAgreeWithModel();
  for (unsigned branching : {2u, 8u}) {
    for (unsigned workers : {0u, 2u}) {
      TestResidualHitDoesNotForceLaterRealProbes(branching, workers);
    }
  }
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena engine checks failed\n", failures);
    return 1;
  }
  std::printf("level-arena engine tests passed\n");
  return 0;
}
