// Residual-stash overflow is a REPORTED failure, not a silent truncation.
//
// Every route and fold an engine runs is a bounded-capacity operation: a
// MergeSplit that cannot place an entry sheds it into a per-butterfly-level
// residual stash, and a stash that cannot hold what was shed has to say so.
// The kernels take that as a template parameter, and with CheckOverflow=false
// they DROP the surplus and return true -- which is the right contract only
// for a caller that has already proved the capacity.  An engine has not: it
// publishes the routed table and republishes the stash as a tier, so a
// truncation there loses records from both.
//
// The bug class this file guards against is an engine's route, fold or
// stash-merge call taking the unchecked default.  What it pins is the
// kernels' side of that contract:
//
//   - the primitive's two contracts, so "unchecked truncates" stays a stated
//     fact rather than a rediscovered one;
//   - the route reporting an overflow of its stash;
//   - the checked and unchecked kernels producing IDENTICAL bytes whenever
//     the capacity holds, so checking preserves successful output;
//   - a successful route conserving every record across table and stashes.
//
// Determinism: the fixture overloads a table well past load 0.5 under a fixed
// seed, so the shed counts are exact numbers this test measures and then
// builds its capacities from.  No fixture waits for a naturally occurring
// overflow under a secret production seed.

#include "src/oram/rebuild/cpu_byteslice_stash_rebuild.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <set>
#include <string>
#include <vector>

namespace {

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::OwnedLevelStashes;

constexpr size_t kSlots = bs::kBucketCapacity;

bs::StashLayout FixtureLayout() {
  bs::StashLayout layout;  // 8-byte key, 16-byte value, 4 tag bytes
  return layout;
}

void WriteFixtureKey(uint8_t* bucket, size_t slot, uint64_t key) {
  bs::WriteSlotKey(bucket, slot, 8, bs::KeyWords{key, 0});
}

uint64_t ReadFixtureKey(const uint8_t* bucket, size_t slot) {
  return bs::ReadSlotKey(bucket, slot, 8).w0;
}

// One overloaded table plus a copy of it, tagged under a fixed nonce.  `fill`
// above kStashTargetRealPerBucket is what makes the butterfly shed at all.
struct OverloadedTable {
  bs::Table table;
  std::vector<uint8_t> pristine;
  std::vector<uint64_t> pristine_masks;

  OverloadedTable(size_t num_buckets, size_t fill, unsigned levels,
                  uint64_t seed)
      : table(bs::Table::Create(num_buckets, FixtureLayout().Base())) {
    const bs::StashLayout layout = FixtureLayout();
    std::memset(table.data.get(), 0, num_buckets * layout.BucketBytes());
    std::mt19937_64 rng(seed);
    uint64_t key = 1;
    for (size_t b = 0; b < num_buckets; ++b) {
      for (size_t i = 0; i < fill; ++i) {
        WriteFixtureKey(table.Bucket(b), i, key++);
        for (size_t vb = 0; vb < layout.value_bytes; ++vb) {
          table.Bucket(b)[(layout.key_bytes + vb) * kSlots + i] =
              static_cast<uint8_t>(rng());
        }
      }
      table.masks[b] = bs::LowMask64(static_cast<unsigned>(fill));
    }
    bs::ComputeRoutingTags(bs::View(table), 0xA1A1 ^ seed, 0xB2B2 ^ seed,
                           bs::RoutingIndexMap{}, levels);
    pristine.assign(table.data.get(),
                    table.data.get() + num_buckets * layout.BucketBytes());
    pristine_masks.assign(table.masks.get(), table.masks.get() + num_buckets);
  }

  // Every route below starts from the same tagged bytes; a route rewrites the
  // table in place.
  void Restore() {
    std::memcpy(table.data.get(), pristine.data(), pristine.size());
    std::memcpy(table.masks.get(), pristine_masks.data(),
                pristine_masks.size() * sizeof(uint64_t));
  }

  bs::TableView View() { return bs::View(table); }
};

std::multiset<uint64_t> StashKeySet(const bs::ResidualStash* stashes,
                                    size_t count) {
  std::multiset<uint64_t> keys;
  for (size_t s = 0; s < count; ++s) {
    for (size_t b = 0; b < stashes[s].num_buckets; ++b) {
      for (size_t slot = 0; slot < kSlots; ++slot) {
        if (!((stashes[s].masks[b] >> slot) & 1)) continue;
        keys.insert(ReadFixtureKey(stashes[s].Bucket(b), slot));
      }
    }
  }
  return keys;
}

// ---------------------------------------------------------------------------
// 1. The primitive's two contracts
// ---------------------------------------------------------------------------
//
// The minimal witness: two disjoint 64-record sets folded into one 64-slot
// stash.  Unchecked, both folds report success and 64
// records are gone; checked, the second reports overflow.  This is the fact
// the whole file exists to keep out of the engine.
void TestUncheckedFoldTruncatesAndCheckedReports() {
  const bs::StashLayout layout = FixtureLayout();
  OwnedLevelStashes source(1, 1, layout);
  OwnedLevelStashes unchecked(1, 1, layout);
  OwnedLevelStashes checked(1, 1, layout);

  const auto fill_source = [&](uint64_t first) {
    source.slots[0].masks[0] = ~uint64_t{0};
    for (size_t s = 0; s < kSlots; ++s) {
      WriteFixtureKey(source.slots[0].Bucket(0), s, first + s);
    }
  };

  fill_source(1);
  Expect(bs::MergeBucketIntoResidualStash</*CheckOverflow=*/false>(
             unchecked.slots[0], source.slots[0].Bucket(0),
             source.slots[0].masks[0], layout.Base().PayloadLines()),
         "the first unchecked fold failed");
  Expect(bs::MergeBucketIntoResidualStash</*CheckOverflow=*/true>(
             checked.slots[0], source.slots[0].Bucket(0),
             source.slots[0].masks[0], layout.Base().PayloadLines()),
         "the first checked fold failed");

  fill_source(1 + kSlots);
  const bool unchecked_ok = bs::MergeBucketIntoResidualStash<
      /*CheckOverflow=*/false>(unchecked.slots[0], source.slots[0].Bucket(0),
                               source.slots[0].masks[0],
                               layout.Base().PayloadLines());
  const bool checked_ok = bs::MergeBucketIntoResidualStash<
      /*CheckOverflow=*/true>(checked.slots[0], source.slots[0].Bucket(0),
                              source.slots[0].masks[0],
                              layout.Base().PayloadLines());
  Expect(unchecked_ok, "the unchecked fold did not report success");
  Expect(unchecked.Count() == kSlots,
         "the unchecked fold did not keep exactly one bucket");
  Expect(!checked_ok, "the checked fold did not report the overflow");
  Expect(checked.Count() == kSlots,
         "the checked fold changed the stash it refused");
  std::printf("  primitive: 128 records into 64 slots -- unchecked reports "
              "success and keeps %zu, checked reports overflow\n",
              unchecked.Count());
}

// The same fold under two different claimant partitions keeps the same
// residual SET and different residual BYTES.  It is here because it is the
// reason a conservation oracle over residuals must be a key/version
// statement and not a memcmp of the residual storage: slot order is a
// function of which worker finished what, and a stash is a set.
void TestSlotPartitionKeepsTheResidualSetNotItsBytes() {
  const bs::StashLayout layout = FixtureLayout();
  OwnedLevelStashes slot0(1, 1, layout), slot1(1, 1, layout);
  OwnedLevelStashes a_then_b(1, 1, layout), b_then_a(1, 1, layout);
  for (size_t s = 0; s < 16; ++s) {
    WriteFixtureKey(slot0.slots[0].Bucket(0), s, 100 + s);
    WriteFixtureKey(slot1.slots[0].Bucket(0), s, 200 + s);
  }
  slot0.slots[0].masks[0] = bs::LowMask64(16);
  slot1.slots[0].masks[0] = bs::LowMask64(16);

  const auto fold = [&](OwnedLevelStashes& into, OwnedLevelStashes& first,
                        OwnedLevelStashes& second) {
    for (OwnedLevelStashes* src : {&first, &second}) {
      Expect(bs::MergeBucketIntoResidualStash</*CheckOverflow=*/true>(
                 into.slots[0], src->slots[0].Bucket(0),
                 src->slots[0].masks[0], layout.Base().PayloadLines()),
             "an ample fold overflowed");
    }
  };
  fold(a_then_b, slot0, slot1);
  fold(b_then_a, slot1, slot0);

  Expect(StashKeySet(a_then_b.ptr(), 1) == StashKeySet(b_then_a.ptr(), 1),
         "fold order changed the residual key set");
  Expect(!a_then_b.SameAs(b_then_a),
         "fold order no longer changes the residual bytes; if the fold became "
         "order-independent, say so here instead of deleting the check");
  std::printf("  fold order: same 32-key residual set, different bytes\n");
}

// ---------------------------------------------------------------------------
// 2. Measuring one overloaded table
// ---------------------------------------------------------------------------
//
// Per butterfly level, how much the route sheds.  The capacities every fixture
// below uses are derived from these numbers, so the test states the regime it
// is in instead of hoping a hard-coded depth still lands there.
struct ShedProfile {
  std::vector<size_t> per_level;
  size_t worst = 0;     // max over levels
  size_t all_shed = 0;  // every level
};

ShedProfile MeasureSheds(OverloadedTable& fixture, unsigned levels) {
  const bs::StashLayout layout = FixtureLayout();
  fixture.Restore();
  OwnedLevelStashes ample(levels, bs::kMaxResidualStashBuckets, layout);
  Expect(bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
             fixture.View(), levels, ample.ptr()),
         "the measuring route overflowed even the deepest stash; lower `fill`");
  ShedProfile profile;
  for (unsigned b = 0; b < levels; ++b) {
    const size_t shed = ample.slots[b].Count();
    profile.per_level.push_back(shed);
    profile.worst = std::max(profile.worst, shed);
    profile.all_shed += shed;
  }
  return profile;
}

// ---------------------------------------------------------------------------
// 3. The route reports an overflow of its stash
// ---------------------------------------------------------------------------
//
// One level's shed set past its stash: the checked route must report it.
void TestRouteReportsOverflow(size_t num_buckets, size_t fill,
                              unsigned levels, uint64_t seed) {
  const bs::StashLayout layout = FixtureLayout();
  OverloadedTable fixture(num_buckets, fill, levels, seed);
  const ShedProfile profile = MeasureSheds(fixture, levels);
  Expect(profile.worst > kSlots,
         "this fixture never sheds a whole bucket into one level's stash; "
         "raise `fill` or `num_buckets`");

  // One bucket of capacity, which the worst level exceeds.
  fixture.Restore();
  OwnedLevelStashes level_stashes(levels, 1, layout);
  Expect(!bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
             fixture.View(), levels, level_stashes.ptr()),
         "the route reported success past its stash");

  // And the unchecked form does not: that is the hazard, stated.
  fixture.Restore();
  OwnedLevelStashes truncating(levels, 1, layout);
  Expect(bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/false>(
             fixture.View(), levels, truncating.ptr()),
         "the unchecked route stopped reporting success");
  Expect(truncating.Count() < profile.all_shed,
         "the unchecked route did not actually drop anything; this fixture no "
         "longer demonstrates the truncation");
  std::printf("  overflow: %zu buckets x %zu fill, %u levels -- worst level "
              "sheds %zu into 64 slots; checked route reports it, unchecked "
              "keeps %zu of %zu\n",
              num_buckets, fill, levels, profile.worst, truncating.Count(),
              profile.all_shed);
}

// ---------------------------------------------------------------------------
// 4. Checking preserves output where the capacity holds
// ---------------------------------------------------------------------------
//
// A fixed-input byte test: with a stash the shed set
// fits in, the checked kernels must write exactly the bytes the unchecked ones
// did.  An erroneous write anywhere in the route -- a mis-sized check that
// consumed a slot, a plan built from the wrong occupancy -- shows up here.
void TestCheckedRouteIsByteIdenticalWhenItFits(size_t num_buckets, size_t fill,
                                               unsigned levels,
                                               uint64_t seed) {
  const bs::StashLayout layout = FixtureLayout();
  OverloadedTable fixture(num_buckets, fill, levels, seed);
  const size_t table_bytes = num_buckets * layout.BucketBytes();
  const size_t depth = bs::kMaxResidualStashBuckets;

  const auto route = [&](bool checked, OwnedLevelStashes* stashes,
                         std::vector<uint8_t>* out,
                         std::vector<uint64_t>* masks) {
    fixture.Restore();
    const bool ok =
        checked
            ? bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
                  fixture.View(), levels, stashes->ptr())
            : bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/false>(
                  fixture.View(), levels, stashes->ptr());
    Expect(ok, "an ample-capacity route reported an overflow");
    out->assign(fixture.table.data.get(),
                fixture.table.data.get() + table_bytes);
    masks->assign(fixture.table.masks.get(),
                  fixture.table.masks.get() + num_buckets);
  };

  // The last level's RoutedLines is the contract for which byte lines are
  // still live; a retired tag line legitimately holds stale bytes.
  const size_t live = layout.Base().RoutedLines(levels - 1) * kSlots;
  std::vector<uint8_t> bytes[2];
  std::vector<uint64_t> masks[2];
  OwnedLevelStashes unchecked(levels, depth, layout);
  OwnedLevelStashes checked(levels, depth, layout);
  route(false, &unchecked, &bytes[0], &masks[0]);
  route(true, &checked, &bytes[1], &masks[1]);

  for (size_t b = 0; b < num_buckets; ++b) {
    const size_t off = b * layout.BucketBytes();
    Expect(std::memcmp(&bytes[0][off], &bytes[1][off], live) == 0,
           "checking changed the bytes the route wrote");
  }
  Expect(masks[1] == masks[0], "checking changed a bucket's occupancy");
  Expect(unchecked.SameAs(checked), "checking changed the residual bytes");
  std::printf("  identical: %zu live bytes/bucket and every mask unchanged by "
              "the check\n",
              live);
}

// ---------------------------------------------------------------------------
// 5. Conservation across the whole route
// ---------------------------------------------------------------------------
//
// The oracle the failure contract is FOR: when a route reports success, every
// input record is either in the table or in the residual stashes, exactly
// once.  A truncating fold is invisible to a byte comparison of the table
// alone -- this is what it breaks.
void TestSuccessfulRouteConservesEveryRecord(size_t num_buckets, size_t fill,
                                             unsigned levels, uint64_t seed) {
  const bs::StashLayout layout = FixtureLayout();
  OverloadedTable fixture(num_buckets, fill, levels, seed);
  // Include values and metadata: conserving keys alone would accept a route
  // or fold that copied the key lines correctly and corrupted the payload.
  using Records = std::multiset<std::vector<uint8_t>>;
  const auto collect = [&](Records& records, const uint8_t* bucket,
                            uint64_t mask) {
    for (size_t slot = 0; slot < kSlots; ++slot) {
      if (!((mask >> slot) & 1)) continue;
      std::vector<uint8_t> record(layout.Base().PayloadLines());
      for (size_t line = 0; line < record.size(); ++line) {
        record[line] = bucket[line * kSlots + slot];
      }
      records.insert(std::move(record));
    }
  };
  Records input;
  for (size_t b = 0; b < num_buckets; ++b) {
    collect(input, fixture.table.Bucket(b), fixture.table.masks[b]);
  }

  OwnedLevelStashes global(levels, bs::kMaxResidualStashBuckets, layout);
  Expect(bs::ButterflyRouteStashCacheOblivious</*CheckOverflow=*/true>(
             fixture.View(), levels, global.ptr()),
         "the conservation route overflowed");

  Records output;
  for (const bs::ResidualStash& stash : global.slots) {
    for (size_t b = 0; b < stash.num_buckets; ++b) {
      collect(output, stash.Bucket(b), stash.masks[b]);
    }
  }
  for (size_t b = 0; b < num_buckets; ++b) {
    collect(output, fixture.table.Bucket(b), fixture.table.masks[b]);
  }
  Expect(input == output,
         "a successful route lost, duplicated or invented a record across the "
         "table and the residual stashes");
  std::printf("  conservation: %zu records in, %zu across table + "
              "residuals\n", input.size(), output.size());
}

}  // namespace

int main() {
  TestUncheckedFoldTruncatesAndCheckedReports();
  TestSlotPartitionKeepsTheResidualSetNotItsBytes();

  // WHICH FILL PUTS A FIXTURE IN WHICH REGIME.  A butterfly at the design
  // load of 32 real entries per bucket sheds nothing at all -- at 256 buckets
  // and fill 40 the shed set is empty -- so every fixture here is
  // deliberately overloaded (fill 60 at 256 buckets sheds 1228 records, 257
  // of them at one level).  The fixtures re-measure the shed set and refuse to
  // run in the wrong regime, so a kernel change that moves it says so instead
  // of quietly testing nothing.
  TestRouteReportsOverflow(256, 60, 8, 0xF00D01);
  TestRouteReportsOverflow(512, 56, 9, 0xF00D02);
  TestCheckedRouteIsByteIdenticalWhenItFits(256, 56, 8, 0xF00D07);
  TestCheckedRouteIsByteIdenticalWhenItFits(128, 60, 7, 0xF00D08);
  TestSuccessfulRouteConservesEveryRecord(256, 56, 8, 0xF00D09);
  TestSuccessfulRouteConservesEveryRecord(512, 56, 9, 0xF00D0A);

  std::puts("cpu_byteslice_residual_overflow_test passed");
  return 0;
}
