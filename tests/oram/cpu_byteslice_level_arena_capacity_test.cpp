// The level-arena engine's COMPLETE byte bill (every byte the engine
// allocates, by role: level arenas, tiers, masks, plan pool, per-level jobs,
// range scratch, staging records, ...) and the capacity LADDER built on it,
// which picks the geometry -- levels L, prefix length r0, top digit D and the
// per-level fanouts -- with the smallest complete bill that covers a
// requested capacity.  The hierarchy's memory footprint and its capacity
// guarantees are public functions of these choices, so they must be exact.
//
// What is checked here:
//
//   - the bill's roles account for every requested byte, at every geometry
//     tried (the bill's own `Validate`, exercised across a sweep);
//   - the bill is STRICTLY larger than the geometry-only `ArenaBytes` --
//     reporting the arenas as the footprint would under-count -- and the gap
//     is a large fraction of a small hierarchy rather than a rounding;
//   - requested and reserved bytes are separated: the reserved total moves
//     with the huge-page policy and the requested total does not;
//   - a constructed engine allocates what the bill predicts -- which the
//     engine checks itself, so what this adds is that the numbers a caller
//     reads off it are the same ones;
//   - the ladder covers the request, prices by the smallest COMPLETE bill,
//     is deterministic under its stated tie break, honours pinned axes, and
//     refuses what it cannot build;
//   - and -- counted, not assumed -- how often pricing by the arenas alone
//     would pick a DIFFERENT geometry in a wide sweep (the pinned count in
//     TestArenaOnlyAgreesOnOrdering).
//     The fixture pins that count, because a future term which moved it would
//     change the geometries this library hands out without anything saying
//     so.
//
// THE LADDER IS CHECKED AGAINST AN INDEPENDENT ENUMERATION, not against
// itself: the test re-walks every (L, r0, D) and fanout ladder with its own
// loop -- the half-fanout prefix at B = 8, the bottom fanout below -- prices
// the survivors, and asserts the ladder's answer is the minimum.  A search
// agreeing with its own tie break is not the interesting failure.
//
// That comparison runs at `byte_slack = 0`, because the library default lets
// the ladder spend up to 1 % of the bill to lengthen the prefix (raise r0) --
// so the two halves of the selection are checked by two fixtures: the byte
// objective against the enumeration, and the r0 preference against its own
// budget.

#include <algorithm>
#include <cstdio>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {
namespace {

using test_support::Expect;

template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

LevelArenaByteBill BillOf(const LevelArenaGeometry::Params& params,
                          size_t key_bytes, size_t value_bytes,
                          unsigned owner_threads,
                          unsigned batch_participants = 1) {
  const LevelArenaGeometry geometry(params.tier_buckets == 0
      ? ResolveLevelArenaTierGeometry(params, uint64_t{1} << 32) : params);
  const Layout layout =
      LevelArenaStoredLayout(key_bytes, value_bytes, geometry);
  const LevelArenaStashSizing sizing(geometry, uint64_t{1} << 32);
  return LevelArenaEngineBytes(geometry, layout, sizing,
                               owner_threads == 0 ? 1u : owner_threads,
                               batch_participants);
}

LevelArenaGeometry::Params Params(unsigned branching, unsigned levels,
                                  unsigned top_digit, unsigned flushes,
                                  unsigned bottom_fanout = 0) {
  LevelArenaGeometry::Params p;
  p.branching = branching;
  p.levels = levels;
  p.top_digit = top_digit;
  p.prefix_flushes = flushes;
  p.stash_buckets = 1;
  p.dense_prefixes = 2;
  // The ladder always states its ladder explicitly, so an enumeration that
  // means to reproduce the ladder's candidates has to state it too: an empty
  // vector and an all-B vector are the same geometry, but only one of them
  // compares equal to what the ladder returns.
  p.level_fanouts.assign(levels - 1, branching);
  if (bottom_fanout != 0) p.level_fanouts[0] = bottom_fanout;
  return p;
}

// THE LADDERS ONE FAMILY SEARCHES at `levels`, stated here rather than read
// from the header so that the enumerations below are independent of it: the
// half-fanout prefix (B = 8), fanout 4 at the lowest a in {1, 2, 3} levels
// and 8 above; or every bottom fanout in {2, ..., B} under B.
std::vector<std::vector<unsigned>> DefaultLadders(unsigned branching,
                                                  unsigned levels,
                                                  bool prefix) {
  std::vector<std::vector<unsigned>> ladders;
  if (prefix) {
    for (unsigned a = 1; a <= 3 && a <= levels - 1; ++a) {
      std::vector<unsigned> ladder(levels - 1, 8);
      for (unsigned l = 0; l < a; ++l) ladder[l] = 4;
      ladders.push_back(ladder);
    }
  } else {
    for (unsigned bottom = 2; bottom <= branching; bottom *= 2) {
      std::vector<unsigned> ladder(levels - 1, branching);
      ladder[0] = bottom;
      ladders.push_back(ladder);
    }
  }
  return ladders;
}

// ---------------------------------------------------------------------------

void TestAutomaticTierPricing() {
  LevelArenaCapacityRequest request;
  request.entries = uint64_t{1} << 27;
  request.branching = 8;
  request.prefix_flushes = 8;
  request.top_digit = 8;
  request.half_fanout_prefix = false;
  request.bottom_fanout = 8;
  const auto choice = PlanLevelArenaCapacity(request);
  Expect(choice.geometry.levels == 6 && choice.geometry.tier_buckets == 2,
         "large capacity planning did not resolve automatic tier width");
  Expect(choice.bill.requested() ==
             BillOf(choice.geometry, 8, 16, 0).requested(),
         "large capacity bill omitted the resolved tier width");
  request.tier_buckets = 1;
  Expect(Throws([&] { PlanLevelArenaCapacity(request); }),
         "large capacity planning accepted an insufficient tier pin");

  // A long horizon makes a small, allocatable fixture require two buckets.
  // Engine construction checks every actual buffer against its byte bill.
  LevelArenaEngine::Options options;
  options.geometry = Params(4, 3, 4, 4);
  const LevelArenaGeometry horizon_geometry(options.geometry);
  options.max_accesses =
      kMaxFamilyOrdinal * horizon_geometry.PrefixPositions() - 1 -
      DirectInitializationSeed(horizon_geometry).access_offset;
  options.geometry.tier_buckets = 0;
  const auto resolved = ResolveLevelArenaTierGeometry(options.geometry,
                                                     options.max_accesses);
  Expect(resolved.tier_buckets == 2, "horizon did not affect tier sizing");
  const LevelArenaGeometry geometry(resolved);
  const auto layout = LevelArenaStoredLayout(8, 16, geometry);
  const LevelArenaStashSizing sizing(geometry, options.max_accesses);
  const auto bill = LevelArenaEngineBytes(geometry, layout, sizing, 1, 1);
  LevelArenaEngine engine(options);
  Expect(engine.geometry().TierBuckets() == 2 &&
             engine.ByteBill().requested() == bill.requested(),
         "constructed engine differs from the automatic tier byte bill");
}

// Every role is accounted for, and the arenas are not the bill.
void TestBillIsComplete() {
  size_t widest_share = 0;  // the largest non-arena share seen
  for (unsigned branching : {2u, 4u, 8u}) {
    for (unsigned levels = 2; levels <= 6; ++levels) {
      for (unsigned digit : {1u, 2u, 4u, 8u}) {
        if (digit > branching) continue;  // the top is no wider than B
        const LevelArenaGeometry::Params params =
            Params(branching, levels, digit, 4);
        const LevelArenaGeometry geometry(params);
        const Layout layout = LevelArenaStoredLayout(8, 16, geometry);
        const LevelArenaByteBill bill = BillOf(params, 8, 16, 0);
        // `Validate` is what LevelArenaEngineBytes already ran; asserting the
        // same identity here is asserting it over a sweep rather than over
        // the one geometry a fixture happened to build.
        Expect(bill.RoleTotal() == bill.requested(),
               "the byte roles do not account for every requested byte");

        const size_t arenas = geometry.ArenaBytes(layout) +
                              LevelArenaSet::TierPayloadBytes(geometry, layout);
        Expect(bill.requested() > arenas,
               "the complete bill is not larger than the arenas alone");
        // The arena roles and the arena-only figure are the same bytes, so
        // the gap is exactly the non-arena terms.
        const size_t arena_roles = bill.At(ByteRole::kMains) +
                                   bill.At(ByteRole::kTiers) +
                                   bill.At(ByteRole::kMasks) +
                                   bill.At(ByteRole::kRetainedTierHoles);
        Expect(arena_roles == arenas,
               "the bill's arena roles disagree with ArenaBytes");
        const size_t outside = bill.requested() - arenas;
        widest_share = std::max(widest_share, 100 * outside / bill.requested());
      }
    }
  }
  // Not a threshold anyone tuned: at the small end of this sweep the plan
  // pool, the per-level jobs and the range scratch are a QUARTER of the
  // engine, which is the whole reason the ladder may not price a geometry by
  // its arenas.  A change that made this small would mean the terms had moved
  // somewhere else, not that they had gone away.
  Expect(widest_share >= 10,
         "the non-arena terms are negligible at every geometry tried, which "
         "contradicts what the ladder is built on");
  printf("  bill: roles complete, arenas alone short by up to %zu %%\n",
         widest_share);
}

// Routing's two-block messages enlarge the public plan templates and scalar /
// batch scratch. Price those buffers normally: this request's minimum moves
// between existing certified geometries, with no change to planner policy.
void TestRoutingScratchChangesByteMinimum() {
  LevelArenaCapacityRequest request;
  request.entries = 8192;
  request.value_bytes = 48;
  request.half_fanout_prefix = false;
  request.byte_slack = 0;
  const auto choice = PlanLevelArenaCapacity(request);
  // Both candidates gain the same 192 scalar and 12,288 batch bytes. The
  // r0=2/fanout8 plan pool gains 12,672 bytes, versus 10,240 for r0=4/fanout4.
  // Without these buffers r0=2/fanout8 would be 896 bytes smaller; with them
  // it is 1,536 bytes larger. Both candidates still have capacity 8192 and
  // belong to the 94-member family.
  Expect(choice.geometry.levels == 2 && choice.geometry.prefix_flushes == 4 &&
             choice.geometry.top_digit == 8 &&
             choice.geometry.level_fanouts == std::vector<unsigned>{4},
         "routing scratch changed the documented byte-minimum geometry");
}

// Requested bytes are the design's; reserved bytes are this process's.
void TestRequestedIsNotReserved() {
  const LevelArenaGeometry::Params params = Params(4, 5, 4, 8);
  const HugePagePolicy saved = CurrentHugePagePolicy();

  SetHugePagePolicy(HugePagePolicy::kOff);
  const LevelArenaByteBill off = BillOf(params, 8, 16, 0);
  SetHugePagePolicy(HugePagePolicy::kOn);
  const LevelArenaByteBill on = BillOf(params, 8, 16, 0);
  SetHugePagePolicy(saved);

  Expect(off.requested() == on.requested(),
         "the requested total moved with the huge-page policy");
  // With huge pages off the only rounding left is the 64-byte alignment every
  // one of these buffers is made at, so the overhead is bounded by one
  // alignment per allocation and cannot be a megabyte of pages.
  Expect(off.reserved() >= off.requested(),
         "reserved bytes are below requested bytes");
  Expect(off.reserved() - off.requested() <= 64 * off.allocated().allocations,
         "with huge pages off, something rounded past its alignment");
  // On this host the policy may be unavailable (no THP, or not Linux), in
  // which case the two agree and there is nothing to compare -- which is a
  // property of the host and not a failure.
  if (UseHugePages(kHugePageBytes)) {
    Expect(on.reserved() > on.requested(),
           "with huge pages on, a multi-megabyte arena should round up");
    Expect(on.reserved() > off.reserved(),
           "the reserved total did not move with the policy");
  }
  printf("  bill: requested %zu B is policy-independent; reserved %zu/%zu B\n",
         off.requested(), off.reserved(), on.reserved());
}

// The engine reports the bill it was built to, and the bill counts the
// executing threads rather than assuming one.
void TestEngineReportsItsBill() {
  for (unsigned threads : {0u, 1u, 3u}) {
    LevelArenaEngine::Options options;
    options.geometry = Params(4, 3, 4, 4);
    options.key_bytes = 8;
    options.value_bytes = 16;
    options.owner_threads = threads;
    LevelArenaEngine engine(options);
    // The engine checks its own components against this at construction; what
    // is added here is that the accessor a caller reads is that same bill.
    const LevelArenaByteBill predicted =
        BillOf(options.geometry, options.key_bytes, options.value_bytes,
               threads);
    Expect(engine.ByteBill() == predicted,
           "the engine's reported bill is not the one the ladder prices it by");
    Expect(engine.ArenaBytes() == predicted.At(ByteRole::kMains) +
               predicted.At(ByteRole::kTiers) + predicted.At(ByteRole::kMasks) +
               predicted.At(ByteRole::kRetainedTierHoles),
           "arena reporting omitted or duplicated pool/retained storage");
    Expect(engine.ByteBill().requested() > engine.ArenaBytes(),
           "the engine's bill is not larger than its arenas");
  }
  // More executing threads is more staging plan records, and the bill has to
  // say so: this is the term a ladder run for an inline engine would
  // under-report for a threaded one.  The range scratch is per LEVEL, so the
  // thread count must not move it.
  const LevelArenaGeometry::Params params = Params(4, 4, 4, 4);
  const LevelArenaByteBill inline_bill = BillOf(params, 8, 16, 0);
  const LevelArenaByteBill threaded = BillOf(params, 8, 16, 4);
  Expect(threaded.At(ByteRole::kTransientScratch) ==
             inline_bill.At(ByteRole::kTransientScratch),
         "owner threads changed the per-level range scratch");
  Expect(threaded.At(ByteRole::kPlans) > inline_bill.At(ByteRole::kPlans),
         "owner threads did not add staging plan records");
  printf("  bill: the engine reports it, and it counts executing threads\n");
}

// The ladder's answer is the minimum of an independent enumeration.
//
// Run at `byte_slack = 0`, which is the pure byte objective: with the default
// slack the ladder may spend up to 1 % to raise r0, so "the smallest bill
// wins" is not the whole rule and this fixture would be asserting
// something the ladder does not promise.  The slack's own behaviour is
// TestLadderPrefersALongPrefix below.
void TestLadderPicksTheSmallestCompleteBill() {
  for (uint64_t entries : {uint64_t{1} << 10, uint64_t{1} << 16,
                           uint64_t{1} << 20, uint64_t{3} << 17}) {
    for (unsigned branching : {2u, 4u, 8u}) {
      LevelArenaCapacityRequest request;
      request.entries = entries;
      request.branching = branching;
      request.min_top_digit = 1;
      request.byte_slack = 0.0;
      const LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(request);

      Expect(choice.capacity >= entries, "the ladder undershot the request");
      Expect(choice.geometry.branching == branching,
             "the ladder moved B, which is the caller's");
      Expect(choice.geometry.stash_buckets == request.stash_buckets,
             "the ladder moved s, which is the caller's");
      Expect(choice.geometry.dense_prefixes == request.dense_prefixes,
             "the ladder moved q, which is the caller's");
      Expect(choice.bill.requested() > 0, "the chosen geometry costs nothing");
      Expect(choice.capacity_ratio >=
                 static_cast<double>(choice.capacity) /
                     static_cast<double>(entries) - 1e-12,
             "the reported capacity ratio is not capacity over request");

      // The independent enumeration: every supported (L, r0, D) and fanout
      // ladder of one family, priced from scratch, with no reference to the
      // ladder's own ordering.  The ladder axis is enumerated here too --
      // pinning it in the request would leave it checked by nothing.
      struct Winner {
        size_t bytes = ~size_t{0};
        LevelArenaGeometry::Params params;
        size_t seen = 0;
      };
      const auto enumerate = [&](bool prefix) {
        Winner w;
        for (unsigned levels = 2; levels <= 20; ++levels) {
          for (unsigned flushes : {2u, 4u, 8u}) {
            for (unsigned digit = 1;
                 digit <= LevelArenaGeometry::kMaxTopDigit; ++digit) {
              for (const std::vector<unsigned>& ladder :
                   DefaultLadders(branching, levels, prefix)) {
                LevelArenaGeometry::Params params =
                    Params(branching, levels, digit, flushes);
                params.level_fanouts = ladder;
                size_t bytes = 0;
                try {
                  if (LevelArenaCapacityOf(params) < entries) continue;
                  auto automatic = params;
                  automatic.tier_buckets = 0;
                  bytes = BillOf(automatic, request.key_bytes,
                                 request.value_bytes, 0)
                              .requested();
                } catch (const std::exception&) {
                  continue;
                }
                ++w.seen;
                if (bytes < w.bytes ||
                    (bytes == w.bytes &&
                     PrefersCapacityCandidate(params, w.params))) {
                  w.bytes = bytes;
                  w.params = params;
                }
              }
            }
          }
        }
        return w;
      };
      // At B = 8 the prefix family's winner, unless the bottom family's
      // rounds to a smaller capacity.
      const Winner bottom = enumerate(false);
      Winner expected = bottom;
      bool expect_prefix = false;
      if (branching == 8) {
        const Winner prefix = enumerate(true);
        if (prefix.seen > 0 &&
            LevelArenaCapacityOf(bottom.params) >=
                LevelArenaCapacityOf(prefix.params)) {
          expected = prefix;
          expect_prefix = true;
        }
      }
      Expect(choice.half_fanout_prefix == expect_prefix,
             "the ladder took the other family than the fallback rule says");
      const size_t best = expected.bytes;
      const LevelArenaGeometry::Params& winner = expected.params;
      const size_t seen = expected.seen;
      Expect(seen > 0, "the enumeration found no feasible geometry");
      // Not `choice.candidates == seen`: the ladder searches L past this
      // loop's bound and applies RoutingDigitFits, so the two walks are
      // deliberately not the same set.  What has to agree is the answer.
      Expect(choice.bill.requested() == best,
             "the ladder did not pick the smallest complete bill");
      Expect(choice.geometry.levels == winner.levels &&
                 choice.geometry.top_digit == winner.top_digit &&
                 choice.geometry.prefix_flushes == winner.prefix_flushes &&
                 choice.geometry.level_fanouts == winner.level_fanouts,
             "the ladder's tie break is not the one it states");
    }
  }
  printf("  ladder: minimal complete bill, checked against an independent "
         "enumeration over (L, r0, D, fanout ladder)\n");
}

// THE SLACK, and what it is for: a longer prefix buys a larger level-1 carry
// and more fanout-B/2 levels, which are faster to rebuild, and neither is a
// byte.  So the ladder admits every candidate within `byte_slack` of the
// smallest bill and takes the largest r0 among them.  Checked as three
// separate claims, because "it picked r0 = 8" alone would also be true of a
// ladder that had simply stopped searching.
void TestLadderPrefersALongPrefix() {
  double worst_ratio = 1.0;
  for (int power = 12; power <= 30; ++power) {
    const uint64_t entries = uint64_t{1} << power;
    LevelArenaCapacityRequest request;
    request.entries = entries;

    LevelArenaCapacityRequest strict = request;
    strict.byte_slack = 0.0;
    const LevelArenaCapacityChoice cheapest = PlanLevelArenaCapacity(strict);
    const LevelArenaCapacityChoice chosen = PlanLevelArenaCapacity(request);

    // 1. It really does raise r0, and never lowers it.
    Expect(chosen.geometry.prefix_flushes >= cheapest.geometry.prefix_flushes,
           "the slack lowered r0, which is the gain it exists to buy");
    // And from 2^19 up the half-fanout prefix reaches every capacity at the
    // LONGEST prefix.  Below that the bill's fixed terms -- the plan pool,
    // the per-level jobs, the range scratch -- are a large fraction of a
    // small hierarchy, so the extra fanout-four level a long prefix needs
    // costs 1-3 % rather than 0.3 % (2^18: r0 = 8 is 2.5 % over), the budget
    // does not reach it, and the ladder correctly declines.  That is the
    // budget working, not failing, and it is pinned here so that a slack
    // silently widened later is visible.
    if (entries >= (uint64_t{1} << 19)) {
      Expect(chosen.geometry.prefix_flushes == 8,
             "the half-fanout prefix did not reach this capacity at r0 = 8");
    }
    // 2. The spend is bounded by the budget the caller set.
    const double ratio = static_cast<double>(chosen.bill.requested()) /
                         static_cast<double>(cheapest.bill.requested());
    Expect(ratio <= 1.0 + request.byte_slack,
           "the ladder spent more than byte_slack to raise r0");
    worst_ratio = std::max(worst_ratio, ratio);
    // 3. And it is still a covering geometry, not a cheaper undershoot.
    Expect(chosen.capacity >= entries, "the slack undershot the request");

    // No slack, no preference: the two are the same search.
    Expect(PlanLevelArenaCapacity(strict).bill.requested() ==
               cheapest.bill.requested(),
           "the ladder is not deterministic");
  }
  printf("  ladder: r0 is maximised within a %.0f%% byte budget (worst spend "
         "%.4f%%)\n",
         100.0 * LevelArenaCapacityRequest{}.byte_slack,
         100.0 * (worst_ratio - 1.0));
}

// THE TOP-DIGIT FLOOR, B/2 + 1 by default, and the ceiling, B.  The only
// binary digit at or above the floor is B itself.  Three claims per B, and
// the first is the one that would break silently: above the smallest D = B
// geometry the floor changes no answer at all, because minimising bytes at a
// fixed capacity is minimising U_L, which is maximising D -- and every
// D <= B/2 has a 2D <= B twin at half the U_L.  Below it
// the floor cannot be met without a bigger top, so it overshoots -- and says
// so through `capacity_ratio`.
void TestTopDigitFloor() {
  for (unsigned branching : {2u, 4u, 8u}) {
    const unsigned floor = branching / 2 + 1;
    // The smallest D = B geometry: L = 2, r0 = 2, b_1 = 2, so U_L = 8s and
    // 32 * B * 8s entries -- 2048 s at B = 8 -- at s = 1.  The half-fanout
    // prefix steps aside at this size, because its floor geometry would
    // double the capacity.
    const uint64_t crossover = 256 * uint64_t{branching};
    bool saw_overshoot = false;
    for (uint64_t entries = 64; entries < (uint64_t{1} << 26); entries *= 3) {
      LevelArenaCapacityRequest floored;
      floored.entries = entries;
      floored.branching = branching;
      floored.byte_slack = 0.0;
      LevelArenaCapacityRequest open = floored;
      open.min_top_digit = 1;

      const LevelArenaCapacityChoice a = PlanLevelArenaCapacity(floored);
      const LevelArenaCapacityChoice b = PlanLevelArenaCapacity(open);
      Expect(a.geometry.top_digit >= floor &&
                 LevelArenaGeometry::IsTopDigit(a.geometry.top_digit) &&
                 LevelArenaGeometry::IsTopDigit(b.geometry.top_digit),
             "the floor did not hold, or the ladder chose a nonbinary top");
      Expect(a.geometry.top_digit <= branching &&
                 b.geometry.top_digit <= branching,
             "the ladder chose a top wider than B");
      if (entries >= crossover) {
        Expect(a.bill.requested() == b.bill.requested(),
               "the top-digit floor cost bytes above its crossover");
      } else if (a.bill.requested() > b.bill.requested()) {
        saw_overshoot = true;
        Expect(a.capacity_ratio > 1.0,
               "a floor that cost bytes did not report an overshoot");
      }
    }
    Expect(saw_overshoot,
           "the floor never overshot, so its escape hatch is untested");
  }
  // A pin below the floor is a caller contradicting itself, not a preference
  // to be resolved silently either way.
  LevelArenaCapacityRequest contradiction;
  contradiction.entries = 1 << 20;
  contradiction.top_digit = 2;
  Expect(Throws([&] { return PlanLevelArenaCapacity(contradiction); }),
         "a pinned D below min_top_digit was silently accepted");
  contradiction.min_top_digit = 1;
  Expect(PlanLevelArenaCapacity(contradiction).geometry.top_digit == 2,
         "lowering the floor did not admit the pin");
  printf("  ladder: the D >= B/2 + 1 floor is free above its crossover, "
         "escapable below it, and refuses a contradicting pin\n");
}

// Compare the full buffer bill with the arena-only proxy over the same
// geometry sweep. Pin the number of differing choices so changes to storage
// costs must be reviewed alongside the independent minimum-bill check above.
void TestArenaOnlyAgreesOnOrdering() {
  size_t compared = 0;
  size_t disagreements = 0;
  for (unsigned branching : {2u, 4u, 8u}) {
    for (size_t stash : {size_t{1}, size_t{4}, size_t{16}}) {
      for (size_t value_bytes : {size_t{8}, size_t{16}, size_t{256}}) {
        for (uint64_t entries = 1 << 9; entries <= (uint64_t{1} << 22);
             entries = entries * 3 / 2 + 1) {
          LevelArenaCapacityRequest request;
          request.entries = entries;
          request.branching = branching;
          request.stash_buckets = stash;
          request.value_bytes = value_bytes;
          request.min_top_digit = 1;
          request.byte_slack = 0.0;
          LevelArenaCapacityChoice choice;
          try {
            choice = PlanLevelArenaCapacity(request);
          } catch (const std::length_error&) {
            continue;  // no geometry covers this request at this B and s
          }

          // The same enumeration, priced by the arenas alone and broken by
          // the same tie rule, so the only thing that differs is the price.
          size_t best_arena = ~size_t{0};
          LevelArenaGeometry::Params arena_winner;
          for (unsigned levels = 2; levels <= 20; ++levels) {
            for (unsigned flushes : {2u, 4u, 8u}) {
              for (unsigned digit = 1;
                   digit <= LevelArenaGeometry::kMaxTopDigit; ++digit) {
                for (const std::vector<unsigned>& ladder : DefaultLadders(
                         branching, levels, choice.half_fanout_prefix)) {
                  LevelArenaGeometry::Params params =
                      Params(branching, levels, digit, flushes);
                  params.level_fanouts = ladder;
                  params.stash_buckets = stash;
                  try {
                    if (LevelArenaCapacityOf(params) < entries) continue;
                    params.tier_buckets = 0;
                    params = ResolveLevelArenaTierGeometry(params,
                                                           request.max_accesses);
                    const LevelArenaGeometry geometry(params);
                    const Layout layout = LevelArenaStoredLayout(
                        request.key_bytes, value_bytes, geometry);
                    if (!RoutingDigitFits(layout)) continue;
                    const size_t bytes = geometry.ArenaBytes(layout);
                    if (bytes < best_arena ||
                        (bytes == best_arena &&
                         PrefersCapacityCandidate(params, arena_winner))) {
                      best_arena = bytes;
                      arena_winner = params;
                    }
                  } catch (const std::exception&) {
                    continue;
                  }
                }
              }
            }
          }
          if (best_arena == ~size_t{0}) continue;
          ++compared;
          if (arena_winner.levels != choice.geometry.levels ||
              arena_winner.top_digit != choice.geometry.top_digit ||
              arena_winner.prefix_flushes != choice.geometry.prefix_flushes ||
              arena_winner.level_fanouts != choice.geometry.level_fanouts) {
            ++disagreements;
          }
        }
      }
    }
  }
  Expect(compared > 500, "the ordering sweep found almost nothing to compare");
  // The two prices disagree mainly where the non-arena terms are a real
  // share of a small map: per-level range scratch and DFS workspaces, each
  // job's task list, the bank-first run's extra tier per level, and the cap
  // of D at B.  At B = 8 the half-fanout prefix moves the arenas and the bill
  // alike, so requests in the prefix family agree more often; it steps aside
  // for the bottom fanout only where it would round the capacity up (below
  // about 2^17 entries).  Each request is compared within the family its
  // choice came from.  The pinned count (85) is the current value of this
  // census; any change to a storage cost that moves it must be reviewed.
  printf("  ladder: arena-only pricing differs on %zu of %zu requests\n",
         disagreements, compared);
  Expect(disagreements == 85,
         "the complete bill and arena-only proxy changed their geometry "
         "ordering; review the storage costs and update the pinned count");
  printf("  ladder: complete and arena-only pricing agree on %zu of %zu "
         "requests swept\n", compared - disagreements, compared);
}

// THE HALF-FANOUT PREFIX (the default at B = 8: the lowest levels use fanout
// B/2 = 4, which rebuild faster).  Representative shapes at eight flushes
// per prefix: 2^21 and 2^24 are all eights under the bottom-fanout search and
// take one more level with three fours; 2^22 has b_1 = 2 there and takes two
// fours at the same L; 2^23 is 4,8,8,8 under both.  The prefix is as short as rounding allows, every power of
// two is hit exactly, it steps aside for small maps, the pins refuse each
// other's ladder, and B < 8 does not move.
void TestHalfFanoutPrefix() {
  struct Case {
    unsigned power;
    std::vector<unsigned> prefix;  // the ladder the rule picks
    std::vector<unsigned> bottom;  // the bottom-fanout search's
  };
  const Case cases[] = {
      {21, {4, 4, 4, 8}, {8, 8, 8}},
      {22, {4, 4, 8, 8}, {2, 8, 8, 8}},
      {23, {4, 8, 8, 8}, {4, 8, 8, 8}},
      {24, {4, 4, 4, 8, 8}, {8, 8, 8, 8}},
  };
  for (const Case& c : cases) {
    LevelArenaCapacityRequest request;
    request.entries = uint64_t{1} << c.power;
    request.prefix_flushes = 8;
    const LevelArenaCapacityChoice prefix = PlanLevelArenaCapacity(request);
    Expect(prefix.half_fanout_prefix && prefix.geometry.level_fanouts == c.prefix,
           ("the half-fanout prefix picked another ladder at 2^" +
            std::to_string(c.power)).c_str());
    Expect(prefix.capacity == request.entries,
           "the half-fanout prefix did not hit a power of two exactly");
    request.half_fanout_prefix = false;
    const LevelArenaCapacityChoice bottom = PlanLevelArenaCapacity(request);
    Expect(bottom.geometry.level_fanouts == c.bottom,
           ("the bottom-fanout search picked another ladder at 2^" +
            std::to_string(c.power)).c_str());
    // Never cheaper: the byte objective would have chosen it otherwise.
    Expect(prefix.bill.requested() >= bottom.bill.requested(),
           "the half-fanout prefix was cheaper than the byte objective");
  }
  // Unpinned r0: the prefix is still the ladder, its length is the one
  // rounding needs, and from 2^19 up it reaches every capacity at the longest
  // prefix.
  for (unsigned power = 17; power <= 30; ++power) {
    LevelArenaCapacityRequest request;
    request.entries = uint64_t{1} << power;
    const LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(request);
    const std::vector<unsigned>& ladder = choice.geometry.level_fanouts;
    const size_t fours = size_t(std::count(ladder.begin(), ladder.end(), 4u));
    Expect(fours >= 1 && fours <= 3 &&
               std::all_of(ladder.begin(), ladder.begin() + fours,
                           [](unsigned f) { return f == 4; }) &&
               std::all_of(ladder.begin() + fours, ladder.end(),
                           [](unsigned f) { return f == 8; }),
           "the default B = 8 ladder is not a prefix of one to three fours");
    Expect(choice.half_fanout_prefix,
           ("the half-fanout prefix stepped aside at 2^" +
            std::to_string(power)).c_str());
    Expect(power < 19 || choice.geometry.prefix_flushes == 8,
           ("the half-fanout prefix did not reach 2^" + std::to_string(power) +
            " at r0 = 8").c_str());
  }
  // A small map keeps the bottom fanout's floor geometry rather than double.
  // At 2^13 the two ladders are one geometry (L = 2, r0 = 4, fanout 4), so
  // either label is right; below the prefix's floor only the bottom's is.
  for (uint64_t entries : {uint64_t{100}, uint64_t{1} << 13}) {
    LevelArenaCapacityRequest small;
    small.entries = entries;
    const LevelArenaCapacityChoice kept = PlanLevelArenaCapacity(small);
    small.half_fanout_prefix = false;
    const LevelArenaCapacityChoice bottom = PlanLevelArenaCapacity(small);
    Expect(kept.capacity == bottom.capacity &&
               kept.geometry.prefix_flushes == bottom.geometry.prefix_flushes &&
               kept.geometry.level_fanouts == bottom.geometry.level_fanouts,
           "the half-fanout prefix rounded a small map up");
    Expect(entries != 100 || !kept.half_fanout_prefix,
           "the half-fanout prefix was used below its floor geometry");
  }
  // Each ladder's pin is refused under the other.
  LevelArenaCapacityRequest pinned;
  pinned.entries = 1 << 20;
  pinned.bottom_fanout = 4;
  Expect(Throws([&] { PlanLevelArenaCapacity(pinned); }),
         "a bottom-fanout pin was accepted under the half-fanout prefix");
  pinned.half_fanout_prefix = false;
  Expect(PlanLevelArenaCapacity(pinned).geometry.level_fanouts.front() == 4,
         "the bottom-fanout pin was not honoured with the prefix off");
  pinned.bottom_fanout = 0;
  pinned.half_prefix_levels = 2;
  Expect(Throws([&] { PlanLevelArenaCapacity(pinned); }),
         "a prefix-length pin was accepted with the prefix off");
  pinned.half_fanout_prefix = true;
  for (unsigned a = 1; a <= 3; ++a) {
    pinned.half_prefix_levels = a;
    const auto& ladder = PlanLevelArenaCapacity(pinned).geometry.level_fanouts;
    Expect(size_t(std::count(ladder.begin(), ladder.end(), 4u)) == a,
           "a pinned prefix length was not honoured");
  }
  pinned.half_prefix_levels = 4;
  Expect(Throws([&] { PlanLevelArenaCapacity(pinned); }),
         "a prefix longer than log2 B was accepted");
  // B < 8 keeps the bottom-fanout search whatever the flag says.
  for (unsigned branching : {2u, 4u}) {
    LevelArenaCapacityRequest request;
    request.entries = 1 << 20;
    request.branching = branching;
    const LevelArenaCapacityChoice on = PlanLevelArenaCapacity(request);
    request.half_fanout_prefix = false;
    const LevelArenaCapacityChoice off = PlanLevelArenaCapacity(request);
    Expect(on.geometry.level_fanouts == off.geometry.level_fanouts &&
               on.bill.requested() == off.bill.requested(),
           "the half-fanout prefix moved a B < 8 ladder");
  }
  printf("  ladder: fanout B/2 at the lowest one to three levels at B = 8, "
         "exact at every power of two\n");
}

// THE PER-LEVEL TIER PROFILE, the automatic sizing.  At 2^22 entries the
// top's tables need two tier buckets and every other level's one, so a shared
// width would put two under every level; the profile keeps each level's own
// and saves the difference at every slot and every pool that holds a tier.
void TestPerLevelTierProfile() {
  LevelArenaGeometry::Params p = Params(8, 6, 8, 2);
  p.level_fanouts = {4, 4, 4, 8, 8};
  const uint64_t horizon = uint64_t{1} << 32;
  p.tier_buckets = 2;
  const LevelArenaGeometry::Params shared =
      ResolveLevelArenaTierGeometry(p, horizon);
  Expect(shared.tier_buckets == 2 && shared.level_tier_buckets.empty(),
         "a pinned shared width did not stay shared");
  p.tier_buckets = 0;
  const LevelArenaGeometry::Params profiled =
      ResolveLevelArenaTierGeometry(p, horizon);
  Expect(profiled.level_tier_buckets ==
                 std::vector<size_t>{1, 1, 1, 1, 1, 2} &&
             profiled.tier_buckets == 2,
         "the per-level profile at 2^22 is not one bucket below a two-bucket "
         "top");
  // Resolving a resolved geometry is the identity, and a pinned profile is
  // checked level by level.
  Expect(ResolveLevelArenaTierGeometry(profiled, horizon).level_tier_buckets ==
             profiled.level_tier_buckets,
         "resolving a resolved profile moved it");
  LevelArenaGeometry::Params short_top = profiled;
  short_top.level_tier_buckets.back() = 1;
  short_top.tier_buckets = 1;
  Expect(Throws([&] { ResolveLevelArenaTierGeometry(short_top, horizon); }),
         "a profile below the top's requirement was accepted");
  LevelArenaGeometry::Params too_narrow = p;
  too_narrow.tier_buckets = 1;
  Expect(Throws([&] { ResolveLevelArenaTierGeometry(too_narrow, horizon); }),
         "a shared width below the top's requirement was accepted");
  // The bill: every tier below the top and the range scratch sized from it.
  const LevelArenaByteBill shared_bill = BillOf(shared, 8, 16, 0);
  const LevelArenaByteBill profiled_bill = BillOf(profiled, 8, 16, 0);
  Expect(profiled_bill.At(ByteRole::kTiers) < shared_bill.At(ByteRole::kTiers) &&
             profiled_bill.requested() < shared_bill.requested() &&
             profiled_bill.At(ByteRole::kMains) == shared_bill.At(ByteRole::kMains),
         "the profile did not save tier bytes and only tier bytes' worth");
  // The ladder resolves it for every candidate.
  LevelArenaCapacityRequest request;
  request.entries = uint64_t{1} << 22;
  const LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(request);
  Expect(choice.geometry.level_tier_buckets.size() == choice.geometry.levels &&
             choice.geometry.level_tier_buckets.back() == 2 &&
             choice.geometry.level_tier_buckets.front() == 1,
         "the ladder did not resolve a per-level profile at 2^22");
  // A built engine allocates what its profile's bill says (the engine checks
  // every buffer against the bill itself); a pinned profile whose top is
  // narrower than its inbox is a legal one.
  LevelArenaEngine::Options options;
  options.geometry = Params(4, 3, 4, 4);
  options.geometry.level_tier_buckets = {1, 2, 1};
  options.geometry.tier_buckets = 2;
  LevelArenaEngine engine(options);
  Expect(engine.geometry().TierBucketsOf(2) == 2 &&
             engine.geometry().TierBucketsOf(3) == 1 &&
             engine.ByteBill() == BillOf(options.geometry, 8, 16, 0),
         "an engine with a pinned profile is not billed at it");
  printf("  tier profile: one bucket below a two-bucket top at 2^22, %.2f%% "
         "fewer bytes, resolved by the ladder\n",
         100.0 * (1.0 - double(profiled_bill.requested()) /
                            double(shared_bill.requested())));
}

// The largest certified capacity, 2^31: the top's stage stash is the
// positive series' four-bucket floor, and its tier the sizing's three.
void TestLargeOutputCertificateWidths() {
  LevelArenaCapacityRequest request;
  request.entries = uint64_t{1} << 31;
  const auto choice = PlanLevelArenaCapacity(request);
  const LevelArenaGeometry geometry(choice.geometry);
  const LevelArenaStashSizing sizing(geometry, request.max_accesses);
  Expect(choice.capacity == request.entries && geometry.TopDigit() == 8,
         "the largest certified capacity retains an exact D=8 default");
  Expect(sizing.Buckets(geometry.Levels()) == 4 &&
             geometry.TierBucketsOf(geometry.Levels()) == 3,
         "large-output stage and tier widths match the positive-series proof");
}

// Pinned axes, threads, and the refusals.
void TestLadderContract() {
  LevelArenaCapacityRequest request;
  request.entries = 1 << 16;
  request.branching = 4;
  request.min_top_digit = 1;

  for (unsigned digit = 1; digit <= request.branching; ++digit) {
    LevelArenaCapacityRequest pinned = request;
    pinned.top_digit = digit;
    if (LevelArenaGeometry::IsTopDigit(digit)) {
      Expect(PlanLevelArenaCapacity(pinned).geometry.top_digit == digit,
             "a pinned D was not honoured");
    } else {
      // Refused by name, not left with no candidate: only a binary top has a
      // certified preparation.
      std::string what;
      try {
        PlanLevelArenaCapacity(pinned);
      } catch (const std::invalid_argument& e) {
        what = e.what();
      }
      Expect(what.find("binary top") != std::string::npos,
             "a nonbinary pinned D was not refused as one");
    }
  }
  for (unsigned flushes : {2u, 4u, 8u}) {
    LevelArenaCapacityRequest pinned = request;
    pinned.prefix_flushes = flushes;
    Expect(PlanLevelArenaCapacity(pinned).geometry.prefix_flushes == flushes,
           "a pinned r0 was not honoured");
  }

  // A thread with no level to drive would park forever, so the ladder may not
  // return a hierarchy shorter than the thread count.
  for (unsigned threads : {1u, 2u, 5u}) {
    LevelArenaCapacityRequest threaded = request;
    threaded.owner_threads = threads;
    const LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(threaded);
    Expect(choice.geometry.levels >= threads,
           "the ladder returned fewer levels than there are owner threads");
  }

  // Pinning the whole search is still a search: the pinned point either
  // covers the request at some L or there is nothing to return.
  Expect(Throws([&] {
           LevelArenaCapacityRequest zero = request;
           zero.entries = 0;
           PlanLevelArenaCapacity(zero);
         }),
         "a capacity of zero was accepted");
  Expect(Throws([&] {
           LevelArenaCapacityRequest wide = request;
           wide.top_digit = LevelArenaGeometry::kMaxTopDigit + 1;
           PlanLevelArenaCapacity(wide);
         }),
         "a D outside [1, 8] was accepted");
  // The top is no wider than B (D <= B), for a pin and a floor.
  Expect(Throws([&] {
           LevelArenaCapacityRequest wide = request;
           wide.top_digit = request.branching + 1;
           PlanLevelArenaCapacity(wide);
         }),
         "a pinned D above B was accepted");
  Expect(Throws([&] {
           LevelArenaCapacityRequest wide = request;
           wide.min_top_digit = request.branching + 1;
           PlanLevelArenaCapacity(wide);
         }),
         "a D floor above B was accepted");
  Expect(Throws([&] {
           LevelArenaCapacityRequest huge = request;
           huge.entries = ~uint64_t{0};
           PlanLevelArenaCapacity(huge);
         }),
         "a capacity no geometry can hold was accepted");
  printf("  ladder: pinned axes, thread floor and refusals\n");
}

// The chosen geometry builds, and the engine it builds holds the capacity the
// ladder promised.  A ladder that returned a shape the engine rejects would
// be arithmetic nobody ran.
void TestChoiceBuilds() {
  for (uint64_t entries : {uint64_t{1} << 12, uint64_t{1} << 16}) {
    for (unsigned branching : {2u, 4u, 8u}) {
      LevelArenaCapacityRequest request;
      request.entries = entries;
      request.branching = branching;
      const LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(request);

      LevelArenaEngine::Options options;
      options.geometry = choice.geometry;
      options.key_bytes = request.key_bytes;
      options.value_bytes = request.value_bytes;
      options.max_accesses = request.max_accesses;
      LevelArenaEngine engine(options);
      Expect(engine.Capacity() == choice.capacity,
             "the engine's capacity is not the one the ladder reported");
      Expect(engine.ByteBill() == choice.bill,
             "the engine's bill is not the one the ladder priced it by");
      Expect(engine.layout().key_bytes == choice.layout.key_bytes &&
                 engine.layout().value_bytes == choice.layout.value_bytes &&
                 engine.layout().tag_bytes == choice.layout.tag_bytes &&
                 engine.layout().digit_bits == choice.layout.digit_bits,
             "the engine's layout is not the one the ladder priced");
    }
  }
  printf("  ladder: every choice builds, at the promised capacity and bill\n");
}


// UNREPRESENTABLE WIDTHS ARE REFUSED, NOT WRAPPED.  Without checked
// arithmetic, a value width near SIZE_MAX would wrap the stored layout into a
// small one and the request scratch's round-up into a one-byte allocation,
// which the engine would then memset with the caller's width (a heap
// overflow).  Each of the three arithmetic steps an
// allocation size takes is checked here on its own, below the map's
// front-door check, since the engine is also built directly.
// A byte budget that rounds below the smallest bill admits no candidate.
// Above 2^53 bytes the bill converts to double inexactly, and a tiny slack
// adds nothing, so the budget can land a few bytes under it; the ladder
// refuses that rather than dereferencing an empty selection.
void TestBudgetBelowTheSmallestBill() {
  const size_t min_bytes = (size_t{1} << 55) + 3;
  Expect(LevelArenaByteBudget(min_bytes, 1e-18) < min_bytes,
         "the rounding this test depends on no longer happens");
  LevelArenaCapacityRequest request;
  request.entries = size_t{1} << 30;
  request.key_bytes = 8;
  request.value_bytes = (size_t{1} << 22) + 5;
  request.byte_slack = 1e-18;
  bool refused = false;
  try {
    (void)PlanLevelArenaCapacity(request);
  } catch (const std::length_error&) {
    refused = true;
  }
  Expect(refused, "a budget below every bill was not refused cleanly");
  printf("  a byte budget below the smallest bill is refused\n");
}

void TestUnrepresentableWidthsAreRefused() {
  const size_t max = std::numeric_limits<size_t>::max();
  const LevelArenaGeometry geometry(Params(8, 2, 1, 2));
  Expect(Throws([&] { (void)LevelArenaStoredLayout(8, max, geometry); }),
         "a value width of SIZE_MAX has no meta line to add, and was taken");
  Expect(Throws([&] { (void)LevelArenaStoredLayout(8, max - 8, geometry); }),
         "a stored entry that wraps size_t was taken");
  Expect(Throws([&] { (void)LevelArenaStoredLayout(8, max / 64, geometry); }),
         "a bucket width that wraps size_t was taken");
  Expect(Throws([&] { (void)Aligned64AllocationBytes(max - 8); }),
         "an allocation's round-up to its alignment wrapped to a small size");
  Expect(Throws([&] { (void)AllocateAligned64(kMaxAligned64Request + 1); }),
         "an allocation above the largest object size reached operator new");
  Expect(LineAllocator<uint8_t>::Bytes(0) == 0 &&
             LineAllocator<uint8_t>::Bytes(128) == 128 &&
             LineAllocator<uint8_t>::Bytes(129) == 256,
         "line-aligned allocation rounding changed at a boundary");
  Expect(Throws([&] { (void)LineAllocator<uint8_t>::Bytes(max); }),
         "a line-aligned byte bill accepted overflowing padding");
  Expect(Throws([&] { (void)LineAllocator<uint64_t>::Bytes(max / 8 + 1); }),
         "a line-aligned element count wrapped its byte product");
  Expect(Throws([&] {
           LineAllocator<uint64_t> allocator;
           const size_t count = max / 8;
           uint64_t* pointer = allocator.allocate(count);
           allocator.deallocate(pointer, count);
         }),
         "a line-aligned allocation wrapped its padding to a small buffer");
  AllocationTally tally;
  tally.AddPlain(max / 2 + 1);
  Expect(Throws([&] { tally.AddPlain(max / 2 + 1); }),
         "a tally of requested bytes wrapped");
  Expect(Throws([&] { tally.AddAligned64(max / 4, 8); }),
         "a tally of count x bytes wrapped");
  LevelArenaEngine::Options options;
  options.geometry = Params(8, 2, 1, 2);
  options.value_bytes = max - 8;
  Expect(Throws([&] { LevelArenaEngine engine(options); }),
         "the engine was built at an unrepresentable value width");
  // Bucket width 2^63 is representable; two buckets are not. Exercise the
  // predictor and allocator separately so agreement on wrapped zero fails.
  const Layout wide{8, (size_t{1} << 57) - 9, 1};
  ValidateLayoutWidths(wide);
  const auto length_error = [](auto&& fn) {
    try {
      fn();
    } catch (const std::length_error&) {
      return true;
    }
    return false;
  };
  Expect(length_error([&] { (void)Table::Create(2, wide); }),
         "a table allocation accepted a wrapped bucket product");
  Expect(length_error([&] { (void)LevelMergeScratch::Bytes(wide, 2); }),
         "the range-scratch predictor accepted a wrapped bucket product");
  Expect(length_error([&] { LevelMergeScratch scratch(wide, 2); }),
         "the range-scratch allocator accepted a wrapped bucket product");
  Expect(length_error([&] { (void)DensePrefixRing::Bytes(geometry, wide); }),
         "the dense predictor accepted a wrapped bucket product");
  Expect(length_error([&] { DensePrefixRing ring(geometry, wide); }),
         "the dense allocator accepted a wrapped bucket product");
  Expect(length_error([&] {
    ParallelBatchResults results;
    results.Resize(max / kMaxBatchLanes);
  }), "aligned batch rows wrapped after rounding the row stride");
  std::printf("  unrepresentable widths: layout, round-up, tally and engine "
              "all refuse\n");
}

}  // namespace
}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram

int main() {
  using namespace microram::byteslice::levelarena;
  using microram::byteslice::CeilLog2;
  using microram::byteslice::Log2Exact;
  const unsigned size_bits = std::numeric_limits<size_t>::digits;
  Expect(CeilLog2(0) == 0 && CeilLog2(1) == 0 && CeilLog2(3) == 2 &&
             CeilLog2(size_t{1} << (size_bits - 1)) == size_bits - 1 &&
             CeilLog2(std::numeric_limits<size_t>::max()) == size_bits &&
             Log2Exact(std::numeric_limits<size_t>::max()) == size_bits,
         "ceiling log2 overflowed or rounded incorrectly");
  printf("level arena: byte bill and capacity ladder\n");
  TestAutomaticTierPricing();
  TestBillIsComplete();
  TestRoutingScratchChangesByteMinimum();
  TestRequestedIsNotReserved();
  TestEngineReportsItsBill();
  TestLadderPicksTheSmallestCompleteBill();
  TestLadderPrefersALongPrefix();
  TestTopDigitFloor();
  TestArenaOnlyAgreesOnOrdering();
  TestHalfFanoutPrefix();
  TestPerLevelTierProfile();
  TestLadderContract();
  TestLargeOutputCertificateWidths();
  TestChoiceBuilds();
  TestUnrepresentableWidthsAreRefused();
  TestBudgetBelowTheSmallestBill();
  printf("level arena 11.6 capacity: OK\n");
  return 0;
}
