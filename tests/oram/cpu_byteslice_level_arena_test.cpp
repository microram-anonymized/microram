// The level arena's foundation: geometry, physical slots and family
// coordinates (cpu_byteslice_level_arena_geometry.hpp, _slots.hpp and
// _family.hpp; src/oram/levelarena/DESIGN.md, "Geometry and storage bound",
// defines the terms).  Every later arena test builds on these: a slot that
// can be written without a lease, or reused before reader retirement, would
// let a merge overwrite a table a reader is still probing.
//
// What is checked here:
//
//   - direct storage sums match the exact main-table storage formula
//     M = 2T + 2 sum(l=2..L) U_l + sum(l<L) (b_l-1) U_l for L = 2..8;
//   - every odd partial fits its level's bank and every even one fits the
//     inbox above, which is where it is built;
//   - every full output exactly fits its receiver slot;
//   - inbox state tests reject writes without a lease and reuse before
//     retirement;
//   - family tests cover consecutive cycles, full-to-full chains, adoption,
//     exhaustion and initialization offsets.
//
// The storage identity is checked TWICE and in two directions: the enumerated
// slots are summed and compared against the analytic sum, and the analytic sum
// is compared against the uniform closed form in exact integer arithmetic.  A
// formula agreeing with itself is not the interesting failure; an allocation
// that disagrees with the formula is.

#include <algorithm>
#include <cstdio>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {
namespace {

using test_support::Expect;

// Ran `fn` and it threw the expected kind of refusal.
template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

// THE LAYOUT BEFORE THE BANK-FIRST RUN, which is what the carry-destination
// fixtures below state digit by digit: odd partials in the bank, even ones in
// the inbox above.  The run's own layout (the default, kNoClone) is stated
// by TestBankFirstRun, and the storage sums cover every mode.
LevelArenaGeometry::Params BaseParams(unsigned branching, unsigned levels,
                                      unsigned top_digit) {
  LevelArenaGeometry::Params p;
  p.branching = branching;
  p.levels = levels;
  p.top_digit = top_digit;
  p.prefix_flushes = 2;
  p.stash_buckets = 1;
  p.bank_first = BankFirst::kOff;
  return p;
}

// Representative top digits up to B (the geometry refuses D > B, and any D
// that is not a power of two): the trivial top and the binary tops.
std::vector<unsigned> TopDigitsUpTo(unsigned branching) {
  if (branching == 2) return {1, 2};
  if (branching == 4) return {1, 2, 4};
  return {1, 4, 8};
}

// -------------------------------------------------------------------------
// Geometry and storage
// -------------------------------------------------------------------------

void TestGeometryBasics() {
  LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
  p.prefix_flushes = 8;
  p.stash_buckets = 1;
  const LevelArenaGeometry g(p);

  Expect(g.OnlineStashEntries() == 64, "64s entries per flush");
  Expect(g.RoutedPrefixBuckets() == 16, "Z = 2 r0 s");
  Expect(g.DensePrefixBuckets() == 8, "Z/2 dense buckets per prefix");
  Expect(g.PrefixPositions() == 64 * 8, "64 s r0 positions per prefix");
  Expect(g.DenseRingBuckets() == 3 * 8, "(q+1) dense prefix slots");
  Expect(g.CarryBuckets(1) == 16 && g.CarryBuckets(2) == 128 &&
             g.CarryBuckets(3) == 1024 && g.CarryBuckets(4) == 8192,
         "U_l = Z B^(l-1)");
  Expect(g.TopBuckets() == 4 * 8192, "T = D U_L");
  // There is no carry size above the top: it never forwards.
  Expect(Throws([&] { return g.CarryBuckets(g.Levels() + 1); }),
         "no carry size above the top");
  Expect(Throws([&] { return g.CarryBuckets(0); }), "levels are one-based");
  Expect(g.CapacityEntries() == 32 * g.TopBuckets(), "capacity is 32T");
  // The access-position offset of a full top is exactly its capacity, which is
  // the identity direct initialization leans on.
  Expect(DirectInitializationSeed(g).access_offset == 32 * g.TopBuckets(),
         "64 s r0 H == 32T");

  Expect(Throws([] { LevelArenaGeometry(BaseParams(3, 4, 4)); }),
         "B must be 2, 4 or 8");
  Expect(Throws([] { LevelArenaGeometry(BaseParams(8, 1, 4)); }),
         "L must be at least 2");
  // 8 is a legal top (the top routes one binary butterfly, so any power of
  // two up to 8 needs no wider radix kernel); 9 is not.
  Expect(!Throws([] { LevelArenaGeometry(BaseParams(8, 4, 8)); }),
         "D = 8 was refused");
  Expect(Throws([] { LevelArenaGeometry(BaseParams(8, 4, 9)); }) &&
             Throws([] { LevelArenaGeometry(BaseParams(8, 4, 16)); }),
         "D must be at most 8");
  // The top is no wider than the fanout, at every B: per access the top
  // moves 2D/(B+1) times what a fanout-B level moves, so D <= B keeps that
  // below two.
  Expect(Throws([] { LevelArenaGeometry(BaseParams(4, 4, 8)); }) &&
             Throws([] { LevelArenaGeometry(BaseParams(2, 4, 4)); }) &&
             !Throws([] { LevelArenaGeometry(BaseParams(4, 4, 4)); }) &&
             !Throws([] { LevelArenaGeometry(BaseParams(2, 4, 2)); }),
         "D must be at most B");
  // And binary: only a power-of-two top has a certified preparation.
  for (unsigned d = 0; d <= LevelArenaGeometry::kMaxTopDigit; ++d) {
    const bool binary = d != 0 && (d & (d - 1)) == 0;
    Expect(LevelArenaGeometry::IsTopDigit(d) == binary &&
               Throws([d] { LevelArenaGeometry(BaseParams(8, 4, d)); }) ==
                   !binary &&
               (!binary || (1u << LevelArenaGeometry::TopPower(d)) == d),
           "the geometry's top digits are not exactly 1, 2, 4 and 8");
  }
  Expect(Throws([] {
           LevelArenaGeometry::Params bad = BaseParams(8, 4, 4);
           bad.stash_buckets = 3;
           return LevelArenaGeometry(bad);
         }),
         "s must be a power of two");
  Expect(Throws([] {
           LevelArenaGeometry::Params bad = BaseParams(8, 4, 4);
           bad.prefix_flushes = 16;
           return LevelArenaGeometry(bad);
         }),
         "r0 must be 2, 4 or 8");
  // A tier is drained into as a ResidualStash, whose occupancy array is
  // kMaxResidualStashBuckets words wide and INLINE.  A wider tier would
  // allocate fine and overrun the stash's own Count() later.
  Expect(Throws([] {
           LevelArenaGeometry::Params bad = BaseParams(8, 4, 4);
           bad.tier_buckets = kMaxResidualStashBuckets + 1;
           return LevelArenaGeometry(bad);
         }),
         "a tier may not exceed a residual stash's occupancy array");
  // Index 0 of the level table is a placeholder, not level 0: asking for it is
  // a bug and must not quietly return an empty plan.
  Expect(Throws([&] { return g.storage().At(0).arena_buckets; }),
         "there is no level 0");
  Expect(Throws([&] { return g.storage().At(g.Levels() + 1).arena_buckets; }),
         "there is no level above the top");
  Expect(Throws([&] { return g.LevelArenaBytes(0, Layout{}); }),
         "no level 0 has bytes");
  {
    const Layout layout;
    uint64_t sum = 0;
    for (unsigned l = 1; l <= g.Levels(); ++l) sum += g.LevelArenaBytes(l, layout);
    Expect(g.ArenaBytes(layout) == sum, "ArenaBytes sums the level arenas");
    Expect(g.ArenaBytes(layout) ==
               g.ArenaBuckets() * (layout.BucketBytes() + sizeof(uint64_t)),
           "arena bytes are buckets plus one occupancy word each");
  }
  printf("  geometry: parameters, derived counts, refusals\n");
}

void TestVariableFanout() {
  // b_1 = 2 at the bottom, then a second two-way level and an eight-way one,
  // so the ladder exercises a fanout below B at level 1 (which keeps its odd
  // bank, having no adoption) and at a level above it (which also keeps one).
  LevelArenaGeometry::Params params = BaseParams(8, 4, 4);
  params.level_fanouts = {2, 2, 8};
  const LevelArenaGeometry geometry(params);

  Expect(geometry.Fanout(1) == 2 && geometry.Fanout(2) == 2 &&
             geometry.Fanout(3) == 8,
         "mixed ladder exposes per-level fanouts");
  Expect(Throws([&] { return geometry.Fanout(geometry.Levels()); }),
         "the top has no fanout, it has a digit");
  Expect(geometry.CarryBuckets(1) == 4 && geometry.CarryBuckets(2) == 8 &&
             geometry.CarryBuckets(3) == 16 && geometry.CarryBuckets(4) == 128,
         "mixed ladder carries use a checked prefix product");
  Expect(geometry.PrefixProduct(1) == 1 && geometry.PrefixProduct(2) == 2 &&
             geometry.PrefixProduct(4) == 32,
         "the prefix product is the ladder's running product");
  Expect(geometry.storage().At(1).odd_bank != LevelPlan::kNoSlot,
         "level 1 has no adoption, so its digit 1 needs a partial bank");
  Expect(geometry.storage().At(2).odd_bank != LevelPlan::kNoSlot,
         "a two-way non-bottom level keeps its first carry in the odd bank");
  Expect(geometry.PlanCarry(1, 2).outcome == CarryOutcome::kForward,
         "the bottom fanout controls forwarding");
  Expect(geometry.PlanCarry(2, 1).outcome == CarryOutcome::kPartial &&
             geometry.PlanCarry(2, 2).outcome == CarryOutcome::kForward,
         "the next level retains its own fanout");
  Expect(geometry.PlanCarry(3, 7).outcome == CarryOutcome::kPartial &&
             geometry.PlanCarry(3, 8).outcome == CarryOutcome::kForward,
         "an eight-way level above two-way ones keeps its own odometer");

  // A family's window end is invariant along the forwarding chain TERM BY
  // TERM, which is the property a per-level ladder has to preserve and the
  // one a B-for-b_l substitution anywhere in the nonce path would break.
  const std::vector<unsigned>& ladder = geometry.params().level_fanouts;
  for (unsigned level = 1; level < geometry.Levels(); ++level) {
    const uint64_t fanout = geometry.Fanout(level);
    for (uint64_t ordinal = 1; ordinal <= 4 * fanout; ++ordinal) {
      const Family here = CanonicalFamily(geometry, level, ordinal);
      Expect(here == CanonicalFamily(ladder, geometry.Levels(), level,
                                     ordinal),
             "the geometry and the raw ladder disagree about a family");
      if (ordinal % fanout != 0) continue;
      Expect(here == CanonicalFamily(geometry, level + 1, ordinal / fanout),
             "a forwarded carry left its family");
      Expect(FamilyPrefixWindowEnd(ladder, here) ==
                 FamilyPrefixWindowEnd(ladder, Family{level, ordinal}),
             "mixed ladder family windows are not invariant across "
             "forwarding");
    }
  }

  // Direct initialization has to land on the state repeated insertion would:
  // every non-top level a whole number of full tables, and no partial.
  const InitialSeed seed = DirectInitializationSeed(geometry);
  Expect(seed.prefixes == 4 * 32, "H is D times the fanout product");
  for (unsigned level = 1; level < geometry.Levels(); ++level) {
    Expect(seed.level_carries[level] % geometry.Fanout(level) == 0,
           "a seeded level would hold a partial");
  }
  Expect(seed.access_offset == 32 * uint64_t{geometry.TopBuckets()},
         "the seeded access offset is not the capacity");

  // And an explicitly uniform ladder is the uniform ladder, slot for slot:
  // stating the default is not a request for a different engine.
  LevelArenaGeometry::Params implicit = BaseParams(8, 4, 4);
  LevelArenaGeometry::Params explicit_uniform = implicit;
  explicit_uniform.level_fanouts = {8, 8, 8};
  const LevelArenaGeometry a(implicit);
  const LevelArenaGeometry b(explicit_uniform);
  Expect(a.MainBuckets() == b.MainBuckets() &&
             a.ArenaBuckets() == b.ArenaBuckets() &&
             a.storage().At(2).slots.size() == b.storage().At(2).slots.size(),
         "an explicit all-B ladder is not the uniform ladder");

  // Refusals: a ladder of the wrong length, a fanout above B, and one that is
  // not a power of two -- U_l is the block width of every butterfly, so a
  // non-power-of-two fanout is a geometry whose tables cannot be routed.
  for (const std::vector<unsigned>& bad :
       {std::vector<unsigned>{8, 8}, std::vector<unsigned>{8, 8, 8, 8},
        std::vector<unsigned>{16, 8, 8}, std::vector<unsigned>{3, 8, 8},
        std::vector<unsigned>{1, 8, 8}}) {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.level_fanouts = bad;
    Expect(Throws([&] { return LevelArenaGeometry(p); }),
           "an illegal fanout ladder was accepted");
  }
  printf("  variable fanout: mixed carries, banks, digits, families, seeds "
         "and refusals\n");
}

// Counts that are DERIVED rather than given, at inputs where the derivation
// wraps.  Every one of these was a silent wrong answer before it was checked:
// the geometry constructed, and a count a buffer would have been sized from
// came out smaller than the truth -- which is the one failure mode a test of
// ordinary parameters can never see.
void TestBoundaryArithmetic() {
  // q + 1 in UNSIGNED arithmetic wraps to zero, which reported a ring of no
  // buckets for a geometry that had constructed successfully.  Widened, it is
  // simply the true count; the product is what can still overflow, and that is
  // refused at construction, before any count can be read out.
  {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.prefix_flushes = 8;
    p.dense_prefixes = ~0u;
    const LevelArenaGeometry g(p);
    Expect(g.DensePrefixBuckets() == 8, "Z/2 is unaffected by q");
    Expect(g.DenseRingBuckets() == (uint64_t{1} << 32) * 8,
           "q = UINT_MAX must not report a ring of no buckets");
  }
  Expect(Throws([] {
           LevelArenaGeometry::Params bad = BaseParams(8, 4, 4);
           bad.dense_prefixes = 1u << 31;
           bad.stash_buckets = size_t{1} << 40;
           return LevelArenaGeometry(bad);
         }),
         "a dense ring above 2^64 buckets must be refused");
  {
    // And the ordinary case still reports (q + 1) prefixes.
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.prefix_flushes = 8;
    p.dense_prefixes = 5;
    const LevelArenaGeometry g(p);
    Expect(g.DenseRingBuckets() == 6 * g.DensePrefixBuckets(),
           "(q + 1) prefix slots");
  }

  // The raw family overload takes B as an argument and so has to reject what
  // the geometry would have: B = 0 is a modulo by zero in the forwarding loop,
  // B = 1 a hierarchy in which every ordinal forwards.
  Expect(Throws([] { return CanonicalFamily(0, 4, 1, 8); }),
         "B = 0 must not reach the forwarding loop");
  Expect(Throws([] { return CanonicalFamily(1, 4, 1, 8); }),
         "B = 1 is not a hierarchy");
  Expect(CanonicalFamily(2, 4, 1, 8) == (Family{4, 1}),
         "the two-way ladder still forwards to the top");

  printf("  boundary arithmetic: derived counts widen or refuse, never wrap\n");
}

size_t CountSlots(const LevelArenaGeometry& g) {
  size_t n = 0;
  for (unsigned l = 1; l <= g.Levels(); ++l) n += g.storage().At(l).slots.size();
  return n;
}

// main/T = 2 + [(3B-1)/((B-1)D)] * (1 - B^-(L-1)), cleared of denominators:
//   main * (B-1) D B^(L-1)
//     == T * [ 2 (B-1) D B^(L-1) + (3B-1)(B^(L-1) - 1) ].
// Use an integer identity.
void ExpectClosedForm(const LevelArenaGeometry& g) {
  const unsigned B = g.Branching();
  const uint64_t D = g.TopDigit();
  const uint64_t pow = CheckedPow(B, g.Levels() - 1, "closed form");
  const uint64_t lhs =
      CheckedMul(g.MainBuckets(), CheckedMul(CheckedMul(B - 1, D, "x"), pow, "x"),
                 "closed form");
  const uint64_t rhs = CheckedMul(
      g.TopBuckets(),
      CheckedAdd(CheckedMul(2 * (B - 1) * D, pow, "x"),
                 CheckedMul(3 * uint64_t{B} - 1, pow - 1, "x"), "x"),
      "closed form");
  Expect(lhs == rhs, "main/T matches the closed form");
}

// THE PER-LEVEL TIER PROFILE (Params::level_tier_buckets): a tier's width is
// its PRODUCER's, so level l's inboxes hold level l-1's width and every other
// slot of level l -- banks, the run bank, the top's banks -- its own.  A merge
// then reads its carry at the level below's width, its older operand at its
// own, except an adopted first carry, which is still in the inbox.
void TestTierProfile() {
  for (BankFirst mode : {BankFirst::kOff, BankFirst::kNoClone}) {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.bank_first = mode;
    p.level_fanouts = {4, 8, 8};
    p.level_tier_buckets = {1, 2, 3, 2};  // the top narrower than its inbox
    p.tier_buckets = 3;
    const LevelArenaGeometry g(p);
    Expect(g.HasTierProfile() && g.TierBuckets() == 3,
           "the profile's widest entry is the geometry's tier width");
    size_t total = 0;
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      for (const SlotSpec& s : g.storage().At(l).slots) {
        const size_t want = s.kind == SlotKind::kInbox
                                ? p.level_tier_buckets[l - 2]
                                : p.level_tier_buckets[l - 1];
        Expect(s.tier_buckets == want,
               ("a slot's tier is not its producer's width at level " +
                std::to_string(l)).c_str());
        total += s.tier_buckets;
      }
      Expect(g.TierBucketsOf(l) == p.level_tier_buckets[l - 1],
             "TierBucketsOf does not read the profile");
      Expect(g.CarryTierBuckets(l) ==
                 (l == 1 ? 0 : p.level_tier_buckets[l - 2]),
             "a carry's tier is not the level below's");
      if (l < g.Levels()) {
        for (unsigned d = 2; d <= g.Fanout(l); ++d) {
          const bool adopted =
              d == 2 && g.PlanCarry(l, 1).outcome == CarryOutcome::kAdopt;
          Expect(g.OlderTierBuckets(l, d) ==
                     (adopted ? p.level_tier_buckets[l - 2]
                              : p.level_tier_buckets[l - 1]),
                 "an older operand's tier is not where it was built");
        }
      }
    }
    Expect(g.OlderTierBuckets(4, 4) == 2 && g.CarryTierBuckets(4) == 3,
           "the top reads A at its own width and B at level 3's");
    Expect(total == g.storage().tier_buckets,
           "tier storage is not the sum of the slots' widths");
    // The shared width is the profile of all one value, byte for byte.
    LevelArenaGeometry::Params flat = p;
    flat.level_tier_buckets = {3, 3, 3, 3};
    LevelArenaGeometry::Params shared = p;
    shared.level_tier_buckets.clear();
    Expect(LevelArenaGeometry(flat).storage().tier_buckets ==
               LevelArenaGeometry(shared).storage().tier_buckets &&
               LevelArenaGeometry(flat).ArenaBuckets() ==
                   LevelArenaGeometry(shared).ArenaBuckets(),
           "a flat profile is not the shared width");
  }
  // Refusals: one width per level, each a stash width, the widest equal to
  // tier_buckets, and none narrower than the level below it below the top.
  const auto refused = [](std::vector<size_t> profile, size_t widest) {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.level_tier_buckets = std::move(profile);
    p.tier_buckets = widest;
    return Throws([&] { LevelArenaGeometry g(p); });
  };
  Expect(refused({1, 1, 2}, 2), "a short profile was accepted");
  Expect(refused({0, 1, 1, 2}, 2), "a zero-width tier was accepted");
  Expect(refused({1, 1, 1, 9}, 9), "a tier past the stash array was accepted");
  Expect(refused({1, 1, 1, 2}, 3), "a profile below tier_buckets was accepted");
  Expect(refused({2, 1, 1, 2}, 2), "a profile narrowing below the top was accepted");
  Expect(!refused({1, 2, 2, 1}, 2), "a top narrower than its inbox was refused");
  printf("  tier profile: producer widths per slot, per carry and per older "
         "operand; refusals\n");
}

void TestStorageSums() {
  // Every mode of the bank-first run: it adds a tier per level and no main,
  // so every main-storage sum and the closed form hold in both.
  for (BankFirst mode : {BankFirst::kOff, BankFirst::kNoClone}) {
  for (unsigned B : {2u, 4u, 8u}) {
    for (unsigned L = 2; L <= 8; ++L) {
      for (unsigned D : TopDigitsUpTo(B)) {
        LevelArenaGeometry::Params params = BaseParams(B, L, D);
        params.bank_first = mode;
        const LevelArenaGeometry g(params);

        // Every non-top level keeps the odd bank in the common layout.
        uint64_t partial = 0, inbox = 0;
        for (unsigned l = 1; l < L; ++l) {
          partial += uint64_t{g.Fanout(l) - 1} * g.CarryBuckets(l);
        }
        for (unsigned l = 2; l <= L; ++l) inbox += 2 * uint64_t{g.CarryBuckets(l)};
        const uint64_t main = partial + inbox + 2 * uint64_t{g.TopBuckets()};

        // The same quantity read off the ENUMERATED slots, which is what is
        // actually allocated.
        uint64_t enumerated_main = 0, enumerated_tier = 0, enumerated_arena = 0;
        uint64_t enumerated_partial = 0, enumerated_inbox = 0,
                 enumerated_top = 0;
        for (unsigned l = 1; l <= L; ++l) {
          const LevelPlan& plan = g.storage().At(l);
          uint64_t level_buckets = 0;
          for (const SlotSpec& s : plan.slots) {
            // The run bank's main is the odd bank's: counted once.
            const uint64_t main = s.shares_main ? 0 : s.main_buckets;
            enumerated_main += main;
            enumerated_tier += s.tier_buckets;
            level_buckets += main + s.tier_buckets;
            switch (s.kind) {
              case SlotKind::kOddBank: enumerated_partial += main; break;
              case SlotKind::kInbox: enumerated_inbox += main; break;
              case SlotKind::kTopBank: enumerated_top += main; break;
              case SlotKind::kRunBank:
                Expect(s.shares_main, "a run bank allocates no main");
                break;
            }
          }
          Expect(level_buckets == plan.arena_buckets,
                 "a level's arena is exactly its slots");
          enumerated_arena += level_buckets;
        }
        Expect(enumerated_partial == partial,
               "partial banks do not sum to the per-level bank rule");
        Expect(enumerated_inbox == inbox, "inboxes sum to 2 sum U_l");
        Expect(enumerated_top == 2 * uint64_t{g.TopBuckets()}, "the top owns 2T");
        Expect(enumerated_main == main, "enumerated main storage matches 6.1");
        Expect(g.MainBuckets() == main, "MainBuckets matches 6.1");
        Expect(g.ArenaBuckets() == enumerated_arena, "ArenaBuckets sums the levels");
        Expect(enumerated_tier == g.storage().tier_buckets,
               "one tier per physical slot");
        Expect(g.storage().tier_buckets ==
                   g.TierBuckets() * CountSlots(g),
               "tier storage is slots x tier size");
        ExpectClosedForm(g);

        // Slots never overlap and never leave a hole.  A slot that shares
        // another's main places only its tier, at the cursor.
        for (unsigned l = 1; l <= L; ++l) {
          const LevelPlan& plan = g.storage().At(l);
          size_t cursor = 0;
          for (const SlotSpec& s : plan.slots) {
            if (s.shares_main) {
              Expect(s.tier_offset == cursor,
                     "a shared-main slot's tier is placed in order");
              cursor = s.tier_offset + s.tier_buckets;
              continue;
            }
            Expect(s.main_offset == cursor, "slot mains are placed in order");
            Expect(s.tier_offset == s.main_offset + s.main_buckets,
                   "a slot's tier follows its main");
            cursor = s.tier_offset + s.tier_buckets;
          }
          Expect(cursor == plan.arena_buckets, "no gap at the end of a level");
        }
      }
    }
  }
  }
  // Every level allocates its odd bank, including fanout-two levels inside
  // a mixed ladder, whose P_1 uses the partial pipeline.
  for (unsigned B : {2u, 4u, 8u}) {
    auto p = BaseParams(B, 5, std::min(B, 4u));
    if (B > 2) p.level_fanouts = {2, 2, B, B};
    const LevelArenaGeometry common(p);
    for (unsigned l = 2; l < common.Levels(); ++l) {
      const bool binary = common.Fanout(l) == 2;
      Expect(common.storage().At(l).odd_bank != LevelPlan::kNoSlot,
             "every level allocates the odd bank");
      Expect(common.PlanCarry(l, 1).outcome ==
                 (binary ? CarryOutcome::kPartial : CarryOutcome::kAdopt),
             "binary P_1 uses the partial pipeline");
    }
    if (B == 2) ExpectClosedForm(common);
  }
  printf("  storage: enumerated slots == per-level bank rule == closed form, "
         "L=2..8\n");
}

// -------------------------------------------------------------------------
// Carry destinations
// -------------------------------------------------------------------------

void TestCarryDestinations() {
  for (unsigned B : {2u, 4u, 8u}) {
    for (unsigned L = 2; L <= 5; ++L) {
      const LevelArenaGeometry g(BaseParams(B, L, std::min(B, 4u)));
      for (unsigned l = 1; l < L; ++l) {
        const LevelPlan& plan = g.storage().At(l);
        const size_t u = g.CarryBuckets(l);
        // Two full cycles: ordinals never reset, so the second cycle must
        // reproduce the same digits and destinations.
        for (uint64_t v = 1; v <= 2 * uint64_t{B}; ++v) {
          const CarryPlan c = g.PlanCarry(l, v);
          const unsigned j = 1 + static_cast<unsigned>((v - 1) % B);
          Expect(c.digit == j, "digit is 1 + (v-1) mod B");
          if (j == B) {
            Expect(c.outcome == CarryOutcome::kForward, "digit B forwards");
            Expect(c.destination_level == l + 1, "forwards to the next level");
            Expect(c.output_buckets == g.CarryBuckets(l + 1),
                   "a full output is exactly U_(l+1)");
            // ... and that is exactly one inbox slot of the receiver.
            const LevelPlan& up = g.storage().At(l + 1);
            for (unsigned i = 0; i < 2; ++i) {
              Expect(up.inbox[i] != LevelPlan::kNoSlot, "receivers have 2 inboxes");
              Expect(up.At(up.inbox[i]).main_buckets == c.output_buckets,
                     "a full output exactly fits its receiver slot");
            }
            continue;
          }
          Expect(c.output_buckets == j * u, "a partial is j U_l");
          if (j == 1 && l >= 2 && B > 2) {
            Expect(c.outcome == CarryOutcome::kAdopt, "digit 1 above level 1 adopts");
            Expect(c.destination_kind == SlotKind::kInbox,
                   "an adopted P_1 stays in its inbox");
            continue;
          }
          Expect(c.outcome == CarryOutcome::kPartial, "other digits merge");
          // PARITY DECIDES WHICH ARENA, not which of two banks: an odd
          // partial is the level's own bank, an even one is built in the
          // level above's inbox under the forwarding lease.
          if (j % 2 == 0) {
            Expect(c.destination_kind == SlotKind::kInbox &&
                       c.destination_level == l + 1,
                   "an even partial is built in the inbox above");
            const LevelPlan& up = g.storage().At(l + 1);
            for (unsigned i = 0; i < 2; ++i) {
              Expect(up.inbox[i] != LevelPlan::kNoSlot &&
                         up.At(up.inbox[i]).main_buckets >= c.output_buckets,
                     "an even partial does not fit the inbox above");
            }
          } else {
            Expect(c.destination_kind == SlotKind::kOddBank &&
                       c.destination_level == l,
                   "an odd partial is built in this level's own bank");
            Expect(plan.odd_bank != LevelPlan::kNoSlot, "the odd bank exists");
            Expect(plan.At(plan.odd_bank).main_buckets >= c.output_buckets,
                   "every odd partial fits the odd bank");
          }
          // Consecutive digits land in DIFFERENT slots, which is the whole
          // point of the parity split: P_(j-1) is the source of P_j.  The
          // comparison is (level, kind) and not kind alone, because at j = 2
          // above level 1 the source is an ADOPTED table in this level's own
          // inbox while the destination is an inbox of the level above --
          // both kInbox, different arenas.
          if (j >= 2) {
            const CarryPlan prev = g.PlanCarry(l, v - 1);
            Expect(prev.destination_level != c.destination_level ||
                       prev.destination_kind != c.destination_kind,
                   "a merge does not overwrite its own source");
          }
        }
      }
      // The top has no odometer.
      for (uint64_t v = 1; v <= 3; ++v) {
        const CarryPlan c = g.PlanCarry(L, v);
        Expect(c.outcome == CarryOutcome::kCompact, "the top compacts");
        Expect(c.output_buckets == g.TopBuckets(), "the top is always T");
        Expect(c.destination_kind == SlotKind::kTopBank, "into a top bank");
      }
      // What a level KEEPS versus what it WRITES: the second is larger at
      // every non-top level, and it is the one the stash planners size from.
      for (unsigned l = 1; l < L; ++l) {
        Expect(g.MaxResidentBuckets(l) ==
                   (B - 1) * g.CarryBuckets(l),
               "a level's largest own table is its digit-(B-1) partial");
        Expect(g.MaxOutputBuckets(l) == g.CarryBuckets(l + 1),
               "a level's largest output is the full table it forwards");
        Expect(g.MaxOutputBuckets(l) > g.MaxResidentBuckets(l),
               "a level writes more than it keeps");
      }
      Expect(g.MaxResidentBuckets(L) == g.TopBuckets() &&
                 g.MaxOutputBuckets(L) == g.TopBuckets(),
             "the top keeps and writes T");
      Expect(Throws([&] { g.PlanCarry(1, 0); }), "ordinals are one-based");
      Expect(Throws([&] { g.PlanCarry(L + 1, 1); }), "no level above the top");
    }
  }
  printf("  carries: parity places every partial, full outputs fit inboxes\n");
}

// -------------------------------------------------------------------------
// Families
// -------------------------------------------------------------------------

void TestFamilies() {
  for (unsigned B : {2u, 4u, 8u}) {
    const unsigned L = B == 2 ? 5 : 4;
    const LevelArenaGeometry g(BaseParams(B, L, std::min(B, 4u)));
    // Members of one family share an id AND a window end; different families
    // never share an id.
    std::vector<std::pair<uint64_t, uint64_t>> seen;  // id -> prefix window end
    for (unsigned l = 1; l <= L; ++l) {
      const uint64_t period = CheckedPow(B, l - 1, "period");
      for (uint64_t v = 1; v <= 4096 / period; ++v) {
        const Family root = CanonicalFamily(g, l, v);
        const uint64_t id = FamilyId(root);
        const uint64_t window = FamilyPrefixWindowEnd(B, root);
        Expect(window == CheckedMul(v, period, "window"),
               "every member ends at the same public prefix boundary");
        bool found = false;
        for (const auto& entry : seen) {
          if (entry.first != id) continue;
          Expect(entry.second == window, "one id, one window end");
          found = true;
        }
        if (!found) seen.emplace_back(id, window);
        // A full-to-full chain agrees with its consumer without talking to it.
        if (l < L && v % B == 0) {
          Expect(root == CanonicalFamily(g, l + 1, v / B),
                 "a forwarded carry keeps its consumer's family");
        }
        // Adoption is terminal at its own level.
        if (l >= 2 && v % B == 1) {
          Expect(root == (Family{l, v}), "digit-1 adoption is terminal");
        }
      }
    }
    // Consecutive cycles do not reuse a family: ordinals are never reset.
    Expect(CanonicalFamily(g, 1, 1) != CanonicalFamily(g, 1, B + 1),
           "the next cycle is a different family");
    // The nonce packs the coordinate, and the id IS the real high word.
    const Family f = CanonicalFamily(g, 1, B + 1);
    const RebuildNonce n = FamilyNonce(f);
    Expect(n.family_id == FamilyId(f), "the nonce carries the family id");
    Expect(n.real_high == FamilyId(f), "family_id is the packed real nonce");
    Expect(n.dummy_high != n.real_high, "the dummy nonce is a separate domain");
    Expect(n.target_level == f.level && n.epoch == f.ordinal,
           "the nonce's level and epoch fields are the coordinate");
    // The reserved empty-top identity is disjoint from every regular family.
    const uint64_t empty = EmptyTopFamilyId(L);
    Expect(empty == L, "an empty top is family L at epoch 0");
    for (const auto& entry : seen) {
      Expect(entry.first != empty, "no regular family collides with the empty top");
    }
    const RebuildNonce empty_nonce = EmptyTopNonce(L);
    Expect(empty_nonce.family_id == empty, "the empty-top nonce agrees");
    Expect(empty_nonce.real_high == empty && empty_nonce.epoch == 0 &&
               empty_nonce.target_level == L,
           "the empty-top nonce is level L at epoch 0");
    Expect(empty_nonce.dummy_high != empty_nonce.real_high,
           "the empty top still has two domains");
  }

  // Exhaustion: refuse before wrapping, rather than quietly reusing a hash.
  Expect(Throws([] { FamilyId(Family{1, 0}); }), "ordinal 0 is not a family");
  Expect(Throws([] { FamilyId(Family{0, 1}); }), "level 0 is reserved for dense");
  Expect(Throws([] { FamilyId(Family{1, kMaxFamilyOrdinal + 1}); }),
         "the ordinal field is 48 bits");
  Expect(Throws([] { FamilyId(Family{1u << 15, 1}); }),
         "the level field is 15 bits");
  Expect(FamilyId(Family{1, kMaxFamilyOrdinal}) != 0, "the last ordinal is legal");
  // A window end from a hand-built coordinate must refuse the same way the id
  // does, rather than wrapping `level - 1` into a four-billion-step power.
  Expect(Throws([] { return FamilyPrefixWindowEnd(8, Family{0, 1}); }),
         "level 0 has no window");
  Expect(Throws([] { return FamilyPrefixWindowEnd(8, Family{1, 0}); }),
         "ordinal 0 has no window");
  printf("  families: cycles, full-to-full chains, adoption, exhaustion\n");
}

void TestInitializationSeed() {
  for (unsigned B : {2u, 4u, 8u}) {
    for (unsigned L = 2; L <= 5; ++L) {
      for (unsigned D : TopDigitsUpTo(B)) {
        const LevelArenaGeometry g(BaseParams(B, L, D));
        const InitialSeed seed = DirectInitializationSeed(g);
        Expect(seed.prefixes == D * CheckedPow(B, L - 1, "H"), "H = D B^(L-1)");
        Expect(seed.level_carries[L] == D, "the top receives D carries");
        Expect(seed.stash_flushes == uint64_t{g.PrefixFlushes()} * seed.prefixes,
               "the flush counter is r0 H");
        Expect(seed.access_offset == 32 * uint64_t{g.TopBuckets()},
               "the access offset is 64 s r0 H = 32T");
        Expect(seed.top_family == (Family{L, D}), "the initial top is family (L,D)");
        for (unsigned l = 1; l < L; ++l) {
          const uint64_t n = seed.level_carries[l];
          Expect(n % B == 0, "every non-top digit is zero after seeding");
          Expect(CanonicalFamily(g, l, n) == seed.top_family,
                 "the seeded levels all belong to the initial top's family");
          // The next carry at every level opens a strictly later window, so no
          // later family can reuse the initial top's coordinate.
          const Family future = CanonicalFamily(g, l, n + 1);
          Expect(FamilyPrefixWindowEnd(B, future) > seed.prefixes,
                 "subsequent families end later than the seeded top");
        }
      }
    }
  }
  printf("  initialization: H, per-level carries, flush and position offsets\n");
}

// -------------------------------------------------------------------------
// Slot lifecycle
// -------------------------------------------------------------------------

Layout TestLayout() {
  Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = 4;
  return layout;
}

// Inspect every physical slot, including both inboxes/top banks and the run
// lifecycle that shares a main. Tier widths deliberately differ at receivers.
void TestCompactTierPool() {
  for (unsigned branching : {2u, 4u, 8u}) {
    for (size_t value_bytes : {size_t{8}, size_t{48}}) {
      auto params = BaseParams(branching, 3, branching);
      params.bank_first = BankFirst::kNoClone;
      params.tier_buckets = 3;
      params.level_tier_buckets = {1, 3, 2};
      const LevelArenaGeometry g(params);
      const Layout layout{8, value_bytes + 1, 4}; // includes meta and tags
      LevelArenaSet arenas(g, layout);
      uint8_t* pool_begin = nullptr;
      uint8_t* cursor = nullptr;
      size_t total_buckets = 0;
      bool kinds[4] = {};
      std::vector<std::pair<uintptr_t, uintptr_t>> main_regions;
      for (unsigned l = 1; l <= g.Levels(); ++l) {
        auto& arena = arenas.At(l);
        size_t legacy_cursor = 0;
        uintptr_t main_base = 0;
        for (unsigned i = 0; i < arena.num_slots(); ++i) {
          const auto& spec = arena.spec(i);
          kinds[static_cast<unsigned>(spec.kind)] = true;
          const size_t width = params.level_tier_buckets[
              spec.kind == SlotKind::kInbox ? l - 2 : l - 1];
          Expect(spec.tier_buckets == width, "slot keeps its producer's tier width");
          if (!spec.shares_main) {
            Expect(spec.main_offset == legacy_cursor, "main offset was compacted");
            legacy_cursor += spec.main_buckets;
          } else {
            Expect(spec.main_offset == arena.spec(arena.plan().odd_bank).main_offset,
                   "run bank no longer shares its odd main");
          }
          Expect(spec.tier_offset == legacy_cursor, "legacy tier hole moved");
          legacy_cursor += width;
          SlotLease lease;
          Expect(arena.TryLease(arena.MakeCredit(i), &lease), "pool slot leases");
          const auto main = arena.WritableMain(lease, spec.main_buckets);
          const uintptr_t base = reinterpret_cast<uintptr_t>(main.data) -
                                 spec.main_offset * layout.BucketBytes();
          if (i == 0) main_base = base;
          Expect(base == main_base, "main view lost its original arena offset");
          auto* tier = arena.WritableTier(lease); // rebuild's destination
          if (pool_begin == nullptr) pool_begin = cursor = tier->data;
          Expect(tier->data == cursor, "pool has a gap, overlap or wrong slot order");
          Expect(reinterpret_cast<uintptr_t>(tier->data) % 64 == 0,
                 "pool slice is not cache-line aligned");
          Expect(tier->num_buckets == width && tier->entry_bytes == layout.EntryBytes(),
                 "pool slice changed capacity or key/value/meta/tag stride");
          for (size_t b = 0; b < width; ++b) {
            Expect(tier->Bucket(b) == cursor + b * layout.BucketBytes(),
                   "multi-bucket tier is not contiguous");
            // Touch the last tag byte as well as the first payload byte.
            tier->Bucket(b)[0] = static_cast<uint8_t>(i + l);
            tier->Bucket(b)[layout.BucketBytes() - 1] = 0xAC;
            tier->masks[b] = uint64_t{1} << b;
          }
          cursor += width * layout.BucketBytes();
          total_buckets += width;
          Expect(arena.Publish(lease), "pool slot publishes");
          const auto published = arena.PublishedTierTable(i);
          Expect(published.data == tier->data && published.masks == tier->masks &&
                     published.num_buckets == width &&
                     published.layout.EntryBytes() == layout.EntryBytes(),
                 "published tier is not the assigned payload and inline masks");
        }
        Expect(legacy_cursor == arena.plan().arena_buckets,
               "original arena region size changed");
        Expect(main_base % Aligned64Alignment(legacy_cursor * layout.BucketBytes()) == 0,
               "main arena allocation lost its original alignment");
        main_regions.emplace_back(main_base, main_base +
            legacy_cursor * layout.BucketBytes());
      }
      const uintptr_t first = reinterpret_cast<uintptr_t>(pool_begin);
      const uintptr_t end = reinterpret_cast<uintptr_t>(cursor);
      for (const auto& region : main_regions) {
        Expect(end <= region.first || first >= region.second,
               "pool overlaps a retained main arena");
      }
      // Later writes must not overwrite even the last bucket of earlier slices.
      for (unsigned l = 1; l <= g.Levels(); ++l) {
        const auto& arena = arenas.At(l);
        for (unsigned i = 0; i < arena.num_slots(); ++i) {
          const auto* tier = arena.PublishedTier(i);
          for (size_t b = 0; b < tier->num_buckets; ++b) {
            Expect(tier->Bucket(b)[0] == i + l &&
                       tier->Bucket(b)[layout.BucketBytes() - 1] == 0xAC &&
                       tier->masks[b] == (uint64_t{1} << b),
                   "another slice overwrote published payload or masks");
          }
        }
      }
      Expect(kinds[0] && kinds[1] && kinds[2] && (kinds[3] == (branching == 8)),
             "pool fixture missed a physical slot kind");
      const size_t payload = total_buckets * layout.BucketBytes();
      Expect(end - first == payload && payload == LevelArenaSet::TierPayloadBytes(g, layout),
             "pool has incorrect total size");
      Expect(arenas.bytes() == LevelArenaSet::Bytes(g, layout) &&
                 arenas.bytes().At(ByteRole::kTiers) == payload &&
                 arenas.bytes().At(ByteRole::kRetainedTierHoles) == payload,
             "live pool and retained holes are not counted exactly once");
      // Keep standalone users usable without a pool or an owner interface.
      LevelArena standalone(g.storage().At(1), layout);
      SlotLease lease;
      Expect(standalone.TryLeaseOwn(standalone.plan().odd_bank, &lease),
             "standalone arena leases");
      const auto& spec = standalone.spec(lease.slot);
      const auto main = standalone.WritableMain(lease, spec.main_buckets);
      Expect(standalone.WritableTier(lease)->data == main.data +
                 (spec.tier_offset - spec.main_offset) * layout.BucketBytes() &&
                 standalone.bytes().At(ByteRole::kRetainedTierHoles) == 0,
             "standalone arena lost its embedded tier");
    }
  }
}

void TestSlotLifecycle() {
  const LevelArenaGeometry g(BaseParams(4, 3, 2));
  LevelArenaSet arenas(g, TestLayout());
  LevelArena& receiver = arenas.At(2);
  const unsigned slot = receiver.plan().inbox[0];
  const size_t buckets = receiver.spec(slot).main_buckets;

  Expect(receiver.State(slot) == SlotState::kFree, "slots start free");

  // A recipient may not read, and a producer may not write, before a lease.
  Expect(Throws([&] { receiver.PublishedMain(slot, buckets); }),
         "an unpublished slot is not readable");
  SlotLease forged;
  forged.arena = &receiver;
  forged.slot = slot;
  forged.generation = 1;
  Expect(Throws([&] { receiver.WritableMain(forged, buckets); }),
         "writing without a live lease is refused");

  // Issue a credit, lease it, write, publish, accept.
  const SlotCredit credit = receiver.MakeCredit(slot);
  Expect(credit.generation == 0 && credit.main_buckets == buckets,
         "a credit names the slot's full extent");
  Expect(credit.tier_buckets == receiver.spec(slot).tier_buckets,
         "a credit names the slot's tier too");
  SlotLease lease;
  Expect(receiver.TryLease(credit, &lease), "a fresh credit leases");
  Expect(receiver.State(slot) == SlotState::kWriting, "leased slots are writing");
  Expect(lease.generation == 1, "an occupancy advances the generation");
  // A second credit for the same slot is stale the moment the first is used.
  Expect(!receiver.TryLease(credit, &lease), "a credit cannot be consumed twice");
  Expect(Throws([&] { receiver.MakeCredit(slot); }),
         "no credit for a slot that is not free");
  // The recipient does not read a leased slot.
  Expect(Throws([&] { receiver.PublishedMain(slot, buckets); }),
         "a leased slot is not readable by its recipient");

  TableView view = receiver.WritableMain(lease, buckets);
  Expect(view.num_buckets == buckets && view.data != nullptr,
         "a lease yields a writable view");
  view.masks[0] = 0x1234;
  // The tier is a STASH, not a table: the rebuild drains into it through
  // ctx.tier_out, and its occupancy is the stash's inline array.
  ResidualStash* tier = receiver.WritableTier(lease);
  Expect(tier->num_buckets == receiver.spec(slot).tier_buckets &&
             tier->entry_bytes == TestLayout().EntryBytes(),
         "a lease yields the slot's own tier stash");
  tier->masks[0] = 0x55;
  tier->Bucket(0)[0] = 0xAB;
  SlotLease wrong_generation = lease;
  wrong_generation.generation = lease.generation + 1;
  Expect(Throws([&] { receiver.WritableTier(wrong_generation); }),
         "a tier needs a live lease too");
  Expect(Throws([&] { receiver.WritableMain(lease, buckets + 1); }),
         "a table may not exceed its slot");

  Expect(receiver.Publish(lease), "the producer publishes");
  Expect(receiver.State(slot) == SlotState::kReady, "published slots are ready");
  Expect(!receiver.Publish(lease), "publishing twice is rejected");
  Expect(receiver.PublishedMain(slot, buckets).masks[0] == 0x1234,
         "the recipient reads what the producer wrote");
  Expect(receiver.PublishedTier(slot)->masks[0] == 0x55 &&
             receiver.PublishedTier(slot)->Bucket(0)[0] == 0xAB,
         "the recipient reads the tier the producer drained into");
  // And the probe plan's view of that tier is the SAME occupancy, not the
  // arena's unused mask words over the tier region.
  Expect(receiver.PublishedTierTable(slot).masks ==
             &receiver.PublishedTier(slot)->masks[0],
         "the plan's tier view and the tier stash disagree about occupancy");
  Expect(!receiver.TryAccept(slot, lease.generation + 1), "a stale Ready is rejected");
  Expect(receiver.TryAccept(slot, lease.generation), "the recipient accepts");
  Expect(receiver.State(slot) == SlotState::kInUse, "an accepted slot is in use");
  // Adoption is exactly this state, held: nothing further happens until the
  // table is replaced.
  Expect(receiver.PublishedMain(slot, buckets).masks[0] == 0x1234,
         "an adopted table keeps its bytes");

  // Reuse before retirement is refused, and retirement alone is not enough:
  // the reader epoch has to pass too.
  Expect(Throws([&] { receiver.MakeCredit(slot); }),
         "an in-use slot yields no credit");
  Expect(receiver.Retire(slot, lease.generation, /*epoch=*/7),
         "the recipient retires a replaced table");
  Expect(receiver.State(slot) == SlotState::kRetired, "retired is not free");
  Expect(Throws([&] { receiver.MakeCredit(slot); }),
         "a retired slot yields no credit until its readers are gone");
  std::vector<unsigned> freed;
  Expect(receiver.Reclaim(/*safe_epoch=*/6, &freed) == 0 && freed.empty(),
         "a pinned slot is not reclaimed");
  Expect(receiver.PublishedMain(slot, buckets).masks[0] == 0x1234,
         "a pinned retired slot keeps its bytes");
  Expect(receiver.PublishedTierTable(slot).data == tier->data &&
             receiver.PublishedTierTable(slot).masks == tier->masks &&
             tier->masks[0] == 0x55 && tier->Bucket(0)[0] == 0xAB,
         "retirement changed a pinned reader's pooled tier");
  uint8_t* const original_tier_data = tier->data;
  Expect(receiver.Reclaim(/*safe_epoch=*/7, &freed) == 1 && freed.size() == 1 &&
             freed[0] == slot,
         "the retirement epoch releases the slot");
  Expect(receiver.State(slot) == SlotState::kFree, "reclaimed slots are free");

  // The next occupancy rejects every message of the previous one.
  const SlotCredit next = receiver.MakeCredit(slot);
  Expect(next.generation == 1, "the generation survives reclamation");
  Expect(!receiver.TryLease(credit, &lease), "the old credit is stale");
  SlotLease second;
  Expect(receiver.TryLease(next, &second) && second.generation == 2,
         "the next occupancy leases");
  Expect(receiver.WritableTier(second)->data == original_tier_data &&
             receiver.WritableTier(second)->Count() == 0,
         "slot reuse moved its permanent slice or kept old occupancy");
  Expect(!receiver.TryAccept(slot, 1), "a Ready from the previous occupancy is stale");
  Expect(receiver.AbandonLease(second), "an unpublished lease can be returned");
  Expect(receiver.State(slot) == SlotState::kFree, "abandoning frees the slot");
  Expect(receiver.rejected() == 5, "every rejection was counted");

  // The level's own bank runs the same machine without a message in between.
  LevelArena& level1 = arenas.At(1);
  const unsigned bank = level1.plan().odd_bank;
  SlotLease own;
  Expect(level1.TryLeaseOwn(bank, &own), "an owner leases its own bank");
  // A partial uses only its actual extent; the rest of the bank is not a table.
  const size_t partial = g.PlanCarry(1, 1).output_buckets;
  Expect(partial < level1.spec(bank).main_buckets, "P_1 is smaller than its bank");
  Expect(level1.WritableMain(own, partial).num_buckets == partial,
         "a partial view is narrowed to its extent");
  Expect(level1.Publish(own) && level1.TryAccept(bank, own.generation),
         "an owner publishes and accepts its own bank");
  Expect(level1.Retire(bank, own.generation, 1) && level1.Reclaim(1) == 1,
         "and retires it through the same epoch rule");
  Expect(level1.rejected() == 0, "the owner's own path rejects nothing");

  // Credits are arena-scoped: one level's credit cannot lease another's slot.
  Expect(Throws([&] {
           SlotLease wrong;
           level1.TryLease(next, &wrong);
         }),
         "a credit belongs to one arena");
  printf("  slots: lease/publish/accept/retire/reclaim, staleness, narrowing\n");
}


// -------------------------------------------------------------------------
// Even digits in the inbox above
// -------------------------------------------------------------------------
//
// A level's even partials
// are built in the level above's inbox slot under the forwarding lease, and a
// level owns ONE bank, for its odd partials.  What this pins is the
// geometry's half of that: storage matches the (3B-1) closed form, every even
// digit below the fanout is planned into an inbox of the level above that
// holds it, odd digits and the full table are in the level's own arena, and
// consecutive digits never share a slot.

void TestEvenDigitsInInbox() {
  for (unsigned B : {2u, 4u, 8u}) {
    for (unsigned L = 2; L <= 6; ++L) {
      for (unsigned D : TopDigitsUpTo(B)) {
        const LevelArenaGeometry g(BaseParams(B, L, D));

        // ---- storage: one bank per level, and no other ---------------------
        uint64_t odd_banks = 0;
        for (unsigned l = 1; l <= L; ++l) {
          const LevelPlan& plan = g.storage().At(l);
          size_t banks = 0;
          for (const SlotSpec& spec : plan.slots) {
            if (spec.kind == SlotKind::kOddBank) ++banks;
          }
          Expect(banks == (plan.odd_bank == LevelPlan::kNoSlot ? 0u : 1u),
                 "a level enumerated a bank its plan does not name");
          Expect(banks <= 1, "a level owns more than one partial bank");
          if (plan.odd_bank != LevelPlan::kNoSlot) {
            odd_banks += plan.At(plan.odd_bank).main_buckets;
          }
        }
        Expect(g.storage().partial_bank_buckets == odd_banks,
               "the partial-bank tally counts something other than odd banks");
        Expect(g.storage().tier_buckets == g.TierBuckets() * CountSlots(g),
               "one tier per physical slot");

        // The uniform closed form (src/oram/levelarena/DESIGN.md, "Geometry and
        // storage bound"): main / T =
        // 2 + (3B-1)/((B-1)D) * (1 - B^-(L-1)), cleared of denominators.
        // The common binary layout obeys this identity too.
        {
          const uint64_t pow = CheckedPow(B, L - 1, "closed form");
          const uint64_t lhs = CheckedMul(
              g.MainBuckets(),
              CheckedMul(CheckedMul(B - 1, D, "x"), pow, "x"), "closed form");
          const uint64_t rhs = CheckedMul(
              g.TopBuckets(),
              CheckedAdd(CheckedMul(2 * (B - 1) * D, pow, "x"),
                         CheckedMul(3 * uint64_t{B} - 1, pow - 1, "x"), "x"),
              "closed form");
          Expect(lhs == rhs, "main/T does not match the (3B-1) closed form");
        }

        // ---- carry plans: two cycles at every level -------------------------
        for (unsigned l = 1; l < L; ++l) {
          for (uint64_t v = 1; v <= 2 * uint64_t{B}; ++v) {
            const CarryPlan c = g.PlanCarry(l, v);
            if (c.outcome != CarryOutcome::kPartial) {
              Expect(UsesForwardingLease(c) ==
                         (c.outcome == CarryOutcome::kForward),
                     "only a forward and an even partial use the lease");
              Expect(!PartialInInbox(c), "a non-partial is a partial in an inbox");
            } else if (c.digit % 2 == 0) {
              Expect(PartialInInbox(c) && UsesForwardingLease(c),
                     "an even partial is not planned into the inbox above");
              Expect(c.destination_level == l + 1 &&
                         c.destination_kind == SlotKind::kInbox,
                     "an even partial's arena is not the level above's");
              const LevelPlan& up = g.storage().At(l + 1);
              for (unsigned i = 0; i < 2; ++i) {
                Expect(up.inbox[i] != LevelPlan::kNoSlot &&
                           up.At(up.inbox[i]).main_buckets > c.output_buckets,
                       "an even partial does not fit strictly inside the "
                       "inbox above");
              }
            } else {
              Expect(!PartialInInbox(c) && !UsesForwardingLease(c),
                     "an odd partial uses the forwarding lease");
              Expect(c.destination_level == l &&
                         c.destination_kind == SlotKind::kOddBank,
                     "an odd partial left its bank");
            }
            // P_(j-1) is P_j's source, so consecutive digits never share a
            // slot -- and the two even partials that DO share the leased slot
            // are two apart, with a publication between them that retires
            // the first.
            if (v >= 2) {
              const CarryPlan prev = g.PlanCarry(l, v - 1);
              Expect(!(prev.destination_level == c.destination_level &&
                       prev.destination_kind == c.destination_kind),
                     "consecutive digits share a slot");
            }
          }
        }
      }
    }
  }
  // A mixed ladder: a two-way bottom has no even digit, and every eight-way
  // level above it sends its even partials up.
  {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.level_fanouts = {2, 8, 8};
    const LevelArenaGeometry g(p);
    Expect(g.storage().At(1).odd_bank != LevelPlan::kNoSlot,
           "a two-way level 1 keeps its odd bank");
    for (unsigned l = 2; l <= 3; ++l) {
      for (unsigned j = 2; j <= 6; j += 2) {
        Expect(PartialInInbox(g.PlanCarry(l, j)),
               "an even digit of a mixed ladder is not in the inbox above");
      }
    }
    Expect(g.PlanCarry(1, 2).outcome == CarryOutcome::kForward,
           "a two-way level's digit 2 forwards");
  }
  printf("  even digits in inbox: one bank per level, the (3B-1) closed form, "
         "every even partial fits the inbox above, no consecutive slot "
         "shared\n");
}

// -------------------------------------------------------------------------
// The bank-first run
// -------------------------------------------------------------------------
//
// The bank-first run (`Params::bank_first`) builds a cycle's first even
// partials in the level's idle odd bank, taking the forwarding lease on the
// inbox above only at a later digit (src/oram/levelarena/DESIGN.md, "Carries
// and preparation").  What the run's placement has to be, stated
// independently rather than read back from the geometry: the run's end is a
// parity rule over b/2 and the offsets are hand-derived layouts.  Then, for every shape, the PAIR
// RULE checked here with this file's own arithmetic -- two consecutive bank
// tables never share an occupancy or a bucket -- and that storage grows by
// one tier per level with a run and by no main bucket.
void TestBankFirstRun() {
  const auto Check = [](bool ok, const std::string& what) {
    Expect(ok, what.c_str());
  };
  struct Expected {
    unsigned B;
    BankFirst mode;
    unsigned end;    // BankRunEnd
    unsigned lease;  // ForwardingLeaseDigit
  };
  const Expected table[] = {
      {2, BankFirst::kOff, 1, 2}, {2, BankFirst::kNoClone, 1, 2},
      {4, BankFirst::kOff, 1, 2}, {4, BankFirst::kNoClone, 1, 2},
      {8, BankFirst::kOff, 1, 2}, {8, BankFirst::kNoClone, 3, 4},
  };
  for (const Expected& e : table) {
    for (unsigned L = 2; L <= 6; ++L) {
      LevelArenaGeometry::Params p = BaseParams(e.B, L, std::min(e.B, 4u));
      p.bank_first = e.mode;
      const LevelArenaGeometry g(p);
      const LevelArenaGeometry off(BaseParams(e.B, L, std::min(e.B, 4u)));
      const std::string name = std::string("B=") + std::to_string(e.B) +
                               " L=" + std::to_string(L) + " " +
                               BankFirstName(e.mode);
      size_t runs = 0;
      for (unsigned l = 1; l < L; ++l) {
        Check(g.BankRunEnd(l) == e.end && g.ForwardingLeaseDigit(l) == e.lease,
               name + ": the run's end or lease digit");
        const LevelPlan& plan = g.storage().At(l);
        Check((plan.run_bank != LevelPlan::kNoSlot) == (e.end >= 2),
               name + ": a run bank exactly where there is a run");
        if (plan.run_bank != LevelPlan::kNoSlot) {
          ++runs;
          const SlotSpec& odd = plan.At(plan.odd_bank);
          const SlotSpec& run = plan.At(plan.run_bank);
          Check(run.kind == SlotKind::kRunBank && run.shares_main &&
                     !odd.shares_main &&
                     run.main_offset == odd.main_offset &&
                     run.main_buckets == odd.main_buckets &&
                     run.tier_offset != odd.tier_offset,
                 name + ": the run bank is the odd bank's main with a tier "
                        "of its own");
        }
        // The pair rule and the lease digit, recomputed.
        const size_t u = g.CarryBuckets(l);
        unsigned first_lease = 0;
        for (uint64_t v = 1; v <= 2 * uint64_t{e.B}; ++v) {
          const CarryPlan c = g.PlanCarry(l, v);
          if (v <= e.B && first_lease == 0 && UsesForwardingLease(c)) {
            first_lease = c.digit;
          }
          const bool in_bank = c.destination_kind == SlotKind::kOddBank ||
                               c.destination_kind == SlotKind::kRunBank;
          if (c.outcome != CarryOutcome::kPartial || !in_bank) continue;
          Check(c.destination_kind == (c.digit % 2 == 1 ? SlotKind::kOddBank
                                                         : SlotKind::kRunBank),
                 name + ": parity alone picks the bank occupancy");
          Check(c.destination_offset + c.output_buckets <=
                     uint64_t{e.B - 1} * u,
                 name + ": a bank table runs off its bank");
          if (c.digit == 1) continue;
          const CarryPlan prev = g.PlanCarry(l, v - 1);
          const bool prev_in_bank =
              prev.outcome == CarryOutcome::kPartial &&
              (prev.destination_kind == SlotKind::kOddBank ||
               prev.destination_kind == SlotKind::kRunBank);
          if (prev_in_bank) {
            Check(prev.destination_kind != c.destination_kind &&
                       (prev.destination_offset + prev.output_buckets <=
                            c.destination_offset ||
                        c.destination_offset + c.output_buckets <=
                            prev.destination_offset),
                   name + ": two consecutive bank tables collide");
          }
        }
        Check(first_lease == e.lease,
               name + ": the lease is first needed at another digit");
      }
      Check(g.MainBuckets() == off.MainBuckets(),
             name + ": the run costs main storage");
      Check(g.storage().tier_buckets ==
                 off.storage().tier_buckets + runs * g.TierBuckets(),
             name + ": the run costs other than one tier per level");
      Check(g.ArenaBuckets() == off.ArenaBuckets() + runs * g.TierBuckets(),
             name + ": the arena grows by other than the run tiers");
      for (unsigned l = 1; l <= L; ++l) {
        size_t buckets = 0;
        for (const SlotSpec& spec : g.storage().At(l).slots) {
          buckets += (spec.shares_main ? 0 : spec.main_buckets) +
                     spec.tier_buckets;
        }
        Check(buckets == g.storage().At(l).arena_buckets,
               name + ": a level's arena is not its slots, counted once");
      }
    }
  }

  // THE REVIEW'S LAYOUTS, offset for offset, in units of U.
  struct Place {
    unsigned digit;
    SlotKind kind;
    size_t offset;  // units of U; ignored outside the bank
  };
  const auto expect_layout = [&](unsigned B, BankFirst mode, unsigned level,
                                 const std::vector<Place>& places) {
    LevelArenaGeometry::Params p = BaseParams(B, 3, 2);
    p.bank_first = mode;
    const LevelArenaGeometry g(p);
    const std::string name = std::string("B=") + std::to_string(B) + " " +
                             BankFirstName(mode) + " level " +
                             std::to_string(level);
    const size_t u = g.CarryBuckets(level);
    for (const Place& want : places) {
      const CarryPlan c = g.PlanCarry(level, want.digit);
      const bool bank = want.kind == SlotKind::kOddBank ||
                        want.kind == SlotKind::kRunBank;
      Check(c.destination_kind == want.kind &&
                 (!bank || c.destination_offset == want.offset * u),
             name + " digit " + std::to_string(want.digit) +
                 ": not the expected placement");
    }
  };
  const SlotKind kOdd = SlotKind::kOddBank, kRun = SlotKind::kRunBank,
                 kIn = SlotKind::kInbox;
  // B = 8: P_2 at [0,2) and P_3 at [4,7), P_4 in the lease.
  expect_layout(8, BankFirst::kNoClone, 1,
                {{1, kOdd, 6}, {2, kRun, 0}, {3, kOdd, 4}, {4, kIn, 0},
                 {5, kOdd, 0}, {6, kIn, 0}, {7, kOdd, 0}, {8, kIn, 0}});

  // A MIXED LADDER runs each level by its own fanout: the two- and four-way
  // levels have no run, and the eight-way one does.
  {
    LevelArenaGeometry::Params p = BaseParams(8, 4, 4);
    p.level_fanouts = {4, 2, 8};
    p.bank_first = BankFirst::kNoClone;
    const LevelArenaGeometry g(p);
    Check(g.BankRunEnd(1) == 1 && g.BankRunEnd(2) == 1 &&
               g.BankRunEnd(3) == 3 &&
               g.storage().At(1).run_bank == LevelPlan::kNoSlot &&
               g.storage().At(2).run_bank == LevelPlan::kNoSlot,
           "a mixed ladder's runs follow each level's own fanout");
    Check(Throws([&] { (void)g.ForwardingLeaseDigit(4); }),
           "the top has no lease digit");
  }
  printf("  bank-first run: parity-chosen ends, the expected layouts, pair "
         "rule, one tier per run\n");
}

}  // namespace
}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram

int main() {
  using namespace microram::byteslice::levelarena;
  printf("level arena, geometry and slots\n");
  TestTierProfile();
  TestGeometryBasics();
  TestVariableFanout();
  TestBoundaryArithmetic();
  TestStorageSums();
  TestCarryDestinations();
  TestEvenDigitsInInbox();
  TestBankFirstRun();
  TestFamilies();
  TestInitializationSeed();
  TestCompactTierPool();
  TestSlotLifecycle();
  printf("level arena geometry and slots: OK\n");
  return 0;
}
