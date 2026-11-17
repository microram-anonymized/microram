// The level-arena merge planners (cpu_byteslice_level_arena_merge.hpp): the
// prepare / install / finish factoring of a non-top level merge, the dense
// carry builder that level 1 uses, and the nonce-sharing rule between a carry
// and the merge that consumes it.  (src/oram/levelarena/DESIGN.md, "Carries
// and preparation", defines carry, digit, partial and preparation.)
//
// At digit j = r * 2^e (r odd) a merge first PREPARES the older sources
// (copy, re-tag and route every pure block, then block 0's older spans,
// recording every shed in the job's private stashes), then INSTALLS the fresh
// carry into the first U_l buckets with a fused copy-and-re-tag, then
// FINISHES with block 0's e deduplicating cross levels, the radix-r pass if
// r > 1, and the residual passes.  Preparation touches no carry data, which is
// what lets an owner run it before the carry exists.
//
// Three claims:
//
//  1. the three phases in sequence emit exactly the absorb's work
//     (PlanAbsorbStep, the single-table merge the shared rebuild code runs).
//     The absorb is the thing this engine reuses, so "same subtasks, same
//     order, minus the one deliberate change" is the strongest statement
//     available without re-deriving the kernels' correctness.  The one
//     deliberate change is the install: kCopyFresher, at the FRONT, becomes
//     kCopyAndRetagFresher, AFTER the preparation.  At digit 1 there is no
//     preparation and no route after the install, which stays the absorb's
//     plain copy, so the two streams are identical.
//
//  2. a sparse merge keeps the newest copy when a key is in both sources, and
//     does so with the carry's stored tag bytes POISONED beforehand: the
//     install is what recomputes them, and if it ever stopped doing so this
//     fixture would place entries by garbage.  (A carry's bucket POSITIONS are
//     valid under its family nonce, but its stored tag bytes may be stale, so
//     they are treated as scratch.)
//
//  3. the merge and the carry share a nonce, the invariant that is easiest to
//     get wrong here.  The install performs no routing: both the carry's
//     bucket index and the merge's map use the same low log2(U_l) bits of the
//     same raw hash, so re-tagging is only correct under the carry's own
//     family nonce.  The test runs the identical fixture with a DIFFERENT
//     merge nonce and requires the result to be wrong -- because a design
//     where that is allowed to pass is a design whose carries are silently
//     misplaced.

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <stdexcept>
#include <set>
#include <utility>
#include <unordered_map>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_merge.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_run.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

using microram::byteslice::test_support::OwnedLevelStashes;

int failures = 0;

void Expect(bool value, const char* message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message);
    ++failures;
  }
}

// Ran `fn` and it refused.
template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

bs::Layout TestLayout() {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 4;
  layout.tag_bytes = 3;
  return layout;
}

bs::Table Zeroed(size_t buckets, const bs::Layout& layout) {
  bs::Table t = bs::Table::Create(buckets, layout);
  std::memset(t.data.get(), 0, buckets * layout.BucketBytes());
  return t;
}

bool SameSubtask(const bs::Subtask& a, const bs::Subtask& b) {
  return a.kind == b.kind && a.begin == b.begin && a.end == b.end &&
         a.levels == b.levels && a.bit == b.bit && a.pass == b.pass &&
         a.log2_stride == b.log2_stride && a.blank_first == b.blank_first;
}

// The entry at (bucket, slot), as (key, value).  Value lives in the first
// value byte; that is all these fixtures need to tell copies apart.
uint64_t SlotKey(const bs::Layout& layout, const uint8_t* bucket, size_t slot) {
  return bs::ReadSlotKey(bucket, slot, layout.key_bytes).w0;
}
uint8_t SlotValue(const bs::Layout& layout, const uint8_t* bucket, size_t slot) {
  return bucket[layout.key_bytes * bs::kBucketCapacity + slot];
}
// The low `bits` bits of a slot's STORED tag.  Tag bit b lives in bit b%8 of
// byte line TagLine(b); no helper exists for this because nothing but a test
// ever reads a stored tag back.
uint64_t SlotTagBits(const bs::Layout& layout, const uint8_t* bucket,
                     size_t slot, unsigned bits) {
  uint64_t tag = 0;
  for (unsigned b = 0; b < bits; ++b) {
    const uint8_t byte = bucket[layout.TagLine(b) * bs::kBucketCapacity + slot];
    tag |= uint64_t{static_cast<uint8_t>((byte >> (b & 7)) & 1)} << b;
  }
  return tag;
}

void Plant(const bs::Layout& layout, uint8_t* bucket, size_t slot, uint64_t key,
           uint8_t value) {
  bs::WriteSlotKey(bucket, slot, layout.key_bytes, key);
  bucket[layout.key_bytes * bs::kBucketCapacity + slot] = value;
}

// Every live entry of a table, keyed by key; fails the caller's check if a key
// occurs twice, which is the uniqueness half of every claim below.
std::map<uint64_t, uint8_t> LiveEntries(const bs::TableView& t, bool* unique) {
  std::map<uint64_t, uint8_t> live;
  *unique = true;
  for (size_t b = 0; b < t.num_buckets; ++b) {
    uint64_t mask = t.masks[b];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      const uint64_t key = SlotKey(t.layout, t.Bucket(b), slot);
      if (!live.emplace(key, SlotValue(t.layout, t.Bucket(b), slot)).second) {
        *unique = false;
      }
    }
  }
  return live;
}

// The first separated continuation cannot shed, but other preparation
// spans can already have filled the same physical stash. It must not touch
// that stash, and later continuation levels must still append their losses.
template <bool CheckOverflow>
void TestSeparatedContinuationStashes() {
  const bs::Layout layout = TestLayout();
  for (unsigned pattern = 0; pattern < 3; ++pattern) {
    bs::Table out = Zeroed(4, layout);
    // The blank buckets are stale, not cleared: the route must not read them.
    std::memset(out.data.get(), 0x3c, 2 * layout.BucketBytes());
    out.masks[0] = 0x5555555555555555ULL;
    out.masks[1] = UINT64_MAX;
    OwnedLevelStashes stashes(3, 1, layout);
    std::memset(stashes.data.get(), 0xa5, stashes.bytes);
    stashes.slots[1].masks[0] = UINT64_MAX;
    const std::vector<uint8_t> before(stashes.data.get(),
                                      stashes.data.get() + stashes.bytes);
    std::map<uint64_t, uint8_t> expected;
    for (size_t b = 2; b < 4; ++b) {
      out.masks[b] = UINT64_MAX;
      for (size_t slot = 0; slot < 64; ++slot) {
        const uint64_t key = b * 64 + slot;
        Plant(layout, out.Bucket(b), slot, key, uint8_t(slot));
        const unsigned direction = pattern < 2 ? pattern : slot % 2;
        out.Bucket(b)[layout.TagLine(1) * 64 + slot] = direction << 1;
        expected[key] = uint8_t(slot);
      }
    }
    bs::RebuildStepContext ctx;
    ctx.out = bs::View(out);
    ctx.upper_offset = 2;
    ctx.level_stashes = stashes.ptr();
    bs::Subtask task;
    task.kind = bs::Subtask::kRouteLevelRange;
    task.bit = 1;
    task.blank_first = true;
    // Resume one pair at a time, including a piece not starting at zero.
    for (size_t i = 0; i < 2; ++i) {
      task.begin = i;
      task.end = i + 1;
      // The last case also proves the first route does not read a stash.
      if (pattern == 2) ctx.level_stashes = nullptr;
      Expect(bs::RunSubtask<CheckOverflow>(ctx, task),
             "blank-input continuation overflowed");
    }
    bool unique = false;
    Expect(LiveEntries(bs::View(out), &unique) == expected && unique,
           "blank-input continuation changed records");
    for (size_t b = 0; b < 4; ++b) {
      uint64_t mask = out.masks[b];
      while (mask) {
        const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
        mask &= mask - 1;
        const uint64_t key = SlotKey(layout, out.Bucket(b), slot);
        const unsigned direction = pattern < 2 ? pattern : key % 2;
        Expect(b == (key / 64 - 2) + 2 * direction,
               "blank-input continuation misplaced a record");
      }
    }
    Expect(stashes.slots[1].masks[0] == UINT64_MAX &&
               std::memcmp(before.data(), stashes.data.get(), stashes.bytes) == 0,
           "blank-input continuation modified an earlier writer's stash");
  }
  bs::Table out = Zeroed(8, layout);
  OwnedLevelStashes stashes(3, 1, layout);
  for (size_t b : {size_t{0}, size_t{4}}) {
    out.masks[b] = UINT64_MAX;
    for (size_t slot = 0; slot < 64; ++slot)
      Plant(layout, out.Bucket(b), slot, b * 64 + slot, uint8_t(slot));
  }
  bs::RebuildStepContext ctx;
  ctx.out = bs::View(out);
  ctx.upper_offset = 2;
  ctx.level_stashes = stashes.ptr();
  bs::Subtask task;
  task.kind = bs::Subtask::kRouteLevelRange;
  task.bit = 2;
  task.end = 1;
  Expect(bs::RunSubtask<CheckOverflow>(ctx, task), "later continuation failed");
  Expect(stashes.slots[2].Count() == 64,
         "later continuation silently dropped its overflow");
}

// Random bytes, masks and stored tags: every stale byte the blank-first
// kernels must not depend on, and every live one they must move.
void FillRandom(std::mt19937_64& rng, uint8_t* bytes, size_t n) {
  for (size_t i = 0; i < n; ++i) bytes[i] = static_cast<uint8_t>(rng());
}

// Occupancy of a given expected density: 0 (empty), 1 (about half), 2 (full).
uint64_t RandomMask(std::mt19937_64& rng, unsigned density) {
  if (density == 0) return 0;
  if (density == 2) return UINT64_MAX;
  return rng();
}

// THE BLANK-FIRST PAIR IS THE GENERAL PAIR OVER A CLEARED FIRST MASK, BYTE FOR
// BYTE.  The oracle is what the preparation ran when it still cleared the
// blank region's masks: the general pair with the first mask zeroed.  The
// blank-first kernel gets the first bucket's stale mask and bytes instead,
// and both buckets' bytes and masks must come out identical at every routed
// bit.
template <bool CheckOverflow>
void TestBlankFirstPairMatchesClearedPair() {
  const bs::Layout layout = TestLayout();
  const size_t bucket_bytes = layout.BucketBytes();
  std::mt19937_64 rng(0x5eed0f1a2bULL);
  bs::Table blank = bs::Table::Create(2, layout);
  bs::Table oracle = bs::Table::Create(2, layout);
  const unsigned tag_bits = static_cast<unsigned>(8 * layout.tag_bytes);
  size_t mismatches = 0;
  for (unsigned trial = 0; trial < 600; ++trial) {
    const unsigned bit = trial % tag_bits;
    FillRandom(rng, blank.data.get(), 2 * bucket_bytes);
    blank.masks[0] = rng();
    blank.masks[1] = RandomMask(rng, trial / tag_bits % 3);
    std::memcpy(oracle.data.get(), blank.data.get(), 2 * bucket_bytes);
    oracle.masks[0] = 0;
    oracle.masks[1] = blank.masks[1];
    const size_t lines = layout.RoutedLines(bit);
    const size_t tag_line = layout.TagLine(bit);
    const bool got = bs::MergeSplitPair<CheckOverflow, /*BlankFirst=*/true>(
        blank.Bucket(0), blank.Bucket(1), &blank.masks[0], &blank.masks[1],
        lines, tag_line, bit);
    const bool want = bs::MergeSplitPair<CheckOverflow>(
        oracle.Bucket(0), oracle.Bucket(1), &oracle.masks[0],
        &oracle.masks[1], lines, tag_line, bit);
    if (got != want || !got || blank.masks[0] != oracle.masks[0] ||
        blank.masks[1] != oracle.masks[1] ||
        std::memcmp(blank.data.get(), oracle.data.get(), 2 * bucket_bytes) !=
            0) {
      ++mismatches;
    }
  }
  Expect(mismatches == 0,
         "the blank-first pair differs from the pair over a cleared mask");
}

// THE BLANK-BLOCK-0 RADIX PASS IS THE GENERAL PASS OVER CLEARED BLOCK-0
// MASKS, BYTE FOR BYTE, output and stash alike -- at every radix a separated
// odd digit reaches, at fixed and dynamic stash depths, with stashes that
// start partly full and tuples that shed (and, checked, overflow).
template <bool CheckOverflow>
void TestBlankFirstRadixMatchesClearedRadix() {
  const bs::Layout layout = TestLayout();
  const size_t bucket_bytes = layout.BucketBytes();
  const size_t digit_line = layout.DigitLine();
  constexpr unsigned kBlockBits = 2;
  constexpr size_t kBlock = size_t{1} << kBlockBits;
  std::mt19937_64 rng(0x7ad1c5ULL);
  size_t mismatches = 0, cases = 0, refused = 0;
  for (unsigned r : {3u, 5u, 7u}) {
    for (size_t depth : {size_t{1}, size_t{2}, size_t{3}, size_t{6},
                         size_t{7}, size_t{8}}) {
      for (unsigned trial = 0; trial < 12; ++trial) {
        const size_t buckets = r * kBlock;
        bs::Table blank = bs::Table::Create(buckets, layout);
        bs::Table oracle = bs::Table::Create(buckets, layout);
        FillRandom(rng, blank.data.get(), buckets * bucket_bytes);
        for (size_t b = 0; b < buckets; ++b) {
          blank.masks[b] = b < kBlock ? rng() : RandomMask(rng, trial % 3);
          // Live slots carry a digit below r, skewed toward direction 1 in
          // odd trials so that tuples shed; the rest keep random bytes.
          for (size_t slot = 0; slot < 64; ++slot) {
            if (b >= kBlock && ((blank.masks[b] >> slot) & 1)) {
              const bool skew = trial % 2 == 1 && rng() % 4 != 0;
              blank.Bucket(b)[digit_line * 64 + slot] =
                  static_cast<uint8_t>(skew ? 1 : rng() % r);
            }
          }
        }
        std::memcpy(oracle.data.get(), blank.data.get(),
                    buckets * bucket_bytes);
        std::copy_n(blank.masks.get(), buckets, oracle.masks.get());
        std::fill_n(oracle.masks.get(), kBlock, 0);
        OwnedLevelStashes blank_stash(1, depth, layout);
        FillRandom(rng, blank_stash.data.get(), blank_stash.bytes);
        for (size_t b = 0; b < depth; ++b) {
          blank_stash.slots[0].masks[b] = rng() & rng();
        }
        OwnedLevelStashes oracle_stash(1, depth, layout);
        std::memcpy(oracle_stash.data.get(), blank_stash.data.get(),
                    blank_stash.bytes);
        std::copy_n(blank_stash.slots[0].masks, bs::kMaxResidualStashBuckets,
                    oracle_stash.slots[0].masks);
        // One tuple per piece, stopping at the first refusal as the runner
        // does.  A refused tuple leaves its buckets as they were, which for
        // the blank kernel means block 0's stale mask: the tuples from the
        // refused one on keep it, and are compared against it.
        std::vector<uint64_t> stale(blank.masks.get(),
                                    blank.masks.get() + kBlock);
        bool got = true, want = true;
        size_t stopped = kBlock;
        for (size_t at = 0; at < kBlock && got && want; ++at) {
          got = bs::RadixPassStashRange<CheckOverflow, /*BlankFirst=*/true>(
              bs::View(blank), kBlockBits, r, blank_stash.slots[0], at,
              at + 1);
          want = bs::RadixPassStashRange<CheckOverflow>(
              bs::View(oracle), kBlockBits, r, oracle_stash.slots[0], at,
              at + 1);
          if (!want) stopped = at;
        }
        ++cases;
        if (!want) ++refused;
        bool masks_match = true;
        for (size_t b = 0; b < buckets; ++b) {
          const uint64_t expect =
              b >= stopped && b < kBlock ? stale[b] : oracle.masks[b];
          masks_match &= blank.masks[b] == expect;
        }
        if (got != want || !blank_stash.SameAs(oracle_stash) || !masks_match ||
            std::memcmp(blank.data.get(), oracle.data.get(),
                        buckets * bucket_bytes) != 0) {
          ++mismatches;
        }
      }
    }
  }
  Expect(mismatches == 0,
         "the blank-block-0 radix pass differs from the pass over cleared "
         "masks");
  // The overflow path must have been exercised, or "checked" proves little.
  Expect(!CheckOverflow || (refused > 0 && refused < cases),
         "the radix equivalence fixture never (or always) overflowed");
}

// ---------------------------------------------------------------------------
// 1. The factoring emits the absorb's work
// ---------------------------------------------------------------------------

// The residual wiring one case runs with.  Switched OFF, a merge's finish is
// its cross levels and its radix pass and nothing else -- which leaves the
// place the two forms could most easily drift entirely untested, because a
// residual pass is the one part of the finish that is neither a fixed shape
// nor emitted unconditionally: it may ride the pass that ends the route, and
// which pass that is depends on the digit.
//
//   kStandalone  two passes at the end, in pass order, the shape every digit
//                supports including digit 1 (which has no route at all).
//   kFused       the absorb's fused form: ONE class-marked pass riding the
//                pass that ends the route -- the radix pass when r > 1, the
//                last cross level when the digit is a power of two -- with a
//                drain-only prefix that outranks the swept slots, so the
//                prologue/epilogue split and the leftover dedup are emitted
//                too.  Digit 1 ends no route and has no such site.
enum class Residuals { kNone, kStandalone, kFused };

// The subtask kinds a residual pass is made of.  Spelled out rather than
// taken as a range of the enum, which would turn inserting a kind into a
// silent change here.
bool IsResidualSubtask(bs::Subtask::Kind kind) {
  switch (kind) {
    case bs::Subtask::kResidualPoolDedup:
    case bs::Subtask::kResidualScatter:
    case bs::Subtask::kResidualScatterRetag:
    case bs::Subtask::kResidualRetag:
    case bs::Subtask::kResidualSweep:
    case bs::Subtask::kResidualLeftoverDedup:
    case bs::Subtask::kResidualDrain:
    case bs::Subtask::kResidualReset:
      return true;
    default:
      return false;
  }
}

// The site a digit's route ENDS at, or kNone when it runs no route.
bs::ResidualFuseSite RouteEndSite(const la::MergeShape& shape) {
  if (shape.has_radix_pass()) return bs::ResidualFuseSite::kRadixPass;
  if (shape.has_cross_levels()) return bs::ResidualFuseSite::kCrossLevel;
  return bs::ResidualFuseSite::kNone;
}

// Storage for one case's passes, attached to a context.
//
// The pool stashes hold capacity and no entries, and the range tables are
// empty, because a plan is a function of PUBLIC sizes alone -- that is what
// makes the schedule data-independent, and it is why a planning fixture needs
// no data.  The shapes here are representative rather than a job's: what
// builds a real pool, with its certified capacities and its freshness ranks,
// is 11.2.  What this establishes is narrower and still worth having -- that
// the two planners emit residual work identically, and that the arena form's
// fuse-site guards ACCEPT the sites it supports rather than only rejecting the
// ones it does not.
class ResidualWiring {
 public:
  ResidualWiring(const bs::Layout& layout, const la::MergeShape& shape,
                 Residuals mode, bs::RebuildStepContext* ctx)
      : sheds_(shape.block_bits + 2, 1, layout), drains_(2, 1, layout) {
    if (mode == Residuals::kNone) return;
    // Where the route sheds, as the runner reads it: bit b into slot b, the
    // radix pass into the slot past the tier's.
    ctx->level_stashes = sheds_.slots.data();
    ctx->radix_stash = &sheds_.slots[shape.block_bits + 1];
    // Every butterfly level's shed, plus a consumed table's second tier --
    // led, in the fused mode, by the shed of the pass it rides, which is the
    // drain-only prefix the fused planners check for.
    bs::ResidualStash* ridden = nullptr;
    if (mode == Residuals::kFused) {
      ridden = shape.has_radix_pass()
                   ? ctx->radix_stash
                   : &ctx->level_stashes[shape.block_bits - 1];
      pool_.push_back(ridden);
    }
    for (unsigned bit = 0; bit < shape.block_bits; ++bit) {
      if (&sheds_.slots[bit] != ridden) pool_.push_back(&sheds_.slots[bit]);
    }
    pool_.push_back(&sheds_.slots[shape.block_bits]);
    // Mixed ranks on purpose: a pool whose slots all rank equal has no pair to
    // dedup and the phase is skipped, which would leave it unplanned in both
    // forms and prove nothing about either.
    rank_.assign(pool_.size(), 1);
    rank_[0] = 0;
    size_t swept = 0;
    for (const bs::ResidualStash* slot : pool_) swept += slot->num_buckets;

    if (mode == Residuals::kFused) {
      // rank_[0] = 0 also makes the drain-only prefix OUTRANK the swept slots,
      // which is exactly the condition PlanResidualFinishPhases puts the
      // leftover dedup between the two halves of the drain for.
      Fill(&ctx->residual[2], *ctx, shape, swept - pool_[0]->num_buckets,
           bs::ResidualDedupRule::kClassMark, RouteEndSite(shape),
           /*drain_only=*/1, &range_a_, &drains_.slots[0]);
      return;
    }
    Fill(&ctx->residual[1], *ctx, shape, swept,
         bs::ResidualDedupRule::kTableWins, bs::ResidualFuseSite::kNone,
         /*drain_only=*/0, &range_a_, &drains_.slots[0]);
    Fill(&ctx->residual[2], *ctx, shape, swept,
         bs::ResidualDedupRule::kResidualWins, bs::ResidualFuseSite::kNone,
         /*drain_only=*/0, &range_b_, &drains_.slots[1]);
  }

  ResidualWiring(const ResidualWiring&) = delete;
  ResidualWiring& operator=(const ResidualWiring&) = delete;

 private:
  void Fill(bs::ResidualPass* rp, const bs::RebuildStepContext& ctx,
            const la::MergeShape& shape, size_t swept,
            bs::ResidualDedupRule rule, bs::ResidualFuseSite fuse,
            size_t drain_only, bs::Table* range, bs::ResidualStash* drain) {
    // A direct plan: a non-DFS pass routes nothing.
    rp->plan = bs::DirectResidualRangePlan(swept, shape.block_bits);
    *range = Zeroed(rp->plan.range_buckets, ctx.out.layout);
    rp->active = true;
    rp->main = ctx.out;
    rp->range = bs::View(*range);
    rp->pool = pool_.data();
    rp->rank = rank_.data();
    rp->pool_slots = pool_.size();
    rp->reset_slots = pool_.size() - 1;  // the borrowed tier stays
    rp->drain_only = drain_only;
    rp->sweep_active = true;
    rp->fuse = fuse;
    rp->drain = drain;
    rp->rule = rule;
    rp->lines = ctx.out.layout.PayloadLines();
    // The FLAT DESTINATION map: the same word on a power-of-two output, the
    // merge's own map packed at its block width on a mixed-radix one.
    if (shape.has_radix_pass()) {
      rp->map.kind = bs::TagMapKind::kRadixDigit;
      rp->map.low_bits = shape.block_bits;
      rp->map.modulus = shape.odd_part;
      rp->map.digit_shift = shape.block_bits;
    }
  }

  OwnedLevelStashes sheds_;
  OwnedLevelStashes drains_;
  std::vector<bs::ResidualStash*> pool_;
  std::vector<uint8_t> rank_;
  bs::Table range_a_, range_b_;
};

void TestPhasesMatchAbsorb() {
  const bs::Layout layout = TestLayout();
  size_t cases = 0;
  const bs::SubtaskBudget budgets[] = {
      bs::SubtaskBudget{~size_t{0}, ~size_t{0}, ~size_t{0}, ~size_t{0},
                        ~size_t{0}, ~size_t{0}},
      bs::SubtaskBudget{1, 1, 1, 1, 1, 1},
      bs::SubtaskBudget{5, 3, 4, 40, 6, 3},
  };
  for (unsigned k : {3u, 4u, 6u}) {
    for (unsigned r : {1u, 3u, 5u, 7u}) {
      for (unsigned e = 0; (r << e) <= 8; ++e) {
        const unsigned digit = r << e;
        const size_t carry = size_t{1} << k;
        const unsigned block_bits = k + e;
        bs::RoutingIndexMap map;
        if (r > 1) {
          map.kind = bs::TagMapKind::kRadixDigit;
          map.low_bits = block_bits;
          map.modulus = r;
          map.digit_shift = bs::RoutingDigitShift(layout);
        }
        bs::Table out = Zeroed(digit * carry, layout);
        bs::Table fresher = Zeroed(carry, layout);
        bs::Table older = Zeroed(std::max<size_t>(1, (digit - 1) * carry),
                                 layout);
        bs::RebuildStepContext base;
        base.out = bs::View(out);
        base.fresher = bs::View(fresher);
        base.older = bs::View(older);
        base.older.num_buckets = (digit - 1) * carry;
        base.upper_offset = carry;
        base.route_levels = block_bits;
        base.map = map;

        const la::MergeShape shape = la::MergeShapeOf(base);
        Expect(shape.digit == digit && shape.odd_part == r &&
                   shape.power == e && shape.block_bits == block_bits &&
                   shape.older_buckets == (digit - 1) * carry,
               "the merge shape disagrees with the digit it was built from");

      for (Residuals mode : {Residuals::kNone, Residuals::kStandalone,
                             Residuals::kFused}) {
        // Digit 1 ends no route and so offers no fusion site.  Its
        // absorb fuses into the COPY of its fresher operand instead, which an
        // arena merge has no kind for -- its install re-tags -- and refuses;
        // TestPhasePreconditionsAreChecked is where that refusal is asserted.
        if (mode == Residuals::kFused &&
            RouteEndSite(shape) == bs::ResidualFuseSite::kNone) {
          continue;
        }
        bs::RebuildStepContext ctx = base;
        const ResidualWiring wiring(layout, shape, mode, &ctx);
        for (const bs::SubtaskBudget& budget : budgets) {
          std::vector<bs::Subtask> absorb, phased;
          bs::PlanAbsorbStep(ctx, budget, &absorb);
          la::PlanSparseLevelMerge(ctx, shape, budget, &phased);

          // The absorb's leading fresher copy, and the phased plan's install.
          //
          // The two are sliced by DIFFERENT budget entries -- a copy and a
          // fused copy-and-re-tag are measured against their own constants --
          // so what has to match is the range they cover, not the cut points.
          std::vector<bs::Subtask> absorb_rest, phased_rest;
          size_t absorb_covered = 0, phased_covered = 0;
          size_t absorb_copies = 0, phased_installs = 0;
          for (const bs::Subtask& t : absorb) {
            if (t.kind == bs::Subtask::kCopyFresher) {
              Expect(absorb_rest.empty(),
                     "the absorb's fresher copy is not at the front");
              Expect(t.begin == absorb_covered, "the fresher copy has a gap");
              absorb_covered = t.end;
              ++absorb_copies;
              continue;
            }
            absorb_rest.push_back(t);
          }
          if (digit == 1) {
            Expect(absorb.size() == phased.size() &&
                       std::equal(absorb.begin(), absorb.end(),
                                  phased.begin(), SameSubtask),
                   "the digit-1 install is not the absorb's plain copy");
          }
          const bs::Subtask::Kind install =
              digit == 1 ? bs::Subtask::kCopyFresher
                         : bs::Subtask::kCopyAndRetagFresher;
          size_t prepared = 0;
          for (const bs::Subtask& t : phased) {
            if (t.kind == install) {
              Expect(phased_rest.size() == prepared,
                     "the install did not follow the preparation");
              Expect(t.begin == phased_covered, "the install has a gap");
              phased_covered = t.end;
              ++phased_installs;
              continue;
            }
            phased_rest.push_back(t);
            if (phased_installs == 0) prepared = phased_rest.size();
          }
          Expect(absorb_copies > 0 && phased_installs > 0,
                 "one of the two plans did not install the carry at all");
          Expect(absorb_covered == carry && phased_covered == carry,
                 "the install does not cover exactly the carry's U buckets");
          Expect(absorb_rest.size() == phased_rest.size(),
                 "the phased plan emits a different amount of work");
          for (size_t i = 0; i < std::min(absorb_rest.size(),
                                          phased_rest.size()); ++i) {
            Expect(SameSubtask(absorb_rest[i], phased_rest[i]),
                   "the phased plan changed the absorb's subtask stream");
          }
          // Phase boundaries: the preparation is exactly the older blocks.
          std::vector<bs::Subtask> prep;
          la::PlanPrepareOlderSources(ctx, shape, budget, &prep);
          Expect(prep.size() == prepared,
                 "preparation is not the prefix of the phased plan");
          for (size_t i = 0; i < std::min(prep.size(), prepared); ++i) {
            Expect(SameSubtask(prep[i], phased_rest[i]),
                   "preparation emitted different work standalone");
          }
          // A residual mode that emitted no residual work would make every
          // comparison above vacuously true, so each one states what it is
          // supposed to have put in the stream.
          size_t residual_tasks = 0;
          bool saw_sweep = false, saw_offers = false;
          for (const bs::Subtask& t : absorb) {
            residual_tasks += IsResidualSubtask(t.kind) ? 1 : 0;
            saw_sweep |= t.kind == bs::Subtask::kResidualSweep;
            saw_offers |= t.kind == bs::Subtask::kCrossLevelOffers ||
                          t.kind == bs::Subtask::kRadixPassOffers;
          }
          Expect((residual_tasks != 0) == (mode != Residuals::kNone),
                 "a residual mode planned the wrong amount of residual work");
          if (mode == Residuals::kStandalone) {
            Expect(saw_sweep && !saw_offers,
                   "the standalone mode did not sweep standalone");
          }
          if (mode == Residuals::kFused) {
            Expect(saw_offers && !saw_sweep,
                   "the fused mode did not ride the pass that ends the route");
          }
          ++cases;
        }
      }
      }
    }
  }
  std::printf("  phases: %zu (digit, budget, residual) cases emit the "
              "absorb's stream\n", cases);
}

// ---------------------------------------------------------------------------
std::map<uint64_t, uint8_t> RunSparseMerge(unsigned k, unsigned r, unsigned e,
                                           uint64_t merge_nonce_hi,
                                           bool poison_tags, bool* unique,
                                           bool* overflowed,
                                           std::map<uint64_t, uint8_t>* model_out) {
  const bs::Layout layout = TestLayout();
  const unsigned digit = r << e;
  const size_t carry_buckets = size_t{1} << k;
  const size_t older_buckets = static_cast<size_t>(digit - 1) * carry_buckets;
  const unsigned block_bits = k + e;
  const uint64_t nonce_lo = 2;
  const uint64_t carry_nonce_hi = 0x1234;
  std::mt19937_64 rng(0xD00D + 64 * k + 8 * r + e);

  bs::RoutingIndexMap map;
  if (r > 1) {
    map.kind = bs::TagMapKind::kRadixDigit;
    map.low_bits = block_bits;
    map.modulus = r;
    map.digit_shift = bs::RoutingDigitShift(layout);
  }

  // The older partial: unique keys, value 1, in whatever buckets -- the merge
  // re-tags and re-routes it from scratch.
  const size_t per_bucket = 12;
  bs::Table older = Zeroed(std::max<size_t>(1, older_buckets), layout);
  std::map<uint64_t, uint8_t> model;
  std::vector<uint64_t> older_keys;
  uint64_t next_key = 1;
  for (size_t b = 0; b < older_buckets; ++b) {
    for (size_t slot = 0; slot < per_bucket; ++slot) {
      const uint64_t key = next_key++;
      Plant(layout, older.Bucket(b), slot, key, 1);
      model[key] = 1;
      older_keys.push_back(key);
    }
    for (size_t slot = per_bucket; slot < bs::kBucketCapacity; ++slot) {
      bs::WriteSlotKey(older.Bucket(b), slot, layout.key_bytes,
                       1 + (rng() % next_key));
    }
    older.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
  }

  // The carry: value 2, a third of its keys shadowing the older partial's, and
  // ROUTED under its family nonce -- which is the nonce the merge will use.
  bs::Table carry = Zeroed(carry_buckets, layout);
  {
    std::vector<uint64_t> keys;
    for (size_t i = 0; i < carry_buckets * per_bucket; ++i) {
      uint64_t key = 0;
      if (!older_keys.empty() && rng() % 3 == 0) {
        key = older_keys[rng() % older_keys.size()];
        if (std::find(keys.begin(), keys.end(), key) != keys.end()) key = 0;
      }
      if (key == 0) key = next_key++;
      keys.push_back(key);
    }
    for (size_t i = 0; i < keys.size(); ++i) {
      const size_t b = i / per_bucket, slot = i % per_bucket;
      Plant(layout, carry.Bucket(b), slot, keys[i], 2);
      model[keys[i]] = 2;
    }
    for (size_t b = 0; b < carry_buckets; ++b) {
      for (size_t slot = per_bucket; slot < bs::kBucketCapacity; ++slot) {
        bs::WriteSlotKey(carry.Bucket(b), slot, layout.key_bytes,
                         1 + (rng() % next_key));
      }
      carry.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
    }
    bs::TableView cv = bs::View(carry);
    // Published as a power-of-two table: kRaw, routed on its own k bits.
    bs::ComputeRoutingTags(cv, nonce_lo, carry_nonce_hi, bs::RoutingIndexMap{},
                           k);
    OwnedLevelStashes route(k, 1, layout);
    if (!bs::ButterflyRouteStashCacheOblivious<true>(cv, k, route.ptr()) ||
        route.Count() != 0) {
      *overflowed = true;
      return {};
    }
  }
  if (poison_tags) {
    // What a payload-only residual sweep leaves behind: positions still valid,
    // stored tag bytes meaningless.  The install is what must repair them.
    for (size_t b = 0; b < carry_buckets; ++b) {
      for (size_t line = layout.TagOffset(); line < layout.EntryBytes(); ++line) {
        for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
          carry.Bucket(b)[line * bs::kBucketCapacity + slot] =
              static_cast<uint8_t>(rng());
        }
      }
    }
  }

  bs::Table out = Zeroed(static_cast<size_t>(digit) * carry_buckets, layout);
  OwnedLevelStashes stashes(block_bits + 2, 1, layout);
  bs::RebuildStepContext ctx;
  ctx.out = bs::View(out);
  ctx.fresher = bs::View(carry);
  ctx.older = bs::View(older);
  ctx.older.num_buckets = older_buckets;
  ctx.upper_offset = carry_buckets;
  ctx.nonce_lo = nonce_lo;
  ctx.nonce_hi = merge_nonce_hi;
  ctx.route_levels = block_bits;
  ctx.level_stashes = stashes.ptr();
  ctx.radix_stash = &stashes.slots[block_bits];
  ctx.merge_stash = &stashes.slots[block_bits + 1];
  ctx.map = map;

  const bs::SubtaskBudget budget{~size_t{0}, ~size_t{0}, ~size_t{0},
                                 ~size_t{0}, ~size_t{0}, ~size_t{0}};
  std::vector<bs::Subtask> plan;
  la::PlanSparseLevelMerge(ctx, la::MergeShapeOf(ctx), budget, &plan);
  *overflowed = false;
  for (const bs::Subtask& task : plan) {
    if (!bs::RunSubtask</*CheckOverflow=*/true>(ctx, task)) *overflowed = true;
  }
  if (stashes.Count() != 0) *overflowed = true;
  if (model_out != nullptr) *model_out = model;
  return LiveEntries(bs::View(out), unique);
}

// The generic fused scatter re-tags from one hash per LOG bucket.  Against the
// unfused reference (scatter, then ComputeRoutingTagsRange) every mask and
// every byte of every live lane agrees -- including a routed width below the
// whole tag, where the lines above it must be left alone, and a radix map,
// whose digit line goes on top.  Dummy lanes may differ: the unfused re-tag
// hashes them, the fused one does not.
void TestDenseScatterRetagMatchesRetag() {
  const bs::Layout layout{8, 16, 4};
  const size_t bytes = layout.BucketBytes();
  const size_t log_buckets = 4;
  const size_t fanout = 2;
  std::mt19937_64 rng(0xD5E7);
  size_t cases = 0;
  for (unsigned route_levels : {0u, 3u, 9u, 17u}) {  // 4, 1, 2, 3 tag bytes
    for (bool radix : {false, true}) {
      bs::RoutingIndexMap map;
      if (radix) {
        map.kind = bs::TagMapKind::kRadixDigit;
        map.low_bits = 9;
        map.modulus = 3;
        map.digit_shift = 24;
      }
      bs::Table log = bs::Table::Create(log_buckets, layout);
      for (size_t i = 0; i < log_buckets * bytes; ++i) {
        log.data[i] = static_cast<uint8_t>(rng());
      }
      for (size_t b = 0; b < log_buckets; ++b) log.masks[b] = rng();
      log.masks[0] = ~uint64_t{0};  // a full bucket feeds both destinations
      bs::Table reference = bs::Table::Create(log_buckets * fanout, layout);
      bs::Table fused = bs::Table::Create(log_buckets * fanout, layout);
      std::memset(reference.data.get(), 0xCD, log_buckets * fanout * bytes);
      std::memset(fused.data.get(), 0xCD, log_buckets * fanout * bytes);

      for (size_t b = 0; b < log_buckets; ++b) {
        bs::ScatterDenseBucket(log.Bucket(b), log.masks[b],
                               reference.Bucket(b * fanout),
                               reference.masks.get() + b * fanout,
                               64 / fanout, layout.EntryBytes(),
                               layout.PayloadLines());
      }
      bs::ComputeRoutingTagsRange(bs::View(reference), 3, 0x51, 0,
                                  log_buckets * fanout, map, route_levels);

      bs::RebuildStepContext ctx;
      ctx.small_log = bs::View(log);
      ctx.out = bs::View(fused);
      ctx.nonce_lo = 3;
      ctx.nonce_hi = 0x51;
      ctx.map = map;
      ctx.route_levels = route_levels;
      // Out of order and in pieces, as a sliced budget would issue it.
      for (size_t b = log_buckets; b-- > 0;) {
        bs::ScatterAndRetagDenseBucket(
            log.Bucket(b), log.masks[b], fused.Bucket(b * fanout),
            fused.masks.get() + b * fanout, 64 / fanout, layout,
            microram::crypto::PackAesCtrHighWord(ctx.nonce_lo, ctx.nonce_hi),
            map, bs::RoutedTagBytes(layout, route_levels),
            bs::RetagWritesDigitLine(layout, map,
                                     bs::RoutedTagBytes(layout, route_levels)),
            *ctx.aes_keys);
      }

      for (size_t b = 0; b < log_buckets * fanout; ++b) {
        Expect(reference.masks[b] == fused.masks[b],
               "the fused scatter changed an occupancy word");
        for (size_t line = 0; line < layout.EntryBytes(); ++line) {
          for (unsigned lane = 0; lane < 64; ++lane) {
            if (((reference.masks[b] >> lane) & 1) == 0) continue;
            Expect(reference.Bucket(b)[64 * line + lane] ==
                       fused.Bucket(b)[64 * line + lane],
                   "the fused scatter changed a live byte");
          }
        }
      }
      ++cases;
    }
  }
  std::printf("  dense scatter: %zu cases re-tag from the log bucket, live "
              "bytes and masks unchanged\n", cases);
}

void TestSparseMerge() {
  size_t cases = 0;
  for (unsigned k : {4u, 5u}) {
    for (unsigned r : {1u, 3u, 5u, 7u}) {
      for (unsigned e = 0; (r << e) <= 8; ++e) {
        // Digit 1 routes nothing, so its install copies the carry's tags
        // unrepaired (7(b)); the job test's binary case covers it.
        if ((r << e) < 2) continue;
        std::map<uint64_t, uint8_t> model, clean_model;
        bool unique = false, overflowed = false;
        const std::map<uint64_t, uint8_t> live =
            RunSparseMerge(k, r, e, /*merge_nonce_hi=*/0x1234,
                           /*poison_tags=*/true, &unique, &overflowed, &model);
        Expect(!overflowed, "the sparse merge shed at this fixture load");
        Expect(unique, "the merged table holds a key twice");
        // THE GATE: every key of either source survives, with the carry's
        // value wherever both hold it.  Nothing weaker would notice a merge
        // that dropped an older key or kept the stale copy of a shared one.
        Expect(live == model,
               "the merge is not exactly the newest copy of every key");
        bool ref_unique = false, ref_overflowed = false;
        const std::map<uint64_t, uint8_t> clean =
            RunSparseMerge(k, r, e, /*merge_nonce_hi=*/0x1234,
                           /*poison_tags=*/false, &ref_unique, &ref_overflowed,
                           &clean_model);
        Expect(!ref_overflowed && ref_unique && clean == clean_model,
               "the clean-tag run failed");
        Expect(live == clean,
               "poisoned carry tags changed the merge's result, so the install "
               "is not re-tagging");
        size_t shadowed = 0, only_older = 0;
        for (const auto& entry : model) {
          shadowed += entry.second == 2;
          only_older += entry.second == 1;
        }
        Expect(shadowed > 0 && only_older > 0,
               "the fixture exercised only one of the two sources");
        ++cases;
      }
    }
  }
  std::printf("  sparse merge: %zu digits resolve to one copy per key, with "
              "the carry's stored tags poisoned\n", cases);
}

// The nonce-sharing rule, stated as the failure it produces.
//
// A merge that draws its own nonce instead of the carry's family nonce
// re-tags every carry entry under a different hash while leaving it in the
// bucket the OLD hash chose -- the install performs no routing, so nothing
// moves it.  What that costs is measurable rather than subtle: the carry copy
// and the older copy of a shared key no longer land in the same cross pair,
// so the merge stops deduplicating and BOTH copies survive.  (A carry key with
// no duplicate is merely unfindable, which only a probe notices -- but any
// fixture with overlapping sources sees the duplicate first.)
//
// So this is an implementation trap and not a silent corruption, and the test
// asserts the loud symptom rather than a bare difference.
void TestMergeNonceMustBeTheCarrysFamily() {
  bool unique = false, overflowed = false;
  const std::map<uint64_t, uint8_t> shared =
      RunSparseMerge(4, 1, 1, /*merge_nonce_hi=*/0x1234, /*poison_tags=*/false,
                     &unique, &overflowed, nullptr);
  Expect(!overflowed && unique && !shared.empty(),
         "the shared-nonce run failed");
  bool foreign_unique = true, foreign_overflowed = false;
  const std::map<uint64_t, uint8_t> foreign =
      RunSparseMerge(4, 1, 1, /*merge_nonce_hi=*/0x9999, /*poison_tags=*/false,
                     &foreign_unique, &foreign_overflowed, nullptr);
  Expect(!foreign_unique,
         "a merge under a foreign nonce still deduplicated, so this fixture "
         "cannot see what a wrong nonce does");
  Expect(foreign != shared, "a foreign nonce produced the same table");
  std::printf("  nonce: a foreign nonce breaks dedup -- the carry and older "
              "copies of a key stop meeting\n");
}

// ---------------------------------------------------------------------------
// 4. A dense merge's two shed classes
// ---------------------------------------------------------------------------
//
// The dense merge is the one shape with TWO routing phases: the older sources'
// butterflies and the prefix builder's own.  They shed different freshness
// classes, and a residual pool slot carries one rank, so they must not shed
// into one array.  At load 0.5 neither sheds at all, which is why
// the fixture below forces both: without that, "they share an array" and "they
// do not" produce byte-identical results and nothing is being tested.

// Keys whose stored index -- the low `bits` bits of the routing word this
// merge's own re-tag will write -- is `target`.  Rejection sampling over the
// real tag function, 64 candidates per AES pass; at bits = 3 it keeps one key
// in eight.
std::vector<uint64_t> KeysAtIndex(const bs::Layout& layout, uint64_t nonce_lo,
                                  uint64_t nonce_hi,
                                  const bs::RoutingIndexMap& map,
                                  unsigned route_levels, unsigned bits,
                                  uint64_t target, size_t count,
                                  uint64_t* next_key) {
  std::vector<uint64_t> keys;
  bs::Table probe = Zeroed(1, layout);
  probe.masks[0] = ~uint64_t{0};
  while (keys.size() < count) {
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      Plant(layout, probe.Bucket(0), slot, (*next_key)++, 0);
    }
    bs::TableView v = bs::View(probe);
    bs::ComputeRoutingTags(v, nonce_lo, nonce_hi, map, route_levels);
    for (size_t slot = 0; slot < bs::kBucketCapacity && keys.size() < count;
         ++slot) {
      if (SlotTagBits(layout, probe.Bucket(0), slot, bits) != target) continue;
      keys.push_back(SlotKey(layout, probe.Bucket(0), slot));
    }
  }
  return keys;
}

// Every live entry of one stash array, as (key, value) pairs.
std::vector<std::pair<uint64_t, uint8_t>> StashEntries(
    const bs::Layout& layout, const OwnedLevelStashes& stashes, size_t first,
    size_t last) {
  std::vector<std::pair<uint64_t, uint8_t>> entries;
  for (size_t s = first; s < last; ++s) {
    const bs::ResidualStash& stash = stashes.slots[s];
    for (size_t b = 0; b < stash.num_buckets; ++b) {
      uint64_t mask = stash.masks[b];
      while (mask != 0) {
        const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
        mask &= mask - 1;
        entries.emplace_back(SlotKey(layout, stash.Bucket(b), slot),
                             SlotValue(layout, stash.Bucket(b), slot));
      }
    }
  }
  return entries;
}

// Every phase precondition is a guard against an out-of-bounds read of some
// other level's arena (or, for route_levels, a silent mis-route), so each one
// must fire in the RELEASE build too -- an assert would not.
// MakeMergeShape is public and callable without a geometry to have vetted its
// arguments, so its own arithmetic has to hold at the edge of the type.  The
// block width is a SHIFT, and a shift of 64 is undefined behaviour rather than
// a wrap a later product check could still catch, so the width must be
// checked before the shift.
void TestMergeShapeBoundaries() {
  Expect(Throws([] { return la::MakeMergeShape(size_t{1} << 63, 2, 1); }),
         "a merge whose block exceeds 2^64 buckets must be refused");
  Expect(Throws([] { return la::MakeMergeShape(size_t{1} << 62, 8, 1); }),
         "a merge whose output exceeds 2^64 buckets must be refused");
  Expect(Throws([] { return la::MakeMergeShape(0, 2, 1); }), "U = 0");
  Expect(Throws([] { return la::MakeMergeShape(12, 2, 1); }),
         "U must be a power of two");
  Expect(Throws([] { return la::MakeMergeShape(16, 6, 4); }),
         "the digit must be a multiple of the map's radix");
  {  // the largest shape that DOES fit still builds
    const la::MergeShape s = la::MakeMergeShape(size_t{1} << 62, 2, 1);
    Expect(s.block_bits == 63 && s.block_buckets == (size_t{1} << 63),
           "the widest representable merge block");
  }
  {  // and an output that is more carries than a digit can count is refused
    const bs::Layout layout = TestLayout();
    bs::RebuildStepContext ctx;
    bs::Table out = Zeroed(4, layout);
    ctx.out = bs::View(out);
    ctx.out.num_buckets = size_t{1} << 40;
    ctx.fresher = bs::View(out);
    ctx.fresher.num_buckets = 1;
    Expect(Throws([&] { return la::MergeShapeOf(ctx); }),
           "a digit that does not fit an unsigned must be refused");
  }
  std::printf("  merge shape: the width is checked before the shift\n");
}

// THE TAG HAS TO HOLD THE INDEX **AND** THE WHOLE DIGIT ABOVE IT.
//
// Two claims, and the index one alone lets a layout through whose digit is
// cut off -- which is not a refusal the engine gets for free later, because a
// truncated digit is a perfectly good digit.  The re-tag writes the top tag
// byte by truncating the mapped tag to eight bits, so a digit with one bit of
// room where its radix needs two sends every entry of block 2 into block 0
// (at tag_bytes = 1 with digit_bits = 7 a dense digit-3 merge would finish
// with entries missing and survivors misrouted).
//
// The rule is PlanRoutingTag's, and it is a rule about LAYOUTS rather than
// about this merge's radix: the digit's three bits are reserved for radices
// 1..7 whatever this particular merge's modulus is, and a layout that cannot
// spare them is given a digit byte of its own and comes back one byte wider.
// Asking the planner rather than restating it is what keeps this check and
// the sizing from drifting.
void TestTagMustHoldTheWholeDigit() {
  const size_t carry = 4;    // U = 4 buckets, so a 2-bit index
  const unsigned digit = 3;  // radix 3: a digit of two bits, inside the three
  const la::MergeShape shape = la::MakeMergeShape(carry, digit, 3);
  Expect(shape.block_bits == 2 && shape.has_radix_pass(),
         "the fixture's shape is not a mixed-radix one");

  // One context for all three phases, which ExpectLevelMergeContexts allows
  // outside a dense install and which makes every disagreement check trivially
  // true: what is left is the tag arithmetic, which is the subject.
  auto check = [&](size_t tag_bytes, size_t digit_bits, unsigned digit_shift) {
    bs::Layout layout;
    layout.key_bytes = 8;
    layout.value_bytes = 4;
    layout.tag_bytes = tag_bytes;
    layout.digit_bits = digit_bits;
    bs::Table out = Zeroed(shape.out_buckets, layout);
    bs::Table older = Zeroed(shape.older_buckets, layout);
    bs::RebuildStepContext ctx;
    ctx.out = bs::View(out);
    ctx.older = bs::View(older);
    ctx.upper_offset = carry;
    ctx.route_levels = shape.block_bits;
    ctx.map.kind = bs::TagMapKind::kRadixDigit;
    ctx.map.low_bits = shape.block_bits;
    ctx.map.modulus = 3;
    ctx.map.digit_shift = digit_shift;
    la::LevelMergeSpec spec;
    spec.shape = shape;
    la::ExpectLevelMergeContexts(la::LevelMergeContexts::Shared(ctx), spec);
  };
  auto at_layout = [&](size_t tag_bytes, size_t digit_bits) {
    bs::Layout layout;
    layout.tag_bytes = tag_bytes;
    layout.digit_bits = digit_bits;
    return bs::RoutingDigitShift(layout);
  };
  auto accepts = [&](size_t tag_bytes, size_t digit_bits, const char* what) {
    Expect(!Throws([&] { check(tag_bytes, digit_bits,
                               at_layout(tag_bytes, digit_bits)); }), what);
  };
  auto refuses = [&](size_t tag_bytes, size_t digit_bits, const char* what) {
    Expect(Throws([&] { check(tag_bytes, digit_bits,
                              at_layout(tag_bytes, digit_bits)); }), what);
  };

  // The two layouts PlanRoutingTag produces for a 2-bit index: packed (the
  // digit shares the index's byte) and reserved (a byte of its own).
  accepts(1, 2, "the packed layout a 2-bit index plans was refused");
  accepts(2, 0, "the reserved-digit-byte layout was refused");
  // And the one that straddles the byte: the index fits, the digit does not.
  // digit_bits = 6 leaves two bits -- enough for THIS radix and not for the
  // reserved three -- and 7 leaves one, which is the repro.
  refuses(1, 7, "a digit with one bit of room for a two-bit radix was "
                "accepted");
  refuses(1, 6, "a digit that straddles the top tag byte was accepted");
  // The index claim is still its own: this layout is one PlanRoutingTag
  // produces (a 1-bit index), and the merge routes two bits.
  refuses(1, 1, "a merge routing more index bits than the layout holds was "
                "accepted");
  // A map whose digit is not where the layout keeps it re-tags at one offset
  // and reads at another.
  Expect(Throws([&] { check(2, 0, /*digit_shift=*/5); }),
         "a digit map that disagrees with its layout was accepted");
  Expect(Throws([&] { check(1, 2, /*digit_shift=*/3); }),
         "a digit map one bit off its layout was accepted");
  std::printf("  tag width: the index AND the whole digit, per PlanRoutingTag\n");
}

void TestPhasePreconditionsAreChecked() {
  const bs::Layout layout = TestLayout();
  const size_t carry = 16, digit = 4;
  bs::Table out = Zeroed(digit * carry, layout);
  bs::Table fresher = Zeroed(carry, layout);
  bs::Table older = Zeroed((digit - 1) * carry, layout);
  const bs::SubtaskBudget budget{~size_t{0}, ~size_t{0}, ~size_t{0},
                                 ~size_t{0}, ~size_t{0}, ~size_t{0}};
  const la::MergeShape shape = la::MakeMergeShape(carry, digit, 1);

  auto fresh_ctx = [&] {
    bs::RebuildStepContext ctx;
    ctx.out = bs::View(out);
    ctx.fresher = bs::View(fresher);
    ctx.older = bs::View(older);
    ctx.upper_offset = carry;
    ctx.route_levels = shape.block_bits;
    return ctx;
  };
  auto refuses = [&](const bs::RebuildStepContext& ctx, const char* what) {
    std::vector<bs::Subtask> plan;
    bool threw = false;
    try {
      la::PlanSparseLevelMerge(ctx, shape, budget, &plan);
    } catch (const std::exception&) {
      threw = true;
    }
    Expect(threw, what);
  };

  {  // the happy path really does plan
    std::vector<bs::Subtask> plan;
    la::PlanSparseLevelMerge(fresh_ctx(), shape, budget, &plan);
    Expect(!plan.empty(), "a well-formed context planned nothing");
  }
  { bs::RebuildStepContext c = fresh_ctx(); c.route_levels = shape.block_bits - 1;
    refuses(c, "a short route_levels was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx(); c.route_levels = shape.block_bits + 1;
    refuses(c, "an over-long route_levels was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx(); c.upper_offset = 0;
    refuses(c, "an older source at offset 0 was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx(); c.older.num_buckets -= 1;
    refuses(c, "a short older view was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx(); c.fresher.num_buckets -= 1;
    refuses(c, "a short carry view was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx(); c.out.num_buckets -= 1;
    refuses(c, "a short output view was accepted"); }
  { // a pass fused where this merge has nothing to fuse it into would be
    // built and then never swept, drained or reset -- a silent loss.
    bs::RebuildStepContext c = fresh_ctx();
    c.residual[0].active = true;
    c.residual[0].fuse = bs::ResidualFuseSite::kOwnLastLevel;
    refuses(c, "a pass fused at an unsupported site was accepted"); }
  { bs::RebuildStepContext c = fresh_ctx();
    c.residual[0].active = true;
    c.residual[0].fuse = bs::ResidualFuseSite::kRadixPass;
    refuses(c, "a radix-fused pass at a power-of-two digit was accepted"); }
  std::printf("  preconditions: every phase guard refuses in Release too\n");
}

}  // namespace

int main() {
  std::printf("level arena, merge phases\n");
  TestSeparatedContinuationStashes<false>();
  TestSeparatedContinuationStashes<true>();
  TestBlankFirstPairMatchesClearedPair<false>();
  TestBlankFirstPairMatchesClearedPair<true>();
  TestBlankFirstRadixMatchesClearedRadix<false>();
  TestBlankFirstRadixMatchesClearedRadix<true>();
  TestPhasesMatchAbsorb();
  // Low fills, then FULL dense buckets -- the production shape, and the only
  // one that drives the scatter's second destination bucket.
  TestDenseScatterRetagMatchesRetag();
  TestSparseMerge();
  // Digit 1 (the dense install alone), a binary digit and a mixed-radix one.
  TestMergeNonceMustBeTheCarrysFamily();
  TestMergeShapeBoundaries();
  TestTagMustHoldTheWholeDigit();
  TestPhasePreconditionsAreChecked();
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena merge checks failed\n", failures);
    return 1;
  }
  std::printf("level arena merge phases: OK\n");
  return 0;
}
