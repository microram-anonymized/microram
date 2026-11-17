#pragma once

// How deep this hierarchy's residual stashes have to be, from the certified
// capacity table rather than from a number somebody liked.  Stashes and range
// scratch are sized with the shared planners for the largest operation each
// level actually runs, and the depths are certified capacities for those
// operations' actual source stashes (DESIGN.md, "Top compaction and
// residuals", describes how these widths feed allocation and pass shapes).
//
// WHAT A STASH IS FOR.  A MergeSplit's destination bucket holds 64 slots, and
// a hashed table runs at logical load 0.5, so a routing level's output bucket
// takes about 32 entries -- but only ABOUT: the count is Binomial and the
// bucket is finite, and the entries that do not fit SHED into that level's
// stash.  The stash is the overflow, and running out of it is a hard failure,
// not a slow path.  So its depth is a probability question, and the answer has
// to hold for a whole deployment's worth of rebuilds rather than for one.
//
// THE MODEL. LevelStashSlots tabulates a Chernoff bound for the sum of
// independent Poisson(32) positive excesses above 64. Applying it to a
// production stage requires a joint MGF domination argument for that stage;
// a fixed total or pairwise negative correlation alone does not supply one.
// Levels get separate stashes and their failure probabilities are unioned,
// not multiplied. This file allocates the modeled stash budget and counts
// executions. The separate tier bound certifies half-load multinomial excess;
// its application to ordinary merges, and residual range routing, rest on
// coupling and domination premises that the bound certification states and
// tracks (analysis/bound_certification/README.md, and "Premises and their
// evidence" in analysis/bound_certification/LEAN_CLAIMS.md).
//
// WHAT THIS FILE CLAIMS.  The Chernoff bound itself lives in the shared
// capacity table (cpu_byteslice_stash_capacity_table.hpp); this file only
// counts THIS geometry's rebuilds, stages and output buckets and passes them
// to it.  It does not claim a new certificate -- it claims that the arguments
// it passes describe the merges this engine actually runs.

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_tier_bound.hpp"
#include "src/oram/rebuild/cpu_byteslice_stash_capacity_table.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// The per-level result, plus the counts it was derived from so that a
// disagreement with the model script is a comparison and not an argument.
struct LevelStashPlan {
  size_t buckets = 0;        // the depth of ONE stash slot at this level
  double rebuilds = 0.0;     // upper bound, including one top initialization
  unsigned block_bits = 0;   // the widest merge's block depth, K_l + e
  unsigned stages = 0;       // shedding stages in the widest of them
  size_t route_buckets = 0;  // buckets the widest routing level writes
  double target_log2 = 0.0;  // the failure probability this depth was bought at
  size_t tier_buckets = 0;   // required published-tier depth at this level
  unsigned tier_exponent = 0;  // per-packing target is 2^-tier_exponent
};

inline unsigned ResidualCeilLog2(uint64_t n) {
  unsigned bits = 0;
  for (uint64_t remaining = n - 1; remaining; remaining >>= 1) ++bits;
  return bits;
}

class LevelArenaStashSizing {
 public:
  // `max_accesses` is the deployment's request horizon -- the number of
  // accesses the 2^-64 failure bound has to cover.  It is not the capacity:
  // a table of 2^24 entries serving 2^40 requests rebuilds far more often than
  // one serving 2^24, and the stash depth follows the rebuilds.
  LevelArenaStashSizing(const LevelArenaGeometry& geometry,
                        uint64_t max_accesses)
      : levels_(geometry.Levels()) {
    if (max_accesses == 0) {
      throw std::invalid_argument(
          "level arena: a stash depth needs a request horizon");
    }
    // The union bound's three factors, in the order they are argued above.
    //
    //  1. ACROSS LEVELS.  L + 1 rather than L: the dense prefix ring (level
    //     0 in this count) is the same kind of failure and shares the budget.
    // Count whole events, conservatively including a partial final period.
    // Integer ceiling avoids rounding a request horizon down before dividing
    // it. Initialization's separate top route is charged below.
    const auto ceil_div = [](uint64_t n, uint64_t d) {
      return n / d + (n % d != 0);
    };
    const uint64_t prefixes = ceil_div(
        ceil_div(max_accesses, geometry.OnlineStashEntries()),
        geometry.PrefixFlushes());
    plans_.assign(levels_ + 1, LevelStashPlan{});
    uint64_t carries = prefixes;  // level 1 takes every complete prefix
    for (unsigned l = 1; l <= levels_; ++l) {
      LevelStashPlan& plan = plans_[l];
      //  2. ACROSS REBUILDS.  Every carry this level accepts, including the
      //     digit-1 adoptions that run no kernel at all and so cannot shed
      //     (AdoptsFirstCarry; a default-layout binary level installs instead,
      //     and that install can shed).  Counting them is the conservative
      //     direction and keeps the count a pure function of the geometry
      //     rather than of which digits a particular run happened to visit.
      // Initialize routes the top once, independently of online accesses.
      // Charge it even when the caller does not use initialization. Its
      // preparation is covered by the same width/stage envelope below.
      const uint64_t executions = carries + (l == levels_ ? 1u : 0u);
      plan.rebuilds = static_cast<double>(executions);
      if (static_cast<uint64_t>(plan.rebuilds) < executions) {
        plan.rebuilds = std::nextafter(
            plan.rebuilds, std::numeric_limits<double>::infinity());
      }
      //  3. ACROSS THE STAGES OF ONE MERGE.  Every stash slot the merge can
      //     overflow is a stage, because the union bound is over "any one of
      //     them ran out".  The base is the BLOCK's routing bits plus the
      //     radix pass's and the fixed merge's: at digit j = r*2^e the block
      //     is 2^(K_l + e) buckets, widest at the largest power-of-two digit
      //     -- j = B below the top, where it is U_(l+1), and j = D at the top,
      //     where it is U_L << e under the top's own rule: all of T for a
      //     binary top, U_L for a whole-digit one (TopBlockBuckets).
      //
      // The top additionally retains its preparation carry.
      // Below the top the widest block is the widest table the level
      // writes: U_(l+1).
      const size_t block = l == levels_ ? geometry.TopBlockBuckets()
                                        : geometry.MaxOutputBuckets(l);
      plan.block_bits = Log2Checked(block, "merge block");
      plan.stages = plan.block_bits + 2;
      if (l == levels_) ++plan.stages;  // the retained preparation carry
      // n_events is how many destination buckets one routing level writes.
      // The widest is the radix pass, over the whole output -- which at the
      // top is D*U_L and so is NOT a power of two, which is why this is a
      // count and the depth above is a log.
      plan.route_buckets = geometry.MaxOutputBuckets(l);
      // Reserve one quarter of the lifetime budget for stage stashes, one
      // quarter for tiers, and leave one half for the still-open terms.
      // Compute ceil(log2((L+1)*R*stages)) exactly. A floating log sum
      // followed by ceil can round a value just above an integer down to
      // that integer. The 128-bit product covers the public integer ranges;
      // the resulting small integer exponent is exactly representable.
      using Wide = unsigned __int128;
      const Wide events = (Wide{levels_} + 1) * executions * plan.stages;
      unsigned event_bits = 0;
      for (Wide remaining = events - 1; remaining; remaining >>= 1)
        ++event_bits;
      plan.target_log2 = -static_cast<double>(66 + event_bits);
      const unsigned slots =
          LevelStashSlots(static_cast<double>(plan.route_buckets),
                          plan.target_log2);
      if (slots == 0) {
        throw std::invalid_argument(
            "level arena: no certified stash depth for this geometry and "
            "request horizon; the capacity table does not reach it");
      }
      plan.buckets = static_cast<size_t>(slots) / kBucketCapacity;
      // The complete-excess positive series used by the certification
      // report's (analysis/bound_certification/REPORT.pdf) conditional
      // certificate is looser than the sizing Chernoff bound at large
      // outputs. Its stage width above 2^25 homes is 4 pages (H=2^32). Keep
      // the horizon-derived depth if larger. Apply the same floor to any
      // level with that output size.
      const size_t series_floor =
          plan.route_buckets > (uint64_t{1} << 25) ? 4 : 0;
      plan.buckets = std::max(plan.buckets, series_floor);
      deepest_ = std::max(deepest_, plan.buckets);
      // At most two residual packing passes per execution, including top
      // preparation and finish. Counting two everywhere also covers init.
      // Rounding each log upward gives an integer, conservative allocation.
      plan.tier_exponent = 67 + ResidualCeilLog2(levels_) +
                           ResidualCeilLog2(executions);
      plan.tier_buckets =
          ResidualTierBuckets(plan.route_buckets, plan.tier_exponent);
      if (plan.tier_buckets == 0) {
        throw std::invalid_argument(
            "level arena: no residual tier depth for this geometry and "
              "request horizon; the occupancy bound does not reach it");
      }
      deepest_tier_ = std::max(deepest_tier_, plan.tier_buckets);
      if (l < levels_) carries = ceil_div(carries, geometry.Fanout(l));
    }
  }

  unsigned levels() const { return levels_; }

  const LevelStashPlan& At(unsigned level) const {
    if (level < 1 || level > levels_) {
      throw std::out_of_range("level arena: no such level");
    }
    return plans_[level];
  }

  // One stash slot's depth at `level`, in buckets.
  size_t Buckets(unsigned level) const { return At(level).buckets; }

  // The deepest over the hierarchy: what a per-THREAD buffer has to be if one
  // thread may execute at more than one level (transient storage per
  // executing thread).
  size_t DeepestBuckets() const { return deepest_; }

  size_t DeepestTierBuckets() const { return deepest_tier_; }

 private:
  unsigned levels_ = 0;
  size_t deepest_ = 0;
  size_t deepest_tier_ = 0;
  std::vector<LevelStashPlan> plans_;  // index 0 unused
};

// THE PER-LEVEL PROFILE a geometry's stash sizing certifies: level l's own
// requirement for the tables it produces (LevelStashPlan::tier_buckets), kept
// non-decreasing below the top.  The floor is what lets a binary level's
// digit-1 install move its carry's tier (level l-1's) into its own output
// tier unchanged.  The top keeps its own requirement, which may be the
// narrower one: at D = 1 the top has level L-1's homes and fewer rebuilds.
inline std::vector<size_t> LevelTierProfile(const LevelArenaGeometry& geometry,
                                            const LevelArenaStashSizing& sizing) {
  std::vector<size_t> profile(geometry.Levels(), 0);
  size_t floor = 1;
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    const size_t own = sizing.At(l).tier_buckets;
    profile[l - 1] = l == geometry.Levels() ? own : std::max(own, floor);
    if (l < geometry.Levels()) floor = profile[l - 1];
  }
  return profile;
}

// Zero requests automatic sizing: each level's own width (LevelTierProfile).
// A pinned width is shared, and a pinned profile is checked level by level.
// Resolve before allocating or pricing anything so range scratch sees these
// widths too.
inline LevelArenaGeometry::Params ResolveLevelArenaTierGeometry(
    LevelArenaGeometry::Params params, uint64_t max_accesses) {
  const size_t requested = params.tier_buckets;
  const std::vector<size_t> pinned = params.level_tier_buckets;
  // Sizing reads no tier width, so any valid placeholder does.
  params.level_tier_buckets.clear();
  params.tier_buckets = 1;
  const LevelArenaGeometry placeholder(params);
  const LevelArenaStashSizing sizing(placeholder, max_accesses);
  if (!pinned.empty()) {
    const std::vector<size_t> need = LevelTierProfile(placeholder, sizing);
    if (pinned.size() != need.size()) {
      throw std::invalid_argument(
          "level arena: a tier profile holds one width per level");
    }
    for (size_t i = 0; i < need.size(); ++i) {
      if (pinned[i] < need[i]) {
        throw std::invalid_argument(
            "level arena: pinned tier profile is below a level's lifetime "
            "occupancy requirement");
      }
    }
    params.level_tier_buckets = pinned;
    params.tier_buckets = *std::max_element(pinned.begin(), pinned.end());
    return params;
  }
  if (requested != 0) {
    if (requested < sizing.DeepestTierBuckets()) {
      throw std::invalid_argument(
          "level arena: pinned residual tier is below the lifetime occupancy "
          "requirement; use tier_buckets=0 for automatic sizing");
    }
    params.tier_buckets = requested;
    return params;
  }
  params.level_tier_buckets = LevelTierProfile(placeholder, sizing);
  params.tier_buckets = *std::max_element(params.level_tier_buckets.begin(),
                                          params.level_tier_buckets.end());
  return params;
}

// ---------------------------------------------------------------------------
// How many stash slots one merge needs
// ---------------------------------------------------------------------------
//
// The DEPTH above is per slot; this is how many slots there are.  A butterfly
// level sheds into level_stashes[bit], and the fused quad reads
// level_stashes[bit + 1] -- the next ROUTED bit's slot, never one past the
// network -- so a route `n` bits deep owns slots [0, n + 1).  The radix pass
// and the fixed merge have one each, after those.
//
// That is the deepest routed bit + 1, plus the two, stated here because the arena's
// job allocates the array itself.
// All three are offsets from `block_bits`: the radix stash is
// level_stashes[block_bits + 1] and the fixed merge's is
// level_stashes[block_bits + 2], leaving [0, block_bits + 1) to the route.
inline constexpr size_t kLevelMergeRadixStashOffset = 1;
inline constexpr size_t kLevelMergeMergeStashOffset = 2;
// THE TOP ONLY (DESIGN.md "Top compaction and residuals").  Its preparation ends in a residual pass of its own and
// RETAINS what that pass could not place, until the merge's pass sweeps it.
// One slot more, because it is a DRAIN and not a shed: the route's slots are
// reset when the preparation's pass ends, and this one has to survive that.
// Its depth is a route slot's: it holds what one routing pass sheds.
inline constexpr size_t kLevelMergePrepCarryStashOffset = 3;

inline size_t LevelMergeStashSlots(unsigned block_bits, bool top = false) {
  return static_cast<size_t>(block_bits) + 1 +
         (top ? kLevelMergePrepCarryStashOffset
              : kLevelMergeMergeStashOffset);
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
