#pragma once

// ONE residual second chance, described declaratively and built once.
//
// A pass is a pool of shed stashes and borrowed tiers, a freshness rank per
// slot, a dedup rule, a drain and -- sometimes -- a routing pass it rides
// instead of sweeping standalone.  Almost none of that is free: which slots
// may be reset, which may be cleared by the pool dedup, which must lead the
// list and which must trail it are PROOF OBLIGATIONS, and getting one wrong
// loses live records silently rather than failing.  So there is one builder
// that validates every shape, and the callers say what they mean rather than
// assembling a ResidualPass field by field.
//
// WHY IT IS HERE and not in an engine.  The level-arena engine
// (src/oram/levelarena/) runs the absorb and needs these passes over its own
// storage; keeping the checks next to the shared planners
// (PlanMergeOlderBlocks, PlanMergeFinish) means every caller validates the
// same rules and no engine carries a drifting copy.  What is engine-specific
// is the caller's, and there are only two such things:
//
//   1. WHERE THE RANGE TABLE LIVES.  BuildResidualPassFields returns the
//      buckets the pass needs and the caller attaches a view of its own
//      scratch through AttachResidualRange, which refuses a view of the
//      wrong size.  Two calls rather than one, so a caller cannot forget:
//      a sweeping pass with no range table would plan a sweep over nothing.
//   2. WHAT IS PUBLISHED.  The PUBLISHED-CLEAR rule below -- a borrowed
//      source the pool dedup may CLEAR must not be a tier the request thread
//      is reading
//      -- is the same rule for every engine, but "is this mask array in the
//      published plan?" is a question only that engine's plan can answer, so
//      it arrives as a predicate.
//
// Nothing here reads occupancy, keys or matches: a pass's shape is a function
// of public capacities and ranks, which is what keeps the schedule
// data-independent.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_residual_range.hpp"
#include "src/oram/rebuild/cpu_byteslice_second_chance.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_run.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"

namespace microram {
namespace byteslice {

// Declarative description of one residual second chance.  Keeping the source
// list, ranks, ownership prefix, drain, and rule together makes the proof
// obligations visible at each call site and lets one builder validate every
// pass shape.
struct ResidualPassSourceSpec {
  ResidualStash* stash = nullptr;
  uint8_t rank = 0;
  // Owns mutable occupancy, not necessarily payload. A private descriptor
  // borrowing pinned payload qualifies; it must never be used as a drain.
  bool owned = false;
  // kClassMark passes only: this swept slot's entries take the tier's
  // kResidualWins rule at the merged offer.  Tier slots must form the swept
  // suffix, so the class boundary is one flat bucket index.
  bool tier_class = false;
};

struct ResidualPassSpec {
  TableView main;
  unsigned main_levels = 0;
  int scratch = -1;
  std::vector<ResidualPassSourceSpec> sources;
  size_t shed_slots = 0;
  // Leading sources that are provably unabsorbable at this pass (their target
  // bucket is full and duplicate-free by construction -- see
  // DrainResidualPoolRange) and therefore skip the range table and the sweep,
  // going straight to the drain after the pool dedup.  Must lie inside the
  // owned reset prefix; the range table is sized from the remaining suffix.
  size_t drain_only_slots = 0;
  // Where the pass's offers run instead of a standalone sweep: the step's
  // cross-source level (kCrossLevel -- the chain step's carry and tier
  // passes, and the power-of-two-digit absorb's), the last level of the
  // pass's own butterfly (kOwnLastLevel -- pass 0, and the r = 1 fixed
  // preparation's), the radix pass (kRadixPass -- the absorb's and the fixed
  // preparation's at r > 1) or the fixed merge (kFixedMerge).  In every case
  // the pass that is ridden sheds AFTER the range table was built, so its
  // own stash must be the drain-only prefix: a swept slot's late sheds would
  // otherwise be reset unread.
  ResidualFuseSite fuse = ResidualFuseSite::kNone;
  ResidualStash* drain = nullptr;
  ResidualDedupRule rule = ResidualDedupRule::kNoDedup;
  size_t lines = 0;
  RoutingIndexMap map;
  // The absorb's final pass remains scheduled when its public source list is
  // empty.  It owns the output tier in that shape, so this is explicit rather
  // than an accidental empty-pool special case in the builder.
  bool force_active = false;
  // A DFS leaf's pages (DfsResidualRangePlan; a direct or empty plan where
  // DFS does not apply).
  size_t dfs_pages = 2;
  // Keep the final tier-class source in a private full-home direct tail of
  // the range allocation, after one-page A leaves. Dedup/reset still use all
  // sources; masks and the coordinated drain still use the whole allocation.
  bool separate_direct_tier = false;

  void AddOwned(ResidualStash* stash, uint8_t rank) {
    sources.push_back({stash, rank, true, false});
  }
  // An owned source that also carries the tier class.  A pass whose fresher
  // class is the job's OWN storage rather than a borrowed tier needs this: the
  // level-arena engine owns private masks for both input tiers before any
  // pass can clear them; level one's direct build owns B's tier outright.  The two orderings the builder
  // enforces -- owned sources first, tier-class sources last -- then have to
  // be satisfied by the same slot, which they can be only if EVERY source is
  // owned.
  void AddOwnedTierClass(ResidualStash* stash, uint8_t rank) {
    sources.push_back({stash, rank, true, true});
  }
  void AddBorrowed(ResidualStash* stash, uint8_t rank,
                   bool tier_class = false) {
    sources.push_back({stash, rank, false, tier_class});
  }
};

template <class PublishedMasks>
inline size_t BuildResidualPassFields(RebuildStepContext* ctx, unsigned pass,
                                      std::vector<ResidualStash*>* pool,
                                      std::vector<uint8_t>* rank,
                                      const ResidualPassSpec& spec,
                                      PublishedMasks&& published_masks) {
  if (pass >= kResidualPasses || pool == nullptr || rank == nullptr) {
    throw std::logic_error("invalid residual pass specification");
  }
  ResidualPass& rp = ctx->residual[pass];
  *pool = {};
  *rank = {};
  rp = ResidualPass{};
  if (!spec.force_active && spec.sources.empty()) return 0;
  if (spec.scratch < 0 || spec.main.num_buckets == 0 ||
      spec.drain == nullptr || spec.lines == 0) {
    throw std::logic_error("active residual pass has incomplete state");
  }
  // The range plan splits main_levels into the coarse range bits and the
  // bits the sweep matches, and the sweep pairs main bucket b with
  // range bucket b >> index_bits.  Fewer levels than the main's index width
  // and the last main buckets pair with range buckets past the table (only a
  // debug assert guards the read); more, and the partition and the match read a
  // tag bit above the destination index, so a candidate with that bit set is
  // offered to no main bucket.  Log2Exact is the CEILING, which is also what
  // a mixed-radix main (r * 2^k buckets) needs: its top ranges stay empty.
  if (spec.main_levels != Log2Exact(spec.main.num_buckets)) {
    throw std::logic_error(
        "a residual pass's main_levels is not its main table's index width");
  }

  size_t reset_slots = 0;
  bool saw_borrowed = false;
  bool saw_tier_class = false;
  for (size_t i = 0; i < spec.sources.size(); ++i) {
    const ResidualPassSourceSpec& source = spec.sources[i];
    if (source.stash == nullptr) {
      throw std::logic_error("residual pass contains a null source");
    }
    if (source.owned) {
      if (saw_borrowed) {
        throw std::logic_error(
            "owned residual sources must form the reset prefix");
      }
      ++reset_slots;
    } else {
      saw_borrowed = true;
    }
    // The class boundary must be ONE flat bucket index, so the tier-class
    // slots have to be the source list's suffix; and a class mark on any slot
    // is only meaningful under the merged rule.
    if (saw_tier_class && !source.tier_class) {
      throw std::logic_error(
          "tier-class residual sources must form the swept suffix");
    }
    if (source.tier_class) {
      if (spec.rule != ResidualDedupRule::kClassMark) {
        throw std::logic_error(
            "a tier-class source needs the class-marked rule");
      }
      if (i < spec.drain_only_slots) {
        throw std::logic_error("a drain-only source cannot carry a class");
      }
      saw_tier_class = true;
    }
    // A stash listed twice is wrong at ANY rank.  At equal rank the two slots
    // are not disjoint; at different ranks the pool dedup compares the stash
    // with itself and clears every live lane of the staler listing, which is
    // every live lane of the stash.
    for (size_t j = 0; j < i; ++j) {
      if (spec.sources[j].stash == source.stash) {
        throw std::logic_error("a residual stash is listed twice in one pass");
      }
    }
    // The drain is written after every source was read and before the owned
    // ones are reset.  Draining into a swept source hands it back its own
    // records as duplicates and then resets them all; draining into a
    // borrowed one writes into payload its owner has pinned (the same race
    // class as the published-clear rule below).
    if (source.stash == spec.drain) {
      throw std::logic_error("a residual pass drains into one of its sources");
    }
  }
  if (spec.rule == ResidualDedupRule::kClassMark && !saw_tier_class) {
    throw std::logic_error("a class-marked pass needs a tier-class source");
  }
  if (spec.shed_slots > reset_slots) {
    throw std::logic_error("residual shed sources are outside reset prefix");
  }
  if (spec.drain_only_slots > reset_slots) {
    throw std::logic_error(
        "drain-only residual sources must be owned (a borrowed tier is "
        "always offered)");
  }
  // The own-last-level fusion is argued for the no-dedup class alone, and it
  // REQUIRES its level's own stash to be the drain-only prefix: the range
  // table is built before that level runs, so a swept slot filled during it
  // would be reset unread.
  if (spec.fuse == ResidualFuseSite::kOwnLastLevel &&
      (spec.rule != ResidualDedupRule::kNoDedup ||
       spec.drain_only_slots == 0)) {
    throw std::logic_error(
        "an own-last-level fused pass needs the kNoDedup rule and its "
        "last-level stash as the drain-only prefix");
  }
  // The other fusions shed from the pass they ride, so they need a drain-only
  // prefix to shed into.  The cross level is one of them: its MergeSplits
  // shed into its bit's stash, and listed as a swept slot that stash would
  // be reset unread (see `fuse`).
  if ((spec.fuse == ResidualFuseSite::kCrossLevel ||
       spec.fuse == ResidualFuseSite::kRadixPass ||
       spec.fuse == ResidualFuseSite::kFixedMerge) &&
      spec.drain_only_slots == 0) {
    throw std::logic_error(
        "a fused pass needs the shed of the pass it rides as the drain-only "
        "prefix");
  }
  // kNoDedup offers without comparing, which is exact only for a pool drawn
  // from ONE source table, and one source table is one rank.  Mixed ranks
  // say the pool holds more than one, whose copies of a key the offer would
  // keep side by side.  (One rank also means such a pass never needs the
  // leftover dedup below, which only a drain-only slot outranking a swept one
  // calls for.)
  if (spec.rule == ResidualDedupRule::kNoDedup) {
    for (const ResidualPassSourceSpec& source : spec.sources) {
      if (source.rank != spec.sources[0].rank) {
        throw std::logic_error("a kNoDedup pass mixes freshness ranks");
      }
    }
  }
  // The leftover dedup (ResidualLeftoverDedupRange), planned wherever a
  // drain-only slot outranks a swept one, resolves a same-key pair between
  // the shed and a range-table leftover by the LANE'S CLASS: a carry-class
  // lane loses to the shed, a tier-class lane beats it.  That is exact only
  // if the ranks say the same thing -- every carry-class swept slot no
  // fresher than every drain-only slot, every tier-class one no staler -- so
  // a spec whose ranks disagree with its classes is a construction error.
  {
    rank->reserve(spec.sources.size());
    for (const ResidualPassSourceSpec& source : spec.sources) {
      rank->push_back(source.rank);
    }
    if (ResidualLeftoverDedupNeeded(rank->data(), rank->size(),
                                    spec.drain_only_slots)) {
      for (size_t d = 0; d < spec.drain_only_slots; ++d) {
        for (size_t s = spec.drain_only_slots; s < spec.sources.size(); ++s) {
          const bool tier = spec.sources[s].tier_class ||
                            spec.rule == ResidualDedupRule::kResidualWins;
          if (tier ? spec.sources[s].rank > spec.sources[d].rank
                   : spec.sources[s].rank < spec.sources[d].rank) {
            throw std::logic_error(
                "a residual pass's leftover dedup rule disagrees with its "
                "ranks");
          }
        }
      }
    }
  }

  // A borrowed source that can be the STALER side of an eligible pair has
  // its occupancy words cleared by the pool dedup (ResidualPoolDedupRange),
  // so it must not be a PUBLISHED stash: the request thread reads a published
  // tier's word through the probe plan with no synchronisation, and a clear
  // here would be an unsynchronised write to a word that thread reads, a
  // data race (the PUBLISHED-CLEAR rule).
  // Every mask array the worker publishes is enumerable under the lock, so
  // the rule is checked rather than trusted.  "Can be the staler side" is
  // taken as "outranked by some source" -- a superset of the window's pairs,
  // which is the safe direction.  Publication is monotone across the pass:
  // the only stash this item publishes later is its own drain, which is
  // owned.  Only the WORKER'S half of `tables` is read -- from `prefix_slots`
  // on, immutable since publication; the dense prefix below it is the request
  // thread's, written under its epoch (ProbePlan says so), and reading it
  // here would be a race of this check's own.  No pool source can be a stash
  // of the prefix anyway: a head has no residual pass.
  {
    uint8_t min_rank = std::numeric_limits<uint8_t>::max();
    for (const ResidualPassSourceSpec& source : spec.sources) {
      min_rank = std::min(min_rank, source.rank);
    }
    for (const ResidualPassSourceSpec& source : spec.sources) {
      if (source.owned || source.rank == min_rank) continue;
      if (published_masks(&source.stash->masks[0])) {
        throw std::logic_error(
            "a borrowed residual source the pool dedup may write is a "
            "published tier");
      }
    }
  }

  pool->reserve(spec.sources.size());
  for (const ResidualPassSourceSpec& source : spec.sources) {
    pool->push_back(source.stash);
  }
  if (spec.separate_direct_tier) {
    // The top's merge is separated too: its sweep resolves every candidate
    // of both offer sets before any allocation (ResolveTopDestination), the
    // direct set as the fresher class, so `drop_unshadowed` needs nothing
    // more here.
    if (spec.fuse != ResidualFuseSite::kFixedMerge ||
        spec.rule != ResidualDedupRule::kClassMark || spec.dfs_pages != 1 ||
        spec.sources.size() <= spec.drain_only_slots + 1 ||
        !spec.sources.back().tier_class) {
      throw std::logic_error(
          "separated residual pass requires a fused one-page A DFS and a "
          "final B tier");
    }
    for (size_t i = spec.drain_only_slots; i + 1 < spec.sources.size(); ++i)
      if (spec.sources[i].tier_class)
        throw std::logic_error("only the final B tier may be direct");
    rp.direct_slots = 1;
    rp.direct_buckets = spec.sources.back().stash->num_buckets;
  }
  rp.active = true;
  rp.main = spec.main;
  rp.pool = pool->data();
  rp.rank = rank->data();
  rp.pool_slots = pool->size();
  rp.reset_slots = reset_slots;
  rp.drain_only = spec.drain_only_slots;
  rp.drain = spec.drain;
  rp.rule = spec.rule;
  rp.lines = spec.lines;
  rp.map = spec.map;
  // The merged pass's class geometry: the boundary is the total capacity of
  // the swept slots BEFORE the first tier-class one, in the same flat
  // swept-pool bucket units the scatter's group index counts in.
  if (spec.rule == ResidualDedupRule::kClassMark) {
    size_t boundary = 0;
    for (size_t i = spec.drain_only_slots; i < spec.sources.size(); ++i) {
      if (spec.sources[i].tier_class) break;
      boundary += spec.sources[i].stash->num_buckets;
    }
    rp.tier_class_from = boundary;
  }
  // Only the swept suffix feeds the range table; the drain-only prefix skips
  // it (provably unabsorbable -- see DrainResidualPoolRange).  Capacity is
  // public, so a zero-capacity suffix skips the whole build-and-sweep unless
  // the pass's shape is forced (the digit-1 absorb, which owns its tier in
  // that shape).
  const size_t swept = ResidualPoolBuckets(rp.pool + rp.drain_only,
                                           rp.pool_slots - rp.drain_only);
  rp.sweep_active = swept != 0 || spec.force_active;
  rp.fuse = spec.fuse;
  if (!rp.sweep_active) return 0;
  // Every caller sizes its scratch from this same call, and
  // AttachResidualRange below refuses any disagreement.  A DFS plan still
  // needs its workspace attached (AttachResidualDfs).
  rp.plan = DfsResidualRangePlan(swept - rp.direct_buckets, spec.main_levels,
                                 spec.dfs_pages);
  return rp.plan.range_buckets + rp.direct_buckets;
}

// No borrowed source is published, which is true of a job whose pool holds
// only its own sheds and private copies -- and of any caller that has not
// published anything yet.  A caller with a live plan passes its own.
struct NoPublishedMasks {
  bool operator()(const uint64_t*) const { return false; }
};

inline size_t BuildResidualPassFields(RebuildStepContext* ctx, unsigned pass,
                                      std::vector<ResidualStash*>* pool,
                                      std::vector<uint8_t>* rank,
                                      const ResidualPassSpec& spec) {
  return BuildResidualPassFields(ctx, pass, pool, rank, spec,
                                 NoPublishedMasks{});
}

// The second half: the range table the pass was sized for.  Separate because
// the storage is the caller's, and CHECKED because a sweeping pass whose
// range view is the wrong size sweeps the wrong extent -- or, at zero, plans
// a build and a sweep over nothing and drops every entry it was meant to
// offer back.
inline void AttachResidualRange(ResidualPass* rp, const TableView& range) {
  if (rp == nullptr || !rp->active || !rp->sweep_active) {
    throw std::logic_error(
        "a residual range table was attached to a pass that does not sweep");
  }
  if (range.num_buckets != rp->plan.range_buckets + rp->direct_buckets) {
    throw std::logic_error(
        "a residual pass was given a range table of a size it was not "
        "planned for");
  }
  rp->range = range;
}

// The third, for a DFS-shaped pass: the workspace, configured for this pass's
// pool and partition.  Refused on any other plan.
inline void AttachResidualDfs(ResidualPass* rp, DfsResidualWorkspace* dfs,
                              size_t dfs_pages) {
  if (rp == nullptr || !rp->active || !rp->sweep_active || dfs == nullptr) {
    throw std::logic_error("a DFS workspace was attached to no sweeping pass");
  }
  const size_t swept =
      ResidualPoolBuckets(rp->pool + rp->drain_only,
                          DistributedPoolSlots(*rp));
  const unsigned main_levels = rp->plan.range_bits + rp->plan.index_bits;
  if (!IsDfsResidualRangePlan(rp->plan, swept, main_levels, dfs_pages) ||
      dfs->pages() != dfs_pages || rp->range.num_buckets !=
                                       rp->plan.range_buckets + rp->direct_buckets) {
    throw std::logic_error(
        "a DFS workspace was attached to a pass without a DFS leaf table");
  }
  DfsResidualWorkspace::Shape shape;
  shape.pool_buckets = swept;
  shape.coarse_bits = rp->plan.range_bits;
  shape.index_bits = rp->plan.index_bits;
  shape.main_buckets = rp->main.num_buckets;
  dfs->Configure(shape);
  rp->dfs = dfs;
  rp->dfs_price = {dfs->Units(), dfs->Touches()};
}

}  // namespace byteslice
}  // namespace microram
