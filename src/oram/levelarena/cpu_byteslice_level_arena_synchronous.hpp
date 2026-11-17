#pragma once

// THE SYNCHRONOUS STORAGE MODE (LevelArenaEngine::Options::synchronous): the
// arena engine's levels, carries, merge jobs and publications, run to
// completion by the request that completes a dense prefix, in a layout that
// keeps each level's table in ONE region.
//
// WHY IT IS SMALLER.  The arena keeps a table probeable while its replacement
// is built, so consecutive digits of a level live in different places (its
// odd bank and the forwarding lease), a receiving level has two inboxes and
// the top two banks: M/T = 2 + (3B-1)/((B-1)D) (DESIGN.md, "Geometry and
// storage bound").  Here nothing reads a table while a merge rewrites it --
// the requester runs every merge between two accesses, with its reader epoch
// closed -- so each level has one region and its table GROWS DOWNWARD in it:
//
//     level l < L:  b_l U_l buckets, digit j's table at [(b_l - j) U_l, b_l U_l)
//     top:          T buckets, compacted in place
//
// A merge at digit j writes P_j = [carry's U | P_(j-1)], and offset U is
// exactly where LevelMergeJob puts its older operand (offset 0 at the top), so
// the binding is in place (LevelMergeBinding::in_place) and the job's copy is
// the identity.  At digit b_l the region is full: U_(l+1) buckets, the carry
// level l+1 merges where it lies.  For a uniform fanout
//
//     M = T + sum(l=2..L) U_l,   M/T = 1 + B/((B-1) D) (1 - B^-(L-1)),
//
// 8/7 at B = D = 8, against the arena's 135/56.
//
// WHAT IS SHARED, AND SO CERTIFIED.  The geometry, the stash and tier sizing,
// the canonical families, every merge's job and its residual routing are the
// arena's objects, run at the same (level, ordinal) in the same order with
// the same plans, so every job has the arena's shape and the geometry's
// certified bound applies (cpu_byteslice_level_arena_certification.hpp; this
// file is not an input to it).  The tables are byte for byte the arena's
// (tests/oram/cpu_byteslice_level_arena_synchronous_test.cpp runs both in
// lockstep).  What differs is not a
// job:
//
//   - an ADOPTED first carry (digit 1 above level 1 at fanout > 2) is copied
//     -- main, masks and tier -- from the level below's region into this
//     level's, where the arena leaves it in the inbox;
//   - a level's tier alternates between two stashes, so a merge's output tier
//     is never its older operand's.
//
// WHAT IT COSTS.  The request that completes a prefix pays for every merge it
// triggers, a top compaction included: no overlap and no owner thread.  The
// dense ring, the probe cascade, the batch path, the publisher and the epoch
// are the engine's own and unchanged.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_bytes.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_family.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_level.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_top_log.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

class SynchronousLevels {
 public:
  struct Wiring {
    const LevelArenaGeometry* geometry = nullptr;
    const LevelArenaStashSizing* sizing = nullptr;
    Layout layout;
    const AesTagKeys* aes_keys = nullptr;
    LevelArenaPublisher* publisher = nullptr;
    DensePrefixRing* dense = nullptr;
    // The engine's range scratch, one per level, index 0 unused.
    std::vector<LevelMergeScratch*> scratch;
    // Diagnostics: the engine's top merge log (null records nothing), and
    // whether the jobs time their pieces (--stage-times).
    TopMergeLog* top_log = nullptr;
    bool time_stages = false;
  };

  explicit SynchronousLevels(const Wiring& wiring) : w_(wiring) {
    if (w_.geometry == nullptr || w_.sizing == nullptr ||
        w_.aes_keys == nullptr || w_.publisher == nullptr ||
        w_.dense == nullptr ||
        w_.scratch.size() != w_.geometry->Levels() + 1) {
      throw std::invalid_argument(
          "level arena: the synchronous levels are missing their wiring");
    }
    const LevelArenaGeometry& g = *w_.geometry;
    levels_.resize(g.Levels() + 1);
    stats_.resize(g.Levels() + 1);
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      Level& level = levels_[l];
      const size_t region = RegionBuckets(g, l);
      const size_t tier = TierWidth(g, l);
      AddRegionBytes(&bytes_, w_.layout, region, tier);
      level.data = AllocateAligned64(
          CheckedTableBytes(region + 2 * tier, w_.layout));
      level.masks = MakeTalliedArray<uint64_t>(region, ByteRole::kMasks,
                                               &bytes_);
      for (unsigned t = 0; t < 2; ++t) {
        level.tiers[t].data =
            level.data.get() + (region + t * tier) * w_.layout.BucketBytes();
        level.tiers[t].num_buckets = g.TierBucketsOf(l);
        level.tiers[t].entry_bytes = w_.layout.EntryBytes();
      }
      level.job = std::make_unique<LevelMergeJob>(g, *w_.sizing, w_.layout, l,
                                                  *w_.aes_keys);
      bytes_.Add(level.job->bytes());
      level.job->EnableStageTiming(w_.time_stages);
    }
    ExpectPredictedBytes(bytes_, Bytes(g, *w_.sizing, w_.layout),
                         "the synchronous levels");
  }

  SynchronousLevels(const SynchronousLevels&) = delete;
  SynchronousLevels& operator=(const SynchronousLevels&) = delete;

  // ---- storage ------------------------------------------------------------

  // A level's region: the full table below the top, which is the next
  // level's carry, and T at the top.
  static size_t RegionBuckets(const LevelArenaGeometry& g, unsigned level) {
    return level == g.TopLevel() ? g.TopBuckets() : g.CarryBuckets(level + 1);
  }

  // A tier stash's width: the tables the level produces, or an adopted first
  // carry's, which keeps the level below's (a tier profile only widens below
  // the top, so this is the level's own wherever it adopts).
  static size_t TierWidth(const LevelArenaGeometry& g, unsigned level) {
    size_t width = g.TierBucketsOf(level);
    if (level >= 2 && level < g.TopLevel()) {
      width = std::max(width, g.TierBucketsOf(level - 1));
    }
    return width;
  }

  // At most one live table per level: a level's region holds one, and a
  // forwarded table leaves the plan in the merge that consumes it.
  static size_t TableSlots(const LevelArenaGeometry& g) { return g.Levels(); }

  // Main buckets over every level, the quantity the header's M counts.
  static size_t MainBuckets(const LevelArenaGeometry& g) {
    uint64_t total = 0;
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      total = CheckedAdd(total, RegionBuckets(g, l), "synchronous mains");
    }
    return static_cast<size_t>(total);
  }

  // Bytes of the regions and their tiers, with an occupancy word per region
  // bucket: the synchronous counterpart of LevelArenaGeometry::ArenaBytes.
  static size_t ArenaBytes(const LevelArenaGeometry& g, const Layout& layout) {
    uint64_t total = 0;
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      const size_t region = RegionBuckets(g, l);
      total = CheckedAdd(
          total,
          CheckedAdd(CheckedTableBytes(region + 2 * TierWidth(g, l), layout),
                     CheckedMul(region, sizeof(uint64_t), "region masks"),
                     "region bytes"),
          "synchronous arena bytes");
    }
    return static_cast<size_t>(total);
  }

  // The regions, their tiers and masks, and one merge job per level.
  static LevelArenaByteBill Bytes(const LevelArenaGeometry& g,
                                  const LevelArenaStashSizing& sizing,
                                  const Layout& layout) {
    LevelArenaByteBill bill;
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      const size_t region = RegionBuckets(g, l);
      AddRegionBytes(&bill, layout, region, TierWidth(g, l));
      bill.AddPlain(ByteRole::kMasks,
                    CheckedSizeMul(region, sizeof(uint64_t), "region masks"));
      bill.Add(LevelMergeJob::StorageBytes(g, sizing, layout, l));
    }
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

  // ---- state --------------------------------------------------------------

  uint64_t ordinal(unsigned level) const { return At(level).ordinal; }
  uint64_t merges() const { return merges_; }
  // Diagnostics: the per-level phase counters and the level's job, as the
  // incremental LevelState reports them -- prepare_nanos is the older half's
  // routing, merge_nanos the carry's install and the finish, publish_nanos the
  // descriptor, the plan install and the bookkeeping after it.  Wall time of
  // the requester's calls, so it contains no waiting.
  LevelStats stats(unsigned level) const { return stats_.at(level); }
  const LevelMergeJob& job(unsigned level) const { return *At(level).job; }
  uint64_t adoptions() const { return adoptions_; }

  // Nothing has happened but the empty top: what Initialize requires.
  bool Pristine() const {
    for (unsigned l = 1; l <= w_.geometry->Levels(); ++l) {
      const Level& level = At(l);
      if (level.ordinal != 0) return false;
      if (l != w_.geometry->TopLevel() && level.table.valid()) return false;
    }
    return true;
  }

  // ---- initialization -----------------------------------------------------

  // THE EMPTY TOP (DescribeEmptyTop): zero masks over the top's region.
  void PublishEmptyTop() {
    Level& top = At(w_.geometry->TopLevel());
    if (top.table.valid()) {
      throw std::logic_error("level arena: the top already has a table");
    }
    const TableView main = Region(w_.geometry->TopLevel(), 0,
                                  w_.geometry->TopBuckets());
    std::fill_n(main.masks, main.num_buckets, uint64_t{0});
    top.tiers[top.tier].Reset();
    PublishedTable table;
    w_.publisher->AllocateTableIds(&table.table_id, &table.tier_table_id);
    DescribeEmptyTop(*w_.geometry, &table);
    table.owner = w_.geometry->TopLevel();
    table.slot = kRegionSlot;
    table.generation = ++generation_;
    FillTableStorage(&table, main, &top.tiers[top.tier]);
    PublicationDelta delta;
    delta.Add(table);
    w_.publisher->Publish(delta);
    top.table = table;
  }

  // THE INITIALIZED TOP (LevelState::PublishInitialTop, in place over the
  // empty top's region).  `scatter(main)` writes the records; the top's
  // ordinary preparation routes them where they lie.  An input that throws
  // leaves the empty top restored and this engine pristine.
  template <class Scatter>
  void PublishInitialTop(Scatter&& scatter) {
    const LevelArenaGeometry& g = *w_.geometry;
    const unsigned l = g.TopLevel();
    Level& top = At(l);
    if (!Pristine() || !top.table.valid()) {
      throw std::logic_error(
          "level arena: an initialized top replaces the empty one");
    }
    const unsigned digit = g.TopDigit();
    const TableView main = Region(l, 0, g.TopBuckets());
    ResidualStash* out_tier = OutputTier(l);
    PublishedTable out;
    try {
      scatter(main);
      LevelMergeBinding binding;
      binding.ordinal = digit;  // the top has accepted D carries' worth
      binding.out = main;
      binding.out_tier = out_tier;
      binding.destination_generation = ++generation_;
      binding.older_main = main;  // the records are already where they belong
      top.job->RouteInitialTop(binding, w_.scratch[l],
                               WholeLevelMergeBudget());
      w_.publisher->AllocateTableIds(&out.table_id, &out.tier_table_id);
      DescribeLevelTable(g, l, Family{l, digit}, digit,
                         MakeTopMergeShape(g.CarryBuckets(l), digit), &out);
      out.owner = l;
      out.slot = kRegionSlot;
      out.generation = binding.destination_generation;
      out.main_buckets = main.num_buckets;
      FillTableStorage(&out, main, out_tier);
      PublicationDelta delta;
      delta.Add(out);
      delta.Remove(top.table.table_id);
      delta.ConsumePrefixes(DirectInitializationSeed(g).prefixes);
      ReclaimPlans();
      w_.publisher->Publish(delta);
    } catch (...) {
      // The empty top is still published, and it is these masks.
      std::fill_n(main.masks, main.num_buckets, uint64_t{0});
      throw;
    }
    top.table = out;
    top.tier ^= 1;
    top.ordinal = digit;
  }

  // The carries a direct initialization says level `level` has accepted
  // (DirectInitializationSeed): whole cycles, so no partial.
  void SeedAcceptedCarries(unsigned level, uint64_t carries) {
    if (level < 1 || level >= w_.geometry->TopLevel()) {
      throw std::logic_error(
          "level arena: only a level below the top is seeded by count");
    }
    Level& l = At(level);
    if (l.ordinal != 0 || l.table.valid()) {
      throw std::logic_error(
          "level arena: only an untouched level can be seeded");
    }
    if (carries % w_.geometry->Fanout(level) != 0) {
      throw std::logic_error(
          "level arena: a seeded non-top level holds no partial");
    }
    l.ordinal = carries;
  }

  // ---- the merges ---------------------------------------------------------

  // Every complete dense prefix, merged as far up as it carries.  The caller
  // is the requester, between two accesses, with its reader epoch closed.
  // Returns how many prefixes it merged.
  size_t MergeCompletedPrefixes() {
    size_t merged = 0;
    while (w_.dense->PrefixReady()) {
      MergePrefix();
      ++merged;
    }
    return merged;
  }

 private:
  // A level's one occupancy, as the publisher names it.
  static constexpr unsigned kRegionSlot = 0;

  struct Level {
    Aligned64Ptr data;  // the region, then its two tiers' buckets
    std::unique_ptr<uint64_t[]> masks;  // the region's
    ResidualStash tiers[2];
    unsigned tier = 0;  // the live table's tier
    std::unique_ptr<LevelMergeJob> job;
    uint64_t ordinal = 0;  // carries accepted
    // The live table, if any.  A forwarded one is the next level's carry.
    PublishedTable table;
  };

  static void AddRegionBytes(LevelArenaByteBill* bill, const Layout& layout,
                             size_t region, size_t tier) {
    bill->AddAligned64Split(
        {RoleShare{ByteRole::kMains, CheckedTableBytes(region, layout)},
         RoleShare{ByteRole::kTiers, CheckedTableBytes(2 * tier, layout)}});
  }

  Level& At(unsigned level) { return levels_.at(level); }
  const Level& At(unsigned level) const { return levels_.at(level); }

  TableView Region(unsigned level, size_t offset, size_t buckets) const {
    const Level& l = At(level);
    TableView view;
    view.layout = w_.layout;
    view.num_buckets = buckets;
    view.data = l.data.get() + offset * w_.layout.BucketBytes();
    view.masks = l.masks.get() + offset;
    return view;
  }

  // The stash the next table of `level` publishes its tier in: the one its
  // live table does not use, at the width the level's tables have.
  ResidualStash* OutputTier(unsigned level) {
    Level& l = At(level);
    ResidualStash* tier = &l.tiers[l.tier ^ 1];
    tier->num_buckets = w_.geometry->TierBucketsOf(level);
    return tier;
  }

  void ReclaimPlans() {
    w_.publisher->ReclaimPlans(w_.publisher->epoch().Observed());
  }

  void MergePrefix() {
    uint64_t prefix = 0;
    uint64_t generation = 0;
    LevelCarry carry;
    carry.ordinal = At(1).ordinal + 1;
    carry.dense_prefix = w_.dense->TakePrefix(&prefix, &generation);
    unsigned level = 1;
    while (Accept(level, carry, prefix, generation)) {
      // Level `level` forwarded: its full table is the next level's carry,
      // available to the top as soon as this publication returned.
      if (level + 1 == w_.geometry->TopLevel()) {
        carry_ready_ns_ = TopLogNowNanos();
      }
      const Level& from = At(level);
      carry = LevelCarry{};
      carry.ordinal = from.ordinal / w_.geometry->Fanout(level);
      carry.family = from.table.family;
      carry.main = Region(level, 0, RegionBuckets(*w_.geometry, level));
      carry.tier = &from.tiers[from.tier];
      ++level;
    }
  }

  // One carry into `level`.  Returns whether the level forwarded its table.
  bool Accept(unsigned level, const LevelCarry& carry, uint64_t prefix,
              uint64_t prefix_generation) {
    const LevelArenaGeometry& g = *w_.geometry;
    Level& l = At(level);
    const uint64_t ordinal = l.ordinal + 1;
    if (carry.ordinal != ordinal) {
      throw std::logic_error("level arena: a carry arrived out of order");
    }
    const CarryPlan plan = g.PlanCarry(level, ordinal);
    if (plan.outcome == CarryOutcome::kAdopt) {
      Adopt(level, carry, ordinal);
      return false;
    }
    const bool top = level == g.TopLevel();
    const size_t u = g.CarryBuckets(level);
    // Digit j's table ends at the region's top (the whole region at the top).
    const size_t offset =
        top ? 0 : RegionBuckets(g, level) - plan.output_buckets;
    const bool logging = top && w_.top_log != nullptr;
    const uint64_t t_begin = TopLogNowNanos();
    LevelMergeBinding binding;
    binding.ordinal = ordinal;
    binding.out = Region(level, offset, plan.output_buckets);
    binding.out_tier = OutputTier(level);
    binding.destination_generation = ++generation_;
    if (MergeHasOlderHalf(top, plan.digit)) {
      if (!l.table.valid()) {
        throw std::logic_error(
            "level arena: this digit absorbs an older table and there is none");
      }
      binding.older_main =
          top ? binding.out
              : Region(level, offset + u, plan.output_buckets - u);
      binding.older_tier = &l.tiers[l.tier];
      binding.in_place = true;
    }
    LevelMergeJob& job = *l.job;
    const uint64_t fold_at_begin = job.fold_nanos();
    job.Begin(binding);
    // The three phases LevelMergeJob::Finish runs, apart so each is timed
    // (PrepareOlder is the preparation InstallCarry would run first).
    const uint64_t t_prepare = TopLogNowNanos();
    job.PrepareOlder(WholeLevelMergeBudget(), w_.scratch[level]);
    const uint64_t t_merge = TopLogNowNanos();
    job.InstallCarry(carry, WholeLevelMergeBudget(), w_.scratch[level]);
    job.FinishMerge(w_.scratch[level], WholeLevelMergeBudget());
    const uint64_t t_merged = TopLogNowNanos();
    ++merges_;

    PublishedTable out;
    w_.publisher->AllocateTableIds(&out.table_id, &out.tier_table_id);
    DescribeLevelTable(g, level, job.family(), plan.digit, job.shape(), &out);
    out.owner = level;
    out.slot = kRegionSlot;
    out.generation = binding.destination_generation;
    out.main_buckets = plan.output_buckets;
    FillTableStorage(&out, binding.out, binding.out_tier);
    PublicationDelta delta;
    delta.Add(out);
    const bool dense = level == 1;
    if (dense) {
      delta.ConsumePrefixes(prefix + 1);
    } else {
      delta.Remove(At(level - 1).table.table_id);
    }
    if (l.table.valid()) delta.Remove(l.table.table_id);
    ReclaimPlans();
    const uint64_t threshold = w_.publisher->Publish(delta);
    const uint64_t t_published = TopLogNowNanos();
    if (dense) {
      w_.dense->NoteConsumed(prefix + 1);
      if (!w_.dense->SendRetirement(
              PrefixRetirement{prefix, prefix_generation, threshold})) {
        throw std::logic_error(
            "level arena: the dense retirement ring is full");
      }
    } else {
      At(level - 1).table = PublishedTable{};
    }
    l.ordinal = ordinal;
    l.tier ^= 1;
    l.table = out;
    const uint64_t t_end = TopLogNowNanos();
    LevelStats& st = stats_[level];
    const uint64_t prepare_ns = t_merge - t_prepare;
    const uint64_t merge_ns = t_merged - t_merge;
    const uint64_t publish_ns = t_end - t_merged;
    st.prepare_nanos += prepare_ns;
    st.merge_nanos += merge_ns;
    st.publish_nanos += publish_ns;
    ++st.merges;
    ++st.publications;
    if (plan.outcome == CarryOutcome::kForward) ++st.forwards;
    if (plan.digit <= kMaxLevelDigit) {
      const uint64_t job_ns = prepare_ns + merge_ns + publish_ns;
      ++st.job_count[plan.digit];
      st.job_nanos[plan.digit] += job_ns;
      st.job_max_nanos[plan.digit] = std::max(st.job_max_nanos[plan.digit], job_ns);
    }
    if (logging) {
      // The top merge log's record.  The merge runs between two accesses with the reader epoch
      // closed, so the carry is taken the moment it is available, and the
      // top compacts in place: the replaced table's storage is the new
      // table's, so its "retirement" is its publication.
      TopMergeRecord r;
      r.ordinal = ordinal;
      r.prepare_start_ns = t_begin;
      r.carry_ready_ns = carry_ready_ns_;
      r.carry_accept_ns = carry_ready_ns_;
      r.merge_start_ns = t_merge;
      r.publish_ns = t_published;
      r.retire_ns = t_published;
      r.retire_in_place = true;
      r.prepare_active_ns = prepare_ns;
      r.merge_active_ns = merge_ns;
      r.publish_active_ns = publish_ns;
      r.fold_ns = job.fold_nanos() - fold_at_begin;
      w_.top_log->Store(r);
    }
    return plan.outcome == CarryOutcome::kForward;
  }

  // Digit 1 at fanout > 2: the carry becomes this level's first table
  // unchanged (same family, window and shape), copied into the top of this
  // level's region with its tier.
  void Adopt(unsigned level, const LevelCarry& carry, uint64_t ordinal) {
    const LevelArenaGeometry& g = *w_.geometry;
    Level& l = At(level);
    Level& below = At(level - 1);
    if (l.table.valid() || !below.table.valid()) {
      throw std::logic_error(
          "level arena: an adopted carry needs an empty level and a "
          "forwarded table below it");
    }
    const size_t u = g.CarryBuckets(level);
    const TableView dst = Region(level, RegionBuckets(g, level) - u, u);
    std::memcpy(dst.data, carry.main.data, u * w_.layout.BucketBytes());
    std::memcpy(dst.masks, carry.main.masks, u * sizeof(uint64_t));
    ResidualStash* tier = &l.tiers[l.tier ^ 1];
    tier->num_buckets = carry.tier->num_buckets;
    std::memcpy(tier->data, carry.tier->data,
                carry.tier->num_buckets * w_.layout.BucketBytes());
    std::copy_n(carry.tier->masks, kMaxResidualStashBuckets, tier->masks);

    PublishedTable out = below.table;
    w_.publisher->AllocateTableIds(&out.table_id, &out.tier_table_id);
    out.owner = level;
    out.slot = kRegionSlot;
    out.generation = ++generation_;
    FillTableStorage(&out, dst, tier);
    PublicationDelta delta;
    delta.Add(out);
    delta.Remove(below.table.table_id);
    ReclaimPlans();
    w_.publisher->Publish(delta);
    below.table = PublishedTable{};
    l.ordinal = ordinal;
    l.tier ^= 1;
    l.table = out;
    ++adoptions_;
  }

  Wiring w_;
  std::vector<Level> levels_;  // index 0 unused
  LevelArenaByteBill bytes_;
  uint64_t generation_ = 0;
  uint64_t carry_ready_ns_ = 0;  // when the carry now at the top was available
  std::vector<LevelStats> stats_;  // index 0 unused
  uint64_t merges_ = 0;
  uint64_t adoptions_ = 0;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
