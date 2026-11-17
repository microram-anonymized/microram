// Deterministic inventory probe (REPORT.tex, "Deterministic inventory").
//
// Plans every phase of every job a selected configuration can bind --
// ordinary digits, the top's preparation/install/finish and the direct
// initialization -- through the job's OWN Begin, pass builders and bounded
// task-list sink, then checks, task by task, every fixed extent a planned
// task can index (the release-mode preconditions the kernels only assert),
// and lists every capacity test the plan can reach: which stash, drain,
// distributor or range route, at which public capacity, written by which
// task kinds.  audit_deterministic_inventory.py maps each listed site to a
// ledger witness.
//
// Record tables are never allocated.  Views carry fake, never-dereferenced
// addresses: planning reads public shapes only and nothing here runs a
// kernel.  The job's own stash arrays, task lists, lane arrays and the
// engine's per-level range scratch (LevelArenaEngine::BuildScratch) are the
// real allocations.  Private planning steps are reached through the explicit
// instantiation access rule ([temp.explicit]), so the job header is compiled
// exactly as the engine compiles it.
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

#include <cstdio>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

namespace bs = microram::byteslice;
namespace la = bs::levelarena;

template <class Tag, typename Tag::type M>
struct Rob {
  friend typename Tag::type Get(Tag) { return M; }
};
#define ROB(NAME, TYPE, MEMBER)                               \
  struct NAME {                                               \
    using type = TYPE;                                        \
    friend type Get(NAME);                                    \
  };                                                          \
  template struct Rob<NAME, &la::LevelMergeJob::MEMBER>;

using Job = la::LevelMergeJob;
using TierViews = std::array<bs::ResidualStash, 2>;
ROB(PlanT, std::vector<bs::Subtask> Job::*, plan_)
ROB(StagesT, std::vector<bs::PlannedStage> Job::*, stages_)
ROB(UnitsT, std::vector<size_t> Job::*, unit_starts_)
ROB(StartPhaseT, void (Job::*)(la::LevelMergePhase, la::LevelMergeScratch*),
    StartPhase)
ROB(BuildFinishT, void (Job::*)(la::LevelMergeScratch*), BuildFinishPass)
ROB(BuildTopPrepT, void (Job::*)(la::LevelMergeScratch*, bs::ResidualStash*),
    BuildTopPreparePass)
ROB(BindCarryT, void (Job::*)(const la::LevelCarry&), BindCarry)
ROB(PrepCarryT, bs::ResidualStash* (Job::*)(), PrepCarry)
ROB(PrepareCtxT, bs::RebuildStepContext Job::*, prepare_)
ROB(InstallCtxT, bs::RebuildStepContext Job::*, install_)
ROB(FinishCtxT, bs::RebuildStepContext Job::*, finish_)
ROB(OlderT, std::vector<bs::ResidualStash> Job::*, older_sheds_)
ROB(LaneShedsT, std::vector<bs::ResidualStash> Job::*, lane_sheds_)
ROB(TierViewsT, TierViews Job::*, tier_views_)
ROB(StrideT, size_t Job::*, lane_mask_stride_)
ROB(InitializingT, bool Job::*, initializing_)
ROB(PhaseRunningT, bool Job::*, phase_running_)
ROB(DenseMasksT, std::vector<uint64_t> Job::*, dense_masks_)

namespace {

std::vector<std::string> g_violations;
size_t g_checks = 0;

void Require(bool ok, const std::string& what) {
  ++g_checks;
  if (!ok) g_violations.push_back(what);
}

// Fake addresses in disjoint 2^40-byte windows.  Planning only compares and
// copies them.
uint8_t* FakeData(unsigned i) {
  return reinterpret_cast<uint8_t*>(uintptr_t{0x100} << 36 | uintptr_t{i} << 40);
}
uint64_t* FakeMasks(unsigned i) {
  return reinterpret_cast<uint64_t*>(uintptr_t{0x200} << 36 |
                                     uintptr_t{i} << 40);
}

bs::TableView FakeView(const bs::Layout& layout, size_t buckets, unsigned i) {
  bs::TableView v;
  v.layout = layout;
  v.num_buckets = buckets;
  v.data = FakeData(i);
  v.masks = FakeMasks(i);
  return v;
}

bs::ResidualStash FakeTier(const bs::Layout& layout, size_t buckets,
                           unsigned i) {
  bs::ResidualStash s;
  s.data = FakeData(i);
  s.num_buckets = buckets;
  s.entry_bytes = layout.EntryBytes();
  return s;
}

struct Env {
  const la::LevelArenaGeometry* g;
  const la::LevelArenaStashSizing* sizing;
  bs::Layout layout;
};

// Where a stash descriptor lives, by identity.
struct Names {
  const std::vector<bs::ResidualStash>* older;
  const TierViews* tiers;
  const bs::ResidualStash* out_tier;
  const bs::ResidualStash* dense_tier;
  std::string operator()(const bs::ResidualStash* s) const {
    if (s == nullptr) return "null";
    if (!older->empty() && s >= older->data() && s < older->data() + older->size())
      return "older:" + std::to_string(s - older->data());
    if (s == &(*tiers)[0]) return "older_tier_view";
    if (s == &(*tiers)[1]) return "carry_tier_view";
    if (s == out_tier) return "out_tier";
    if (s == dense_tier) return "dense_tier";
    return "other";
  }
};

// A capacity test the plan can reach, keyed by its storage.
struct Site {
  std::string kind;     // stash | drain | dfs_partition | blank_pair
  std::string storage;  // older:i, dense_tier, out_tier, ...
  size_t slots = 0;     // public capacity in records
  std::set<std::string> writers;
  bool drain_only = false;  // a pool's drain-only prefix slot
  bool swept = false;       // a pool's swept (range-building) slot
};

std::string Json(const std::set<std::string>& s) {
  std::string out = "[";
  bool first = true;
  for (const std::string& v : s) {
    out += (first ? "\"" : ",\"") + v + "\"";
    first = false;
  }
  return out + "]";
}

void Record(Job& job, const Env& env, la::LevelMergeScratch* scratch,
            const bs::ResidualStash* out_tier, unsigned level, unsigned digit,
            const char* job_kind, la::LevelMergePhase phase, size_t lanes) {
  const auto& plan = job.*Get(PlanT{});
  const auto& stages = job.*Get(StagesT{});
  const auto& units = job.*Get(UnitsT{});
  const bs::RebuildStepContext& ctx =
      phase == la::LevelMergePhase::kPrepareOlder ? job.*Get(PrepareCtxT{})
      : phase == la::LevelMergePhase::kInstallCarry ? job.*Get(InstallCtxT{})
                                                    : job.*Get(FinishCtxT{});
  const auto& older = job.*Get(OlderT{});
  const auto& lane_sheds = job.*Get(LaneShedsT{});
  const auto& tiers = job.*Get(TierViewsT{});
  const size_t stride = job.*Get(StrideT{});
  const Names name{&older, &tiers, out_tier, job.dense_tier()};
  const size_t capacity = la::LevelPhasePlanCapacity(*env.g, env.layout, level);
  std::ostringstream where;
  where << job_kind << " L" << level << " d" << digit << " "
        << la::LevelMergePhaseName(phase) << " lanes=" << lanes;
  const std::string at = where.str();

  // (A) The task list, stages and lane units: vectors reserved at
  // construction and refused past their capacity (BoundedPlanSink).
  Require(plan.size() <= capacity, at + ": tasks exceed LevelPhasePlanCapacity");
  Require(plan.capacity() == capacity, at + ": task list reallocated");
  Require(stages.size() <= capacity + 1, at + ": stages exceed reservation");
  Require(units.size() <= capacity, at + ": lane units exceed reservation");

  size_t level_array = 0;
  if (ctx.level_stashes == older.data()) level_array = older.size();

  std::map<std::string, Site> sites;
  auto site = [&](const std::string& kind, const bs::ResidualStash* s,
                  const std::string& writer) {
    const std::string key = kind + "/" + name(s);
    Site& x = sites[key];
    x.kind = kind;
    x.storage = name(s);
    x.slots = s ? s->Capacity() : 0;
    x.writers.insert(writer);
    return &x;
  };

  std::map<std::string, size_t> kinds;
  unsigned max_radix = 0, max_ways = 0, max_subnetwork = 0, max_sets = 0;
  size_t max_groups = 0;
  const size_t out_n = ctx.out.num_buckets;
  for (size_t i = 0; i < plan.size(); ++i) {
    const bs::Subtask& t = plan[i];
    const std::string kname = bs::SubtaskKindName(t.kind);
    ++kinds[kname];
    Require(t.begin <= t.end, at + ": " + kname + " inverted range");
    const size_t half = t.bit < 63 ? size_t{1} << t.bit : 0;
    // (B) Each kind's release-mode indexing precondition, and its capacity
    // test if it has one.
    switch (t.kind) {
      case bs::Subtask::kCopyAndRetagRange:
      case bs::Subtask::kCopyAndRetagTile:
        Require(t.end <= out_n && t.begin >= ctx.upper_offset &&
                    t.end - ctx.upper_offset <= ctx.older.num_buckets,
                at + ": copy-retag outside out/older");
        break;
      case bs::Subtask::kCopyAndRetagFresher:
      case bs::Subtask::kCopyFresher:
        Require(t.end <= out_n && t.end <= ctx.fresher.num_buckets,
                at + ": fresher copy outside out/fresher");
        break;
      case bs::Subtask::kRetagRange:
      case bs::Subtask::kDropErased:
        Require(t.end <= out_n, at + ": " + kname + " outside out");
        break;
      case bs::Subtask::kDropErasedTier:
        Require(ctx.tier_out != nullptr && t.end <= ctx.tier_out->num_buckets,
                at + ": tier drop outside tier");
        break;
      case bs::Subtask::kButterflySubnetwork: {
        max_subnetwork = std::max(max_subnetwork, t.levels);
        Require(t.levels < 64 && t.end <= out_n &&
                    t.log2_stride + t.levels <= bs::Log2Exact(out_n) &&
                    t.log2_stride + t.levels <= level_array,
                at + ": butterfly subnetwork outside out or stash array");
        Require(t.log2_stride + t.levels <= 8 * env.layout.tag_bytes,
                at + ": butterfly routes past the tag");
        for (unsigned b = t.log2_stride; b < t.log2_stride + t.levels && b < level_array; ++b)
          site("stash", &ctx.level_stashes[b], kname);
        break;
      }
      case bs::Subtask::kRouteLevelRange:
        Require(t.end <= half && 2 * half <= out_n,
                at + ": route-level pairs outside out");
        if (t.blank_first) {
          Require(half == ctx.upper_offset, at + ": blank-first pair not the blank region");
          Site& x = sites["blank_pair/level:" + std::to_string(t.bit)];
          x.kind = "blank_pair";
          x.storage = "none";
          x.slots = bs::kBucketCapacity;
          x.writers.insert(kname);
        } else {
          Require(t.bit < level_array, at + ": route-level stash index past array");
          if (t.bit < level_array) site("stash", &ctx.level_stashes[t.bit], kname);
        }
        break;
      case bs::Subtask::kCrossLevelRange:
      case bs::Subtask::kCrossLevelOffers:
        Require(t.end <= half && 2 * half <= out_n && t.bit < level_array,
                at + ": cross-level outside out or stash array");
        if (t.bit < level_array) site("stash", &ctx.level_stashes[t.bit], kname);
        break;
      case bs::Subtask::kButterflyLevelOffers: {
        const bs::ResidualPass& rp = ctx.residual[t.pass];
        Require(t.end <= half && rp.main.num_buckets == 2 * half && t.bit < level_array,
                at + ": butterfly-offers outside its main or stash array");
        if (t.bit < level_array) site("stash", &ctx.level_stashes[t.bit], kname);
        break;
      }
      case bs::Subtask::kFixedMergeRange:
      case bs::Subtask::kFixedMergeOffers: {
        const unsigned r = t.bit < 1 ? 1u : t.bit;
        max_ways = std::max(max_ways, r);
        Require(r <= bs::kMaxFixedMergeWays && ctx.fresher.num_buckets != 0 &&
                    out_n == ctx.fresher.num_buckets * r &&
                    t.end <= ctx.fresher.num_buckets,
                at + ": fixed merge outside its arrays or tables");
        site("stash", ctx.merge_stash, kname);
        break;
      }
      case bs::Subtask::kRadixPassRange:
      case bs::Subtask::kRadixRouteRange:
      case bs::Subtask::kRadixPassOffers:
      case bs::Subtask::kRadixRouteOffers: {
        const unsigned r = t.bit;
        max_radix = std::max(max_radix, r);
        const bool offers = t.kind == bs::Subtask::kRadixPassOffers ||
                            t.kind == bs::Subtask::kRadixRouteOffers;
        const size_t block = r ? out_n / r : 0;
        Require(r >= 2 && r <= bs::kMaxRadix && out_n % r == 0 && t.end <= block &&
                    (offers || size_t{1} << t.levels == block),
                at + ": radix pass outside its arrays or tables");
        site("stash", ctx.radix_stash, kname);
        break;
      }
      case bs::Subtask::kDenseHomes:
        Require(ctx.dense_homes != nullptr &&
                    t.end <= ctx.small_log.num_buckets,
                at + ": direct home cache outside prefix");
        break;
      case bs::Subtask::kDenseSelect:
        Require(ctx.dense_homes != nullptr &&
                    t.levels == ctx.small_log.num_buckets &&
                    t.end <= ctx.fresher.num_buckets,
                at + ": direct selection outside prefix or B main");
        break;
      case bs::Subtask::kDenseDrain:
        Require(ctx.dense_tier != nullptr &&
                    t.end <= ctx.small_log.num_buckets,
                at + ": direct drain outside prefix or missing tier");
        site("drain", ctx.dense_tier, kname);
        break;
      case bs::Subtask::kPrefixLogDedup: {
        const size_t unit = t.levels, n = t.bit;
        Require(unit != 0 && n >= 2 && ctx.small_log.num_buckets == unit * n &&
                    t.end <= unit * unit * n * (n - 1) / 2,
                at + ": prefix dedup outside its unit pairs");
        break;
      }
      default:
        break;
    }
    // Residual-pass kinds: their [begin, end) against the pass's public units.
    if (t.pass < bs::kResidualPasses) {
      const bs::ResidualPass& rp = ctx.residual[t.pass];
      const size_t distributed = rp.sweep_active ? rp.range.num_buckets - rp.direct_buckets : 0;
      switch (t.kind) {
        case bs::Subtask::kResidualPoolDedup:
          Require(rp.active && t.end <= bs::ResidualPoolDedupPairs(
                      rp.pool, rp.rank, rp.pool_slots, rp.drain_only,
                      static_cast<bs::ResidualDedupWindow>(t.bit)),
                  at + ": pool dedup past its pairs");
          break;
        case bs::Subtask::kResidualScatterRetag:
        case bs::Subtask::kResidualScatter:
          if (t.levels == 1 && t.kind == bs::Subtask::kResidualScatterRetag) {
            Require(rp.direct_slots == 1 && t.end <= rp.direct_buckets,
                    at + ": direct tail scatter past B's tier");
          } else {
            Require(rp.sweep_active && t.end <= bs::ResidualScatterGroups(
                        bs::DistributedResidualRange(rp), rp.plan),
                    at + ": scatter past its groups");
          }
          break;
        case bs::Subtask::kResidualRetag:
          Require(t.end <= distributed, at + ": residual retag past range");
          break;
        case bs::Subtask::kResidualDfsGather:
          Require(rp.dfs != nullptr &&
                      t.end == bs::ResidualPoolBuckets(rp.pool + rp.drain_only,
                                                       bs::DistributedPoolSlots(rp)) &&
                      t.end <= rp.dfs->shape().pool_buckets,
                  at + ": DFS gather past its buffer");
          break;
        case bs::Subtask::kResidualDfsPartition: {
          Require(rp.dfs != nullptr && t.end <= rp.dfs->Units() &&
                      rp.dfs->shape().coarse_bits <= bs::DfsResidualWorkspace::kMaxCoarseBits &&
                      rp.dfs->Units() <= (size_t{1} << rp.dfs->shape().coarse_bits),
                  at + ": DFS partition past its unit list");
          Site& x = sites["dfs_partition/pass:" + std::to_string(t.pass)];
          x.kind = "dfs_partition";
          x.storage = "leaf";
          x.slots = rp.plan.groups * bs::kBucketCapacity;  // pages per leaf
          x.writers.insert(kname);
          break;
        }
        case bs::Subtask::kResidualSweep:
          Require(t.end <= rp.main.num_buckets * rp.plan.groups,
                  at + ": sweep past main x groups");
          break;
        case bs::Subtask::kResidualDrain: {
          const size_t range_units = rp.sweep_active ? rp.range.num_buckets : 0;
          Require(rp.drain != nullptr &&
                      t.end <= range_units + bs::ResidualPoolBuckets(rp.pool, rp.drain_only),
                  at + ": drain past range + drain-only buckets");
          site("drain", rp.drain, kname);
          break;
        }
        case bs::Subtask::kResidualLeftoverDedup:
          Require(rp.drain != nullptr &&
                      t.end <= bs::ResidualLeftoverDedupUnits(*rp.drain, rp.pool, rp.drain_only),
                  at + ": leftover dedup past its units");
          break;
        case bs::Subtask::kResidualReset:
          Require(t.end <= rp.reset_slots, at + ": reset past owned slots");
          break;
        default:
          break;
      }
      if (t.kind >= bs::Subtask::kResidualPoolDedup &&
          t.kind <= bs::Subtask::kResidualReset) {
        Require(rp.active, at + ": " + kname + " names an inactive pass");
      }
    }
    // (C) Fused offer sets: the fixed 2 * kResidualPasses array; chain
    // lengths the kernels guard publicly (kMaxChainedOfferGroups and
    // kMaxBucketChainedOfferGroups fall back to unchained offers).
    if (t.kind == bs::Subtask::kCrossLevelOffers ||
        t.kind == bs::Subtask::kFixedMergeOffers ||
        t.kind == bs::Subtask::kRadixPassOffers ||
        t.kind == bs::Subtask::kRadixRouteOffers) {
      const bs::ResidualFuseSite fuse =
          t.kind == bs::Subtask::kCrossLevelOffers ? bs::ResidualFuseSite::kCrossLevel
          : t.kind == bs::Subtask::kFixedMergeOffers ? bs::ResidualFuseSite::kFixedMerge
                                                     : bs::ResidualFuseSite::kRadixPass;
      unsigned sets = 0;
      size_t groups = 0;
      for (unsigned p = 0; p < bs::kResidualPasses; ++p) {
        const bs::ResidualPass& rp = ctx.residual[p];
        if (!rp.active || rp.fuse != fuse || !rp.sweep_active) continue;
        sets += rp.direct_slots ? 2 : 1;
        groups += rp.plan.groups + (rp.direct_slots ? rp.direct_buckets : 0);
      }
      max_sets = std::max(max_sets, sets);
      max_groups = std::max(max_groups, groups);
      Require(sets <= 2 * bs::kResidualPasses, at + ": offer sets exceed array");
    }
  }

  // (D) Every stash and drain reached: its inline occupancy array.
  for (const auto& [key, x] : sites) {
    if (x.kind == "stash" || x.kind == "drain")
      Require(x.slots <= bs::kMaxResidualStashBuckets * bs::kBucketCapacity &&
                  x.slots != 0,
              at + ": " + key + " is empty or deeper than its inline masks");
  }

  // (E) Lanes: stage folds and private range masks.
  size_t max_offer_range = 0;
  for (size_t s = 0; s < stages.size(); ++s) {
    const bs::StageMark& m = stages[s].mark;
    size_t used = 0;
    for (unsigned p = 0; p < bs::kResidualPasses; ++p)
      if ((m.offer_passes >> p) & 1u) used += ctx.residual[p].range.num_buckets;
    max_offer_range = std::max(max_offer_range, used);
    if (!m.lanes || lanes <= 1) continue;
    Require(used <= stride, at + ": offer stage wider than lane range masks");
    const size_t end = s + 1 < stages.size() ? stages[s + 1].first_task : plan.size();
    std::set<unsigned> shed;
    bool radix = false, merge = false;
    for (size_t i = stages[s].first_task; i < end; ++i) {
      const bs::Subtask& t = plan[i];
      switch (t.kind) {
        case bs::Subtask::kButterflySubnetwork:
          for (unsigned b = t.log2_stride; b < t.log2_stride + t.levels; ++b) shed.insert(b);
          break;
        case bs::Subtask::kRouteLevelRange:
          if (!t.blank_first) shed.insert(t.bit);
          break;
        case bs::Subtask::kCrossLevelRange:
        case bs::Subtask::kCrossLevelOffers:
        case bs::Subtask::kButterflyLevelOffers:
          shed.insert(t.bit);
          break;
        default:
          radix |= t.kind == bs::Subtask::kRadixPassOffers ||
                   t.kind == bs::Subtask::kRadixRouteOffers ||
                   t.kind == bs::Subtask::kRadixPassRange ||
                   t.kind == bs::Subtask::kRadixRouteRange;
          merge |= t.kind == bs::Subtask::kFixedMergeOffers ||
                   t.kind == bs::Subtask::kFixedMergeRange;
          if (t.kind >= bs::Subtask::kResidualPoolDedup &&
              t.kind <= bs::Subtask::kResidualReset)
            Require(false, at + ": a residual pass task in a laned stage");
          break;
      }
    }
    // Every stash a lane writes is folded back, and its lane copy exists.
    for (unsigned b : shed) {
      Require(ctx.level_stashes == older.data() && b >= m.shed_lo && b < m.shed_hi &&
                  m.shed_hi <= older.size(),
              at + ": laned stage writes a level stash its fold misses");
      if (ctx.level_stashes == older.data() && b < older.size())
        site("lane_fold", &older[b], "fold");
    }
    Require(!radix || (m.radix_shed && ctx.radix_stash != nullptr),
            at + ": laned radix stage without radix fold");
    Require(!merge || (m.merge_shed && ctx.merge_stash != nullptr),
            at + ": laned merge stage without merge fold");
    if (radix) site("lane_fold", ctx.radix_stash, "fold");
    if (merge) site("lane_fold", ctx.merge_stash, "fold");
  }
  Require(lanes <= 1 || lane_sheds.size() == lanes * older.size(),
          at + ": lane stash arrays not lane x slot");

  // (F) Residual passes: range, DFS and pool extents; which slots drain only.
  std::ostringstream passes;
  passes << "[";
  bool first = true;
  for (unsigned p = 0; p < bs::kResidualPasses; ++p) {
    const bs::ResidualPass& rp = ctx.residual[p];
    if (!rp.active) continue;
    size_t swept = 0;
    std::ostringstream pool;
    pool << "[";
    for (size_t s = 0; s < rp.pool_slots; ++s) {
      const bs::ResidualStash* st = rp.pool[s];
      if (s >= rp.drain_only) swept += st->num_buckets;
      Require(st->num_buckets <= bs::kMaxResidualStashBuckets,
              at + ": pool slot deeper than inline masks");
      pool << (s ? "," : "") << "{\"storage\":\"" << name(st)
           << "\",\"buckets\":" << st->num_buckets << ",\"rank\":" << unsigned(rp.rank[s])
           << ",\"drain_only\":" << (s < rp.drain_only ? "true" : "false")
           << ",\"direct\":" << (s + rp.direct_slots >= rp.pool_slots ? "true" : "false")
           << "}";
      const std::string key = "stash/" + name(st);
      if (sites.count(key)) {
        if (s < rp.drain_only) sites[key].drain_only = true;
        else sites[key].swept = true;
      }
    }
    pool << "]";
    if (rp.sweep_active) {
      Require(rp.range.num_buckets <= scratch->range_buckets(),
              at + ": range table wider than level scratch");
      Require(rp.range.num_buckets == rp.plan.range_buckets + rp.direct_buckets,
              at + ": range view not the planned size");
      Require(rp.plan.range_bits + rp.plan.index_bits <= 8 * env.layout.tag_bytes,
              at + ": range plan routes past the tag");
    }
    if (rp.dfs != nullptr) {
      Require(rp.dfs->shape().pool_buckets <= (size_t{1} << 20) &&
                  rp.dfs->pages() == rp.plan.groups,
              at + ": DFS workspace shape");
    }
    passes << (first ? "" : ",") << "{\"pass\":" << p
           << ",\"fuse\":" << unsigned(rp.fuse) << ",\"rule\":" << unsigned(rp.rule)
           << ",\"pool\":" << pool.str() << ",\"drain_only\":" << rp.drain_only
           << ",\"swept_buckets\":" << swept
           << ",\"drain\":\"" << name(rp.drain) << "\""
           << ",\"drain_buckets\":" << (rp.drain ? rp.drain->num_buckets : 0)
           << ",\"sweep_active\":" << (rp.sweep_active ? "true" : "false")
           << ",\"range_buckets\":" << rp.range.num_buckets
           << ",\"scratch_buckets\":" << scratch->range_buckets()
           << ",\"range_bits\":" << rp.plan.range_bits
           << ",\"index_bits\":" << rp.plan.index_bits
           << ",\"groups\":" << rp.plan.groups
           << ",\"direct_buckets\":" << rp.direct_buckets
           << ",\"dfs\":" << (rp.dfs ? "true" : "false")
           << ",\"dfs_units\":" << (rp.dfs ? rp.dfs->Units() : 0)
           << ",\"dfs_coarse_bits\":" << (rp.dfs ? rp.dfs->shape().coarse_bits : 0) << "}";
    first = false;
  }
  passes << "]";

  uint64_t fingerprint = 1469598103934665603ull;
  const auto mix = [&](uint64_t v) {
    fingerprint = (fingerprint ^ v) * 1099511628211ull;
  };
  for (const bs::Subtask& t : plan) {
    mix(t.kind); mix(t.begin); mix(t.end); mix(t.log2_stride); mix(t.levels);
    mix(t.bit); mix(t.pass); mix(t.blank_first);
  }
  for (const bs::PlannedStage& st : stages) {
    mix(st.first_task); mix(st.first_unit); mix(st.mark.lanes);
    mix(st.mark.by_range); mix(st.mark.offer_passes); mix(st.mark.shed_lo);
    mix(st.mark.shed_hi); mix(st.mark.radix_shed); mix(st.mark.merge_shed);
  }
  for (size_t u : units) mix(u);
  const la::MergeShape& shape = job.shape();
  std::printf("{\"kind\":\"phase\",\"job\":\"%s\",\"level\":%u,\"digit\":%u,"
              "\"ordinal\":%llu,\"block_bits\":%u,\"odd_part\":%u,\"out_buckets\":%zu,"
              "\"fingerprint\":\"%016llx\","
              "\"phase\":\"%s\",\"lanes\":%zu,\"tasks\":%zu,\"task_capacity\":%zu,"
              "\"stages\":%zu,\"lane_units\":%zu,\"level_stash_slots\":%zu,"
              "\"lane_mask_stride\":%zu,\"max_offer_stage_range\":%zu,"
              "\"max_radix\":%u,\"max_ways\":%u,\"max_subnetwork_levels\":%u,"
              "\"max_offer_sets\":%u,\"max_offer_groups\":%zu,\"passes\":%s,"
              "\"task_kinds\":{",
              job_kind, level, digit,
              static_cast<unsigned long long>(job.ordinal()), shape.block_bits,
              shape.odd_part, shape.out_buckets,
              static_cast<unsigned long long>(fingerprint),
              la::LevelMergePhaseName(phase), lanes, plan.size(), capacity, stages.size(), units.size(), level_array,
              stride, max_offer_range, max_radix, max_ways, max_subnetwork,
              max_sets, max_groups, passes.str().c_str());
  bool comma = false;
  for (const auto& [k, n] : kinds) {
    std::printf("%s\"%s\":%zu", comma ? "," : "", k.c_str(), n);
    comma = true;
  }
  std::printf("},\"capacity_sites\":[");
  comma = false;
  for (const auto& [key, x] : sites) {
    std::printf("%s{\"kind\":\"%s\",\"storage\":\"%s\",\"slots\":%zu,"
                "\"writers\":%s,\"drain_only\":%s,\"swept\":%s}",
                comma ? "," : "", x.kind.c_str(), x.storage.c_str(), x.slots,
                Json(x.writers).c_str(), x.drain_only ? "true" : "false",
                x.swept ? "true" : "false");
    comma = true;
  }
  std::printf("]}\n");
  job.*Get(PhaseRunningT{}) = false;
}

void Probe(const Env& env, size_t lanes) {
  const la::LevelArenaGeometry& g = *env.g;
  const bs::AesTagKeys& keys = bs::DefaultAesTagKeys();
  for (unsigned l = 1; l <= g.Levels(); ++l) {
    // The engine's per-level scratch (LevelArenaEngine::BuildScratch).
    la::LevelMergeScratch scratch(
        env.layout, la::MaxLevelMergeRangeBuckets(g, *env.sizing, l),
        la::MaxLevelDfsAllocation(g, *env.sizing, l));
    Job job(g, *env.sizing, env.layout, l, keys, lanes);
    const auto& older = job.*Get(OlderT{});
      std::printf("{\"kind\":\"job\",\"level\":%u,\"fanout\":%u,\"lanes\":%zu,\"older_slots\":%zu,"
                "\"stash_buckets\":%zu,\"tier_view_buckets\":%zu,"
                "\"tier_buckets\":%zu,\"scratch_range_buckets\":%zu,\"dfs_workspace\":%s,"
                "\"task_capacity\":%zu,\"dense_masks\":%zu}\n",
                l, l == g.Levels() ? g.TopDigit() : g.Fanout(l), lanes, older.size(),
                env.sizing->Buckets(l),
                (job.*Get(TierViewsT{}))[0].num_buckets, g.TierBucketsOf(l),
                scratch.range_buckets(), scratch.dfs() ? "true" : "false",
                la::LevelPhasePlanCapacity(g, env.layout, l),
                (job.*Get(DenseMasksT{})).size());
    Require(env.sizing->Buckets(l) <= bs::kMaxResidualStashBuckets,
            "stash deeper than inline masks");
    Require(g.TierBucketsOf(l) <= bs::kMaxResidualStashBuckets &&
                g.TierBuckets() <= bs::kMaxResidualStashBuckets,
            "tier deeper than inline masks");
    const unsigned digits = l == g.Levels() ? 1 : g.Fanout(l);
    // Two cycles: a plan must be a function of (level, digit) alone.
    for (unsigned cycle = 0; cycle < 2; ++cycle)
    for (unsigned d = 1; d <= digits; ++d) {
      const uint64_t ordinal = l == g.Levels() ? 1 + cycle : d + cycle * digits;
      const la::CarryPlan cp = g.PlanCarry(l, ordinal);
      const unsigned digit = cp.digit;
      if (cp.outcome == la::CarryOutcome::kAdopt) {
        std::printf("{\"kind\":\"adoption\",\"level\":%u,\"digit\":%u,\"lanes\":%zu,"
                    "\"tier_buckets\":%zu,\"carry_tier_buckets\":%zu}\n",
                    l, digit, lanes, g.OlderTierBuckets(l, 2), g.CarryTierBuckets(l));
        continue;
      }
      const bool top = l == g.Levels();
      const size_t u = g.CarryBuckets(l);
      bs::ResidualStash out_tier = FakeTier(env.layout, g.TierBucketsOf(l), 1);
      bs::ResidualStash older_tier =
          FakeTier(env.layout, g.OlderTierBuckets(l, digit), 2);
      bs::ResidualStash carry_tier = FakeTier(env.layout, g.CarryTierBuckets(l), 3);
      la::LevelMergeBinding b;
      b.ordinal = ordinal;
      b.out = FakeView(env.layout, size_t{digit} * u, 4);
      b.out_tier = &out_tier;
      b.destination_generation = 1;
      if (la::MergeHasOlderHalf(top, digit)) {
        b.older_main = FakeView(env.layout, (top ? digit : digit - 1) * u, 5);
        b.older_tier = &older_tier;
      }
      job.Begin(b);
      const char* kind = top ? "top" : "ordinary";
      if (top) (job.*Get(BuildTopPrepT{}))(&scratch, (job.*Get(PrepCarryT{}))());
      if (top || digit != 1) {
        (job.*Get(StartPhaseT{}))(la::LevelMergePhase::kPrepareOlder, &scratch);
        Record(job, env, &scratch, &out_tier, l, digit, kind,
               la::LevelMergePhase::kPrepareOlder, lanes);
      }
      la::LevelCarry carry;
      carry.ordinal = ordinal;
      std::vector<uint64_t> dense_masks;
      if (l == 1) {
        dense_masks.assign(g.DensePrefixBuckets(), 0);
        carry.dense_prefix = FakeView(env.layout, g.DensePrefixBuckets(), 6);
        carry.dense_prefix.masks = dense_masks.data();
      } else {
        carry.family = job.family();
        carry.main = FakeView(env.layout, u, 7);
        carry.tier = &carry_tier;
      }
      (job.*Get(BindCarryT{}))(carry);
      (job.*Get(StartPhaseT{}))(la::LevelMergePhase::kInstallCarry, &scratch);
      Record(job, env, &scratch, &out_tier, l, digit, kind,
             la::LevelMergePhase::kInstallCarry, lanes);
      (job.*Get(BuildFinishT{}))(&scratch);
      (job.*Get(StartPhaseT{}))(la::LevelMergePhase::kFinish, &scratch);
      Record(job, env, &scratch, &out_tier, l, digit, kind,
             la::LevelMergePhase::kFinish, lanes);
      job.Cancel();
    }
    if (l == g.Levels()) {
      // Direct initialization, exactly RouteInitialTop's steps without the run.
      bs::ResidualStash out_tier = FakeTier(env.layout, g.TierBucketsOf(l), 1);
      la::LevelMergeBinding b;
      b.ordinal = 1;
      b.out = FakeView(env.layout, g.TopBuckets(), 4);
      b.out_tier = &out_tier;
      b.destination_generation = 1;
      b.older_main = b.out;
      job.*Get(InitializingT{}) = true;
      job.Begin(b);
      (job.*Get(PrepareCtxT{})).source_in_place = true;
      (job.*Get(BuildTopPrepT{}))(&scratch, &out_tier);
      (job.*Get(StartPhaseT{}))(la::LevelMergePhase::kPrepareOlder, &scratch);
      Record(job, env, &scratch, &out_tier, l, g.TopDigit(), "initialization",
             la::LevelMergePhase::kPrepareOlder, lanes);
      job.*Get(InitializingT{}) = false;
      job.Cancel();
    }
  }
}

}  // namespace

int main(int argc, char** argv) {
  try {
    // Eight public parameters, then the fanout ladder for levels 1..L-1
    // ("4,4,4,8,8,8"), "-" for the uniform ladder -- configuration_probe.cpp's
    // spelling.  The library runs one residual routing (separated sources,
    // one-page DFS top preparation), so there is no routing argument.
    if (argc != 10)
      throw std::invalid_argument("expected eight public parameters and a fanout ladder");
    la::LevelArenaGeometry::Params p;
    p.branching = std::stoul(argv[1]);
    p.levels = std::stoul(argv[2]);
    p.top_digit = std::stoul(argv[3]);
    p.prefix_flushes = std::stoul(argv[4]);
    p.stash_buckets = std::stoull(argv[5]);
    p.dense_prefixes = std::stoul(argv[6]);
    p.tier_buckets = std::stoull(argv[7]);
    const uint64_t horizon = std::stoull(argv[8]);
    if (std::string(argv[9]) != "-") {
      const std::string ladder = argv[9];
      size_t at = 0;
      while (at <= ladder.size()) {
        const size_t comma = std::min(ladder.find(',', at), ladder.size());
        size_t used = 0;
        const std::string item = ladder.substr(at, comma - at);
        const unsigned long fanout = std::stoul(item, &used);
        if (used != item.size()) throw std::invalid_argument("malformed fanout ladder");
        p.level_fanouts.push_back(static_cast<unsigned>(fanout));
        at = comma + 1;
      }
    }
    Env env;
    p = la::ResolveLevelArenaTierGeometry(p, horizon);
    const la::LevelArenaGeometry g(p);
    const la::LevelArenaStashSizing sizing(g, horizon);
    env.g = &g;
    env.sizing = &sizing;
    // No count depends on the value width; 8-byte keys and values, the
    // engine's own derivation of the stored layout.
    env.layout = la::LevelArenaStoredLayout(8, 8, g);
    const la::InitialSeed seed = la::DirectInitializationSeed(g);
    std::printf("{\"kind\":\"geometry\",\"levels\":%u,\"top_buckets\":%zu,"
                "\"tier_buckets\":%zu,\"key_bytes\":%zu,\"value_bytes\":%zu,"
                "\"tag_bytes\":%zu,\"digit_bits\":%zu,\"bank_first\":%u,"
                "\"capacity_entries\":%llu,\"online_stash_entries\":%zu,"
                "\"prefix_positions\":%llu,\"dense_prefixes\":%u,"
                "\"seed_prefixes\":%llu,\"seed_access_offset\":%llu,"
                "\"max_family_ordinal\":%llu,\"max_family_level\":%llu}\n",
                g.Levels(), g.TopBuckets(), g.TierBuckets(), env.layout.key_bytes,
                env.layout.value_bytes, env.layout.tag_bytes, env.layout.digit_bits,
                unsigned(p.bank_first),
                static_cast<unsigned long long>(g.CapacityEntries()),
                g.OnlineStashEntries(),
                static_cast<unsigned long long>(g.PrefixPositions()),
                unsigned(g.DensePrefixes()),
                static_cast<unsigned long long>(seed.prefixes),
                static_cast<unsigned long long>(seed.access_offset),
                static_cast<unsigned long long>(la::kMaxFamilyOrdinal),
                static_cast<unsigned long long>(la::kMaxFamilyLevel));
    for (unsigned l = 1; l <= g.Levels(); ++l) {
      // The last ordinal any job through the horizon can bind (Proposition
      // "ordinal-exposures"), after a direct initialization's seed, and the
      // nonce family it uses: FamilyId refuses exhaustion, so evaluating it
      // at the largest ordinal checks the field.
      const uint64_t positions = la::CheckedMul(32, g.CarryBuckets(l), "positions");
      const uint64_t last = seed.level_carries[l] + horizon / positions + 1;
      const la::Family f = la::CanonicalFamily(g, l, last);
      (void)la::FamilyId(f);
      std::printf("{\"kind\":\"ordinal\",\"level\":%u,\"carry_positions\":%llu,"
                  "\"seeded\":%llu,\"last_ordinal\":%llu,\"family_level\":%u,"
                  "\"family_ordinal\":%llu}\n",
                  l, static_cast<unsigned long long>(positions),
                  static_cast<unsigned long long>(seed.level_carries[l]),
                  static_cast<unsigned long long>(last), f.level,
                  static_cast<unsigned long long>(f.ordinal));
    }
    for (size_t lanes : {size_t{1}, size_t{64}}) Probe(env, lanes);
    for (const std::string& v : g_violations)
      std::printf("{\"kind\":\"violation\",\"what\":\"%s\"}\n", v.c_str());
    std::printf("{\"kind\":\"summary\",\"checks\":%zu,\"violations\":%zu}\n",
                g_checks, g_violations.size());
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 2;
  }
}
