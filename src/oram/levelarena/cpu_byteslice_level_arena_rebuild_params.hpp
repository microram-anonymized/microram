#pragma once

// THE REBUILD'S PARAMETERS AS ONE VALUE, AND THE HEURISTIC THAT CHOOSES THEM
// (DESIGN.md, "Publication, readers and progress", summarizes the result).
// None of these choices affects what is stored or which buckets an access
// touches; they decide only which thread runs which level, and when.
//
// WHAT IS CHOSEN.  How the levels are divided among owner threads, how many
// helper threads the top's group gets and how many lanes its stages run at,
// the request rate the rebuild's pieces are sized for, and the inline
// executor's share per flush.  `LevelArenaRebuildParams` holds all of it and
// `ApplyRebuildParams` (cpu_byteslice_level_arena_engine.hpp) puts it on an
// engine's Options.
//
// WHO CHOOSES IT.  `HeuristicRebuildParams`, from public sizes, a thread
// budget and a cost model (LevelArenaRebuildCost).  The model's defaults are
// calibration constants fitted on one development machine; they are a
// starting point, not a property of the design.  A target's model comes from
// the tuner (`python3 -m analysis.oram_bench fit-rebuild`,
// analysis/oram_bench/tuner.py), which fits it to the level-arena
// benchmark's `--fit-rows` on that machine; the heuristic then divides every
// geometry by it, and the engine takes the result without asking how it was
// chosen.
//
// THE COST MODEL.  A level's average rebuild cost per access is
//
//     (routing x line_picos + residual x residual_line_picos
//        + offers x offer_line_picos) x lines / 1000  +  jobs x job_nanos
//
// where `routing` is the routing work its planners count per access
// (LevelArenaPrefixTouches), `residual` and `offers` its residual passes'
// sweeps and the offers they add under the certified residual routing
// (LevelArenaResidualPrefixTouchSplit), `lines` the 64-byte lines of a bucket
// and `jobs` the carries it absorbs per access.  The three touch terms cost
// differently per line: a route streams the level's tables, a sweep passes
// over stash-sized buffers that stay in cache, an offer merges a pool bucket
// into a main bucket.  The residual terms are separate from the per-job term
// because a DFS or direct finish's partition and offers grow with the main;
// folding them into a per-job constant would underprice the middle levels
// and group them onto too few threads.
//
// The model has no term for a table's size against the cache, so it fits
// cache-resident levels (level 1, and sometimes the top) less closely than
// the middle levels.  It only has to rank divisions of the levels, not
// predict throughput.
//
// THE GROUPING RULE.  Contiguous groups -- neighbours -- chosen to minimise
// the largest group's DEMAND,
//
//     demand = sum of its members' costs
//              + middle_burst x its largest middle level's cost,
//                unless the group holds the top,
//
// and then, among the divisions that reach that, the sum of squared demands,
// so the groups that do not bind are left balanced.  The second term is a
// worst-case correction folded into one number: a middle level's work is
// linear in its digit, so its heaviest carries arrive together and a group of
// middle levels needs headroom above its average rate to meet its deadlines
// (EDF, earliest deadline first, is how a group orders its members).  Level 1
// and the top have flat per-carry work, and a group that holds the top
// absorbs a bursty neighbour, because the top's deadline is far enough away
// for EDF to run it around the burst.  This simple rule agrees with a
// per-digit processor-demand analysis on the configurations it was checked
// against.
//
// THREADS BEYOND THE GROUPS.  Only the top's group can use more than one
// thread: its stages run in lanes that helper threads share (DESIGN.md,
// "Carries and preparation"),
// at `helper_speedup_ppm` per doubling of its threads, up to
// `max_top_threads`.  So each budget is tried as every split into groups and
// helpers, and a thread is spent only if it lowers the bottleneck by more
// than `thread_gain_floor_ppm` (all in LevelArenaRebuildCost).

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// The model's constants (calibration defaults; see the header)
// ---------------------------------------------------------------------------

// THE COST MODEL AS ONE VALUE.  The defaults are calibration constants from
// one development machine (the header); a target's come from the tuner, which fits them to the
// level-arena benchmark's `--fit-rows` output (analysis/oram_bench/tuner.py)
// and ships them as resolver overrides (`rebuild_cost_*`).  Integers, so that
// a resolved plan names its model exactly.
struct LevelArenaRebuildCost {
  // A level's cost per access is touch_lines x line + residual_lines x
  // residual_line + offer_lines x offer_line + jobs x job
  // (LevelRebuildFeatures): picoseconds per 64-byte line its routing
  // touches, per line its residual passes sweep, per line their offers merge
  // into the main, and nanoseconds per job it runs.
  uint64_t line_picos = 845;
  uint64_t residual_line_picos = 397;
  uint64_t offer_line_picos = 1696;
  uint64_t job_nanos = 2659;
  // A group of middle levels, at its worst, as a fraction of its largest
  // middle member's average cost (the header's grouping rule): the headroom
  // a group needs when it meets its deadlines at about 77% of its average
  // rate, 1/0.77 - 1.
  uint64_t middle_burst_ppm = 300000;
  // The top's lanes on m threads run 1 + s log2 m times as fast (a
  // calibration constant; the tuner refits it).
  uint64_t helper_speedup_ppm = 550000;
  // The most threads the top's group is given, its owner included.  The log
  // curve above would keep buying threads for ever, and the top eventually
  // streams from DRAM with no more bandwidth to take.  Where that happens is
  // a property of the machine's memory bandwidth, not of how many cores one
  // L3 holds; the default is one 8-core L3 domain.  The tuner sets it from
  // where a measured doubling stops paying.
  unsigned max_top_threads = 8;
  // A thread is spent only if it lowers the bottleneck demand by more than
  // this fraction: two configurations the model cannot tell apart are not
  // worth a core.  A policy, not a measurement.
  uint64_t thread_gain_floor_ppm = 10000;
  // THE SEQUENTIAL REQUESTER'S PROBE COST, for the rate the rebuild's pieces
  // are sized for: an access probes about 2L + 2 buckets (the cascade sampled
  // at B = 4 and 8, L = 4..8), each at `probe_bucket_picos` plus
  // `probe_line_picos` per 64-byte line.  Fitted to the cache-resident
  // shapes, so that the rate it gives is close to, or ABOVE, what one
  // requester reaches, and further above it once the tables no longer fit
  // the cache.  A rate that is too high only cuts the
  // pieces finer; one that is too low lets a piece outlast the smallest
  // level's window.  The tuner keeps that side: it scales its fit so that the
  // modeled cost is at most every measured one.
  uint64_t probe_bucket_picos = 20000;
  uint64_t probe_line_picos = 450;
  // WHAT A PIECE'S BUCKET TOUCH IS BUDGETED AT, per 64-byte line, when an
  // owner cuts a phase into pieces for the slice limit (SliceTouches).  The
  // worst line cost rather than the average `line_picos`, because a piece that
  // costs more than budgeted overruns its window and stalls the requester.
  uint64_t slice_line_picos = 1500;

  double NanosPerLine() const { return double(line_picos) / 1000.0; }
  double NanosPerResidualLine() const {
    return double(residual_line_picos) / 1000.0;
  }
  double NanosPerOfferLine() const { return double(offer_line_picos) / 1000.0; }
  double NanosPerJob() const { return double(job_nanos); }
  double MiddleLevelBurst() const { return double(middle_burst_ppm) / 1e6; }
  double HelperSpeedupPerDoubling() const {
    return double(helper_speedup_ppm) / 1e6;
  }
  double ThreadGainFloor() const { return double(thread_gain_floor_ppm) / 1e6; }
  double ProbeNanosPerBucket() const {
    return double(probe_bucket_picos) / 1000.0;
  }
  double ProbeNanosPerLine() const { return double(probe_line_picos) / 1000.0; }
  double SliceNanosPerLine() const { return double(slice_line_picos) / 1000.0; }

  void Validate() const {
    if (max_top_threads == 0) {
      throw std::invalid_argument(
          "level arena: the rebuild cost model's max_top_threads must be at "
          "least one (the top's owner)");
    }
    if (line_picos == 0 && residual_line_picos == 0 && offer_line_picos == 0 &&
        job_nanos == 0) {
      throw std::invalid_argument(
          "level arena: the rebuild cost model prices no rebuild work");
    }
    if (probe_bucket_picos == 0 && probe_line_picos == 0) {
      throw std::invalid_argument(
          "level arena: the rebuild cost model prices no probe work");
    }
    if (slice_line_picos == 0) {
      throw std::invalid_argument(
          "level arena: the rebuild cost model budgets a piece's line at zero");
    }
    if (thread_gain_floor_ppm >= 1000000) {
      throw std::invalid_argument(
          "level arena: a thread gain floor of 100% or more spends no thread");
    }
  }
};

static_assert(LevelArenaRebuildCost{}.slice_line_picos ==
                  static_cast<uint64_t>(kSliceNanosPerTouchLine * 1000),
              "the cost model's slice default is SliceTouches' default");

// ---------------------------------------------------------------------------
// The model
// ---------------------------------------------------------------------------

// WHAT A LEVEL'S RESIDUAL PASSES ARE COUNTED FROM, beside the geometry: the
// request horizon their stash depths are certified for.  The default is the
// engine's; every caller that builds or plans an engine passes its own.
struct LevelResidualInputs {
  uint64_t max_accesses = uint64_t{1} << 32;
};

// THE MODEL'S INPUTS FOR ONE LEVEL, per access: the 64-byte lines its
// routing touches, the lines its residual passes sweep and the lines their
// offers merge (LevelArenaResidualPrefixTouchSplit), and the jobs it runs.
// The model and the tuner's fit both read them from here, so the fitted
// constants price exactly what the model counts.
struct LevelCostFeatures {
  double touch_lines = 0;     // the routing planners' (LevelArenaPrefixTouches)
  double residual_lines = 0;  // the residual passes', offers aside
  double offer_lines = 0;     // the offers the residual passes add
  double jobs = 0;
};

inline LevelCostFeatures LevelRebuildFeatures(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, unsigned level) {
  const double lines = double(layout.BucketBytes()) / 64.0;
  const double accesses_per_prefix = double(geometry.PrefixPositions());
  const double routed =
      LevelArenaPrefixTouches(geometry, layout, level) / accesses_per_prefix;
  const ResidualTouchSplit residual =
      LevelArenaResidualPrefixTouchSplit(geometry, layout, sizing, level);
  // One job per carry absorbed; level 1's carries are the prefixes.
  const double jobs = 1.0 / (double(geometry.PrefixProduct(level)) *
                             accesses_per_prefix);
  return {routed * lines, residual.passes / accesses_per_prefix * lines,
          residual.offers / accesses_per_prefix * lines, jobs};
}

inline LevelCostFeatures LevelRebuildFeatures(
    const LevelArenaGeometry& geometry, const Layout& layout, unsigned level,
    const LevelResidualInputs& residual = {}) {
  const LevelArenaStashSizing sizing(geometry, residual.max_accesses);
  return LevelRebuildFeatures(geometry, layout, sizing, level);
}

inline double LevelRebuildNanos(const LevelCostFeatures& f,
                                const LevelArenaRebuildCost& cost) {
  return f.touch_lines * cost.NanosPerLine() +
         f.residual_lines * cost.NanosPerResidualLine() +
         f.offer_lines * cost.NanosPerOfferLine() + f.jobs * cost.NanosPerJob();
}

// Level `level`'s average rebuild cost, in nanoseconds per access.
inline double LevelRebuildNanosPerAccess(
    const LevelArenaGeometry& geometry, const Layout& layout, unsigned level,
    const LevelArenaRebuildCost& cost = {},
    const LevelResidualInputs& residual = {}) {
  return LevelRebuildNanos(
      LevelRebuildFeatures(geometry, layout, level, residual), cost);
}

// THE PROBE MODEL'S INPUTS, per access: buckets probed, and buckets times
// their 64-byte lines.
struct ProbeCostFeatures {
  double buckets = 0;
  double bucket_lines = 0;
};

inline ProbeCostFeatures SaturatedProbeFeatures(const LevelArenaGeometry& geometry,
                                                const Layout& layout) {
  const double buckets = 2.0 * double(geometry.Levels()) + 2.0;
  return {buckets, buckets * double(layout.BucketBytes()) / 64.0};
}

// THE RATE ONE SEQUENTIAL REQUESTER SATURATES AT, in accesses per second
// (see LevelArenaRebuildCost::probe_bucket_picos).  It is what the rebuild's
// pieces are sized for by default: a closed-loop caller issuing its next
// request as soon as the last returns, which is the fastest the dense
// prefixes can fill and so the tightest every level's window gets.
inline double SaturatedOnlineRate(const LevelArenaGeometry& geometry,
                                  const Layout& layout,
                                  const LevelArenaRebuildCost& cost = {}) {
  const ProbeCostFeatures f = SaturatedProbeFeatures(geometry, layout);
  const double nanos = f.buckets * cost.ProbeNanosPerBucket() +
                       f.bucket_lines * cost.ProbeNanosPerLine();
  return 1e9 / nanos;
}

// What `threads` threads on the top's lanes are worth, against one.
inline double HelperSpeedup(unsigned threads,
                            const LevelArenaRebuildCost& cost = {}) {
  return threads <= 1 ? 1.0
                      : 1.0 + cost.HelperSpeedupPerDoubling() *
                                  std::log2(double(threads));
}

// Every level's cost, and whether its stages can take lanes (a table of at
// least the default LevelLaneConfig::min_buckets), indexed by level.
struct LevelLoadModel {
  unsigned levels = 0;
  LevelArenaRebuildCost model_cost;
  std::vector<double> cost;       // ns per access; [0] unused
  std::vector<bool> takes_lanes;  // [0] unused

  LevelLoadModel(const LevelArenaGeometry& geometry, const Layout& layout,
                 const LevelArenaRebuildCost& rebuild_cost = {},
                 const LevelResidualInputs& residual = {})
      : levels(geometry.Levels()),
        model_cost(rebuild_cost),
        cost(geometry.Levels() + 1, 0.0),
        takes_lanes(geometry.Levels() + 1, false) {
    model_cost.Validate();
    const LevelArenaStashSizing sizing(geometry, residual.max_accesses);
    LevelLaneConfig probe;
    probe.lanes = 2;
    for (unsigned l = 1; l <= levels; ++l) {
      cost[l] = LevelRebuildNanos(
          LevelRebuildFeatures(geometry, layout, sizing, l), model_cost);
      takes_lanes[l] = LevelLaneCount(geometry, l, probe) > 1;
    }
  }

  // The DEMAND of the group [first, last] (see the header), with the top's
  // group on `top_threads` threads.
  double Demand(unsigned first, unsigned last, unsigned top_threads) const {
    const bool holds_top = last == levels;
    const double speedup = HelperSpeedup(top_threads, model_cost);
    double sum = 0;
    double burst = 0;
    for (unsigned l = first; l <= last; ++l) {
      sum += holds_top && takes_lanes[l] ? cost[l] / speedup : cost[l];
      if (l != 1 && l != levels) burst = std::max(burst, cost[l]);
    }
    return holds_top ? sum : sum + model_cost.MiddleLevelBurst() * burst;
  }
};

// ---------------------------------------------------------------------------
// The division of the levels
// ---------------------------------------------------------------------------

// One division and what the model says of it.
struct LevelDivision {
  std::vector<LevelGroupPlan> groups;  // highest first
  double bottleneck = std::numeric_limits<double>::infinity();
  double squares = std::numeric_limits<double>::infinity();

  bool found() const { return !groups.empty(); }
  // Lower bottleneck first, then better balanced.
  bool BetterThan(const LevelDivision& other) const {
    if (!found()) return false;
    if (!other.found()) return true;
    if (bottleneck != other.bottleneck) return bottleneck < other.bottleneck;
    return squares < other.squares;
  }
};

namespace rebuild_params_detail {

// Levels [lo, hi] in exactly `k` contiguous groups: the smallest largest
// demand, then the smallest sum of squared demands among the divisions whose
// every group stays within `cap` (the first pass's bottleneck when `cap` is
// negative).  Two dynamic programs over prefixes of the range, O(n^2 k).
inline LevelDivision DivideRange(const LevelLoadModel& model, unsigned lo,
                                 unsigned hi, unsigned k, unsigned top_threads,
                                 double cap = -1.0) {
  LevelDivision out;
  const unsigned n = hi + 1 - lo;
  if (k == 0 || k > n) return out;
  constexpr double kInf = std::numeric_limits<double>::infinity();
  const auto demand = [&](unsigned from, unsigned to) {  // offsets in [0, n)
    return model.Demand(lo + from, lo + to, top_threads);
  };
  // best[j][i]: groups 1..j over the first i levels of the range.
  std::vector<std::vector<double>> best(k + 1,
                                        std::vector<double>(n + 1, kInf));
  if (cap < 0) {
    best[0][0] = 0;
    for (unsigned j = 1; j <= k; ++j) {
      for (unsigned i = j; i <= n; ++i) {
        for (unsigned p = j - 1; p < i; ++p) {
          if (best[j - 1][p] == kInf) continue;
          best[j][i] = std::min(best[j][i],
                                std::max(best[j - 1][p], demand(p, i - 1)));
        }
      }
    }
    cap = best[k][n];
  }
  // The rounding slack admits the first pass's own optimum exactly.
  const double limit = cap * (1.0 + 1e-12);
  std::vector<std::vector<double>> squares(k + 1,
                                           std::vector<double>(n + 1, kInf));
  std::vector<std::vector<unsigned>> parent(k + 1,
                                            std::vector<unsigned>(n + 1, 0));
  squares[0][0] = 0;
  for (unsigned j = 1; j <= k; ++j) {
    for (unsigned i = j; i <= n; ++i) {
      for (unsigned p = j - 1; p < i; ++p) {
        if (squares[j - 1][p] == kInf) continue;
        const double d = demand(p, i - 1);
        if (d > limit) continue;
        const double s = squares[j - 1][p] + d * d;
        if (s < squares[j][i]) {
          squares[j][i] = s;
          parent[j][i] = p;
        }
      }
    }
  }
  if (squares[k][n] == kInf) return out;
  out.squares = squares[k][n];
  out.bottleneck = 0;
  // Walk back from the top of the range, which is also the order the groups
  // are listed in: highest first.
  unsigned i = n;
  for (unsigned j = k; j >= 1; --j) {
    const unsigned p = parent[j][i];
    out.groups.push_back(LevelGroupPlan{lo + p, lo + i - 1});
    out.bottleneck = std::max(out.bottleneck, demand(p, i - 1));
    i = p;
  }
  return out;
}

// Two divisions of the two sides of a boundary, far (above it) first.
inline LevelDivision Join(const LevelDivision& far, const LevelDivision& near) {
  LevelDivision out;
  if (!far.found() || !near.found()) return out;
  out.groups = far.groups;
  out.groups.insert(out.groups.end(), near.groups.begin(), near.groups.end());
  out.bottleneck = std::max(far.bottleneck, near.bottleneck);
  out.squares = far.squares + near.squares;
  return out;
}

// `groups` groups over every level.  With a boundary strictly inside the
// hierarchy no group straddles it (cpu_byteslice_level_arena_placement.hpp),
// except that one group holds
// everything; `near_cap` and `far_cap` bound how many groups each side may
// have, 0 meaning no bound.
inline LevelDivision SearchDivision(const LevelLoadModel& model,
                                    unsigned groups, unsigned near_max_level,
                                    unsigned top_threads, unsigned near_cap = 0,
                                    unsigned far_cap = 0) {
  const unsigned levels = model.levels;
  const bool split = near_max_level >= 1 && near_max_level < levels;
  // One group over a split straddles it, and is far because its top is;
  // any far cap a caller passes is at least that one group.
  if (!split || groups == 1) {
    return DivideRange(model, 1, levels, groups, top_threads);
  }
  LevelDivision best;
  for (unsigned near = 1; near < groups; ++near) {
    const unsigned far = groups - near;
    if (near > near_max_level || far > levels - near_max_level) continue;
    if (near_cap != 0 && near > near_cap) continue;
    if (far_cap != 0 && far > far_cap) continue;
    const LevelDivision far_first = DivideRange(
        model, near_max_level + 1, levels, far, top_threads);
    const LevelDivision near_first =
        DivideRange(model, 1, near_max_level, near, top_threads);
    if (!far_first.found() || !near_first.found()) continue;
    // Rebalance both sides against the joint bottleneck.
    const double cap = std::max(far_first.bottleneck, near_first.bottleneck);
    const LevelDivision joined = Join(
        DivideRange(model, near_max_level + 1, levels, far, top_threads, cap),
        DivideRange(model, 1, near_max_level, near, top_threads, cap));
    if (joined.BetterThan(best)) best = joined;
  }
  return best;
}

}  // namespace rebuild_params_detail

// THE DIVISION AN ENGINE IS BUILT WITH when its caller names no other:
// `threads` contiguous groups, highest first, by the grouping rule of the
// header, with the top's group on `top_threads` threads (its owner and its
// helpers).  With a near/far boundary strictly inside the hierarchy no group
// straddles it, except when one group holds everything.
//
// Refused rather than clamped when `threads` exceeds the levels: an owner
// thread with no level to drive would park forever.
inline std::vector<LevelGroupPlan> PlanLevelGroups(
    const LevelArenaGeometry& geometry, const Layout& layout, unsigned threads,
    unsigned near_max_level = 0, unsigned top_threads = 1,
    const LevelArenaRebuildCost& cost = {},
    const LevelResidualInputs& residual = {}) {
  if (threads == 0 || threads > geometry.Levels()) {
    throw std::invalid_argument(
        "level arena: owner threads must be between one and the number of "
        "levels; a thread with no level to drive would park forever");
  }
  if (near_max_level > geometry.Levels()) {
    throw std::invalid_argument(
        "level arena: the near/far boundary must be a level of this "
        "hierarchy");
  }
  const LevelLoadModel model(geometry, layout, cost, residual);
  const LevelDivision division = rebuild_params_detail::SearchDivision(
      model, threads, near_max_level, std::max(1u, top_threads));
  if (!division.found()) {
    throw std::logic_error("level arena: no division of the levels was found");
  }
  return division.groups;
}

// ---------------------------------------------------------------------------
// The parameter struct and the heuristic
// ---------------------------------------------------------------------------

// WHAT A REBUILD MAY USE.  `threads` is every thread the rebuild may run on,
// owners and helpers alike, and not the request thread or its batch
// participants.  The rest is the cache-domain split
// (cpu_byteslice_level_arena_placement.hpp): with a boundary
// strictly inside the hierarchy, the groups at or below it are NEAR (placed on
// the request thread's domain) and the rest FAR, and each side may be capped
// at the cores its domains have left.  The top's helpers sit with the top's
// group, which is far whenever there is a split.
struct LevelArenaThreadBudget {
  unsigned threads = 0;         // 0 is the inline executor
  unsigned near_max_level = 0;  // 0: one domain, nothing is near or far
  unsigned near_threads = 0;    // cap on near groups; 0 is no cap
  unsigned far_threads = 0;     // cap on far groups plus helpers; 0 is no cap
};

// Everything the rebuild runs with.  Produced by `HeuristicRebuildParams`
// (over a cost model the tuner may refit per target) or stated explicitly;
// applied with `ApplyRebuildParams`.
struct LevelArenaRebuildParams {
  // One group per owner thread, highest first.  Empty is the inline
  // executor: the request thread runs the rebuild at its flushes.
  std::vector<LevelGroupPlan> groups;
  // Helper threads on the top's group, and the lanes they share.  Lanes go
  // to the top's group only: `lanes.min_buckets` is its smallest laned table.
  unsigned top_helpers = 0;
  LevelLaneConfig lanes;
  // The request rate the owner groups size their pieces for.
  double slice_target_rate = 0;
  // The inline executor's share per flush (Options::inline_work_factor).
  double inline_work_factor = kLevelArenaInlineWorkFactor;
  // The near/far boundary the groups respect, 0 for none.
  unsigned near_max_level = 0;
  // What the model predicts: the largest group demand in ns per access, and
  // so the rebuild capacity 1e9 / demand_nanos in accesses per second.  0 for
  // the inline executor, which has no groups to compare.
  double demand_nanos = 0;

  unsigned threads() const {
    return static_cast<unsigned>(groups.size()) + top_helpers;
  }
};

// THE HEURISTIC: the division, helpers and lanes that minimise the model's
// bottleneck for this budget, spending a thread only where it pays (see the
// header), and the slice rate of a saturated sequential requester.
inline LevelArenaRebuildParams HeuristicRebuildParams(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaThreadBudget& budget,
    const LevelArenaRebuildCost& cost = {},
    const LevelResidualInputs& residual = {}) {
  const unsigned levels = geometry.Levels();
  if (budget.near_max_level > levels) {
    throw std::invalid_argument(
        "level arena: the near/far boundary must be a level of this "
        "hierarchy");
  }
  cost.Validate();
  LevelArenaRebuildParams params;
  params.slice_target_rate = SaturatedOnlineRate(geometry, layout, cost);
  params.near_max_level = budget.near_max_level;
  if (budget.threads == 0) return params;

  const LevelLoadModel model(geometry, layout, cost, residual);
  const bool split =
      budget.near_max_level >= 1 && budget.near_max_level < levels;
  struct Candidate {
    LevelDivision division;
    unsigned helpers = 0;
    unsigned threads() const {
      return static_cast<unsigned>(division.groups.size()) + helpers;
    }
  };
  std::vector<Candidate> candidates;
  for (unsigned helpers = 0;
       helpers < budget.threads && helpers < cost.max_top_threads; ++helpers) {
    // Helpers need a laned table in the top's group; the top is the largest.
    if (helpers > 0 && !model.takes_lanes[levels]) break;
    for (unsigned groups = 1; groups <= std::min(levels, budget.threads - helpers);
         ++groups) {
      // ONE GROUP OVER A SPLIT straddles it and is far, which leaves the near
      // side empty: that is only acceptable for a single thread, which has
      // nowhere else to go (PlanNearFarPlacement refuses it otherwise).
      if (split && groups == 1 && budget.threads > 1) continue;
      unsigned near_cap = split ? budget.near_threads : 0;
      unsigned far_cap = 0;
      if (split && budget.far_threads != 0) {
        if (helpers >= budget.far_threads) continue;
        far_cap = budget.far_threads - helpers;
      }
      if (!split && budget.near_max_level == levels &&
          budget.near_threads != 0 && groups + helpers > budget.near_threads) {
        continue;  // everything near: the near domain holds every thread
      }
      Candidate c;
      c.helpers = helpers;
      c.division = rebuild_params_detail::SearchDivision(
          model, groups, budget.near_max_level, 1 + helpers, near_cap,
          far_cap);
      if (c.division.found()) candidates.push_back(std::move(c));
    }
  }
  if (candidates.empty()) {
    throw std::invalid_argument(
        "level arena: no division of the levels fits this thread budget and "
        "its cache-domain caps");
  }
  double floor = std::numeric_limits<double>::infinity();
  for (const Candidate& c : candidates) {
    floor = std::min(floor, c.division.bottleneck);
  }
  // The FEWEST threads within the thread gain floor of the best, then the lower
  // bottleneck, the better balance, and fewer helpers.
  const Candidate* chosen = nullptr;
  for (const Candidate& c : candidates) {
    if (c.division.bottleneck > floor * (1.0 + cost.ThreadGainFloor())) continue;
    if (chosen == nullptr || c.threads() < chosen->threads() ||
        (c.threads() == chosen->threads() &&
         (c.division.BetterThan(chosen->division) ||
          (!chosen->division.BetterThan(c.division) &&
           c.helpers < chosen->helpers)))) {
      chosen = &c;
    }
  }
  params.groups = chosen->division.groups;
  params.top_helpers = chosen->helpers;
  params.demand_nanos = chosen->division.bottleneck;
  if (params.top_helpers > 0) {
    // Twice as many lanes as threads, so a preempted lane has somewhere to
    // go, and at least four, the lane count the helper speedup was
    // calibrated at.
    params.lanes.lanes =
        std::min<size_t>(64, std::max<size_t>(4, 2 * (1 + params.top_helpers)));
    const LevelGroupPlan& top = params.groups.front();
    size_t smallest = std::numeric_limits<size_t>::max();
    for (unsigned l = top.first; l <= top.last; ++l) {
      if (!model.takes_lanes[l]) continue;
      smallest = std::min(smallest,
                          l == levels ? geometry.TopBuckets()
                                      : geometry.CarryBuckets(l) *
                                            geometry.Fanout(l));
    }
    params.lanes.min_buckets = std::max(params.lanes.min_buckets, smallest);
  }
  return params;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
