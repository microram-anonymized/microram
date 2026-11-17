// THE REBUILD'S PARAMETERS: the load model, the grouping rule and the thread
// budget heuristic of cpu_byteslice_level_arena_rebuild_params.hpp.  The
// heuristic divides the hierarchy's levels into contiguous GROUPS, one owner
// thread each, so that the largest group's per-flush demand (a static cost
// model counted from the routing planners) is as small as possible, and adds
// helper threads and lanes to the top's group once it is the bottleneck
// (src/oram/levelarena/DESIGN.md, "Publication, readers and progress").
//
// Everything here is a pure function of public sizes, so what is checked is
// the POLICY: that the division is always one the engine can build, that it
// is the pinned division at three reference shapes (the rule's own choices
// under the certified routing, which prices every pass the engine runs),
// that threads go where the model says they pay, and that whatever the
// heuristic chooses an engine really builds.  Whether the
// model's constants are right for a machine is the tuner's question, not
// this file's.

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_rebuild_params.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
using G = la::LevelGroupPlan;

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

std::string Describe(const std::vector<G>& groups) {
  std::string out;
  for (const G& g : groups) {
    out += "{" + std::to_string(g.first) + "-" + std::to_string(g.last) + "}";
  }
  return out;
}

bool Same(const std::vector<G>& a, const std::vector<G>& b) {
  if (a.size() != b.size()) return false;
  for (size_t i = 0; i < a.size(); ++i) {
    if (a[i].first != b[i].first || a[i].last != b[i].last) return false;
  }
  return true;
}

// The geometries the capacity ladder picks for the reference shapes, spelled
// out so a ladder change cannot move the fixtures: 8 B keys, 16 B values,
// r0 = 2, s = 1, q = 2.
struct Shape {
  const char* name;
  la::LevelArenaGeometry::Params params;
};

la::LevelArenaGeometry::Params Params(unsigned branching, unsigned levels,
                                      unsigned top_digit,
                                      std::vector<unsigned> fanouts) {
  la::LevelArenaGeometry::Params p;
  p.branching = branching;
  p.levels = levels;
  p.top_digit = top_digit;
  p.prefix_flushes = 2;
  p.stash_buckets = 1;
  p.dense_prefixes = 2;
  p.level_fanouts = std::move(fanouts);
  return p;
}

const Shape kB8At32M{"B=8 32M", Params(8, 6, 8, {8, 8, 8, 8, 8})};
const Shape kB8At4M{"B=8 4M", Params(8, 5, 8, {8, 8, 8, 8})};
const Shape kB4At4M{"B=4 D=4 4M", Params(4, 8, 4, {2, 4, 4, 4, 4, 4, 4})};

bs::Layout LayoutOf(const la::LevelArenaGeometry& geometry) {
  return la::LevelArenaStoredLayout(8, 16, geometry);
}

// ---------------------------------------------------------------------------
// The model
// ---------------------------------------------------------------------------

void TestModel() {
  const la::LevelArenaGeometry geometry(kB8At32M.params);
  Expect(geometry.CapacityEntries() == uint64_t{1} << 25,
         "the 32M fixture is not the ladder's 32M geometry");
  const bs::Layout layout = LayoutOf(geometry);
  const la::LevelLoadModel model(geometry, layout);
  // The shape of the certified routing's costs: the top is the heaviest
  // level, level 1 -- its dense build, a job per prefix and its one-page DFS
  // finish over the whole of U_1 -- the next, and the middle levels grow with
  // their routing depth.  (These are the model's relative costs; how well
  // they match a given machine is for the tuner to calibrate.)
  for (unsigned l = 1; l < geometry.Levels(); ++l) {
    Expect(model.cost[geometry.Levels()] > model.cost[l],
           "the top is not the heaviest level");
  }
  for (unsigned l = 3; l + 1 < geometry.Levels(); ++l) {
    Expect(model.cost[l + 1] > model.cost[l],
           "a middle level costs less than the one below it");
  }
  Expect(model.cost[1] > model.cost[2],
         "level 1's per-prefix job and DFS finish are missing");
  // Only tables of at least 2^15 buckets take lanes: level 5 and the top.
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    Expect(model.takes_lanes[l] == (l >= 5),
           "the lane rule moved at level " + std::to_string(l));
  }
  // The flush share is the sum of the per-level counts, routing and residual
  // passes, per flush.  Every level's residual passes are priced: the DFS
  // partition, its leaf tables' offers and the drains grow with the main.
  const la::LevelArenaStashSizing sizing(geometry, uint64_t{1} << 32);
  double per_prefix = 0;
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    const double residual =
        la::LevelArenaResidualPrefixTouches(geometry, layout, sizing, l);
    Expect(residual > 0, "level " + std::to_string(l) + " has no residual work");
    per_prefix += la::LevelArenaPrefixTouches(geometry, layout, l) + residual;
  }
  Expect(std::abs(la::LevelArenaFlushTouches(geometry, layout, sizing) -
                  per_prefix / geometry.PrefixFlushes()) < 1e-6,
         "the flush share is not the sum of the levels' touches");
  // THE SATURATED RATE stays above its calibration lower bounds (below; the
  // model may only overestimate the requester's rate) and of the same order:
  // too high only cuts pieces finer, too low lets them outlast a window.
  const double rate = la::SaturatedOnlineRate(geometry, layout);
  Expect(rate > 1.38e6 && rate < 4e6, "the 32M saturated rate is off scale");
  const la::LevelArenaGeometry small(kB8At4M.params);
  Expect(la::SaturatedOnlineRate(small, LayoutOf(small)) > 2.03e6,
         "the 4M saturated rate is below the measured one");
  // Wider entries probe more lines, so the requester is slower.
  Expect(la::SaturatedOnlineRate(geometry,
                                 la::LevelArenaStoredLayout(8, 64, geometry)) <
             rate,
         "64 B values did not lower the saturated rate");
  Expect(la::HelperSpeedup(1) == 1.0 && la::HelperSpeedup(2) > 1.5 &&
             la::HelperSpeedup(4) > la::HelperSpeedup(2),
         "the helper speedup is not the measured curve");
  std::printf("  the model: the certified routing's shape, the lane rule, the "
              "rate\n");
}

// ---------------------------------------------------------------------------
// The grouping rule
// ---------------------------------------------------------------------------

// THE PINNED PARTITIONS at the reference shapes, under the certified
// routing.  The certified routing's DFS finishes cost more at the lower
// levels than a plain butterfly would, which pulls those levels' group
// boundaries down; level one's direct build is cheaper, which pushes them
// back up.  These are the rule's choices, pinned so that a change to the
// model or the rule is noticed; they are not measured optima, and the
// grouping can be retuned for a target machine.
void TestReviewPartitions() {
  struct Case {
    const Shape* shape;
    unsigned threads;
    std::vector<G> expected;
  };
  const Case cases[] = {
      {&kB8At32M, 2, {G{5, 6}, G{1, 4}}},
      {&kB8At32M, 3, {G{6, 6}, G{3, 5}, G{1, 2}}},
      {&kB8At4M, 2, {G{4, 5}, G{1, 3}}},
      {&kB8At4M, 3, {G{5, 5}, G{3, 4}, G{1, 2}}},
      {&kB4At4M, 2, {G{5, 8}, G{1, 4}}},
  };
  for (const Case& c : cases) {
    const la::LevelArenaGeometry geometry(c.shape->params);
    const std::vector<G> got =
        la::PlanLevelGroups(geometry, LayoutOf(geometry), c.threads);
    Expect(Same(got, c.expected),
           std::string(c.shape->name) + " with " + std::to_string(c.threads) +
               " owners: " + Describe(got) + ", pinned " +
               Describe(c.expected));
  }
  // THREE OWNERS AT B = 4, where the obvious hand division is
  // {8},{4-7},{1-3}.  The rule's own choice must beat that one by its own
  // measure, or it is not a rule at all.
  const la::LevelArenaGeometry b4(kB4At4M.params);
  const la::LevelLoadModel model(b4, LayoutOf(b4));
  const std::vector<G> got = la::PlanLevelGroups(b4, LayoutOf(b4), 3);
  Expect(Same(got, {G{7, 8}, G{3, 6}, G{1, 2}}),
         "B=4 with 3 owners moved: " + Describe(got));
  const auto bottleneck = [&](const std::vector<G>& groups) {
    double worst = 0;
    for (const G& g : groups) {
      worst = std::max(worst, model.Demand(g.first, g.last, 1));
    }
    return worst;
  };
  Expect(bottleneck(got) <= bottleneck({G{8, 8}, G{4, 7}, G{1, 3}}),
         "the rule's B=4 division is worse than the hand division by its own "
         "model");
  // THE NAIVE TOP-DOWN RULE -- the top k-1 levels alone, the rest in one
  // group -- leaves the bottom group overloaded: at B = 8, 32M with two
  // owners this model puts it more than 10 % short of the rule's division.
  const la::LevelArenaGeometry b8(kB8At32M.params);
  const la::LevelLoadModel b8_model(b8, LayoutOf(b8));
  const auto b8_bottleneck = [&](const std::vector<G>& groups) {
    double worst = 0;
    for (const G& g : groups) {
      worst = std::max(worst, b8_model.Demand(g.first, g.last, 1));
    }
    return worst;
  };
  Expect(b8_bottleneck({G{6, 6}, G{1, 5}}) >
             1.10 * b8_bottleneck(la::PlanLevelGroups(b8, LayoutOf(b8), 2)),
         "the top-down rule is not a loss against the planned division");
  std::printf("  the pinned partitions: B=8 at 32M and 4M, B=4 at 4M\n");
}

// EVERY DIVISION IS ONE THE ENGINE TAKES, at every shape, count and
// boundary, and none straddles a boundary strictly inside the hierarchy.
void TestEveryDivisionIsValid() {
  size_t divisions = 0;
  for (unsigned branching : {2u, 4u, 8u}) {
    for (unsigned levels = 2; levels <= 8; ++levels) {
      la::LevelArenaGeometry::Params p;
      p.branching = branching;
      p.levels = levels;
      p.top_digit = branching;
      p.prefix_flushes = 2;
      p.stash_buckets = 1;
      p.dense_prefixes = 2;
      const la::LevelArenaGeometry geometry(p);
      const bs::Layout layout = LayoutOf(geometry);
      for (unsigned threads = 1; threads <= levels; ++threads) {
        for (unsigned boundary = 0; boundary <= levels; ++boundary) {
          const std::vector<G> groups =
              la::PlanLevelGroups(geometry, layout, threads, boundary);
          const std::string where = "B=" + std::to_string(branching) +
                                    " L=" + std::to_string(levels) + " t=" +
                                    std::to_string(threads) + " nb=" +
                                    std::to_string(boundary);
          Expect(groups.size() == threads, where + ": not one group a thread");
          Expect(!Throws([&] { la::ValidateLevelGroups(levels, groups); }),
                 where + ": an invalid division " + Describe(groups));
          if (threads >= 2 && boundary >= 1 && boundary < levels) {
            bool near = false, far = false;
            for (const G& g : groups) {
              Expect(g.last <= boundary || g.first > boundary,
                     where + ": a group straddles the boundary");
              (g.last <= boundary ? near : far) = true;
            }
            Expect(near && far, where + ": a side of the split is empty");
          }
          ++divisions;
          if (failures != 0) return;
        }
      }
    }
  }
  const la::LevelArenaGeometry geometry(kB8At4M.params);
  Expect(Throws([&] { la::PlanLevelGroups(geometry, LayoutOf(geometry), 0); }),
         "zero owner threads was planned");
  Expect(Throws([&] { la::PlanLevelGroups(geometry, LayoutOf(geometry), 6); }),
         "more owner threads than levels was planned");
  Expect(Throws([&] {
           la::PlanLevelGroups(geometry, LayoutOf(geometry), 2, 6);
         }),
         "a boundary above the top was planned");
  std::printf("  every division valid: %zu of them\n", divisions);
}

// ---------------------------------------------------------------------------
// The thread budget
// ---------------------------------------------------------------------------

void TestBudget() {
  const la::LevelArenaGeometry geometry(kB8At32M.params);
  const bs::Layout layout = LayoutOf(geometry);
  // NO THREADS is the inline executor: no groups, the default share, and
  // the saturated rate still reported.
  const la::LevelArenaRebuildParams none =
      la::HeuristicRebuildParams(geometry, layout, {});
  Expect(none.groups.empty() && none.top_helpers == 0 &&
             none.threads() == 0 &&
             none.inline_work_factor == la::kLevelArenaInlineWorkFactor &&
             none.slice_target_rate ==
                 la::SaturatedOnlineRate(geometry, layout),
         "a zero budget is not the inline executor");
  // WHILE A GROUP BINDS, threads become groups: the pinned partitions.  With
  // level one built directly, three groups already leave the top the
  // binding group, so the fourth thread is the top's helper.
  for (unsigned threads = 1; threads <= 3; ++threads) {
    const la::LevelArenaRebuildParams p =
        la::HeuristicRebuildParams(geometry, layout, {threads});
    Expect(p.top_helpers == 0 && p.lanes.lanes == 1,
           std::to_string(threads) + " threads went to helpers");
    Expect(Same(p.groups, la::PlanLevelGroups(geometry, layout, threads)),
           std::to_string(threads) + " threads are not the plain division");
  }
  {
    const la::LevelArenaRebuildParams four =
        la::HeuristicRebuildParams(geometry, layout, {4});
    Expect(four.top_helpers == 1 &&
               Same(four.groups, {G{5, 6}, G{3, 4}, G{1, 2}}),
           "four threads at 32M are not three groups and a top helper: " +
               Describe(four.groups) + " + " +
               std::to_string(four.top_helpers));
  }
  // ONCE THE TOP BINDS -- four groups at 32M, {6},{4,5},{2,3},{1} -- the next
  // thread is the top's: its group gets a second thread, laned.
  const la::LevelArenaRebuildParams five =
      la::HeuristicRebuildParams(geometry, layout, {5});
  Expect(five.threads() == 5 && five.top_helpers == 1,
         "the fifth thread did not go to the top: " +
             Describe(five.groups) + " + " +
             std::to_string(five.top_helpers));
  Expect(Same(five.groups, {G{6, 6}, G{4, 5}, G{2, 3}, G{1, 1}}),
         "five threads at 32M: " + Describe(five.groups));
  Expect(five.lanes.lanes >= 2 * (1 + five.top_helpers),
         "the helpers have fewer lanes than two a thread");
  // Lanes go to the top's group only: level 5 is outside it here, and
  // level 4 has no table wide enough for them anyway.
  Expect(la::LevelLaneCount(geometry, 6, five.lanes) > 1 &&
             la::LevelLaneCount(geometry, 5, five.lanes) == 1 &&
             la::LevelLaneCount(geometry, 4, five.lanes) == 1,
         "the lanes are not the top group's");
  // MORE THREADS NEVER MAKE THE MODEL WORSE, and past the point where the
  // model gains nothing they are not spent.
  double previous = 1e300;
  unsigned used = 0;
  for (unsigned threads = 1; threads <= 24; ++threads) {
    const la::LevelArenaRebuildParams p =
        la::HeuristicRebuildParams(geometry, layout, {threads});
    Expect(p.threads() <= threads, "the heuristic overspent its budget");
    Expect(p.groups.size() <= geometry.Levels(),
           "the heuristic made a group with no level");
    Expect(p.demand_nanos <= previous * (1 + la::LevelArenaRebuildCost{}.ThreadGainFloor()),
           "a bigger budget made the bottleneck worse");
    previous = std::min(previous, p.demand_nanos);
    used = p.threads();
  }
  Expect(used < 24, "24 threads were all spent on a 6-level hierarchy");
  for (unsigned threads = 1; threads <= 24; ++threads) {
    Expect(la::HeuristicRebuildParams(geometry, layout, {threads})
                   .top_helpers < la::LevelArenaRebuildCost{}.max_top_threads,
           "the top's group was given more threads than the cap");
  }
  // A hierarchy with no laned table gives the top no helpers at all.
  la::LevelArenaGeometry::Params tiny = kB8At4M.params;
  tiny.levels = 3;
  tiny.level_fanouts = {8, 8};
  const la::LevelArenaGeometry small(tiny);
  const la::LevelArenaRebuildParams small_params =
      la::HeuristicRebuildParams(small, LayoutOf(small), {8});
  Expect(small_params.top_helpers == 0 && small_params.threads() <= 3,
         "a hierarchy too small for lanes was given helpers");
  std::printf("  the budget: groups while a group binds, then the top's "
              "helpers; never worse, never overspent\n");
}

// THE COST MODEL IS AN INPUT (the tuner's output): the defaults are the
// calibration constants every other test here pins (re-derived for a machine
// by `python -m analysis.oram_bench fit-rebuild`), and a different model
// moves exactly what it prices.
void TestCostModel() {
  const la::LevelArenaGeometry geometry(kB8At32M.params);
  const bs::Layout layout = LayoutOf(geometry);
  const la::LevelArenaRebuildCost defaults;
  // The features are what the model prices: cost = routing lines x line +
  // residual lines x residual line + offer lines x offer line + jobs x job.
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    const la::LevelCostFeatures f = la::LevelRebuildFeatures(geometry, layout, l);
    Expect(f.touch_lines > 0 && f.residual_lines > 0 && f.offer_lines > 0 &&
               f.jobs > 0,
           "a level has no modeled work");
    Expect(std::abs(la::LevelRebuildNanosPerAccess(geometry, layout, l) -
                    (f.touch_lines * 0.845 + f.residual_lines * 0.397 +
                     f.offer_lines * 1.696 + f.jobs * 2659.0)) < 1e-9,
           "the default model is not the development host's constants");
  }
  const la::ProbeCostFeatures probe = la::SaturatedProbeFeatures(geometry, layout);
  Expect(std::abs(la::SaturatedOnlineRate(geometry, layout) -
                  1e9 / (probe.buckets * 20.0 + probe.bucket_lines * 0.45)) < 1e-6,
         "the default probe model is not the development host's constants");
  // A slower probe halves the rate the pieces are sized for.
  la::LevelArenaRebuildCost slow_probe;
  slow_probe.probe_bucket_picos *= 2;
  slow_probe.probe_line_picos *= 2;
  Expect(std::abs(la::SaturatedOnlineRate(geometry, layout, slow_probe) * 2 -
                  la::SaturatedOnlineRate(geometry, layout)) < 1e-3,
         "the probe constants do not set the slice rate");
  Expect(la::HeuristicRebuildParams(geometry, layout, {4}, slow_probe).slice_target_rate ==
             la::SaturatedOnlineRate(geometry, layout, slow_probe),
         "the heuristic ignores its cost model's probe constants");
  // THE TOP'S THREAD CAP binds when the top stays the bottleneck while each
  // doubling still pays: slow helpers (0.2 per doubling) and a machine whose
  // helper curve keeps rising past 8 threads.  Fast helpers never reach it,
  // because the top soon stops being the bottleneck (level 1's group binds).
  // Under the certified routing's own prices level 1 binds at 32M before any
  // cap does, so the cap is exercised on a model whose residual passes are
  // free, where the top dominates.
  la::LevelArenaRebuildCost scaling;
  scaling.helper_speedup_ppm = 200000;
  scaling.max_top_threads = 16;
  scaling.residual_line_picos = 0;
  scaling.offer_line_picos = 0;
  unsigned most = 0;
  for (unsigned threads = 1; threads <= 24; ++threads) {
    const la::LevelArenaRebuildParams p =
        la::HeuristicRebuildParams(geometry, layout, {threads}, scaling);
    Expect(p.top_helpers < scaling.max_top_threads, "the cap was exceeded");
    most = std::max(most, p.top_helpers);
  }
  Expect(most + 1 > defaults.max_top_threads,
         "a machine whose top scales to 16 threads was held to the default cap: " +
             std::to_string(most) + " helpers");
  la::LevelArenaRebuildCost held = scaling;
  held.max_top_threads = defaults.max_top_threads;
  for (unsigned threads = 1; threads <= 24; ++threads) {
    Expect(la::HeuristicRebuildParams(geometry, layout, {threads}, held).top_helpers + 1 <=
               defaults.max_top_threads,
           "the default cap did not hold the same slow curve");
  }
  la::LevelArenaRebuildCost capped = scaling;
  capped.max_top_threads = 2;
  for (unsigned threads = 1; threads <= 24; ++threads) {
    Expect(la::HeuristicRebuildParams(geometry, layout, {threads}, capped).top_helpers <= 1,
           "max_top_threads = 2 gave the top more than one helper");
  }
  // THE RESIDUAL PASSES ARE PRICED: they are over a quarter of levels 1 and
  // 2's cost, and free they would be nothing -- a model that leaves them
  // out misjudges the DFS finish, where they are most of the work.
  la::LevelArenaRebuildCost free_residual;
  free_residual.residual_line_picos = 0;
  free_residual.offer_line_picos = 0;
  const la::LevelLoadModel priced(geometry, layout);
  const la::LevelLoadModel unpriced(geometry, layout, free_residual);
  Expect(unpriced.cost[1] < 0.75 * priced.cost[1] &&
             unpriced.cost[2] < 0.75 * priced.cost[2],
         "the residual terms do not carry levels 1 and 2's cost");
  la::LevelArenaRebuildCost free_jobs;
  free_jobs.job_nanos = 0;
  // The engine divides an owner count by the model on its Options, which is
  // how a resolved plan and the engine it builds agree.
  // The fixture's raw Params pin one tier bucket; engine options size the
  // tier for the request horizon (0 = automatic), and the engine divides the
  // geometry it resolves, so the reference is priced on that one too.
  la::LevelArenaEngine::Options options;
  options.geometry = kB8At32M.params;
  options.geometry.tier_buckets = 0;
  options.key_bytes = 8;
  options.value_bytes = 16;
  options.owner_threads = 3;
  options.rebuild_cost = free_jobs;
  const la::LevelArenaGeometry resolved(
      la::ResolveLevelArenaTierGeometry(options.geometry, options.max_accesses));
  Expect(Same(la::LevelArenaEngine::PlannedLevelGroups(options),
              la::PlanLevelGroups(resolved, LayoutOf(resolved), 3, 0, 1, free_jobs)),
         "the engine does not divide by its Options' cost model");
  // Models that cannot price anything are refused.
  const std::vector<void (*)(la::LevelArenaRebuildCost&)> breaks = {
                      [](la::LevelArenaRebuildCost& c) { c.max_top_threads = 0; },
                      [](la::LevelArenaRebuildCost& c) {
                        c.line_picos = 0; c.residual_line_picos = 0;
                        c.offer_line_picos = 0; c.job_nanos = 0; },
                      [](la::LevelArenaRebuildCost& c) {
                        c.probe_bucket_picos = 0; c.probe_line_picos = 0; },
                      [](la::LevelArenaRebuildCost& c) { c.thread_gain_floor_ppm = 1000000; }};
  for (const auto broken : breaks) {
    la::LevelArenaRebuildCost c;
    broken(c);
    Expect(Throws([&] { la::HeuristicRebuildParams(geometry, layout, {4}, c); }),
           "an unusable cost model was accepted");
  }
  std::printf("  the cost model: defaults are the host's constants; the cap, "
              "probe and job terms steer the heuristic\n");
}

// NEAR AND FAR (see cpu_byteslice_level_arena_placement.hpp): the division respects the boundary, the near side
// stays within the cores its domain has, and helpers need far cores.
void TestBudgetCaps() {
  const la::LevelArenaGeometry geometry(kB8At32M.params);
  const bs::Layout layout = LayoutOf(geometry);
  for (unsigned boundary = 1; boundary < geometry.Levels(); ++boundary) {
    for (unsigned threads = 2; threads <= 8; ++threads) {
      for (unsigned near_cap : {0u, 1u, 2u}) {
        la::LevelArenaThreadBudget budget;
        budget.threads = threads;
        budget.near_max_level = boundary;
        budget.near_threads = near_cap;
        const la::LevelArenaRebuildParams p =
            la::HeuristicRebuildParams(geometry, layout, budget);
        unsigned near = 0;
        for (const G& g : p.groups) {
          Expect(g.last <= boundary || g.first > boundary,
                 "a budgeted group straddles the boundary");
          near += g.last <= boundary ? 1 : 0;
        }
        Expect(near_cap == 0 || near <= near_cap,
               "the near side got more groups than its cores");
        Expect(p.groups.size() < 2 || near >= 1,
               "a split budget left the near side empty");
        Expect(p.near_max_level == boundary,
               "the params lost the boundary they were planned at");
      }
    }
  }
  // Far cores are what the top's helpers need: with room for two far
  // threads and a far top group, there is room for one helper at most.
  la::LevelArenaThreadBudget tight;
  tight.threads = 8;
  tight.near_max_level = 3;
  tight.far_threads = 2;
  const la::LevelArenaRebuildParams p =
      la::HeuristicRebuildParams(geometry, layout, tight);
  unsigned far = p.top_helpers;
  for (const G& g : p.groups) far += g.first > 3 ? 1 : 0;
  Expect(far <= 2, "the far side got more threads than its cores");
  Expect(Throws([&] {
           la::LevelArenaThreadBudget bad;
           bad.threads = 2;
           bad.near_max_level = 7;
           la::HeuristicRebuildParams(geometry, layout, bad);
         }),
         "a boundary above the top was accepted");
  std::printf("  the caps: no straddle, near cores respected, helpers need "
              "far cores\n");
}

// ---------------------------------------------------------------------------
// And an engine built from them
// ---------------------------------------------------------------------------

void TestEngineTakesTheParams() {
  const int failures_before = failures;
  la::LevelArenaEngine::Options options;
  options.geometry = Params(4, 4, 2, {4, 4, 4});
  options.geometry.tier_buckets = 0;  // automatic, as engine options default
  options.key_bytes = 8;
  options.value_bytes = 8;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0x9A7A);
  const la::LevelArenaGeometry geometry(
      la::ResolveLevelArenaTierGeometry(options.geometry, options.max_accesses));
  const bs::Layout layout = la::LevelArenaStoredLayout(8, 8, geometry);
  for (unsigned threads : {0u, 1u, 2u, 3u}) {
    la::LevelArenaRebuildParams params =
        la::HeuristicRebuildParams(geometry, layout, {threads});
    la::ApplyRebuildParams(params, &options);
    la::LevelArenaEngine engine(options);
    const std::string where = std::to_string(threads) + " threads";
    Expect(engine.threaded() == (threads != 0), where + ": the wrong shape");
    if (threads == 0) {
      Expect(engine.inline_flush_touches() > 0,
             where + ": the inline executor has no share");
    } else {
      Expect(engine.owner_groups() == params.groups.size(),
             where + ": the engine lost a group");
      for (size_t g = 0; g < params.groups.size(); ++g) {
        Expect(engine.owner_group(g).first == params.groups[g].first &&
                   engine.owner_group(g).last == params.groups[g].last,
               where + ": the engine built another division");
      }
      Expect(engine.slice_target_rate() == params.slice_target_rate,
             where + ": the engine sized its pieces for another rate");
    }
    std::vector<uint8_t> key(8, 0), value(8, 0), got(8, 0);
    for (uint64_t k = 0; k < 900; ++k) {
      std::memcpy(key.data(), &k, sizeof(k));
      std::memcpy(value.data(), &k, sizeof(k));
      engine.Write(key.data(), value.data());
    }
    engine.Drain();
    for (uint64_t k = 0; k < 900; ++k) {
      std::memcpy(key.data(), &k, sizeof(k));
      std::memcpy(value.data(), &k, sizeof(k));
      Expect(engine.Read(key.data(), got.data()) && got == value,
             where + ": a key was lost");
      if (failures != failures_before) return;
    }
  }
  // An engine given no rate sizes its pieces for the saturated requester.
  options.owner_threads = 2;
  options.groups.clear();
  options.slice_target_rate = 0;
  {
    la::LevelArenaEngine engine(options);
    Expect(engine.slice_target_rate() ==
               la::SaturatedOnlineRate(geometry, layout),
           "the default slice rate is not the saturated one");
    Expect(Same({engine.owner_group(0), engine.owner_group(1)},
                la::PlanLevelGroups(geometry, layout, 2)),
           "the default division is not the heuristic's");
  }
  options.owner_threads = 0;
  options.inline_work_factor = 0;
  Expect(Throws([&] { la::LevelArenaEngine engine(options); }),
         "an inline executor with no share was accepted");
  std::printf("  the engine: builds what the params say, at every budget\n");
}

void TestFloatingWorkBudgets() {
  const double infinity = std::numeric_limits<double>::infinity();
  const double nan = std::numeric_limits<double>::quiet_NaN();
  const double largest = std::numeric_limits<double>::max();
  const bs::Layout layout{8, 8, 1};
  for (double invalid : {-1.0, nan, infinity, 0x1p64, largest}) {
    Expect(Throws([&] { la::CheckedTouchBudget(invalid); }),
           "an unrepresentable floating touch budget was accepted");
  }
  const double upper = std::nextafter(0x1p64, 0.0);
  Expect(la::CheckedTouchBudget(upper) == static_cast<size_t>(upper),
         "the largest representable double below 2^64 was rejected");
  Expect(la::CheckedTouchBudget(0.0) == 1 &&
             la::CheckedTouchBudget(0.25) == 1 &&
             la::CheckedTouchBudget(3.75) == 3,
         "valid work budgets lost their floor or integer rounding");
  for (double invalid : {-1.0, nan, infinity}) {
    Expect(Throws([&] { la::SliceTouches(invalid, layout); }),
           "an invalid slice duration was accepted");
    Expect(Throws([&] { la::SliceTouches(1.0, layout, invalid); }),
           "an invalid slice line cost was accepted");
  }
  Expect(Throws([&] { la::SliceTouches(1.0, layout, 0.0); }),
         "a zero slice line cost was accepted");

  la::LevelArenaEngine::Options options;
  options.geometry = Params(2, 2, 2, {2});
  options.geometry.tier_buckets = 0;
  options.value_bytes = 8;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0xB0D6E7);
  for (double invalid : {0.0, -1.0, nan, infinity, largest}) {
    options.inline_work_factor = invalid;
    Expect(Throws([&] { la::LevelArenaEngine engine(options); }),
           "an invalid or overflowing inline work factor was accepted");
  }
  options.inline_work_factor = la::kLevelArenaInlineWorkFactor;
  options.owner_threads = 1;
  options.defer_owner_start = true;
  for (double invalid : {-1.0, nan, infinity,
                          std::numeric_limits<double>::denorm_min()}) {
    options.slice_target_rate = invalid;
    Expect(Throws([&] { la::LevelArenaEngine engine(options); }),
           "an invalid rate or overflowing owner slice was accepted");
  }
  std::printf("  floating work budgets: reject nonfinite and overflowing counts\n");
}

}  // namespace

int main() {
  std::printf("level arena rebuild params\n");
  TestModel();
  TestReviewPartitions();
  TestEveryDivisionIsValid();
  TestBudget();
  TestCostModel();
  TestBudgetCaps();
  TestEngineTakesTheParams();
  TestFloatingWorkBudgets();
  if (failures != 0) {
    std::fprintf(stderr, "%d rebuild-params checks failed\n", failures);
    return 1;
  }
  std::printf("level arena rebuild params: OK\n");
  return 0;
}
