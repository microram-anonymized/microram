// The probe plan's laminarity predicate (PlanWindowsLaminar in
// cpu_byteslice_probe_plan.hpp).  Each table in a probe plan covers a WINDOW
// of access positions; in probe order every pair of distinct windows must be
// nested or disjoint, and a window's residual tiers must follow its main
// table in ascending order.  That is what makes "the first table that has the
// key holds its freshest copy" true, so a plan that violates it would return
// stale values.  Checked on hand-built plans, both as a snapshot and as a
// live plan, against an independent pairwise geometric oracle.
#include "src/oram/table/cpu_byteslice_probe_plan.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <cstdio>
#include <initializer_list>
#include <utility>
#include <vector>

namespace bs = microram::byteslice;
using bs::test_support::Expect;

static bs::TableShape Window(uint64_t begin, uint64_t end, uint32_t tier = 0) {
  bs::TableShape out;
  out.window_begin = begin;
  out.window_end = end;
  out.tier = tier;
  return out;
}

static bs::ProbePlanSnapshot Plan(
    std::initializer_list<std::pair<uint64_t, uint64_t>> windows,
    bool with_tiers = false) {
  bs::ProbePlanSnapshot out;
  for (auto [begin, end] : windows) {
    out.tables.push_back(Window(begin, end));
    if (with_tiers) out.tables.push_back(Window(begin, end, 1));
  }
  return out;
}

static void Check(const bs::ProbePlanSnapshot& snapshot, bool expected,
                  const char* message, size_t first = 0) {
  Expect(bs::PlanWindowsLaminar(snapshot, first) == expected, message);
  bs::ProbePlan live;
  for (const auto& shape : snapshot.tables) {
    bs::TableEntry entry;
    static_cast<bs::TableShape&>(entry) = shape;
    live.tables.push_back(entry);
  }
  Expect(bs::PlanWindowsLaminar(live, first) == expected, message);
}

// Independent geometric oracle for positive main-only windows already sorted
// by end.  Containment and disjointness are symmetric pairwise properties.
static bool GeometricallyValid(const bs::ProbePlanSnapshot& plan) {
  if (plan.tables.empty() || plan.tables.back().window_begin != 0) return false;
  for (size_t i = 0; i < plan.tables.size(); ++i) {
    const auto& a = plan.tables[i];
    for (size_t j = i + 1; j < plan.tables.size(); ++j) {
      const auto& b = plan.tables[j];
      if (a.window_end == b.window_end) return false;
      const bool disjoint = a.window_end <= b.window_begin ||
                            b.window_end <= a.window_begin;
      const bool a_contains_b = a.window_begin <= b.window_begin &&
                                a.window_end >= b.window_end;
      const bool b_contains_a = b.window_begin <= a.window_begin &&
                                b.window_end >= a.window_end;
      if (!disjoint && !a_contains_b && !b_contains_a) return false;
    }
  }
  return true;
}

int main() {
  for (bool tiers : {false, true}) {
    Check(Plan({{5, 10}, {6, 8}, {0, 6}}, tiers), false,
          "nonadjacent crossing accepted");
    Check(Plan({{0, 10}, {6, 8}, {0, 6}}, tiers), true,
          "nested siblings sharing an endpoint rejected");
    Check(Plan({{5, 10}, {6, 8}, {0, 5}}, tiers), true,
          "disjoint window following nesting rejected");
    Check(Plan({{0, 10}, {0, 8}, {0, 6}}, tiers), true,
          "nested windows with equal starts rejected");
  }

  Check(Plan({}), false, "empty plan accepted");
  Check(Plan({{0, 0}}), false, "empty single window accepted");
  Check(Plan({{1, 2}, {0, 0}}), false, "empty final window accepted");
  Check(Plan({{1, 2}}), false, "oldest window did not start at zero");
  Check(Plan({{3, 2}, {0, 1}}), false, "reversed interval accepted");
  Check(Plan({{0, 1}, {0, 2}}), false, "ascending window ends accepted");
  Check(Plan({{1, 2}, {0, 2}}), false, "unequal windows sharing an end accepted");
  Check(Plan({{0, 2}, {0, 2}}), false, "duplicate main accepted");

  auto tiers = Plan({{0, 2}}, true);
  tiers.tables[0].tier = 1;
  tiers.tables[1].tier = 2;
  Check(tiers, false, "leading residual without a main accepted");
  tiers = Plan({{0, 2}, {0, 1}}, true);
  tiers.tables.erase(tiers.tables.begin() + 2);
  Check(tiers, false, "nested residual without a main accepted");
  tiers = Plan({{1, 2}, {0, 1}}, true);
  tiers.tables.erase(tiers.tables.begin() + 2);
  Check(tiers, false, "disjoint residual without a main accepted");
  tiers = Plan({{0, 2}}, true);
  tiers.tables.push_back(Window(0, 2, 3));
  Check(tiers, true, "increasing nonconsecutive tiers rejected");
  tiers.tables.push_back(Window(0, 2, 2));
  Check(tiers, false, "descending tiers accepted");

  auto prefix = Plan({{0, 0}, {0, 0}});
  Check(prefix, true, "empty suffix behind reserved prefix rejected", 2);
  Check(prefix, false, "range past end accepted", 3);
  prefix.tables.push_back(Window(0, 2));
  Check(prefix, true, "invalid reserved prefix was checked", 2);
  prefix.tables.push_back(Window(0, 0));
  Check(prefix, false, "empty last suffix window accepted", 2);

  // More simultaneously nested windows than the bounded fast-path stack,
  // followed by a window that either touches or crosses the outermost one.
  bs::ProbePlanSnapshot deep;
  for (uint64_t i = 0; i < 160; ++i) {
    deep.tables.push_back(Window(10 + i, 1000 - i));
    deep.tables.push_back(Window(10 + i, 1000 - i, 1));
  }
  deep.tables.push_back(Window(0, 10));
  Check(deep, true, "deep valid family rejected");
  deep.tables.back().window_end = 11;
  Check(deep, false, "deep nonadjacent crossing accepted");
  deep.tables.back().window_end = 0;
  Check(deep, false, "deep family bypassed final interval validation");

  // Exhaust every subset of the 15 positive intervals on endpoints 0..5.
  // This includes nested branches, disjoint gaps, shared ends, and crossings.
  std::vector<bs::TableShape> windows;
  for (uint64_t end = 5; end != 0; --end) {
    for (uint64_t begin = 0; begin < end; ++begin) {
      windows.push_back(Window(begin, end));
    }
  }
  for (uint32_t mask = 0; mask < (uint32_t{1} << windows.size()); ++mask) {
    bs::ProbePlanSnapshot plan;
    for (size_t i = 0; i < windows.size(); ++i) {
      if (mask & (uint32_t{1} << i)) plan.tables.push_back(windows[i]);
    }
    const bool expected = GeometricallyValid(plan);
    Check(plan, expected, "interval subset disagreed with geometric oracle");
    bs::ProbePlanSnapshot paired;
    for (auto window : plan.tables) {
      paired.tables.push_back(window);
      window.tier = 1;
      paired.tables.push_back(window);
    }
    Check(paired, expected, "tier pairs changed interval validation");
  }
  std::puts("probe plan window validation passed");
}
