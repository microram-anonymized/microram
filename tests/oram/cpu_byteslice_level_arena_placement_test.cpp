// NEAR AND FAR: the level grouping and the thread placement of
// cpu_byteslice_level_arena_placement.hpp, for hosts whose cores are split
// across several L3 cache domains (CCDs).  The NEAR class of rebuild owners
// shares the request thread's L3 and runs the small, cache-resident levels;
// the FAR class runs the large, DRAM-streaming levels on another domain.
//
// The thing under test is a POLICY and not a machine.  `AutoNearMaxLevel`,
// `PlanLevelGroups` with a boundary, and `PlanNearFarPlacement` are pure functions of
// public numbers -- a geometry, a layout, a cache size, a list of CPUs per
// cache domain -- precisely so that the rule can be checked on a host that
// has one domain, or twelve, or a hypothetical three.  Whether pinning the
// threads that way is FASTER is a measurement and is the benchmark's; what
// this file owes is that the assignment is the one the rule describes.
//
// WHY THE RULE IS WORTH PINNING AT ALL.  The rule is one-sided: the class
// SPLIT plus the placement keeps the small levels beside the request thread,
// while moving the whole rebuild pool to another domain WITHOUT the split only
// takes the small levels' cache away from the request path and loses.  So the
// two halves have to travel together, and the
// fixtures below hold them together -- no group straddles the boundary, the
// request thread and its batch participants keep the near domain, and a
// placement with no boundary is refused rather than silently becoming the
// arm that loses.

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_placement.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;

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

la::LevelArenaGeometry::Params Params(unsigned branching, unsigned levels,
                                      unsigned top_digit) {
  la::LevelArenaGeometry::Params params;
  params.branching = branching;
  params.levels = levels;
  params.top_digit = top_digit;
  params.prefix_flushes = 4;
  params.stash_buckets = 1;
  params.dense_prefixes = 2;
  return params;
}

// ---------------------------------------------------------------------------
// The boundary
// ---------------------------------------------------------------------------

void TestAutoBoundary() {
  const la::LevelArenaGeometry geometry(Params(4, 6, 4));
  const bs::Layout layout = la::LevelArenaStoredLayout(8, 16, geometry);
  const size_t bucket_bytes = layout.BucketBytes();

  // A cache that holds nothing puts the boundary at its floor, which is level
  // 1: the smallest carry in the hierarchy is near work whatever the cache
  // is, because a split with no near level is the "whole pool moved across"
  // arm and that one loses.
  Expect(la::AutoNearMaxLevel(geometry, layout, 0) == 1,
         "a zero cache did not leave the boundary at its floor");
  // A cache that holds everything puts it at the top.
  Expect(la::AutoNearMaxLevel(geometry, layout, size_t{1} << 40) ==
             geometry.Levels(),
         "an unlimited cache did not make every level near");

  // And in between it is exactly "the largest level whose full output table
  // is under half the cache", checked against the definition rather than
  // against a remembered number.
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    const size_t table = la::FullLevelOutputBuckets(geometry, l) * bucket_bytes;
    // A cache of exactly twice this table's size: level l is NOT under half
    // of it (the rule is strict), so the boundary must land below l.
    const unsigned strict = la::AutoNearMaxLevel(geometry, layout, 2 * table);
    Expect(strict < l || l == 1,
           "a level exactly half the cache was counted as near");
    // One byte more and it is.
    const unsigned inclusive =
        la::AutoNearMaxLevel(geometry, layout, 2 * table + 2);
    Expect(inclusive >= l, "a level under half the cache was counted as far");
  }

  // Monotone in the cache size, which is what makes it a boundary rather
  // than a lookup.
  unsigned previous = 0;
  for (size_t cache = 1u << 12; cache <= (size_t{1} << 34); cache *= 2) {
    const unsigned boundary = la::AutoNearMaxLevel(geometry, layout, cache);
    Expect(boundary >= previous, "the boundary fell as the cache grew");
    previous = boundary;
  }
  std::printf("  the boundary: floor, ceiling, the strict half rule, "
              "monotone\n");
}

// ---------------------------------------------------------------------------
// The grouping
// ---------------------------------------------------------------------------

// Every group is contiguous, the groups cover 1..L exactly once, there are as
// many as there are threads, and NONE of them straddles the boundary.
void CheckGrouping(const std::vector<la::LevelGroupPlan>& groups,
                   unsigned levels, unsigned threads, unsigned boundary,
                   const std::string& where) {
  Expect(groups.size() == threads, where + ": not one group per thread");
  std::vector<unsigned> seen;
  for (const la::LevelGroupPlan& group : groups) {
    Expect(group.first <= group.last, where + ": an inverted group");
    for (unsigned l = group.first; l <= group.last; ++l) seen.push_back(l);
    // ONE THREAD IS THE ONE CASE THAT MAY STRADDLE, because its single
    // group holds every level and there is nowhere else to put them.  Every
    // other division must keep the two classes apart.
    Expect(threads == 1 || group.last <= boundary || group.first > boundary,
           where + ": a group straddles the near/far boundary");
  }
  std::sort(seen.begin(), seen.end());
  Expect(seen.size() == levels, where + ": the groups do not cover the levels");
  for (unsigned l = 1; l <= levels && l <= seen.size(); ++l) {
    Expect(seen[l - 1] == l, where + ": a level is missing or repeated");
  }
}

void TestGrouping() {
  size_t split_groupings = 0;
  for (unsigned levels = 2; levels <= 8; ++levels) {
    const la::LevelArenaGeometry geometry(Params(4, levels, 4));
    const bs::Layout layout = la::LevelArenaStoredLayout(8, 16, geometry);
    for (unsigned threads = 1; threads <= levels; ++threads) {
      for (unsigned boundary = 1; boundary <= levels; ++boundary) {
        const std::vector<la::LevelGroupPlan> groups =
            la::PlanLevelGroups(geometry, layout, threads, boundary);
        CheckGrouping(groups, levels, threads, boundary,
                      "L=" + std::to_string(levels) + " threads=" +
                          std::to_string(threads) + " boundary=" +
                          std::to_string(boundary));
        // With the boundary at the top -- everything near -- or one thread,
        // the division must be the one planned without a boundary, so that
        // turning the split off is the engine as it was rather than another
        // shape of it.
        if (boundary == levels || threads == 1) {
          const std::vector<la::LevelGroupPlan> plain =
              la::PlanLevelGroups(geometry, layout, threads);
          Expect(groups.size() == plain.size(),
                 "the near/far division changed a grouping it should not");
          for (size_t g = 0; g < groups.size() && g < plain.size(); ++g) {
            Expect(groups[g].first == plain[g].first &&
                       groups[g].last == plain[g].last,
                   "the near/far division changed a grouping it should not");
          }
        }
        bool near = false, far = false;
        for (const la::LevelGroupPlan& group : groups) {
          (la::GroupIsNear(group, boundary) ? near : far) = true;
        }
        // Both classes are populated whenever there is a level on each side
        // and a thread to give it.  That is the half of the rule the
        // measurement depends on, and it is easy to lose to a rounding.
        if (boundary < levels && threads >= 2) {
          Expect(near && far,
                 "a split boundary with two threads left one class empty");
          ++split_groupings;
        }
        if (failures != 0) return;
      }
    }
  }
  const la::LevelArenaGeometry four(Params(4, 4, 4));
  const bs::Layout four_layout = la::LevelArenaStoredLayout(8, 16, four);
  Expect(Throws([&] { la::PlanLevelGroups(four, four_layout, 5, 2); }),
         "more owner threads than levels was accepted");
  Expect(Throws([&] { la::PlanLevelGroups(four, four_layout, 2, 5); }),
         "a boundary outside the hierarchy was accepted");
  std::printf("  the grouping: %zu split divisions, none straddling, and "
              "both classes populated\n", split_groupings);
}

// ---------------------------------------------------------------------------
// The placement
// ---------------------------------------------------------------------------

la::HostCacheDomains Host(std::vector<std::vector<int>> domains) {
  la::HostCacheDomains host;
  host.domains = std::move(domains);
  return host;
}

void TestPlacement() {
  const unsigned levels = 6, threads = 4, boundary = 3;
  const la::LevelArenaGeometry six(Params(4, levels, 4));
  const bs::Layout six_layout = la::LevelArenaStoredLayout(8, 16, six);
  const std::vector<la::LevelGroupPlan> groups =
      la::PlanLevelGroups(six, six_layout, threads, boundary);

  // ONE DOMAIN IS NOT A SPLIT: nothing is placed, which is the library's
  // default behaviour and the arm the two-CCD measurement compares against.
  const la::NearFarPlacement single =
      la::PlanNearFarPlacement(Host({{0, 1, 2, 3, 4, 5}}), groups, boundary, 2);
  Expect(single.requester == -1 && !single.split,
         "a single-domain host was given a placement");
  for (int cpu : single.groups) {
    Expect(cpu == -1, "a single-domain host pinned an owner group");
  }

  // Two domains of six cores each, a common two-CCD shape.
  const la::HostCacheDomains two =
      Host({{0, 1, 2, 3, 4, 5}, {6, 7, 8, 9, 10, 11}});
  const la::NearFarPlacement placement =
      la::PlanNearFarPlacement(two, groups, boundary, 3);
  Expect(placement.split, "a two-domain host reported no split");
  Expect(placement.requester == 0, "the request thread did not take a CPU");
  Expect(placement.participants.size() == 3, "a participant was not placed");
  Expect(placement.participants[0] == placement.requester,
         "participant 0 is not the calling thread");
  // The participants are NEAR, always: they probe the same dense prefix and
  // the same top of the cascade as the request thread, in the same chunk.
  std::set<int> near_cpus(two.domains[0].begin(), two.domains[0].end());
  for (int cpu : placement.participants) {
    Expect(near_cpus.count(cpu) == 1,
           "a batch participant was placed off the request thread's domain");
  }
  // Distinct cores throughout: two threads of this engine on one core is a
  // measurement of the scheduler, not a placement.
  std::set<int> used;
  used.insert(placement.participants.begin(), placement.participants.end());
  const size_t distinct_participants = used.size();
  for (int cpu : placement.groups) used.insert(cpu);
  Expect(distinct_participants == placement.participants.size() &&
             used.size() == placement.participants.size() +
                                placement.groups.size(),
         "two threads were placed on one core");
  for (size_t g = 0; g < groups.size(); ++g) {
    const bool is_near = groups[g].last <= boundary;
    Expect(placement.group_is_near[g] == is_near,
           "a group was classified against its own levels");
    Expect((near_cpus.count(placement.groups[g]) == 1) == is_near,
           "a group was placed on the wrong side of the boundary");
  }

  // THE TOP'S HELPERS go with the top's group -- far here -- each on a core
  // of its own that no group has, and they count against the far cores.
  const la::NearFarPlacement helped =
      la::PlanNearFarPlacement(two, groups, boundary, 1, 2);
  Expect(helped.helpers.size() == 2, "a top helper was not placed");
  std::set<int> helped_used(helped.groups.begin(), helped.groups.end());
  helped_used.insert(helped.requester);
  for (int cpu : helped.helpers) {
    Expect(near_cpus.count(cpu) == 0,
           "a helper of the far top was placed on the near domain");
    Expect(helped_used.insert(cpu).second,
           "a helper shares a core with another thread");
  }
  Expect(helped.Describe().find("top helpers") != std::string::npos,
         "the placement report omits the helpers");
  // A far domain with one core past the far groups holds one helper, not
  // two.
  size_t far_groups = 0;
  for (const la::LevelGroupPlan& g : groups) far_groups += g.first > boundary;
  std::vector<int> near_domain, far_domain;
  for (size_t i = 0; i < groups.size() + 1; ++i) near_domain.push_back(int(i));
  for (size_t i = 0; i < far_groups + 1; ++i) {
    far_domain.push_back(int(groups.size() + 1 + i));
  }
  const la::HostCacheDomains snug = Host({near_domain, far_domain});
  Expect(!Throws([&] {
           la::PlanNearFarPlacement(snug, groups, boundary, 1, 1);
         }),
         "a far domain with room for one helper refused it");
  Expect(Throws([&] {
           la::PlanNearFarPlacement(snug, groups, boundary, 1, 2);
         }),
         "more far groups and helpers than far cores was accepted");

  // THREE DOMAINS: the far groups are spread round robin, so both of the
  // other dies are used before either is used twice.
  const la::HostCacheDomains three = Host({{0, 1, 2}, {3, 4}, {5, 6}});
  const std::vector<la::LevelGroupPlan> wide =
      la::PlanLevelGroups(six, six_layout, 4, 2);
  const la::NearFarPlacement spread =
      la::PlanNearFarPlacement(three, wide, 2, 1);
  std::vector<int> far_used;
  for (size_t g = 0; g < wide.size(); ++g) {
    if (!spread.group_is_near[g]) far_used.push_back(spread.groups[g]);
  }
  Expect(far_used.size() >= 2, "the fixture placed fewer than two far groups");
  Expect(far_used.size() < 2 || (far_used[0] == 3 && far_used[1] == 5),
         "the far groups did not alternate between the other two domains");

  // IT REFUSES RATHER THAN OVERSUBSCRIBING, and the message names the
  // arithmetic because the fix is always to spend fewer threads.
  Expect(Throws([&] {
           la::PlanNearFarPlacement(Host({{0, 1}, {2, 3}}), groups,
                                    boundary, 2);
         }),
         "a near domain too small for the participants and near groups was "
         "accepted");
  Expect(Throws([&] {
           la::PlanNearFarPlacement(Host({{0, 1, 2, 3}, {4}}), groups, boundary,
                                    1);
         }),
         "more far groups than far cores was accepted");
  // And the two shapes that would put the WHOLE rebuild on another die: no
  // boundary at all, and one owner thread whose single group straddles.  Both
  // are the losing arm described at the top of this file.
  Expect(Throws([&] { la::PlanNearFarPlacement(two, groups, 0, 1); }),
         "a placement with no near/far boundary was accepted");
  Expect(Throws([&] {
           la::PlanNearFarPlacement(
               two, la::PlanLevelGroups(six, six_layout, 1, 3), 3, 1);
         }),
         "a placement whose only group straddles the boundary was accepted");
  std::printf("  the placement: one domain, two, three; distinct cores; the "
              "three refusals\n");
}

// ---------------------------------------------------------------------------
// And through the engine
// ---------------------------------------------------------------------------

// The boundary is an ENGINE option, so what a caller gets has to be the
// grouping the policy describes -- and the byte bill has to still add up,
// because the transient range scratch is sized per group and a different
// division is a different bill.
void TestEngineGrouping() {
  for (unsigned boundary : {0u, 1u, 2u, 3u}) {
    la::LevelArenaEngine::Options options;
    options.geometry = Params(4, 4, 2);
    options.key_bytes = 8;
    options.value_bytes = 8;
    options.owner_threads = 3;
    options.near_max_level = boundary;
    options.secret_seed = microram::crypto::SecretKeySeed::Fixed(0x11E7);
    la::LevelArenaEngine engine(options);
    Expect(engine.near_max_level() == boundary,
           "the engine did not report the boundary it was built with");
    Expect(engine.owner_groups() == 3, "the engine lost an owner thread");
    if (boundary != 0) {
      std::vector<la::LevelGroupPlan> groups;
      for (size_t g = 0; g < engine.owner_groups(); ++g) {
        groups.push_back(engine.owner_group(g));
      }
      CheckGrouping(groups, 4, 3, boundary,
                    "engine boundary " + std::to_string(boundary));
    }
    // The bill is checked against what the components allocated inside the
    // constructor; reaching here at all is that check passing.  What is
    // asserted here is the other half: the roles still account for it.
    Expect(engine.ByteBill().RoleTotal() == engine.ByteBill().requested(),
           "the byte roles stopped accounting for every requested byte");
    // The hierarchy still works under every division, which is the only
    // thing the boundary must not change.
    std::vector<uint8_t> key(8, 0), value(8, 0), got(8, 0);
    for (uint64_t k = 0; k < 600; ++k) {
      std::memcpy(key.data(), &k, sizeof(k));
      std::memcpy(value.data(), &k, sizeof(k));
      engine.Write(key.data(), value.data());
    }
    engine.Drain();
    for (uint64_t k = 0; k < 600; ++k) {
      std::memcpy(key.data(), &k, sizeof(k));
      std::memcpy(value.data(), &k, sizeof(k));
      Expect(engine.Read(key.data(), got.data()) && got == value,
             "a key was lost under a near/far grouping");
      if (failures != 0) return;
    }
  }
  std::printf("  the engine: four boundaries, the same hierarchy, the bill "
              "still adds up\n");
}

}  // namespace

int main() {
  std::printf("level arena: near and far\n");
  TestAutoBoundary();
  TestGrouping();
  TestPlacement();
  TestEngineGrouping();
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena placement checks failed\n", failures);
    return 1;
  }
  std::printf("level arena placement: OK\n");
  return 0;
}
