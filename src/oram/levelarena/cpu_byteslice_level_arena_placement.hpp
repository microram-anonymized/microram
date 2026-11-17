#pragma once

// NEAR AND FAR ON A MULTI-CCD HOST: an optional thread placement for hosts
// whose cores are split across several L3 cache domains (CCDs).
//
// THE RULE, and it is one-sided: splitting the rebuild into a NEAR class that
// shares the request thread's L3 and a FAR class on another die lets the
// small, cache-resident levels stay beside the request thread while the
// large, DRAM-streaming levels run elsewhere; moving the WHOLE rebuild pool
// across instead only takes the small levels' cache away from the request
// path, and is a loss.  A reader who takes "put the workers on the other
// CCD" without the split gets the loss.  So the placement and the split are
// one decision and are planned together here.
//
// WHY THIS NEEDS NO SCHEDULER CHANGE.  A scheduler in which one worker pool
// takes work from every level would have to decide the class of each work
// item separately; here the levels are already divided into contiguous
// groups with a thread each (`PlanLevelGroups`), so "which
// class does this work belong to" is answered once, statically, by which
// group holds the level.  All that is left is (a) not letting a group straddle
// the boundary, which `PlanLevelGroups` promises when given one, and (b) telling
// the caller which CPU each thread should run on, which is what
// `PlanNearFarPlacement` is for.  Neither is a scheduling policy and both are
// pure functions of public numbers, so both are testable without a machine.
//
// WHY THE PINNING ITSELF IS NOT HERE.  The engine's `worker_init` and
// `batch_thread_init` hooks exist precisely so that a caller can place its
// threads without this library -- which is included everywhere -- growing a
// dependency on <sched.h> or <windows.h>.  This file computes the assignment;
// the benchmark reads the host's topology and applies it.  That split is also
// what lets a fixture check the policy on a host that has one L3 domain.
//
// THE BATCH PARTICIPANTS ARE NEAR, ALWAYS.  They are not a third class: every
// participant scans the same dense prefix and the same top of the cascade as
// the request thread in the same chunk, so they want that thread's L3 for the
// same reason the near rebuild class does.  What a participant must never do
// is displace the request thread, which is why the reserved-core constraint
// below counts the caller.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include "src/oram/table/cpu_byteslice_host_cache.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// `near_max_level` asking to be resolved against this host's cache rather than
// stated.  Distinct from every legal level, which starts at 1.
inline constexpr unsigned kNearMaxLevelAuto = 0xFFFFFFFFu;

// The buckets of the largest single table level `l` writes: `B * U_l` for a
// non-top level -- the full table it builds into its receiver's inbox -- and
// `T` for the top, whose compaction destination is a whole bank.  This is the
// quantity the boundary is stated over, because what decides whether a merge streams from DRAM is the size of what it PRODUCES.
inline size_t FullLevelOutputBuckets(const LevelArenaGeometry& geometry,
                                     unsigned level) {
  if (level < 1 || level > geometry.Levels()) {
    throw std::invalid_argument("level arena: that level is not in this "
                                "hierarchy");
  }
  return level == geometry.Levels()
             ? geometry.TopBuckets()
             : geometry.CarryBuckets(level + 1);
}

// THE BOUNDARY: the largest level whose full output table is under half the
// given cache.  Strictly below half, so a level exactly the size of the cache
// is far; and level 1 is the floor, because the smallest carry in the
// hierarchy is near work whatever the cache is -- a hierarchy with no near
// level would leave the near class with nothing to do and reduce the split to
// the "whole pool moved across" arrangement, which loses.
inline unsigned AutoNearMaxLevel(const LevelArenaGeometry& geometry,
                                 const Layout& layout, size_t cache_bytes) {
  const size_t half = cache_bytes / 2;
  const size_t bucket_bytes = layout.BucketBytes();
  unsigned boundary = 1;
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    if (FullLevelOutputBuckets(geometry, l) * bucket_bytes < half) boundary = l;
  }
  return boundary;
}

// ---------------------------------------------------------------------------
// Grouping that respects the boundary
// ---------------------------------------------------------------------------
//
// NO GROUP STRADDLES THE BOUNDARY, so that each group can be placed as a
// unit: `PlanLevelGroups` (cpu_byteslice_level_arena_rebuild_params.hpp)
// divides the near range [1, near_max_level] and the far range
// (near_max_level, L] separately, and chooses how many threads each side gets
// by the same load model it divides with -- not by level counts, which can
// leave one side's thread with most of the work.
// ONE THREAD IS THE ONE CASE THAT STRADDLES, and it must: a single group holds
// every level because there is nowhere else to put them.  It is also why
// `PlanNearFarPlacement` refuses a set of groups with no near one -- placing
// that single group is placing the whole rebuild on another die.

// Whether a group is near work: every level it holds is at or below the
// boundary.  A group planned against the boundary is never mixed, and one
// planned without it may be -- in which case it is FAR, because the large
// level in it is what decides whether its thread streams from DRAM.
inline bool GroupIsNear(const LevelGroupPlan& group, unsigned near_max_level) {
  return group.last <= near_max_level;
}

// ---------------------------------------------------------------------------
// Placement
// ---------------------------------------------------------------------------

// The host as a placement problem: one entry per cache domain (an L3 on an
// AMD Zen part, hence one CCD), each listing the CPUs the calling process may
// use on it.  Filled by whoever can read the host -- the benchmark does it from
// /sys/devices/system/cpu -- and never read from inside this library, which is
// the whole reason it is a parameter.
struct HostCacheDomains {
  std::vector<std::vector<int>> domains;

  bool Split() const { return domains.size() > 1; }
};

// Which CPU each thread of one engine should run on.  Every field is an index
// into the host's CPU numbering, and `-1` means "this thread is not placed",
// which is what a single-domain host gets: with one shared L3 there is no
// near/far distinction to exploit, so placement is left to the OS.
struct NearFarPlacement {
  int requester = -1;
  std::vector<int> participants;  // one per BATCH participant, caller included
  std::vector<int> groups;        // one per owner group, in group order
  std::vector<bool> group_is_near;
  // One per helper thread of the top's group, on the top group's side.
  std::vector<int> helpers;
  unsigned near_max_level = 0;
  bool split = false;  // whether near and far really landed on two domains

  std::string Describe() const {
    std::string out = "requester cpu " + std::to_string(requester) +
                      "; near boundary level " +
                      std::to_string(near_max_level) +
                      (split ? "" : " (one domain)");
    out += "; participants";
    for (int cpu : participants) out += " " + std::to_string(cpu);
    out += "; groups";
    for (size_t g = 0; g < groups.size(); ++g) {
      out += " " + std::to_string(groups[g]) +
             (group_is_near[g] ? "(near)" : "(far)");
    }
    if (!helpers.empty()) {
      out += "; top helpers";
      for (int cpu : helpers) out += " " + std::to_string(cpu);
    }
    return out;
  }
};

// THE ASSIGNMENT.  The request thread takes the first CPU of the first domain;
// that domain is NEAR by definition, and the batch participants and the near
// owner groups fill the rest of it in that order -- participants first,
// because a participant that cannot be placed beside the requester is a
// participant that would be probing the requester's dense prefix across a die.
// The far groups are spread over the remaining domains, round robin, so that a
// host with three CCDs uses all of them rather than piling every far group on
// one.
//
// It REFUSES rather than oversubscribing.  Two threads of this engine on one
// core is not a placement, it is a measurement of the scheduler: both of them
// are busy at the same moments by construction (a participant probes while the
// owners rebuild), so sharing a core would make the number reported a fact
// about preemption.  The message names the arithmetic, because the fix is
// always to spend fewer threads and the caller has to know how many fit.
//
// THE TOP'S HELPER THREADS (`top_helpers`) run the top group's lanes, so
// they go where that group goes -- far whenever there is a split -- each on a
// core of its own after the groups of that side.
inline NearFarPlacement PlanNearFarPlacement(
    const HostCacheDomains& host, const std::vector<LevelGroupPlan>& groups,
    unsigned near_max_level, unsigned participants, unsigned helpers = 0) {
  if (participants == 0) {
    throw std::invalid_argument(
        "level arena: a batch has at least one participant, the caller");
  }
  if (near_max_level == 0) {
    // PLACING WITHOUT THE SPLIT IS THE LOSING ARRANGEMENT: with every group
    // far, this would pin the whole rebuild to another die, which is slower
    // than leaving it unpinned (see the header).  A caller that does not want the split wants no placement at
    // all, which is what leaving the hooks unset already does.
    throw std::invalid_argument(
        "level arena: a near/far placement needs a near/far boundary; "
        "without one every group is far, which is the arm that loses");
  }
  NearFarPlacement placement;
  placement.near_max_level = near_max_level;
  placement.participants.assign(participants, -1);
  placement.groups.assign(groups.size(), -1);
  placement.group_is_near.assign(groups.size(), false);
  placement.helpers.assign(helpers, -1);
  for (size_t g = 0; g < groups.size(); ++g) {
    placement.group_is_near[g] = GroupIsNear(groups[g], near_max_level);
  }
  if (host.domains.empty()) return placement;
  // ONE DOMAIN IS NOT A SPLIT.  The rule this file implements needs at least
  // two cache domains; on one die there is nothing for the split to buy, so
  // on a single-domain host nothing is placed, which is the library's default
  // behaviour.
  if (!host.Split()) return placement;

  const std::vector<int>& near = host.domains.front();
  size_t near_owners = 0;
  for (bool is_near : placement.group_is_near) near_owners += is_near ? 1 : 0;
  // The top's group is the first; its helpers are on its side.
  const bool helpers_near = !groups.empty() && placement.group_is_near.front();
  const size_t near_helpers = helpers_near ? helpers : 0;
  const size_t far_helpers = helpers_near ? 0 : helpers;
  const size_t needed = size_t{participants} + near_owners + near_helpers;
  if (needed > near.size()) {
    throw std::invalid_argument(
        "level arena: " + std::to_string(participants) +
        " batch participants (the caller included), " +
        std::to_string(near_owners) + " near owner groups and " +
        std::to_string(near_helpers) + " near helpers need " +
        std::to_string(needed) + " cores on the request thread's cache "
        "domain, which has " + std::to_string(near.size()) +
        "; spend fewer threads or move the boundary down");
  }
  if (near_owners == 0 && !groups.empty()) {
    // THE SPLIT AND THE PLACEMENT TRAVEL TOGETHER.  With no near group there
    // is no split, and pinning every group off the request thread's domain is
    // exactly the losing arrangement the header describes.
    // It happens for one reason -- one owner thread, whose single group holds
    // every level and is therefore far -- and the fix is another thread.
    throw std::invalid_argument(
        "level arena: no owner group is near (a single group holds every "
        "level), so this placement would move the whole rebuild off the "
        "request thread's cache domain, which is the arm that loses");
  }
  size_t far_cpus = 0;
  for (size_t d = 1; d < host.domains.size(); ++d) {
    far_cpus += host.domains[d].size();
  }
  const size_t far_owners = groups.size() - near_owners;
  if (far_owners + far_helpers > far_cpus) {
    throw std::invalid_argument(
        "level arena: " + std::to_string(far_owners) + " far owner groups and " +
        std::to_string(far_helpers) +
        " far helpers need as many cores outside the request thread's "
        "cache domain, which has " + std::to_string(far_cpus));
  }

  size_t at = 0;
  placement.requester = near[at];
  placement.participants[0] = near[at++];  // the caller IS participant 0
  for (unsigned p = 1; p < participants; ++p) {
    placement.participants[p] = near[at++];
  }
  for (size_t g = 0; g < groups.size(); ++g) {
    if (placement.group_is_near[g]) placement.groups[g] = near[at++];
  }
  if (helpers_near) {
    for (unsigned h = 0; h < helpers; ++h) placement.helpers[h] = near[at++];
  }
  // The far CPUs in ROUND-ROBIN order across the domains, so a host with
  // three CCDs spreads its far groups over both of the other two before it
  // puts a second one on either.
  std::vector<int> far;
  far.reserve(far_cpus);
  for (size_t index = 0;; ++index) {
    bool any = false;
    for (size_t d = 1; d < host.domains.size(); ++d) {
      if (index >= host.domains[d].size()) continue;
      far.push_back(host.domains[d][index]);
      any = true;
    }
    if (!any) break;
  }
  size_t next_far = 0;
  for (size_t g = 0; g < groups.size(); ++g) {
    if (placement.group_is_near[g]) continue;
    placement.groups[g] = far[next_far++];
  }
  if (!helpers_near) {
    for (unsigned h = 0; h < helpers; ++h) placement.helpers[h] = far[next_far++];
  }
  placement.split = far_owners != 0;
  return placement;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
