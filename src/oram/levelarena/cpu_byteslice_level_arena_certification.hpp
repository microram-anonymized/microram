#pragma once

// WHAT THE CERTIFICATION SAYS ABOUT ONE GEOMETRY.  The capacity planner
// (cpu_byteslice_level_arena_capacity.hpp) chooses a geometry by bytes and a
// few stated rules; it does not consult the failure-probability analysis in
// analysis/bound_certification.  This header is the other direction: given
// the geometry the planner (or a caller's pins) produced and the request
// horizon, it looks the geometry up in the table of configurations that
// analysis certified and reports
//
//   - kCertified: a record matches and its composed conditional bound on
//     "some rebuild capacity test overflows within the horizon" is at most
//     2^-64;
//   - kAboveTarget: a record matches but its bound is above 2^-64 (that
//     certifies nothing; it does not show that failures are frequent);
//   - kNotCovered: no record applies, with the first unmet requirement.
//
// It never refuses anything: an uncovered configuration still builds and
// runs, and the report says so.
//
// EVERY BOUND HERE IS CONDITIONAL.  The composed bound of
// certify_configuration_space.py holds under the checker's undischarged
// premises (native-source and frontier propositions supplying the logical
// histories, the imported certificates' recorded assumptions, an empty or
// directly initialized start, and the deterministic inventory's reviewed
// per-rule classification; analysis/bound_certification/REPORT.pdf and
// CONFIGURATION_SPACE.md there list them).  With those premises undischarged
// the unconditional bound is still 1.  A reported bound is ceil(1000 log2 bound) / 1000, rounded UP from the
// exact rational, so it never understates the certified number.
//
// THE KEY, and why it is complete.  A per-job bound is a function of the
// job's public native shape, which is a function of the geometry and of the
// stash sizing alone (CONFIGURATION_SPACE.md, "Scope and exact keys").  So
// a record applies exactly when B, s, q, L, r0, D, the fanout ladder of levels 1..L-1, the
// per-level tier widths and the per-level stash depths that
// LevelArenaStashSizing gives AT THE CALLER'S HORIZON all equal the
// record's, the options the analysis does not model are off, and the
// caller's horizon is at most the record's.  The last condition is what
// makes a shorter horizon safe: with identical sizing every job has the
// identical per-job bound and runs no more often, so the record's lifetime
// sum is an upper bound for it.  A shorter horizon whose sizing comes out
// different (shallower stashes, a narrower tier) is a different shape and
// is not covered.  What does NOT enter:
//   - the value width: probe rows carry no layout, and the level-one writer
//     lists are checked identical at 1..1024 value bytes;
//   - the key width: jobs route on the keyed hash of the stored key, never
//     on its width; a key of 16 bytes or more is stored as its 128-bit AES
//     rehash, whose collisions are a correctness event outside this
//     capacity bound, not a capacity failure;
//   - the scheduling knobs (owner threads, level groups, helpers, lanes,
//     batch participants, near/far boundary, slicing): they decide which
//     thread runs a job and when, not the job's shape; lanes are
//     byte-identical across lane counts.
// Out of scope, reported as kNotCovered: bank_first kOff (the analysis does
// not model it), and anything the table has no
// record for (other B, s, q, capacities, ladders or tier widths).
//
// WHY THIS IS A SEPARATE HEADER.  The table below is generated from the
// certification artifacts, so no probe may compile against it: the artifacts
// would then depend on their own output.  (What they do record is the SHA-256
// of the engine headers that decide job shapes and stash sizes, listed in
// analysis/bound_certification/code/source_scope.py.)  So this header and its generated .inc are
// included only from include/cpu_byteslice_oram/byte_map.hpp, and
// export_certified_bounds.py and cpu_byteslice_level_arena_certification_test
// both check that no probe's include closure reaches them.  Do not include
// this from anything under src/ that a probe could reach.
//
// Regenerate the table after rerunning the analysis:
//   cd analysis/bound_certification/code && python3 export_certified_bounds.py

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <limits>
#include <optional>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// One certified configuration, as export_certified_bounds.py writes it.
// The ladder and the stash depths are comma-separated strings so a record
// is one constexpr literal; they are compared as strings of the same form.
struct CertifiedBoundRecord {
  const char* name;           // the analysis's candidate name
  const char* artifact;       // configuration_space_2p<k>.json
  uint64_t capacity_entries;  // 32T
  unsigned branching;         // B
  size_t stash_buckets;       // s
  unsigned dense_prefixes;    // q
  uint64_t horizon_accesses;  // the horizon the bound covers
  unsigned levels;            // L
  unsigned prefix_flushes;    // r0
  unsigned top_digit;         // D
  const char* level_fanouts;  // levels 1..L-1, e.g. "4,4,4,8,8,8"
  const char* level_stash_buckets;  // levels 1..L
  const char* level_tier_buckets;   // levels 1..L, the tables each produces
  int bound_log2_millis;      // ceil(1000 log2 conditional lifetime bound)
  bool meets_target;          // the EXACT bound is <= 2^-64
};

#include "src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc"

inline constexpr int kLevelArenaCertificationTargetLog2 = -64;

enum class LevelArenaCertificationStatus { kCertified, kAboveTarget, kNotCovered };

inline const char* LevelArenaCertificationStatusName(
    LevelArenaCertificationStatus status) {
  switch (status) {
    case LevelArenaCertificationStatus::kCertified: return "certified";
    case LevelArenaCertificationStatus::kAboveTarget: return "above_target";
    case LevelArenaCertificationStatus::kNotCovered: return "not_covered";
  }
  return "?";
}

struct LevelArenaCertification {
  LevelArenaCertificationStatus status =
      LevelArenaCertificationStatus::kNotCovered;
  // ceil(1000 log2 bound) of the matching record: the CONDITIONAL lifetime
  // failure bound is at most 2^(millis / 1000).  Empty without a record.
  std::optional<int> failure_bound_log2_millis;
  int target_log2 = kLevelArenaCertificationTargetLog2;
  uint64_t certified_horizon = 0;  // the record's horizon; 0 without one
  std::string record;              // the record's name; empty without one
  std::string artifact;            // the artifact it came from
  // The table was exported with --allow-stale: its artifacts do not match
  // the tree they describe, so nothing it says is a certificate.
  bool development_table = kCertifiedBoundsStale;
  std::string reason;

  bool certified() const {
    return status == LevelArenaCertificationStatus::kCertified;
  }
  std::optional<double> failure_bound_log2() const {
    if (!failure_bound_log2_millis) return std::nullopt;
    return *failure_bound_log2_millis / 1000.0;
  }
};

namespace certification_detail {

inline std::string Join(const std::vector<size_t>& values) {
  std::string text;
  for (size_t i = 0; i < values.size(); ++i) {
    text += (i ? "," : "") + std::to_string(values[i]);
  }
  return text;
}

// 2^k for a power of two, the decimal otherwise.
inline std::string Count(uint64_t n) {
  if (n != 0 && (n & (n - 1)) == 0) {
    return "2^" + std::to_string(__builtin_ctzll(n));
  }
  return std::to_string(n);
}

// "-67.190": exact from the integer millis, no floating-point formatting.
inline std::string Millis(int millis) {
  const long long magnitude = std::llabs(static_cast<long long>(millis));
  std::string fraction = std::to_string(magnitude % 1000);
  fraction.insert(0, 3 - fraction.size(), '0');
  return (millis < 0 ? "-" : "") + std::to_string(magnitude / 1000) + "." +
         fraction;
}

inline std::string Premises() {
  return "conditional on the certification checker's undischarged premises "
         "(the unconditional bound is 1)";
}

inline LevelArenaCertification NotCovered(std::string reason) {
  LevelArenaCertification result;
  result.reason = "not covered: " + std::move(reason);
  if (result.development_table) {
    result.reason += " [development table exported with --allow-stale]";
  }
  return result;
}

}  // namespace certification_detail

// A report for something outside this analysis altogether (the tree ORAM),
// under the same type.
inline LevelArenaCertification LevelArenaNotCovered(std::string reason) {
  return certification_detail::NotCovered(std::move(reason));
}

// THE LOOKUP.  `params` is the geometry the engine is built from; an
// automatic tier width (tier_buckets = 0) is resolved here at the horizon,
// exactly as the engine resolves it.  `max_accesses` is the caller's request
// horizon, the one the engine sizes its stashes for.
inline LevelArenaCertification CertifyLevelArenaGeometry(
    LevelArenaGeometry::Params params, uint64_t max_accesses) {
  namespace cd = certification_detail;
  // Options the analysis does not model, first: no record can apply.
  if (params.bank_first != BankFirst::kNoClone) {
    return cd::NotCovered(
        "bank_first other than kNoClone is outside the certification (the "
        "checker models the default no-clone bank placement)");
  }
  if (max_accesses == 0) return cd::NotCovered("a zero request horizon");
  // The public shape: the ladder written out, the tier resolved, the stash
  // depths at THIS horizon.
  std::vector<size_t> fanouts;
  std::vector<size_t> stash;
  std::vector<size_t> tiers;
  uint64_t capacity = 0;
  try {
    if (params.tier_buckets == 0) {
      params = ResolveLevelArenaTierGeometry(params, max_accesses);
    }
    const LevelArenaGeometry geometry(params);
    const LevelArenaStashSizing sizing(geometry, max_accesses);
    for (unsigned l = 1; l < geometry.Levels(); ++l) {
      fanouts.push_back(geometry.Fanout(l));
    }
    for (unsigned l = 1; l <= geometry.Levels(); ++l) {
      stash.push_back(sizing.Buckets(l));
      tiers.push_back(geometry.TierBucketsOf(l));
    }
    capacity = geometry.CapacityEntries();
  } catch (const std::exception& error) {
    return cd::NotCovered(std::string("the geometry does not build: ") +
                          error.what());
  }
  const std::string fanout_text = cd::Join(fanouts);
  const std::string stash_text = cd::Join(stash);
  const std::string tier_text = cd::Join(tiers);

  const CertifiedBoundRecord* const begin = kCertifiedBoundRecords;
  const CertifiedBoundRecord* const end = begin + kCertifiedBoundRecordCount;
  if (begin == end) return cd::NotCovered("the certified table is empty");
  // Narrow the table one requirement at a time, so the reason names the
  // first one that fails.
  bool same_bsq = false;
  bool same_capacity = false;
  bool horizon_fits = false;
  bool same_geometry = false;
  bool same_tier = false;
  uint64_t widest_horizon = 0;
  std::string tabled_capacities;
  std::string tabled_settings;
  const CertifiedBoundRecord* geometry_match = nullptr;
  const CertifiedBoundRecord* best = nullptr;
  for (const CertifiedBoundRecord* r = begin; r != end; ++r) {
    const std::string setting = "B = " + std::to_string(r->branching) +
                                ", s = " + std::to_string(r->stash_buckets) +
                                ", q = " + std::to_string(r->dense_prefixes);
    if (tabled_settings.find(setting) == std::string::npos) {
      tabled_settings += (tabled_settings.empty() ? "" : "; ") + setting;
    }
    if (r->branching != params.branching ||
        r->stash_buckets != params.stash_buckets ||
        r->dense_prefixes != params.dense_prefixes) {
      continue;
    }
    same_bsq = true;
    const std::string c = cd::Count(r->capacity_entries);
    if (tabled_capacities.find(c) == std::string::npos) {
      tabled_capacities += (tabled_capacities.empty() ? "" : ", ") + c;
    }
    if (r->capacity_entries != capacity) continue;
    same_capacity = true;
    widest_horizon = std::max(widest_horizon, r->horizon_accesses);
    if (r->horizon_accesses < max_accesses) continue;
    horizon_fits = true;
    if (r->levels != params.levels || r->prefix_flushes != params.prefix_flushes ||
        r->top_digit != params.top_digit || fanout_text != r->level_fanouts) {
      continue;
    }
    same_geometry = true;
    geometry_match = r;
    if (tier_text != r->level_tier_buckets) continue;
    same_tier = true;
    if (stash_text != r->level_stash_buckets) continue;
    // Every matching record bounds this configuration; report the least.
    if (best == nullptr || r->bound_log2_millis < best->bound_log2_millis) {
      best = r;
    }
  }
  const std::string shape =
      "L = " + std::to_string(params.levels) +
      ", r0 = " + std::to_string(params.prefix_flushes) +
      ", D = " + std::to_string(params.top_digit) + ", fanouts " + fanout_text;
  if (!same_bsq) {
    return cd::NotCovered(
        "B = " + std::to_string(params.branching) +
        ", s = " + std::to_string(params.stash_buckets) +
        ", q = " + std::to_string(params.dense_prefixes) +
        " has no certified configurations (tabled: " + tabled_settings + ")");
  }
  if (!same_capacity) {
    return cd::NotCovered("capacity " + cd::Count(capacity) +
                          " has no certified configurations (tabled: " +
                          tabled_capacities + ")");
  }
  if (!horizon_fits) {
    return cd::NotCovered("horizon " + cd::Count(max_accesses) +
                          " exceeds the certified " + cd::Count(widest_horizon));
  }
  if (!same_geometry) {
    return cd::NotCovered("geometry " + shape + " is not among the certified "
                          "configurations at capacity " + cd::Count(capacity));
  }
  if (!same_tier) {
    return cd::NotCovered(
        "per-level tier widths " + tier_text + " differ from the certified " +
        geometry_match->level_tier_buckets +
        " (an explicit tier pin, or a horizon whose automatic sizing "
        "differs)");
  }
  if (best == nullptr) {
    return cd::NotCovered(
        "per-level stash depths " + stash_text + " at horizon " +
        cd::Count(max_accesses) + " differ from the certified " +
        geometry_match->level_stash_buckets + " (sized for " +
        cd::Count(geometry_match->horizon_accesses) + ")");
  }
  LevelArenaCertification result;
  result.status = best->meets_target
                      ? LevelArenaCertificationStatus::kCertified
                      : LevelArenaCertificationStatus::kAboveTarget;
  result.failure_bound_log2_millis = best->bound_log2_millis;
  result.certified_horizon = best->horizon_accesses;
  result.record = best->name;
  result.artifact = best->artifact;
  result.reason =
      std::string(best->meets_target ? "certified" : "above target") +
      ": capacity-failure probability at most 2^" +
      cd::Millis(best->bound_log2_millis) + (best->meets_target ? " <= " : " > ") +
      "2^" + std::to_string(kLevelArenaCertificationTargetLog2) + " over " +
      cd::Count(best->horizon_accesses) + " accesses";
  if (max_accesses < best->horizon_accesses) {
    result.reason += " (the certified horizon; an upper bound for the " +
                     cd::Count(max_accesses) + " requested, at identical sizing)";
  }
  result.reason += ", " + cd::Premises() + "; record " + best->name + " in " +
                   best->artifact;
  if (!best->meets_target) {
    result.reason += "; a bound above the target certifies nothing";
  }
  if (result.development_table) {
    result.reason += " [development table exported with --allow-stale: not a "
                     "certificate]";
  }
  return result;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
