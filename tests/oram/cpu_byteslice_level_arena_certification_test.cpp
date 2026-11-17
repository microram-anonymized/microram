// The planner's certification report
// (src/oram/levelarena/cpu_byteslice_level_arena_certification.hpp).  Every
// resolved plan says whether its exact configuration -- geometry, per-level
// tier widths, stash depths and access horizon -- is covered by a certified
// record, i.e. one for which the offline analysis
// (analysis/bound_certification/README.md) bounds the probability of any
// capacity overflow over the horizon, and if not, why not.  An uncovered plan
// is flagged, not refused.
//
// Every expectation is read from the generated table, never hard-coded, so
// regenerating the table from new artifacts
// (analysis/bound_certification/code/export_certified_bounds.py) needs no
// edit here.  What IS fixed is the semantics: which configurations a record
// applies to, and the reason an uncovered one names.  The file also guards
// against a hash cycle: the certification artifacts hash the headers their
// native probes compile, so no probe may include the generated table.

#include <algorithm>
#include <cpu_byteslice_oram/configuration.hpp>
#include <cpu_byteslice_oram/oram.hpp>

#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {
namespace o = cpu_byteslice_oram;
namespace la = microram::byteslice::levelarena;
using Status = la::LevelArenaCertificationStatus;

int failures = 0;
void Expect(bool value, const std::string& what) {
  if (!value) {
    std::fprintf(stderr, "FAIL: %s\n", what.c_str());
    ++failures;
  }
}
bool Contains(const std::string& text, const std::string& part) {
  return text.find(part) != std::string::npos;
}

const o::ResolvedChoice* FindChoice(const o::ResolvedPlan& plan, const std::string& field) {
  for (const auto& c : plan.choices())
    if (c.field == field) return &c;
  return nullptr;
}

std::vector<unsigned> Split(const char* text) {
  std::vector<unsigned> out;
  std::stringstream in(text);
  std::string part;
  while (std::getline(in, part, ',')) out.push_back(static_cast<unsigned>(std::stoul(part)));
  return out;
}

la::LevelArenaGeometry::Params ParamsOf(const la::CertifiedBoundRecord& r) {
  la::LevelArenaGeometry::Params p;
  p.branching = r.branching;
  p.levels = r.levels;
  p.top_digit = r.top_digit;
  p.prefix_flushes = r.prefix_flushes;
  p.stash_buckets = r.stash_buckets;
  p.dense_prefixes = r.dense_prefixes;
  p.level_fanouts = Split(r.level_fanouts);
  for (unsigned w : Split(r.level_tier_buckets)) p.level_tier_buckets.push_back(w);
  p.tier_buckets = *std::max_element(p.level_tier_buckets.begin(), p.level_tier_buckets.end());
  // The exported records cover the default dense-direct level one.
  return p;
}

// The per-level tier widths a geometry's params give, a shared width
// written out per level.
std::vector<unsigned> TierWidths(const la::LevelArenaGeometry::Params& g) {
  if (g.level_tier_buckets.empty()) return std::vector<unsigned>(g.levels, unsigned(g.tier_buckets));
  return std::vector<unsigned>(g.level_tier_buckets.begin(), g.level_tier_buckets.end());
}

bool SameShape(const la::CertifiedBoundRecord& r, const la::LevelArenaGeometry::Params& g) {
  std::vector<unsigned> fanouts = g.level_fanouts;
  if (fanouts.empty()) fanouts.assign(g.levels - 1, g.branching);
  return r.branching == g.branching && r.levels == g.levels && r.prefix_flushes == g.prefix_flushes &&
         r.top_digit == g.top_digit && Split(r.level_fanouts) == fanouts &&
         Split(r.level_tier_buckets) == TierWidths(g) && r.stash_buckets == g.stash_buckets &&
         r.dense_prefixes == g.dense_prefixes;
}

std::vector<const la::CertifiedBoundRecord*> Records() {
  std::vector<const la::CertifiedBoundRecord*> out;
  for (size_t i = 0; i < la::kCertifiedBoundRecordCount; ++i) out.push_back(&la::kCertifiedBoundRecords[i]);
  return out;
}

// The least bound among the records a certified lookup could have used.
const la::CertifiedBoundRecord* Expected(const la::LevelArenaGeometry::Params& g, uint64_t horizon) {
  const la::CertifiedBoundRecord* best = nullptr;
  const la::LevelArenaGeometry geometry(g);
  const la::LevelArenaStashSizing sizing(geometry, horizon);
  std::string stash;
  for (unsigned l = 1; l <= geometry.Levels(); ++l)
    stash += (l > 1 ? "," : "") + std::to_string(sizing.Buckets(l));
  for (const auto* r : Records()) {
    if (r->capacity_entries != geometry.CapacityEntries() || r->horizon_accesses < horizon ||
        !SameShape(*r, g) || stash != r->level_stash_buckets)
      continue;
    if (!best || r->bound_log2_millis < best->bound_log2_millis) best = r;
  }
  return best;
}

void ExpectMatches(const la::LevelArenaCertification& c, const la::CertifiedBoundRecord& r,
                   const std::string& what) {
  Expect(c.status == (r.meets_target ? Status::kCertified : Status::kAboveTarget),
         what + ": status follows the record's exact comparison");
  Expect(c.failure_bound_log2_millis && *c.failure_bound_log2_millis == r.bound_log2_millis,
         what + ": the recorded bound is reported");
  Expect(c.record == r.name && c.artifact == r.artifact && c.certified_horizon == r.horizon_accesses,
         what + ": the record is named");
  Expect(c.target_log2 == -64, what + ": target is 2^-64");
  Expect(Contains(c.reason, "conditional") && Contains(c.reason, "unconditional bound is 1"),
         what + ": the reason states the bound is conditional");
  Expect(c.development_table == la::kCertifiedBoundsStale &&
             (!la::kCertifiedBoundsStale || Contains(c.reason, "development table")),
         what + ": a stale table says so");
}

void ExpectNotCovered(const la::LevelArenaCertification& c, const std::string& part,
                      const std::string& what) {
  Expect(c.status == Status::kNotCovered, what + ": not covered");
  Expect(!c.failure_bound_log2_millis && c.record.empty(), what + ": no bound without a record");
  Expect(Contains(c.reason, part), what + ": reason names '" + part + "' (got: " + c.reason + ")");
}

o::OptionOverrides Incremental() {
  o::OptionOverrides p;
  p.scheme = o::Scheme::kHierarchicalIncremental;
  p.incremental.emplace();
  return p;
}

// ---------------------------------------------------------------------------

void TestTableSelfConsistency() {
  Expect(la::kCertifiedBoundRecordCount > 0, "the generated table holds records");
  std::set<std::string> names;
  for (const auto* r : Records()) {
    Expect(names.insert(std::string(r->artifact) + "/" + r->name).second, "record names are unique");
    Expect(Split(r->level_fanouts).size() + 1 == r->levels && Split(r->level_stash_buckets).size() == r->levels,
           std::string(r->name) + ": ladder and stash lists fit L");
    Expect(r->bound_log2_millis <= 0, std::string(r->name) + ": a bound is at most 1");
    // The millis round the exact bound UP, so "meets 2^-64" and "millis at
    // most -64000" are the same statement.
    Expect(r->meets_target == (r->bound_log2_millis <= -64000),
           std::string(r->name) + ": the rounded bound agrees with the exact comparison");
    // EVERY RECORD MUST MATCH ITS OWN SHAPE UNDER THE CURRENT SIZING: a
    // record whose stash depths the production sizing does not reproduce
    // would be dead weight, and this is where that shows.
    const auto p = ParamsOf(*r);
    const auto c = la::CertifyLevelArenaGeometry(p, r->horizon_accesses);
    Expect(c.status != Status::kNotCovered, std::string(r->name) + ": record matches its own shape (" +
                                                c.reason + ")");
    if (c.status != Status::kNotCovered) {
      const auto* e = Expected(p, r->horizon_accesses);
      Expect(e && c.record == e->name && c.artifact == e->artifact,
             std::string(r->name) + ": least bound among matching records");
    }
    ExpectNotCovered(la::CertifyLevelArenaGeometry(p, r->horizon_accesses + 1), "exceeds the certified",
                     std::string(r->name) + " one access past its horizon");
  }
  Expect(la::certification_detail::Millis(-67190) == "-67.190" && la::certification_detail::Millis(-5) == "-0.005" &&
             la::certification_detail::Millis(0) == "0.000",
         "millis are formatted exactly");
}

void TestDefaultAt2p27() {
  const o::MapSpec spec{size_t{1} << 27, 8, 16};
  const auto plan = o::resolve_options(spec, {1}, {}, Incremental());
  const auto& g = plan.hierarchy_certification();
  const auto& geometry = [&] {
    // The plan's geometry, through the choices it exposes.
    la::LevelArenaGeometry::Params p;
    p.branching = 8;
    p.levels = static_cast<unsigned>(std::stoul(FindChoice(plan, "hierarchy.levels")->value));
    p.prefix_flushes = static_cast<unsigned>(std::stoul(FindChoice(plan, "hierarchy.prefix_flushes")->value));
    p.top_digit = static_cast<unsigned>(std::stoul(FindChoice(plan, "hierarchy.top_digit")->value));
    p.tier_buckets = 0;
    for (unsigned l = 1; l < p.levels; ++l)
      p.level_fanouts.push_back(
          static_cast<unsigned>(std::stoul(FindChoice(plan, "hierarchy.fanout." + std::to_string(l))->value)));
    // The automatic tier resolution the plan used: each level's own width.
    return la::ResolveLevelArenaTierGeometry(p, spec.max_accesses);
  }();
  const auto* record = Expected(geometry, spec.max_accesses);
  Expect(record != nullptr, "the planner's default at 2^27 has a record");
  if (record) {
    ExpectMatches(g, *record, "default 2^27");
    Expect(record->meets_target && g.certified(), "the planner's default at 2^27 is certified");
  }
  Expect(plan.certification().status == g.status &&
             plan.certification().failure_bound_log2_millis == g.failure_bound_log2_millis,
         "an incremental map's certification is its hierarchy's");
  // The choices carry the same report.
  const auto* status = FindChoice(plan, "hierarchy.certification");
  const auto* bound = FindChoice(plan, "hierarchy.failure_bound_log2");
  const auto* top = FindChoice(plan, "certification");
  const auto* top_bound = FindChoice(plan, "failure_bound_log2");
  Expect(status && bound && top && top_bound, "certification choices appear");
  if (status && bound && top && top_bound) {
    Expect(status->value == la::LevelArenaCertificationStatusName(g.status) && status->reason == g.reason &&
               status->source == o::ChoiceSource::kDerived,
           "hierarchy.certification is the status with the reason");
    Expect(g.failure_bound_log2_millis &&
               bound->value == la::certification_detail::Millis(*g.failure_bound_log2_millis),
           "hierarchy.failure_bound_log2 is the bound");
    Expect(top->value == status->value && top_bound->value == bound->value, "the map-level report is the same");
  }
  Expect(!Contains(plan.configuration_key(), "certification") &&
             !Contains(plan.configuration_key(), "failure_bound_log2"),
         "the report is not part of the configuration key");

  // A horizon ABOVE the record's is not covered, whatever the geometry.
  bool longer_tabled = false;
  for (const auto* r : Records())
    longer_tabled = longer_tabled || (r->capacity_entries == spec.requested_capacity &&
                                      r->horizon_accesses >= (uint64_t{1} << 40));
  if (!longer_tabled) {
    const auto longer = o::resolve_options({spec.requested_capacity, 8, 16, uint64_t{1} << 40}, {1}, {},
                                           Incremental());
    ExpectNotCovered(longer.hierarchy_certification(), "horizon 2^40 exceeds the certified",
                     "a 2^40 horizon at 2^27");
    const auto* c = FindChoice(longer, "hierarchy.failure_bound_log2");
    Expect(c && c->value == "none", "no bound is reported for an uncovered plan");
  }

  // A horizon BELOW it: covered exactly when the sizing is identical.
  bool shorter_same = false;
  bool shorter_different = false;
  for (unsigned k = 31; k >= 12; --k) {
    const uint64_t h = uint64_t{1} << k;
    auto p = geometry;
    const auto c = la::CertifyLevelArenaGeometry(p, h);
    const la::LevelArenaGeometry lg(p);
    const la::LevelArenaStashSizing at(lg, h);
    const la::LevelArenaStashSizing full(lg, spec.max_accesses);
    // The tier is the plan's explicit width here, so only the stash depths
    // can differ.
    bool same = true;
    for (unsigned l = 1; l <= lg.Levels(); ++l) same = same && at.Buckets(l) == full.Buckets(l);
    if (same && record) {
      shorter_same = true;
      ExpectMatches(c, *record, "horizon 2^" + std::to_string(k) + " at identical sizing");
      Expect(Contains(c.reason, "upper bound for the 2^" + std::to_string(k)),
             "a shorter horizon says the recorded bound is an upper bound");
    } else if (!same) {
      shorter_different = true;
      ExpectNotCovered(c, "stash depths", "horizon 2^" + std::to_string(k) + " with shallower stashes");
    }
  }
  Expect(shorter_same, "some shorter horizon keeps the 2^32 sizing");
  Expect(shorter_different, "some shorter horizon changes the sizing");

  // An explicit tier wider than the automatic one is a different shape.
  auto wide = Incremental();
  wide.incremental->tier_buckets = geometry.tier_buckets + 1;
  ExpectNotCovered(o::resolve_options(spec, {1}, {}, wide).hierarchy_certification(), "tier widths",
                   "an explicit wider tier");
  // A shared pin at the widest automatic width is the same shape exactly
  // when the automatic profile is uniform.
  wide.incremental->tier_buckets = geometry.tier_buckets;
  const std::vector<unsigned> widths = TierWidths(geometry);
  const bool uniform = std::all_of(widths.begin(), widths.end(),
                                   [&](unsigned w) { return w == widths.front(); });
  Expect((o::resolve_options(spec, {1}, {}, wide).hierarchy_certification().status == g.status) ==
             (uniform || g.status == Status::kNotCovered),
         "a shared tier pin keeps the report exactly when the profile is uniform");
}

void TestTopDigitPin() {
  const o::MapSpec spec{size_t{1} << 27, 8, 16};
  for (unsigned d : {1u, 2u, 4u}) {
    auto pin = Incremental();
    pin.incremental->top_digit = d;
    const auto plan = o::resolve_options(spec, {1}, {}, pin);
    const auto& c = plan.hierarchy_certification();
    bool tabled = false;
    for (const auto* r : Records()) tabled = tabled || (r->capacity_entries == spec.requested_capacity && r->top_digit == d);
    if (!tabled) {
      ExpectNotCovered(c, "not among the certified", "D = " + std::to_string(d) + " without a record");
      continue;
    }
    Expect(c.status != Status::kNotCovered, "a D = " + std::to_string(d) + " pin at 2^27 has its record (" +
                                                c.reason + ")");
    for (const auto* r : Records())
      // Names repeat across online-stash settings; the artifact tells them apart.
      if (r->name == c.record && r->artifact == c.artifact) {
        Expect(r->top_digit == d, "the D pin's record has that D");
        ExpectMatches(c, *r, "D = " + std::to_string(d) + " pin");
      }
  }
}

void TestUncovered() {
  // A capacity with no records, found from the table rather than assumed.
  bool found = false;
  for (unsigned k = 12; k <= 36 && !found; ++k) {
    const uint64_t n = uint64_t{1} << k;
    bool tabled = false;
    for (const auto* r : Records()) tabled = tabled || r->capacity_entries == n;
    if (tabled) continue;
    const auto plan = o::resolve_options({n, 8, 16}, {1}, {}, Incremental());
    if (plan.actual_capacity() != n) continue;
    found = true;
    ExpectNotCovered(plan.hierarchy_certification(), "capacity 2^" + std::to_string(k) +
                     " has no certified configurations", "an untabled capacity");
    const auto* c = FindChoice(plan, "hierarchy.certification");
    Expect(c && c->value == "not_covered" && Contains(c->reason, "has no certified"),
           "the choice flags the untabled capacity with its reason");
  }
  Expect(found, "some capacity in 2^12..2^36 is untabled (else extend this test)");

  // B = 4.
  auto b4 = Incremental();
  b4.incremental->branching_factor = 4;
  ExpectNotCovered(o::resolve_options({size_t{1} << 27, 8, 16}, {1}, {}, b4).hierarchy_certification(), "B = 4",
                   "B = 4");

  // Options the analysis does not model.
  const auto base = o::resolve_options({size_t{1} << 27, 8, 16}, {1}, {}, Incremental());
  const la::LevelArenaGeometry::Params p = [&] {
    for (const auto* r : Records())
      if (r->name == base.hierarchy_certification().record &&
          r->artifact == base.hierarchy_certification().artifact)
        return ParamsOf(*r);
    return ParamsOf(la::kCertifiedBoundRecords[0]);
  }();
  auto bank_off = p;
  bank_off.bank_first = la::BankFirst::kOff;
  ExpectNotCovered(la::CertifyLevelArenaGeometry(bank_off, uint64_t{1} << 32), "bank_first", "bank-first off");
  // A shared tier pin of the widest width is a different shape from the
  // automatic per-level profile wherever the profile is not uniform.
  auto shared = p;
  shared.level_tier_buckets.clear();
  shared.tier_buckets = 2;
  ExpectNotCovered(la::CertifyLevelArenaGeometry(shared, uint64_t{1} << 32), "per-level tier widths",
                   "a shared tier pin");
}

void TestSchemes() {
  const o::MapSpec spec{size_t{1} << 16, 8, 512};
  o::OptionOverrides tree;
  tree.scheme = o::Scheme::kTree;
  const auto t = o::resolve_options(spec, {4}, {}, tree);
  ExpectNotCovered(t.certification(), "tree ORAM", "a tree map");
  const auto* top = FindChoice(t, "certification");
  const auto* pm = FindChoice(t, "position_map.certification");
  const auto* pm_bound = FindChoice(t, "position_map.failure_bound_log2");
  Expect(top && top->value == "not_covered", "a tree's top-level report is not covered");
  Expect(pm && pm_bound && pm->value == la::LevelArenaCertificationStatusName(t.hierarchy_certification().status),
         "a tree reports its position map under its prefix");
  Expect(!FindChoice(t, "hierarchy.certification"), "a tree has no hierarchy.* report");

  o::OptionOverrides sync;
  sync.scheme = o::Scheme::kHierarchicalSynchronous;
  // The synchronous storage mode runs the same planner and residual routing,
  // so it is certified from the same table as the incremental scheme.
  const auto s = o::resolve_options({size_t{1} << 16, 8, 16}, {1}, {}, sync);
  const auto& sh = s.hierarchy_certification();
  Expect(sh.status != Status::kNotCovered && !sh.record.empty() && sh.failure_bound_log2_millis,
         "a synchronous plan is certified from the table (got: " + sh.reason + ")");
  Expect(s.certification().status == sh.status && s.certification().record == sh.record,
         "a synchronous map's report is its hierarchy's");
  const auto* sc = FindChoice(s, "hierarchy.certification");
  Expect(sc && sc->value == la::LevelArenaCertificationStatusName(sh.status),
         "a synchronous plan reports its certification");
}

void TestByteMapAccessor() {
  o::Options options;
  options.deamortized_owner_threads = 0;
  options.max_accesses = uint64_t{1} << 30;
  o::ByteMap<true> map(4096, 8, 8, options);
  const auto c = map.certification();
  const auto e = la::CertifyLevelArenaGeometry(map.geometry_choice().geometry, options.max_accesses);
  Expect(c.status == e.status && c.reason == e.reason, "ByteMap::certification is the planner's lookup");
}

// THE HASH-CYCLE GUARD.  No native probe of the certification may include
// the table: the artifacts hash every header their probes compile against.
// A lexical include scan (every #include, conditional or not, resolved
// against the including file's directory, the repository root and include/)
// over-approximates the compiler's closure, so a clean scan is sufficient.
std::filesystem::path SourceRoot() {
#ifdef CPU_BYTESLICE_ORAM_SOURCE_DIR
  return CPU_BYTESLICE_ORAM_SOURCE_DIR;
#else
  return std::filesystem::path(__FILE__).parent_path().parent_path().parent_path();
#endif
}

void TestProbesDoNotReachTheTable() {
  namespace fs = std::filesystem;
  const fs::path root = SourceRoot();
  const fs::path probes = root / "analysis/bound_certification/code";
  Expect(fs::is_directory(probes), "the certification probes are found at " + probes.string());
  if (!fs::is_directory(probes)) return;
  const std::set<std::string> guarded = {
      fs::weakly_canonical(root / "src/oram/levelarena/cpu_byteslice_level_arena_certification.hpp").string(),
      fs::weakly_canonical(root / "src/oram/levelarena/cpu_byteslice_level_arena_certified_bounds.inc").string()};
  const std::regex include(R"(^\s*#\s*include\s*[<"]([^>"]+)[>"])");
  size_t scanned = 0;
  for (const auto& entry : fs::directory_iterator(probes)) {
    if (entry.path().extension() != ".cpp") continue;
    ++scanned;
    std::vector<fs::path> todo{fs::weakly_canonical(entry.path())};
    std::set<std::string> seen;
    while (!todo.empty()) {
      const fs::path file = todo.back();
      todo.pop_back();
      if (!seen.insert(file.string()).second) continue;
      Expect(!guarded.count(file.string()),
             entry.path().filename().string() + " reaches " + file.string() + " (a hash cycle)");
      std::ifstream in(file);
      std::string line;
      std::smatch m;
      while (std::getline(in, line)) {
        if (!std::regex_search(line, m, include)) continue;
        for (const fs::path& base : {file.parent_path(), root, root / "include"}) {
          const fs::path candidate = base / m[1].str();
          if (fs::is_regular_file(candidate)) {
            todo.push_back(fs::weakly_canonical(candidate));
            break;
          }
        }
      }
    }
  }
  Expect(scanned > 0, "some probe was scanned");
  // And the scan does see the table where it IS included.
  std::vector<fs::path> todo{fs::weakly_canonical(root / "include/cpu_byteslice_oram/byte_map.hpp")};
  std::set<std::string> seen;
  bool reached = false;
  while (!todo.empty()) {
    const fs::path file = todo.back();
    todo.pop_back();
    if (!seen.insert(file.string()).second) continue;
    reached = reached || guarded.count(file.string());
    std::ifstream in(file);
    std::string line;
    std::smatch m;
    while (std::getline(in, line)) {
      if (!std::regex_search(line, m, include)) continue;
      for (const fs::path& base : {file.parent_path(), root, root / "include"}) {
        const fs::path candidate = base / m[1].str();
        if (fs::is_regular_file(candidate)) {
          todo.push_back(fs::weakly_canonical(candidate));
          break;
        }
      }
    }
  }
  Expect(reached, "the scan finds the table from byte_map.hpp (the instrument works)");
}

}  // namespace

void TestOnlineStashSettings() {
  // Each online stash setting has its own direct level-one certificate.
  // At 2^24 the actual defaults use r0 = 8, including s = 4 (U_1 = 64).
  // Coverage must include that default as well as a smaller pinned prefix.
  const o::MapSpec spec{size_t{1} << 24, 8, 16};
  auto s2 = Incremental();
  s2.incremental->online_stash_entries = 128;
  const auto c2 = o::resolve_options(spec, {1}, {}, s2).hierarchy_certification();
  Expect(c2.certified(), "s = 2 default at 2^24 is certified (" + c2.reason + ")");
  Expect(Contains(c2.artifact, "configuration_space_s2_q2_"), "s = 2 is certified from its own artifact");
  auto s4 = Incremental();
  s4.incremental->online_stash_entries = 256;
  const auto default4 = o::resolve_options(spec, {1}, {}, s4);
  const auto& default_c4 = default4.hierarchy_certification();
  const auto* prefix4 = FindChoice(default4, "hierarchy.prefix_flushes");
  Expect(prefix4 && prefix4->value == "8", "s = 4 default uses r0 = 8 at 2^24");
  Expect(default_c4.certified(), "s = 4 default at 2^24 is certified (" + default_c4.reason + ")");
  Expect(default_c4.failure_bound_log2_millis.has_value(), "s = 4 default has a bound");
  Expect(Contains(default_c4.artifact, "configuration_space_s4_q2_2p24.json"),
         "s = 4 default is certified from its own capacity artifact");
  s4.incremental->prefix_flushes = 4;
  const auto c4 = o::resolve_options(spec, {1}, {}, s4).hierarchy_certification();
  Expect(c4.certified(), "s = 4, r0 = 4 at 2^24 is certified (" + c4.reason + ")");
}

int main() {
  TestTableSelfConsistency();
  TestDefaultAt2p27();
  TestTopDigitPin();
  TestOnlineStashSettings();
  TestUncovered();
  TestSchemes();
  TestByteMapAccessor();
  TestProbesDoNotReachTheTable();
  if (failures) {
    std::fprintf(stderr, "%d failure(s)\n", failures);
    return 1;
  }
  std::printf("level arena certification report tests passed (%zu records%s)\n", la::kCertifiedBoundRecordCount,
              la::kCertifiedBoundsStale ? ", DEVELOPMENT table" : "");
}
