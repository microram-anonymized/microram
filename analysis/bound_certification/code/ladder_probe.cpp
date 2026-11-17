// Which fanout ladder the engine's capacity planner builds at a stated
// capacity.  Reads the public planner only; allocates no tables.
//
// Arguments: B L D r0 s q tier H [ladder], as configuration_probe.cpp.  The
// request asks for exactly the configuration's rounded capacity with r0 and
// D pinned (the analysis pins both) and every other planner option at its
// default -- in particular the default half-fanout prefix -- and reports the
// geometry the planner chooses.  `default_ladder` says whether that is this
// configuration's ladder.
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"

#include <cstdio>
#include <iostream>
#include <string>

namespace la = microram::byteslice::levelarena;

int main(int argc, char** argv) {
  try {
    if (argc != 9 && argc != 10)
      throw std::invalid_argument("expected eight public parameters and an optional fanout ladder");
    la::LevelArenaGeometry::Params p;
    p.branching = std::stoul(argv[1]);
    p.levels = std::stoul(argv[2]);
    p.top_digit = std::stoul(argv[3]);
    p.prefix_flushes = std::stoul(argv[4]);
    p.stash_buckets = std::stoull(argv[5]);
    p.dense_prefixes = std::stoul(argv[6]);
    p.tier_buckets = std::stoull(argv[7]);
    const uint64_t horizon = std::stoull(argv[8]);
    if (argc == 10 && std::string(argv[9]) != "-") {
      const std::string ladder = argv[9];
      size_t at = 0;
      while (at <= ladder.size()) {
        const size_t comma = std::min(ladder.find(',', at), ladder.size());
        p.level_fanouts.push_back(std::stoul(ladder.substr(at, comma - at)));
        at = comma + 1;
      }
    }
    la::LevelArenaCapacityRequest r;
    r.entries = la::LevelArenaCapacityOf(p);
    r.max_accesses = horizon;
    r.branching = p.branching;
    r.stash_buckets = p.stash_buckets;
    r.dense_prefixes = p.dense_prefixes;
    r.tier_buckets = p.tier_buckets;
    r.prefix_flushes = p.prefix_flushes;
    r.top_digit = p.top_digit;
    r.min_top_digit = p.top_digit;
    const auto choice = la::PlanLevelArenaCapacity(r);
    std::vector<unsigned> chosen = choice.geometry.level_fanouts;
    if (chosen.empty()) chosen.assign(choice.geometry.levels - 1, choice.geometry.branching);
    std::vector<unsigned> stated = p.level_fanouts;
    if (stated.empty()) stated.assign(p.levels - 1, p.branching);
    std::printf("{\"kind\":\"planner_ladder\",\"capacity_entries\":%llu,\"levels\":%u,"
                "\"top_digit\":%u,\"prefix_flushes\":%u,\"half_fanout_prefix\":%s,"
                "\"level_fanouts\":[",
                static_cast<unsigned long long>(choice.capacity), choice.geometry.levels,
                choice.geometry.top_digit, choice.geometry.prefix_flushes,
                choice.half_fanout_prefix ? "true" : "false");
    for (size_t i = 0; i < chosen.size(); ++i) std::printf("%s%u", i ? "," : "", chosen[i]);
    std::printf("],\"default_ladder\":%s}\n",
                choice.geometry.levels == p.levels && chosen == stated &&
                        choice.capacity == r.entries
                    ? "true" : "false");
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n';
    return 2;
  }
}
