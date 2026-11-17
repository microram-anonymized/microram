// Unit test for thread placement (benchmarks/support/placement.hpp): how the
// worker maps the harness, the caller and the library's worker roles (owners,
// online helpers, rebuild threads) onto the CPU list and cache domains it is
// given.  Topologies are injected; nothing is pinned.
#include "benchmarks/support/placement.hpp"
#include "benchmarks/support/worker.hpp"
#include <iostream>

namespace ob = oram_bench;
struct Role { int role; unsigned index; std::optional<unsigned> cpu; };
template <class F> void Reject(F&& f) {
  try { f(); } catch (const std::exception&) { return; }
  throw std::runtime_error("expected placement rejection");
}
void Check(bool value) { if (!value) throw std::runtime_error("placement assertion failed"); }
int main() {
  try {
    auto parse=[](std::string cpus, std::string scheme="tree") {
      std::vector<std::string> args{"worker","--resolve-only","1","--scheme",scheme,"--cores","2","--cpu-ids",cpus};
      std::vector<char*> argv;
      for (auto& arg:args) argv.push_back(arg.data());
      return ob::ParseWorker(static_cast<int>(argv.size()),argv.data());
    };
    Check(parse("3,11").cpu_ids==std::vector<unsigned>({3,11}));
    for (const auto* invalid : {"", "3", "3,3", "3,11,", "3,,11", "-1,3", "3,4294967296"})
      Reject([&] { parse(invalid); });
    Reject([&] { parse("3,11","fake"); });
    auto policy=[](std::string value, std::string scheme="tree", bool explicit_slots=false) {
      std::vector<std::string> args{"worker","--resolve-only","1","--scheme",scheme,
                                    "--cores","2","--placement",value};
      if (explicit_slots) { args.push_back("--cpu-ids"); args.push_back("3,11"); }
      std::vector<char*> argv;
      for (auto& arg:args) argv.push_back(arg.data());
      return ob::ParseWorker(static_cast<int>(argv.size()),argv.data());
    };
    Check(policy("near_far").placement=="near_far");
    Check(policy("unplaced","fake").placement=="unplaced");
    Check(policy("explicit","tree",true).cpu_ids==std::vector<unsigned>({3,11}));
    Reject([&] { policy("near_far","fake"); });
    Reject([&] { policy("explicit"); });
    Reject([&] { policy("near_far","tree",true); });
    Reject([&] { policy("unplaced","tree",true); });
    Reject([&] { policy("unknown"); });
    std::vector<ob::topology::Cpu> cpus;
    for (unsigned i : {3u, 7u, 11u, 15u}) {
      ob::topology::Cpu cpu; cpu.id = i; cpu.package = 0; cpu.core = i;
      cpu.l3 = i < 10 ? "3,7" : "11,15"; cpu.l3_bytes = 32u << 20;
      cpu.siblings = std::to_string(i);
      cpus.push_back(cpu);
    }
    using Locality=ob::PlacementLocality;
    const auto caller=Locality::kCaller, online=Locality::kOnline, background=Locality::kBackground;
    const std::vector<Locality> roles{caller,background,online};
    // The harness takes the lowest core (3), so domain {3,7} has no local core
    // left for the online helper and the caller moves to {11,15}, taking its
    // highest core. Owner precedes online helper but cannot steal its core.
    Check(ob::NearFarSlots(cpus,roles,4)==std::vector<unsigned>({15,7,11,3}));
    Check(ob::NearFarSlots(cpus,{caller},4)==std::vector<unsigned>({7,11,15,3}));
    Check(ob::NearFarSlots(cpus,{caller,background,background,background},4,0)==
          std::vector<unsigned>({7,11,15,3}));
    auto reversed=cpus; std::reverse(reversed.begin(),reversed.end());
    Check(ob::NearFarSlots(reversed,roles,4)==ob::NearFarSlots(cpus,roles,4));
    auto smt_auto=cpus;
    smt_auto[0].siblings="3,23";
    auto sibling=smt_auto[0]; sibling.id=23;
    smt_auto[0].l3=sibling.l3=smt_auto[1].l3="3,7,23";
    smt_auto.push_back(sibling);
    Check(ob::NearFarSlots(smt_auto,roles,4)==ob::NearFarSlots(cpus,roles,4));
    Reject([&] { ob::NearFarSlots(smt_auto,roles,5); });
    smt_auto.erase(smt_auto.begin()); // Only the higher SMT sibling is allowed.
    Check(ob::NearFarSlots(smt_auto,roles,4)==std::vector<unsigned>({15,23,11,7}));
    auto uneven=cpus;
    uneven[0].l3="3";
    for (size_t i=1;i<uneven.size();++i) uneven[i].l3="7,11,15";
    Check(ob::NearFarSlots(uneven,roles,4)==std::vector<unsigned>({15,11,7,3}));
    auto single=cpus;
    for (auto& cpu:single) cpu.l3="3,7,11,15";
    Check(ob::NearFarSlots(single,roles,4)==std::vector<unsigned>({15,11,7,3}));
    // Two eight-core domains, as on a two-CCD Zen 5 host: the harness keeps
    // CPU 0 and the caller its domain's highest core; near-side rebuild
    // threads are placed like online helpers, far ones remote first.
    std::vector<ob::topology::Cpu> two;
    for (unsigned i=0;i<16;++i) {
      ob::topology::Cpu cpu; cpu.id=i; cpu.package=0; cpu.core=i;
      cpu.l3=i<8 ? "0-7" : "8-15"; cpu.l3_bytes=32u<<20; cpu.siblings=std::to_string(i);
      two.push_back(cpu);
    }
    const auto eight=ob::NearFarSlots(two,{caller,background,background,online,online},16);
    Check(eight[0]==7 && eight[1]==8 && eight[2]==9 && eight[3]==1 && eight[4]==2 && eight[15]==0);
    Reject([&] { ob::NearFarSlots(cpus,{caller,online,online},4); });
    Reject([&] { ob::NearFarSlots(cpus,{},4); });
    Reject([&] { ob::NearFarSlots(cpus,{online},4); });
    Reject([&] { ob::NearFarSlots(cpus,{caller,caller},4); });
    Reject([&] { ob::NearFarSlots(cpus,roles,3); });
    Reject([&] { ob::NearFarSlots(cpus,{caller},1); });
    Reject([&] { ob::NearFarSlots(cpus,{caller},2,3); });
    Reject([&] { ob::NearFarSlots(cpus,{caller},5); });
    for (unsigned kind=0;kind<9;++kind) {
      auto bad=cpus;
      switch (kind) {
        case 0: bad[0].siblings.clear(); break;
        case 1: bad[0].core=-1; break;
        case 2: bad[0].siblings="3,7"; break;
        case 3: bad[0].l3="3,11"; break;
        case 4: bad[0].l3_bytes=1; break;
        case 5: bad[0].l3="7"; break;
        case 6: bad.push_back(bad[0]); break;
        case 7: bad[0].siblings="7"; break;
        case 8: bad[0].l3_bytes=0; break;
      }
      Reject([&] { ob::NearFarSlots(bad,roles,4); });
    }
    Check(ob::TopologyCpuList("0-2,7")==std::set<unsigned>({0,1,2,7}));
    for (const auto* value:{"","-1","1-0","0,","0,,1","0,0","0-2,2","0-1-2"," 0","0-999999999"})
      Reject([&] { ob::TopologyCpuList(value); });
    std::vector<unsigned> mask{3,7,11,15};
    ob::AffinityAccess access{[&](unsigned cpu) { mask = {cpu}; }, [&] { return mask; }};
    ob::VerifiedPlacement placement(cpus, {3,7,11,15}, access);
    placement.Bind(Role{0,0,3});
    Reject([&] { placement.VerifyComplete(std::vector<Role>{{0,0,3},{1,0,11}}); });
    // Model the helper inheriting the caller's singleton mask.
    placement.Bind(Role{1,0,11});
    placement.VerifyComplete(std::vector<Role>{{0,0,3},{1,0,11}});
    Reject([&] { placement.VerifyComplete(std::vector<Role>{{0,0,3},{1,0,7}}); });
    Reject([&] { placement.VerifyComplete(std::vector<Role>{{0,0,3},{0,0,3}}); });
    auto records = placement.Snapshot();
    Check(records.size() == 2 && records[1].inherited == std::vector<unsigned>{3});
    Check(records[1].applied == std::vector<unsigned>{11});
    Reject([&] { placement.Bind(Role{2,0,99}); });
    Reject([&] { placement.Bind(Role{2,0,std::nullopt}); });
    Reject([&] { placement.Bind(Role{1,0,7}); });
    Reject([&] { placement.Bind(Role{2,0,3}); });
    // Harness threads (negative roles) share the harness slot under distinct
    // identities; none may take a library thread's CPU or repeat an identity.
    placement.Bind(Role{-1,0,15});
    placement.Bind(Role{-2,0,15});
    Reject([&] { placement.Bind(Role{-2,0,15}); });
    Reject([&] { placement.Bind(Role{-3,0,3}); });
    Reject([&] { placement.Bind(Role{2,0,15}); });
    placement.VerifyComplete(std::vector<Role>{{0,0,3},{1,0,11},{-1,0,15},{-2,0,15}});
    Reject([&] { ob::VerifiedPlacement p(cpus, {3,99}, access); });
    Reject([&] { ob::VerifiedPlacement p(cpus, {3,3}, access); });
    auto smt = cpus; smt[1].core = smt[0].core;
    Reject([&] { ob::VerifiedPlacement p(smt, {3,7}, access); });
    auto missing = cpus; missing[2].l3.clear();
    Reject([&] { ob::VerifiedPlacement p(missing, {3,11}, access); });
    ob::VerifiedPlacement ignored(cpus, {3}, {[](unsigned) {}, [] { return std::vector<unsigned>{3,7}; }});
    Reject([&] { ignored.Bind(Role{0,0,3}); });
    Check(ignored.Snapshot().empty());
    ob::VerifiedPlacement failed(cpus, {3}, {[](unsigned) { throw std::runtime_error("restricted"); }, access.get});
    Reject([&] { failed.Bind(Role{0,0,3}); });
    Check(failed.Snapshot().empty());
    ob::VerifiedPlacement unreadable(cpus, {3}, {access.set, []() -> std::vector<unsigned> { throw std::runtime_error("unreadable"); }});
    Reject([&] { unreadable.Bind(Role{0,0,3}); });
    Check(unreadable.Snapshot().empty());
    return 0;
  } catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; }
}
