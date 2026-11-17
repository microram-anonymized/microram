#include "benchmarks/support/worker.hpp"
#include <iostream>

namespace ob=oram_bench;
// All memory values are injected; this test never inspects host memory or runs
// a worker. Filesystem output and cross-phase sampling use the production code.
int main() {
  const auto root=std::filesystem::temp_directory_path()/
      ("oram-memory-fixture-"+std::to_string(std::chrono::steady_clock::now().time_since_epoch().count()));
  std::filesystem::create_directory(root);
  try {
    ob::MemorySnapshot snapshot;
    snapshot.rss=1234; snapshot.swap=0;
    ob::MemoryRecorder* active=nullptr;
    bool transition=false;
    ob::MemoryRecorder memory(root/"samples.csv",1,[&](bool include_pss) {
      ob::Require(!include_pss,"periodic sample walked smaps_rollup for PSS");
      if (transition) active->SetPhase("final_drain");
      return snapshot;
    });
    active=&memory;
    memory.SetPhase("measure"); memory.SampleCurrentPhase();
    transition=true; memory.SampleCurrentPhase(); transition=false;
    memory.SampleCurrentPhase();
    memory.SetPhase("log_flush"); memory.SampleCurrentPhase(); memory.Close();
    const auto csv=ob::ReadProc(root/"samples.csv");
    ob::Require(csv.find("\nmeasure,")!=std::string::npos &&
                csv.find("\nphase_transition,")!=std::string::npos &&
                csv.find("\nfinal_drain,")!=std::string::npos &&
                csv.find("\nlog_flush,")!=std::string::npos,
                "phase labels or transition detection lost");
    ob::Require(csv.find(",1234,,,0,,,,,\n")!=std::string::npos,
                "unknown memory fields became zero or known zero became null");

    // memory.max "max" at every level up to the hierarchy root (which
    // has no memory.max) is unlimited; a missing level or a cgroup-namespace
    // root (cgroup.type present, ancestors hidden) stays unknown.
    const auto tree=root/"cgroup";
    auto put=[](const std::filesystem::path& path,const std::string& text) {
      std::filesystem::create_directories(path.parent_path());
      std::ofstream(path)<<text<<'\n';
    };
    put(tree/"cgroup.controllers","memory");
    for (const auto& group:{tree/"a",tree/"a"/"b"}) { put(group/"memory.max","max"); put(group/"cgroup.type","domain"); }
    put(tree/"a"/"b"/"memory.current","7"); put(tree/"a"/"b"/"memory.peak","9");
    auto cgroup=[&](const std::string& membership) {
      ob::MemorySnapshot result; ob::CgroupMemory(result,membership,tree); return result;
    };
    auto observed=cgroup("0::/a/b\n");
    ob::Require(observed.cgroup_unlimited && !observed.cgroup_limit &&
                observed.cgroup_current==uint64_t{7} && observed.cgroup_peak==uint64_t{9},
                "all-max hierarchy is not unlimited");
    ob::Require(cgroup("0::/\n").cgroup_unlimited,"hierarchy root membership is not unlimited");
    put(tree/"a"/"memory.max","4096");
    observed=cgroup("0::/a/b\n");
    ob::Require(observed.cgroup_limit==uint64_t{4096} && !observed.cgroup_unlimited,"ancestor limit lost");
    std::filesystem::remove(tree/"a"/"memory.max");
    observed=cgroup("0::/a/b\n");
    ob::Require(!observed.cgroup_limit && !observed.cgroup_unlimited,"missing memory.max became unlimited");
    put(tree/"a"/"memory.max","max"); put(tree/"cgroup.type","domain");
    ob::Require(!cgroup("0::/a/b\n").cgroup_unlimited,"namespace root hid its ancestors' limits");
    ob::MemorySnapshot unlimited; unlimited.cgroup_unlimited=true;
    ob::MemoryRecorder marker(root/"unlimited.csv",1,[&](bool) { return unlimited; });
    marker.Sample("before_construction"); unlimited.cgroup_limit=5; marker.Sample("after_construction");
    marker.Close();
    const auto marked=ob::ReadProc(root/"unlimited.csv");
    ob::Require(marked.find("\nbefore_construction,")!=std::string::npos &&
                marked.find(",,,,,,,,,unlimited\n")!=std::string::npos &&
                marked.find(",,,,,,,,,5\n")!=std::string::npos,
                "unlimited cgroup marker not written, or written over a known limit");

    ob::WorkerOptions options; options.output=(root/"trial").string();
    bool constructed=false;
    try {
      ob::WorkerArtifacts artifacts(options,"{\"synthetic\":true}",[&](bool include_pss) {
        ob::Require(!constructed,"baseline collected after construction");
        ob::Require(include_pss,"phase-boundary sample omitted PSS");
        return snapshot;
      });
      // Boundary samples are flushed even while the artifact owner is alive.
      ob::Require(ob::ReadProc(root/"trial"/"memory.csv").find("\nbefore_construction,")!=std::string::npos,
                  "baseline is buffered until successful construction");
      constructed=true;
      throw std::runtime_error("injected constructor failure");
    } catch (const std::runtime_error& error) {
      ob::Require(std::string(error.what())=="injected constructor failure","unexpected construction failure");
    }
    ob::Require(ob::ReadProc(root/"trial"/"resolved.json")=="{\"synthetic\":true}\n" &&
                std::filesystem::exists(root/"trial"/"invocation.json"),
                "constructor failure lost replay inputs");
    bool rejected=false;
    try { ob::WorkerArtifacts duplicate(options,"{}",[&](bool) { return snapshot; }); }
    catch (const std::exception&) { rejected=true; }
    ob::Require(rejected,"existing output directory was overwritten");
    std::filesystem::remove_all(root);
  } catch (...) { std::filesystem::remove_all(root); throw; }
  std::cout<<"oram_bench_memory_test passed\n";
}
