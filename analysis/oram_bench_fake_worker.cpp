// oram_bench_fake_worker: the portable one-trial worker with only the synthetic
// backends (`fake`, which stores every value behind a hash index, and `noop`,
// which stores nothing and measures caller-side overhead).  It runs the same
// phased trial runner, workload adapter and event/checkpoint logging as the
// real worker (benchmarks/support/worker.hpp) without the ORAM's ISA
// requirements, so the campaign tooling's planning, recovery and reduction
// paths can be tested on any host (analysis/oram_bench/WORKER.md).
#include "benchmarks/support/worker.hpp"
int main(int argc,char** argv) {
  try {
    if (argc==1 || (argc==2 && std::string(argv[1])=="--help")) {
      oram_bench::WorkerHelp(); return 0;
    }
    if (oram_bench::PrintCompiledIsa(argc,argv)) return 0;
    const auto o=oram_bench::ParseWorker(argc,argv);
    oram_bench::Require(oram_bench::SyntheticScheme(o.scheme),"portable worker supports only the fake and noop backends");
    return oram_bench::RunSyntheticWorker(o);
  } catch (const std::exception& error) {
    std::cerr << "oram_bench_worker: " << error.what() << '\n'; return 2;
  }
}
