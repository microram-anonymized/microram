// Parser/serializer fixture only: no backend, topology discovery or clock.
#include "benchmarks/support/worker.hpp"
int main(int argc, char** argv) {
  try {
    const auto options = oram_bench::ParseWorker(argc, argv);
    oram_bench::Require(options.resolve_only, "fixture requires resolve-only input");
    std::cout << oram_bench::ResolverRequestJson(options) << '\n';
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n'; return 2;
  }
}
