// THE RELEASE MACRO ITSELF COMPILES: every public header, and every header
// that reads an instrumentation macro, included with CPU_BYTESLICE_ORAM_RELEASE
// defined and nothing else, then one round trip through the default map so the
// binary is not an empty main.  The refusals -- release plus an
// instrumentation macro -- are checked by tests/release_guard/, which has to
// run the compiler itself because a failing build cannot be a CTest binary.
#define CPU_BYTESLICE_ORAM_RELEASE 1

#include <cpu_byteslice_oram/configuration.hpp>
#include <cpu_byteslice_oram/oram.hpp>
#include <cpu_byteslice_oram/tree_oram.hpp>
#include "src/oram/levelarena/cpu_byteslice_level_arena_pause.hpp"

#include <cstdint>
#include <cstdio>

int main() {
  cpu_byteslice_oram::Map<uint64_t, uint64_t> map(4096);
  map.insert_or_assign(7, 42);
  const auto value = map.find(7);
  if (!value || *value != 42) {
    std::fprintf(stderr, "FAIL: release-mode round trip\n");
    return 1;
  }
  return 0;
}
