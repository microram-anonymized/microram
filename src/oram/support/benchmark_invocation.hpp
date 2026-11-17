#pragma once
// The service-timing bracket: optionally read the clock immediately before
// and after one public map call (saturated trials with service timing on).
#include <cstdint>

namespace oram_bench {
struct InvocationTiming {
  uint64_t start = 0;
  uint64_t end = 0;
};

// Select the public entry point before entering this boundary. Preparation,
// validation and accounting belong to the enclosing coarse window.
template <typename Timebase, typename Invoke>
InvocationTiming InvokePrepared(Timebase& clock, bool timed, Invoke&& invoke) {
  if (!timed) {
    invoke();
    return {};
  }
  const uint64_t start = clock.Now();
  invoke();
  const uint64_t end = clock.Now();
  return {start, end};
}
}  // namespace oram_bench
