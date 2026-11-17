#pragma once
// Maintenance spans a backend can report, on steady_clock (for our hierarchy:
// top-level merges), so latency analysis can line up tail requests with
// rebuild work. A backend either gives spans (`source` names where they come
// from) or says why it cannot (`unavailable`). The worker writes them as
// worker/markers.csv.
#include <chrono>
#include <cstdint>
#include <string>
#include <vector>

namespace oram_bench {
struct MaintenanceSpan { std::string role; unsigned level=0; uint64_t start_ns=0, end_ns=0; };
struct MaintenanceMarkers { std::string source, unavailable; std::vector<MaintenanceSpan> spans; };
inline uint64_t SteadyNanos() {
  return static_cast<uint64_t>(std::chrono::duration_cast<std::chrono::nanoseconds>(
      std::chrono::steady_clock::now().time_since_epoch()).count());
}
}  // namespace oram_bench
