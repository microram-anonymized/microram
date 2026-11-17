#pragma once

// Portable arrival generation; no wall clock or engine dependency.  Arrival
// times are computed from public parameters (rate, group size), never from
// engine progress, so a slow call delays service but not later arrivals and
// the resulting queueing delay is charged to latency (see DESIGN.md).
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace oram_bench {

// The workload shapes.  kSaturating is the degenerate one: every request is
// due at time 0, so the loop issues back to back and only `service` means
// anything.  It is how a run measures the saturation throughput that a
// fixed-rate run's offered rate is chosen as a fraction of.
enum class ArrivalProfile : uint8_t {
  kSaturating,
  kFixedRate,
};

inline const char* ProfileName(ArrivalProfile profile) {
  switch (profile) {
    case ArrivalProfile::kSaturating: return "saturating";
    case ArrivalProfile::kFixedRate: return "fixed";
  }
  return "?";
}

struct ScheduleSpec {
  ArrivalProfile profile = ArrivalProfile::kFixedRate;
  size_t num_accesses = 0;
  double rate_kops = 100.0;  // offered rate; request k arrives at floor(k * 1e6 / rate_kops) ns
  // Requests arriving at one instant: request k arrives with the first of its
  // group, k - k % arrival_group, so groups come every arrival_group requests'
  // worth of gaps at the same offered rate (a caller handing over whole batches).
  size_t arrival_group = 1;
  uint64_t seed = 0x5EEDull;  // fixed arrivals are deterministic; kept because plan identity binds it
};

// Fixed-rate arrivals in closed form: request k arrives at floor(k * gap)
// nanoseconds, or with the first of its group, so nothing is generated or
// stored per request.
class FixedArrivals {
 public:
  explicit FixedArrivals(double rate_kops, size_t group = 1) : gap_ns_(1e6 / rate_kops), group_(group) {
    if (!std::isfinite(gap_ns_) || gap_ns_ <= 0)
      throw std::invalid_argument("arrival rate must be positive and finite");
    if (!group_) throw std::invalid_argument("arrival group must be positive");
  }
  uint64_t At(uint64_t k) const { return Single(k - k % group_); }
  // How many requests arrive strictly before `limit` ns, compared as integers
  // so that a large limit is not first rounded into a double. A group arrives
  // whole: when its first request is before the limit, so are the others.
  uint64_t Before(uint64_t limit) const {
    uint64_t k = static_cast<uint64_t>(static_cast<double>(limit) / gap_ns_);
    while (k > 0 && Single(k - 1) >= limit) --k;
    while (Single(k) < limit) ++k;
    const uint64_t groups = k / group_ + (k % group_ != 0);
    return groups > UINT64_MAX / group_ ? UINT64_MAX : groups * group_;
  }
 private:
  uint64_t Single(uint64_t k) const {
    const double t = static_cast<double>(k) * gap_ns_;
    // UINT64_MAX rounds to 2^64 as a double. Use that exclusive bound.
    if (t >= std::ldexp(1.0, 64)) throw std::overflow_error("arrival timestamp exceeds uint64 nanoseconds");
    return static_cast<uint64_t>(t);
  }
  double gap_ns_;
  size_t group_;
};

}  // namespace oram_bench
