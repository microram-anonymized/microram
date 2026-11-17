#pragma once

// Portable benchmark statistics. No map, ISA, timer, or platform dependencies.
// The streaming log-linear Histogram below holds every latency, queueing and
// service observation in fixed memory, so measurement memory does not grow
// with run length (bounds derived in DESIGN.md).
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <stdexcept>

namespace oram_bench {
inline void Require(bool condition, const char* message) {
  if (!condition) throw std::invalid_argument(message);
}
inline uint64_t CheckedAdd(uint64_t a, uint64_t b) {
  if (b > std::numeric_limits<uint64_t>::max() - a)
    throw std::overflow_error("benchmark statistic exceeds uint64");
  return a + b;
}
inline uint64_t CheckedMultiply(uint64_t a, uint64_t b) {
  if (a && b > std::numeric_limits<uint64_t>::max() / a)
    throw std::overflow_error("benchmark statistic exceeds uint64");
  return a * b;
}
inline uint64_t SaturatingAdd(uint64_t a, uint64_t b) {
  return b > std::numeric_limits<uint64_t>::max() - a ? std::numeric_limits<uint64_t>::max() : a + b;
}
inline uint64_t SaturatingMultiply(uint64_t a, uint64_t b) {
  return a && b > std::numeric_limits<uint64_t>::max() / a ? std::numeric_limits<uint64_t>::max() : a * b;
}

// Version 1 log-linear histogram: 512 exact integer-nanosecond bins, then
// 256 bins per power-of-two range; 14,592 bins cover all uint64 values.
// Quantiles use nearest rank and the occupied bin's upper bound, clamped to
// the observed maximum. Relative overstatement is at most 1/256 (0.390625%).
// Count, sum and extrema are exact uint64 integers. Overflow throws before
// mutation; the mean is rounded only when formatted as a floating value.
class Histogram {
 public:
  static constexpr unsigned kVersion = 1;
  // The initial linear range has 512 bins; later octaves have 256.
  static constexpr unsigned kSubBits = 9;
  static constexpr uint64_t kSubCount = uint64_t{1} << kSubBits;
  // Octave 63 needs shift 64 - kSubBits; the last index is that many
  // half-octaves in, plus the widest sub-bucket.
  static constexpr size_t kBucketCount =
      static_cast<size_t>((64 - kSubBits) * (kSubCount / 2) + kSubCount);

  void Add(uint64_t value_ns) {
    const auto new_sum = CheckedAdd(sum_ns_, value_ns);
    const auto new_count = CheckedAdd(count_, 1);
    sum_ns_ = new_sum;
    count_ = new_count;
    if (value_ns < min_ns_) min_ns_ = value_ns;
    if (value_ns > max_ns_) max_ns_ = value_ns;
    ++buckets_[IndexOf(value_ns)];
  }

  uint64_t count() const { return count_; }
  uint64_t sum_ns() const { return sum_ns_; }
  std::optional<uint64_t> minimum_ns() const {
    return count_ ? std::optional<uint64_t>(min_ns_) : std::nullopt;
  }
  std::optional<uint64_t> maximum_ns() const {
    return count_ ? std::optional<uint64_t>(max_ns_) : std::nullopt;
  }
  const auto& bins() const { return buckets_; }

  // Restores the exact sufficient statistics, never representative bin values.
  static Histogram Restore(uint64_t count, uint64_t sum,
                           std::optional<uint64_t> minimum,
                           std::optional<uint64_t> maximum,
                           const std::array<uint64_t, kBucketCount>& bins) {
    Require(minimum.has_value() == (count != 0) &&
            maximum.has_value() == (count != 0), "invalid empty histogram extrema");
    Histogram h;
    if (!count) {
      Require(sum == 0, "nonzero empty histogram sum");
    } else {
      Require(*minimum <= *maximum, "reversed histogram extrema");
      Require(bins[IndexOf(*minimum)] && bins[IndexOf(*maximum)],
              "histogram extrema missing from bins");
    }
    uint64_t total = 0, lower_sum = 0, upper_sum = 0;
    for (size_t i = 0; i < kBucketCount; ++i) {
      total = CheckedAdd(total, bins[i]);
      if (!bins[i]) continue;
      Require(count && i >= IndexOf(*minimum) && i <= IndexOf(*maximum),
              "histogram bin outside extrema");
      const uint64_t lo = std::max(LowerBoundOf(i), *minimum);
      const uint64_t hi = std::min(UpperBoundOf(i), *maximum);
      // A lower bound overflow proves no uint64 sum can describe these bins.
      lower_sum = CheckedAdd(lower_sum, CheckedMultiply(lo, bins[i]));
      upper_sum = SaturatingAdd(upper_sum, SaturatingMultiply(hi, bins[i]));
    }
    Require(total == count && lower_sum <= sum && sum <= upper_sum,
            "histogram count/sum disagrees with bins");
    if (count) {
      // Both extrema must actually occur, including when they share a bin.
      const auto min_index = IndexOf(*minimum), max_index = IndexOf(*maximum);
      Require(count != 1 || *minimum == *maximum, "one sample has distinct extrema");
      if (*minimum != *maximum && min_index == max_index)
        Require(bins[min_index] >= 2, "extrema require two samples in bin");
      lower_sum = CheckedAdd(lower_sum, *maximum - std::max(LowerBoundOf(max_index), *minimum));
      // Compute the maximum with the minimum observation reserved explicitly,
      // so saturation cannot hide an impossible sum.
      upper_sum = 0;
      for (size_t i = 0; i < kBucketCount; ++i) {
        if (!bins[i]) continue;
        auto n = bins[i] - (i == min_index ? 1 : 0);
        upper_sum = SaturatingAdd(upper_sum, SaturatingMultiply(std::min(UpperBoundOf(i), *maximum), n));
      }
      upper_sum = SaturatingAdd(upper_sum, *minimum);
      Require(lower_sum <= sum && sum <= upper_sum, "histogram sum disagrees with extrema");
    }
    h.count_ = count;
    h.sum_ns_ = sum;
    h.min_ns_ = minimum.value_or(std::numeric_limits<uint64_t>::max());
    h.max_ns_ = maximum.value_or(0);
    h.buckets_ = bins;
    return h;
  }

  // Throws what Merge would, without changing anything.
  void CheckMerge(const Histogram& other) const {
    (void)CheckedAdd(count_, other.count_);
    (void)CheckedAdd(sum_ns_, other.sum_ns_);
  }

  // Checked before mutation; merging never silently wraps integer statistics.
  void Merge(const Histogram& other) {
    auto count = CheckedAdd(count_, other.count_);
    auto sum = CheckedAdd(sum_ns_, other.sum_ns_);
    for (size_t i = 0; i < kBucketCount; ++i) buckets_[i] += other.buckets_[i];
    count_ = count;
    sum_ns_ = sum;
    min_ns_ = std::min(min_ns_, other.min_ns_);
    max_ns_ = std::max(max_ns_, other.max_ns_);
  }

  // Integer nearest-rank avoids floating rank rounding for published quantiles.
  std::optional<uint64_t> QuantilePpm(uint32_t ppm) const {
    Require(ppm <= 1000000, "quantile outside [0,1]");
    if (!count_) return std::nullopt;
    uint64_t rank = (count_ / 1000000) * ppm +
        ((count_ % 1000000) * ppm + 999999) / 1000000;
    rank = std::max(uint64_t{1}, rank);
    uint64_t seen = 0;
    for (size_t i = 0; i < kBucketCount; ++i) {
      seen += buckets_[i];
      if (seen >= rank) return std::min(UpperBoundOf(i), max_ns_);
    }
    throw std::logic_error("invalid histogram count");
  }

  bool HasTailSamples(uint32_t percentile_ppm, uint64_t minimum_tail_count = 100) const {
    Require(percentile_ppm <= 1000000 && minimum_tail_count > 0, "invalid tail policy");
    const uint64_t tail = 1000000 - percentile_ppm;
    // floor(count * tail / 1e6), without overflowing the product.
    return (count_ / 1000000) * tail + (count_ % 1000000) * tail / 1000000 >= minimum_tail_count;
  }

 public:
  // Values below kSubCount get one bucket each and are therefore EXACT; above
  // it, an octave is split into kSubCount/2 buckets of equal width.
  static size_t IndexOf(uint64_t v) {
    if (v < kSubCount) return static_cast<size_t>(v);
    const unsigned octave = 63u - static_cast<unsigned>(CountLeadingZeros(v));
    const unsigned shift = octave - kSubBits + 1u;
    const uint64_t sub = v >> shift;  // in [kSubCount/2, kSubCount)
    return static_cast<size_t>(shift * (kSubCount / 2) + sub);
  }

  // Largest value that lands in bucket `i`, the exact inverse of IndexOf.
  // Above the linear region IndexOf packs shift*(kSubCount/2) + sub with sub
  // in [kSubCount/2, kSubCount), so the leading half-octave has to come back
  // out before the division or every shift reads one too high.
  static uint64_t LowerBoundOf(size_t i) {
    Require(i < kBucketCount, "histogram bin out of range");
    return i == 0 ? 0 : UpperBoundOf(i - 1) + 1;
  }

  static uint64_t UpperBoundOf(size_t i) {
    Require(i < kBucketCount, "histogram bin out of range");
    if (i < kSubCount) return static_cast<uint64_t>(i);
    const uint64_t half = kSubCount / 2;
    const uint64_t offset = static_cast<uint64_t>(i) - half;
    const uint64_t shift = offset / half;
    const uint64_t sub = offset % half + half;
    return ((sub + 1) << shift) - 1;
  }

 private:
  static unsigned CountLeadingZeros(uint64_t v) {
    return static_cast<unsigned>(__builtin_clzll(v));
  }

  std::array<uint64_t, kBucketCount> buckets_{};
  uint64_t count_ = 0;
  uint64_t sum_ns_ = 0;
  uint64_t min_ns_ = std::numeric_limits<uint64_t>::max();
  uint64_t max_ns_ = 0;
};

}  // namespace oram_bench
