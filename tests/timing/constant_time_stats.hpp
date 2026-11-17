#pragma once

// Statistics for the constant-time timing test (avx512_constant_time_test).
//
// The design is a randomized block experiment: every round times each operand
// class once, in a fresh random order.  Under the null hypothesis (timing does
// not depend on the operand) the classes are exchangeable within a round, so
// the per-round difference between two classes is symmetric about zero, and
// the tests below are valid without assuming normal timing noise.
//
//   location  the mean of the per-round differences between a class and the
//             reference class, over the rounds in which neither sample is an
//             outlier (above the pooled median of all classes by more than a
//             fixed margin).  Censoring whole rounds at one threshold for
//             every class removes preemption and interrupt spikes while
//             keeping the classes exchangeable.  A plain mean rather than a
//             quantile-trimmed one because the TSC is coarse on some hosts
//             (tens of ticks per step under some hypervisors): quantile
//             trimming on a lattice of values has no valid normal
//             approximation, while the
//             mean of dithered quantized samples is unbiased and has the
//             usual standard error.
//   tail      an exact binomial test on how many of each class's samples are
//             outliers.  Interrupts land on every class at the same rate, so
//             an operand that is slow only sometimes (and that censoring
//             would hide) shows up as an excess here.
//
// Both use one per-comparison threshold chosen so the family-wise false-alarm
// rate over the whole run stays at `alpha` (Bonferroni over every comparison
// the run makes).

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace microram {
namespace timing {

// Standard normal upper tail, P(Z > z).
inline double NormalUpperTail(double z) {
  return 0.5 * std::erfc(z / std::sqrt(2.0));
}

// z with P(|Z| > z) = p, by bisection (p in (0, 1)).
inline double TwoSidedNormalThreshold(double p) {
  double lo = 0.0, hi = 40.0;
  for (int i = 0; i < 200; ++i) {
    const double mid = 0.5 * (lo + hi);
    if (2.0 * NormalUpperTail(mid) > p) {
      lo = mid;
    } else {
      hi = mid;
    }
  }
  return 0.5 * (lo + hi);
}

template <typename T>
inline double Median(std::vector<T> x) {
  if (x.empty()) return 0.0;
  const size_t mid = x.size() / 2;
  std::nth_element(x.begin(), x.begin() + static_cast<std::ptrdiff_t>(mid),
                   x.end());
  const double upper = static_cast<double>(x[mid]);
  if (x.size() % 2 == 1) return upper;
  const double lower = static_cast<double>(*std::max_element(
      x.begin(), x.begin() + static_cast<std::ptrdiff_t>(mid)));
  return 0.5 * (upper + lower);
}

struct PairedTest {
  size_t n = 0;       // rounds kept
  double mean = 0.0;  // mean difference, class minus reference
  double se = 0.0;    // its standard error
  double t = 0.0;     // mean / se (0 when both are 0)
};

// Paired mean test on class samples `a` and reference samples `b` (same
// rounds), skipping every round in which a[r] > a_cut or b[r] > b_cut.
template <typename T>
inline PairedTest CensoredPairedMean(const std::vector<T>& a,
                                     const std::vector<T>& b, double a_cut,
                                     double b_cut) {
  PairedTest r;
  double sum = 0.0, sum_sq = 0.0;
  const size_t n = std::min(a.size(), b.size());
  for (size_t i = 0; i < n; ++i) {
    const double x = static_cast<double>(a[i]), y = static_cast<double>(b[i]);
    if (x > a_cut || y > b_cut) continue;
    const double d = x - y;
    sum += d;
    sum_sq += d * d;
    ++r.n;
  }
  if (r.n < 2) return r;
  const double k = static_cast<double>(r.n);
  r.mean = sum / k;
  const double var = std::max(0.0, (sum_sq - k * r.mean * r.mean) / (k - 1.0));
  r.se = std::sqrt(var / k);
  if (r.se > 0.0) {
    r.t = r.mean / r.se;
  } else if (r.mean != 0.0) {
    r.t = r.mean > 0.0 ? 1e9 : -1e9;
  }
  return r;
}

// Exact two-sided p-value for `a` successes out of `a + b` Bernoulli(1/2)
// trials: the probability, under equal rates, of a split at least this
// uneven.  Used with equal sample counts per class, so equal outlier rates
// mean each outlier is equally likely to belong to either class.
inline double BinomialHalfTwoSidedP(uint64_t a, uint64_t b) {
  const uint64_t n = a + b;
  if (n == 0) return 1.0;
  const uint64_t m = std::min(a, b);
  if (2 * m == n) return 1.0;
  const double log_half_n = static_cast<double>(n) * std::log(0.5);
  const double lg_n1 = std::lgamma(static_cast<double>(n) + 1.0);
  double total = 0.0;  // P(X <= m)
  for (uint64_t i = 0; i <= m; ++i) {
    total += std::exp(lg_n1 - std::lgamma(static_cast<double>(i) + 1.0) -
                      std::lgamma(static_cast<double>(n - i) + 1.0) +
                      log_half_n);
  }
  return std::min(1.0, 2.0 * total);
}

}  // namespace timing
}  // namespace microram
