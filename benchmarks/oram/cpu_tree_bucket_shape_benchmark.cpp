// THE STASH TAIL OF THE READ-PATH TREE, MEASURED (src/oram/tree/DESIGN.md,
// "Stash size"): how many stash lanes a row's shape needs for a per-access
// failure probability of `2^-96`.
//
// WHAT IT MEASURES.  The plan is a function of the metadata and the public
// leaf alone, so no kernel is needed: `cpu_tree_stash_sim.hpp` is the
// engine's plan over metadata, and `tests/oram/cpu_tree_read_path_oram_test.cpp`
// holds it to the engine slot for slot.  Each access's LEFTOVER COUNT --
// stash entries the plan could place nowhere on the path, which is the
// quantity the engine's overflow check tests against `64 A - 1` -- goes into
// a histogram.
//
// THE TARGET IS `2^-96` PER ACCESS.  No number of trials observes `2^-96`
// directly, so the target is reached by extrapolating a straight line in
// `log2 P[x >= k]` -- the standard Path ORAM tail shape -- and the trial
// count is what decides how far that line is fitted before it is continued.
// This benchmark therefore
//
//   * runs many independent seeds in parallel and pools their histograms, so
//     the observed tail reaches `2^-30` and beyond;
//   * fits the tail over its DEEP end only (from `2^-10` down), where the
//     geometric regime has set in, rather than from just past the mode;
//   * reports a JACKKNIFE standard error over the seeds for every fitted
//     quantity, so the extrapolation carries an error bar instead of a digit
//     count -- successive accesses are correlated, and only independent
//     (mixed, the default) seeds give an honest one;
//   * reports the slope of the shallow and the deep half of the window
//     separately, because a tail that steepens with `k` makes the straight
//     line conservative and one that flattens makes it optimistic, and which
//     of the two is happening is not visible in a single slope.
//
// The `2^-96` column is still an extrapolation of a fitted line and nothing
// here upgrades it to a bound.
//
// Usage:
//   cpu_tree_bucket_shape_benchmark [options] row [row ...]
//
//   --ops N           steady operations per seed (default 2000000); counts
//                     take digits or an integral float such as 5e8
//   --seeds S         seeds per row, pooled (default 16); independent unless
//                     --no-seed-mix
//   --threads T       (default: as many as seeds, capped at hardware)
//   --workload W      uniform | roundrobin | hotset | misses | churn
//   --target BITS     the per-access failure exponent to solve for (96)
//   --tail-min C      the least tail count a fitted point may have (30)
//   --tail-start B    the fit window opens where the tail passes 2^-B (10)
//   --detail          print the whole tail, with the local slope per point
//   --levels          per-level occupancy after the steady phase, seed 1
//   --fit-phases      fit the fill and warm phases too, not the steady one alone
//   --series NAME     op-max (default) | access-pass | after-op | all
//   --seed-base B     the first seed (default 1); seed i of a row is B + i
//   --seed-mix        hash each seed before the simulator sees it (the
//                     default; accepted for older command lines)
//   --no-seed-mix     hand the simulator the raw seeds (below), as unmixed
//                     runs and their saved files were made
//   --save FILE       also write every seed's histograms to FILE (one row only)
//   --merge FILE ...  run nothing: pool the seeds saved in the FILEs, grouped
//                     by row, workload and seeding, and report them as if run
//                     together
//
//   SEEDS AND THEIR STREAMS.  `TreeSim` starts its SplitMix64 state at
//   `seed * gamma + c` and every draw adds gamma, so seed `s + 1`'s stream is
//   seed `s`'s shifted by ONE draw: raw consecutive seeds are not independent
//   streams, only differently aligned reads of one.  Once the fill is
//   forgotten, seed `s + 1` under round-robin reads (`s + 2` under uniform
//   reads) replays seed `s` one operation later.  Seed mixing (the default)
//   starts each seed at a hashed point of the 2^64 cycle instead.  Unmixed
//   runs (`--no-seed-mix`, or saved files that record `seed_mix 0`) of more
//   than one seed therefore print no error bar and no verdict.
//   `--save`/`--merge` exist so a long run can be split into one process per
//   seed and resumed (analysis/run_stash_tail_long.py).
//
//   A row is `key=value,...`: lam (leaf bits), fold, logn or n (entries), a
//   (stash registers, default the rule's for the fold), ops, seeds, label.
//   z=4, b=2, sched=readpath, plan=inplace and preg (the path's registers)
//   may be given and are checked against the engine's shape.  Example:
//
//     cpu_tree_bucket_shape_benchmark --ops 20000000 lam=18,fold=3,logn=20

#include "benchmarks/oram/cpu_tree_stash_row.hpp"
#include "benchmarks/oram/cpu_tree_stash_sim.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include <unistd.h>

namespace {

namespace sim = microram::tree::stash_sim;

using sim::MixSeed;
using sim::ParseCount;
using sim::ParseRow;
using sim::Row;
using Clock = std::chrono::steady_clock;

// A positive, finite number of bits; a trailing character is refused.
double ParseBits(const std::string& what, const std::string& text) {
  char* end = nullptr;
  const double v = std::strtod(text.c_str(), &end);
  if (text.empty() || *end != '\0' || !std::isfinite(v) || !(v > 0)) {
    throw std::invalid_argument(what + " is not a positive number: `" + text + "`");
  }
  return v;
}

// ---------------------------------------------------------------------------
// Histograms and the tail fit
// ---------------------------------------------------------------------------

// A leftover count of 0..1022, with 1023 meaning "1023 or more".  The engine
// fails past 64 A - 1; the range is this wide so that a shape which does not
// fit still yields a distribution to fit rather than a wall of saturated bins.
constexpr unsigned kBins = 1024;

struct Hist {
  std::vector<uint64_t> bin;
  uint64_t samples = 0;
  unsigned max = 0;
  Hist() : bin(kBins, 0) {}
  void Add(unsigned x) {
    ++bin[x >= kBins ? kBins - 1 : x];
    ++samples;
    if (x > max) max = x;
  }
  void Merge(const Hist& o) {
    for (unsigned k = 0; k < kBins; ++k) bin[k] += o.bin[k];
    samples += o.samples;
    if (o.max > max) max = o.max;
  }
  // tail[k] = the number of samples with x >= k.
  std::vector<uint64_t> Tail() const {
    std::vector<uint64_t> t(kBins + 1, 0);
    for (int k = kBins - 1; k >= 0; --k) t[k] = t[k + 1] + bin[k];
    return t;
  }
  unsigned Mode() const {
    unsigned m = 0;
    for (unsigned k = 1; k < kBins; ++k) {
      if (bin[k] > bin[m]) m = k;
    }
    return m;
  }
};

struct Window {
  unsigned k0 = 0, k1 = 0;
  bool ok = false;
};

// The fit window: from where the tail has passed `2^-tail_start` -- deep
// enough that the geometric regime has set in and the mode's shoulder is
// behind -- to the deepest point that still has `tail_min` samples under it.
Window ChooseWindow(const Hist& h, unsigned tail_start, uint64_t tail_min) {
  Window w;
  if (h.samples == 0) return w;
  const std::vector<uint64_t> tail = h.Tail();
  const unsigned mode = h.Mode();
  const double threshold = static_cast<double>(h.samples) * std::exp2(-double(tail_start));
  unsigned k0 = mode + 1;
  while (k0 < kBins && static_cast<double>(tail[k0]) > threshold) ++k0;
  if (k0 < mode + 2) k0 = mode + 2;
  unsigned k1 = k0;
  for (unsigned k = k0; k < kBins; ++k) {
    if (tail[k] >= tail_min) k1 = k;
  }
  if (k1 < k0 + 4) {
    // Not enough of a deep tail: fall back to a window that opens just past
    // the mode, so a row with a short tail still reports something.
    k0 = mode + 2;
    k1 = k0;
    for (unsigned k = k0; k < kBins; ++k) {
      if (tail[k] >= tail_min) k1 = k;
    }
  }
  w.k0 = k0;
  w.k1 = k1;
  w.ok = k1 >= k0 + 3;
  return w;
}

struct Fit {
  bool ok = false;
  double slope = 0;      // bits per lane, positive
  double intercept = 0;  // log2 P[x >= 0] of the fitted line, i.e. its `a`
  double r2 = 0;
  double slope_lo = 0, slope_hi = 0;  // the window's shallow and deep halves
  unsigned points = 0;
  // The fitted line is `log2 P[x >= k] = intercept - slope k`, so it reaches
  // `2^-bits` at this many lanes.
  double KAt(double bits) const { return (bits + intercept) / slope; }
};

// Ordinary least squares of log2 P[x >= k] on k over the window.  Unweighted:
// the points are nested tail counts and their errors are
// neither independent nor of equal variance, so a weighting scheme would be a
// claim this measurement does not need -- the error bar comes from the seeds
// instead.
Fit FitTail(const std::vector<uint64_t>& tail, uint64_t samples, Window w) {
  Fit f;
  if (!w.ok || samples == 0) return f;
  double sx = 0, sy = 0, sxx = 0, sxy = 0;
  unsigned n = 0;
  for (unsigned k = w.k0; k <= w.k1; ++k) {
    if (tail[k] == 0) break;
    const double y = std::log2(static_cast<double>(tail[k]) / static_cast<double>(samples));
    sx += k; sy += y; sxx += double(k) * k; sxy += double(k) * y;
    ++n;
  }
  if (n < 4) return f;
  const double denom = n * sxx - sx * sx;
  if (denom == 0) return f;
  const double b = (n * sxy - sx * sy) / denom;
  const double a = (sy - b * sx) / n;
  if (b >= 0) return f;
  f.ok = true;
  f.slope = -b;
  f.intercept = a;
  f.points = n;
  // R^2 over the window.
  double ss_tot = 0, ss_res = 0;
  const double mean = sy / n;
  for (unsigned k = w.k0; k <= w.k0 + n - 1; ++k) {
    const double y = std::log2(static_cast<double>(tail[k]) / static_cast<double>(samples));
    ss_tot += (y - mean) * (y - mean);
    const double r = y - (a + b * k);
    ss_res += r * r;
  }
  f.r2 = ss_tot > 0 ? 1.0 - ss_res / ss_tot : 1.0;
  // The two halves, so a curving tail is visible rather than averaged away.
  const unsigned mid = w.k0 + n / 2;
  const auto half = [&](unsigned lo, unsigned hi) {
    double ax = 0, ay = 0, axx = 0, axy = 0;
    unsigned m = 0;
    for (unsigned k = lo; k <= hi; ++k) {
      if (tail[k] == 0) break;
      const double y = std::log2(static_cast<double>(tail[k]) / static_cast<double>(samples));
      ax += k; ay += y; axx += double(k) * k; axy += double(k) * y;
      ++m;
    }
    if (m < 3) return std::nan("");
    const double d = m * axx - ax * ax;
    return d == 0 ? std::nan("") : -(m * axy - ax * ay) / d;
  };
  f.slope_lo = half(w.k0, mid);
  f.slope_hi = half(mid, w.k0 + n - 1);
  return f;
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

enum Workload { kUniform, kRoundRobin, kHotSet, kMisses, kChurn };
const char* WorkloadName(Workload w) {
  switch (w) {
    case kUniform: return "uniform";
    case kRoundRobin: return "roundrobin";
    case kHotSet: return "hotset";
    case kMisses: return "misses";
    default: return "churn";
  }
}
Workload ParseWorkload(const std::string& s) {
  if (s == "roundrobin") return kRoundRobin;
  if (s == "hotset") return kHotSet;
  if (s == "misses") return kMisses;
  if (s == "churn") return kChurn;
  if (s != "uniform") throw std::invalid_argument("unknown workload: " + s);
  return kUniform;
}

enum Phase { kFill, kWarm, kSteady, kPhases };
const char* PhaseName(Phase p) {
  return p == kFill ? "fill" : (p == kWarm ? "warm" : "steady");
}
// An access is one pass, so access-pass and op-max hold the same counts, and
// evict-pass (a pass that is not an access's) stays empty; all four keep
// their places in the --save format, so every saved run merges.
enum Series { kAccessPass, kEvictPass, kOpMax, kAfterOp, kSeries };
const char* SeriesName(Series s) {
  switch (s) {
    case kAccessPass: return "access-pass";
    case kEvictPass: return "evict-pass";
    case kOpMax: return "op-max";
    default: return "after-op";
  }
}


// ---------------------------------------------------------------------------
// One seed
// ---------------------------------------------------------------------------

struct SeedRun {
  std::vector<Hist> hist;  // [phase][series]
  uint64_t seed = 0;
  uint64_t operations = 0;
  bool diverged = false;
  std::string note;
  SeedRun() : hist(kPhases * kSeries) {}
  Hist& at(Phase p, Series s) { return hist[p * kSeries + s]; }
  const Hist& at(Phase p, Series s) const { return hist[p * kSeries + s]; }
};

void RunSeed(const Row& row, uint64_t ops, Workload workload, uint64_t seed,
             SeedRun* out, std::vector<uint64_t>* level_occupancy) {
  const uint64_t n = row.n();
  sim::TreeSim s(row.geometry(), n, seed);
  Phase phase = kFill;
  const auto record = [&](const sim::OpResult& r) {
    out->at(phase, kAccessPass).Add(r.leftovers);
    out->at(phase, kOpMax).Add(r.leftovers);
    out->at(phase, kAfterOp).Add(r.occupancy_after);
  };
  try {
    for (uint64_t k = 0; k < n; ++k) record(s.Insert(k));
    // The warm phase reads block `state % n`, the generator's raw STATE and
    // not a draw.  Each read advances the state by the odd SplitMix64 gamma,
    // so for a power-of-two `n` this is one pass over every block in a fixed
    // stride order (a round-robin-like burn-in), not `n` uniform reads.  It is
    // not fitted unless `--fit-phases` is given; every saved run depends on it.
    phase = kWarm;
    for (uint64_t i = 0; i < n; ++i) record(s.ReadBlock(s.rng() % n));
    phase = kSteady;
    const uint64_t hot = n / 64 == 0 ? 1 : n / 64;
    uint64_t& rng = s.rng();
    // The blocks of the next operations are known in advance for these two
    // workloads, so their paths are requested `kAhead` operations early (the
    // positions themselves `2 kAhead` early for uniform reads, whose blocks
    // are scattered).  A prefetch changes no state: the histograms are
    // bit-for-bit those of the loop without it.
    constexpr uint64_t kAhead = 4;
    uint64_t rr_block = 0, rr_ahead = kAhead % n;
    for (uint64_t i = 0; i < ops; ++i) {
      switch (workload) {
        case kUniform: {
          // An operation draws its block and then its fresh leaf, so the
          // block `k` operations ahead is the stream's draw `2 k + 1`.
          s.PrefetchPosition(sim::SimSplitMix64Peek(rng, 4 * kAhead + 1) % n);
          s.PrefetchOp(sim::SimSplitMix64Peek(rng, 2 * kAhead + 1) % n);
          record(s.ReadBlock(sim::SimSplitMix64(rng) % n));
          break;
        }
        case kRoundRobin:
          s.PrefetchOp(rr_ahead);
          record(s.ReadBlock(rr_block));
          if (++rr_block == n) rr_block = 0;
          if (++rr_ahead == n) rr_ahead = 0;
          break;
        case kHotSet: {
          const uint64_t v = sim::SimSplitMix64(rng);
          record(s.ReadBlock((v % 10) < 9 ? (v >> 8) % hot : (v >> 8) % n));
          break;
        }
        case kMisses:
          record(s.MissBlock());
          break;
        case kChurn: {
          const uint64_t k = sim::SimSplitMix64(rng) % n;
          record(s.EraseBlock(k));
          record(s.Insert(k));
          break;
        }
      }
      ++out->operations;
    }
    if (level_occupancy != nullptr) {
      // Which levels are full.  A shape that fails because its buckets
      // cannot hold the blocks that belong in them looks different from one
      // that fails because it does not evict often enough, and this is what
      // tells them apart.
      const sim::Geometry& g = s.geometry();
      level_occupancy->assign(g.leaf_bits + 1, 0);
      for (unsigned j = g.fold; j <= g.leaf_bits; ++j) {
        for (uint64_t b = 0; b < (uint64_t{1} << j); ++b) {
          for (unsigned t = 0; t < sim::kZ; ++t) {
            (*level_occupancy)[j] += s.TreeSlot(j, b, t).block >= 0;
          }
        }
      }
    }
  } catch (const sim::SimDivergedError& e) {
    out->diverged = true;
    out->note = std::string(e.what()) + " in the " + PhaseName(phase) +
                " phase after " + std::to_string(out->operations) +
                " steady operations";
  }
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

struct Options {
  uint64_t ops = 2000000;
  unsigned seeds = 16;
  unsigned threads = 0;
  Workload workload = kUniform;
  double target_bits = 96;
  uint64_t tail_min = 30;
  unsigned tail_start = 10;
  bool detail = false;
  bool levels = false;
  bool fit_phases = false;
  std::string series = "op-max";
  uint64_t seed_base = 1;
  bool seed_mix = true;
  std::string save;
};

struct Jack {
  double value = 0, se = 0;
  bool ok = false;
};

// The jackknife over seeds: refit with each seed's samples removed, and take
// the spread of the results.  Consecutive accesses of one seed are strongly
// correlated -- the stash is a slowly mixing Markov chain -- so a binomial
// error bar on a tail count would be far too small.  Mixed seeds (the
// default) are independent by construction and are the only thing here that
// is; unmixed seeds are shifted copies of one stream, so `PrintSeries` prints
// no error bar for more than one of them.
struct JackFit {
  Fit pooled;
  Jack slope, k_target, k64, k80;
};

JackFit Jackknife(const std::vector<const Hist*>& per_seed, Window w,
                  double target_bits) {
  JackFit out;
  Hist pooled;
  for (const Hist* h : per_seed) pooled.Merge(*h);
  out.pooled = FitTail(pooled.Tail(), pooled.samples, w);
  if (!out.pooled.ok) return out;
  // The point estimates are the pooled fit's whatever happens next; the
  // jackknife below only adds the error bar, and it needs seeds to do it.
  out.slope.value = out.pooled.slope;
  out.k_target.value = out.pooled.KAt(target_bits);
  out.k64.value = out.pooled.KAt(64);
  out.k80.value = out.pooled.KAt(80);
  if (per_seed.size() < 3) return out;
  std::vector<double> slope, kt, k64, k80;
  for (size_t i = 0; i < per_seed.size(); ++i) {
    Hist loo;
    for (size_t j = 0; j < per_seed.size(); ++j) {
      if (j != i) loo.Merge(*per_seed[j]);
    }
    const Fit f = FitTail(loo.Tail(), loo.samples, w);
    if (!f.ok) return out;
    slope.push_back(f.slope);
    kt.push_back(f.KAt(target_bits));
    k64.push_back(f.KAt(64));
    k80.push_back(f.KAt(80));
  }
  const auto jack = [&](const std::vector<double>& v, double point) {
    Jack j;
    const double m = static_cast<double>(v.size());
    double mean = 0;
    for (double x : v) mean += x;
    mean /= m;
    double ss = 0;
    for (double x : v) ss += (x - mean) * (x - mean);
    j.value = point;
    j.se = std::sqrt((m - 1.0) / m * ss);
    j.ok = true;
    return j;
  };
  out.slope = jack(slope, out.pooled.slope);
  out.k_target = jack(kt, out.pooled.KAt(target_bits));
  out.k64 = jack(k64, out.pooled.KAt(64));
  out.k80 = jack(k80, out.pooled.KAt(80));
  return out;
}

std::string Commas(uint64_t v) {
  std::string s = std::to_string(v), out;
  int c = 0;
  for (int i = static_cast<int>(s.size()) - 1; i >= 0; --i) {
    out.push_back(s[i]);
    if (++c % 3 == 0 && i > 0) out.push_back(',');
  }
  std::reverse(out.begin(), out.end());
  return out;
}

void PrintSeries(const std::vector<SeedRun>& runs, Phase phase, Series series,
                 const Options& o, unsigned lanes) {
  std::vector<const Hist*> per_seed;
  for (const SeedRun& r : runs) per_seed.push_back(&r.at(phase, series));
  Hist pooled;
  for (const Hist* h : per_seed) pooled.Merge(*h);
  if (pooled.samples == 0) return;
  if (pooled.Mode() > lanes) {
    // Not a tail question at all: the stash SITS above the lane count, so the
    // shape does not work at this load whatever the extrapolation says.
    std::printf("  %-6s %-11s %14s  mode %3u  max %4u | THE STASH SITS ABOVE "
                "THE %u LANES: this shape does not hold at this load\n",
                PhaseName(phase), SeriesName(series),
                Commas(pooled.samples).c_str(), pooled.Mode(), pooled.max,
                lanes);
    return;
  }
  const Window w = ChooseWindow(pooled, o.tail_start, o.tail_min);
  const JackFit jf = Jackknife(per_seed, w, o.target_bits);
  const std::vector<uint64_t> tail = pooled.Tail();
  const double deepest =
      tail[w.k1] > 0
          ? -std::log2(static_cast<double>(tail[w.k1]) / double(pooled.samples))
          : 0;

  std::printf("  %-6s %-11s %14s  mode %3u  max %4u |", PhaseName(phase),
              SeriesName(series), Commas(pooled.samples).c_str(), pooled.Mode(),
              pooled.max);
  if (!jf.pooled.ok) {
    std::printf(" tail too short to fit (%s samples past k = %u)\n",
                Commas(tail[pooled.Mode() + 2]).c_str(), pooled.Mode() + 2);
    return;
  }
  // Unmixed seeds are shifted copies of one stream: their spread is no error
  // bar, and a verdict resting on it is none either.
  const bool unmixed = !o.seed_mix && runs.size() > 1;
  std::printf(" fit k %u..%u to 2^-%.0f, %.3f", w.k0, w.k1, deepest,
              jf.pooled.slope);
  if (jf.slope.ok && !unmixed) std::printf(" +- %.3f", jf.slope.se);
  char halves[64];
  if (std::isnan(jf.pooled.slope_hi)) {
    std::snprintf(halves, sizeof(halves), "%.2f/--", jf.pooled.slope_lo);
  } else {
    std::snprintf(halves, sizeof(halves), "%.2f/%.2f", jf.pooled.slope_lo,
                  jf.pooled.slope_hi);
  }
  std::printf(" bits/lane (halves %s, R2 %.4f)\n", halves, jf.pooled.r2);
  const double kt = jf.k_target.value;
  std::printf("  %-6s %-11s lanes at 2^-64 %6.1f | 2^-80 %6.1f | 2^-%-3.0f "
              "%6.1f", "", "", jf.k64.value, jf.k80.value, o.target_bits, kt);
  // The verdict is taken two standard errors up, so it needs an error bar:
  // three seeds or more, every leave-one-out fit good, and mixed seeds.
  if (unmixed || !jf.k_target.ok) {
    std::printf(" | %s: no error bar, no verdict against %u lanes\n",
                unmixed ? "unmixed seeds (one shifted stream)"
                        : "fewer than three seeds or a failed leave-one-out fit",
                lanes);
  } else {
    const double conservative = kt + 2 * jf.k_target.se;
    std::printf(" +- %.1f", jf.k_target.se);
    std::printf(" (2 s.e. up: %.1f) | %u lanes: %s\n", conservative, lanes,
                conservative <= lanes
                    ? (kt <= lanes ? "FITS" : "fits, margin inside the error bar")
                    : "DOES NOT FIT");
  }
  if (o.detail) {
    // The whole observed tail, and the LOCAL slope between consecutive points:
    // the straight line is the model, and this is the data it is fitted to.
    // A local slope that grows with k is a tail steepening away from the line,
    // which makes the extrapolation conservative; one that shrinks does not.
    unsigned last = 0;
    for (unsigned k = 0; k < kBins; ++k) {
      if (tail[k] != 0) last = k;
    }
    const auto bits = [&](unsigned k) {
      return -std::log2(static_cast<double>(tail[k]) / double(pooled.samples));
    };
    std::printf("           k :");
    for (unsigned k = 1; k <= last; ++k) std::printf(" %6u", k);
    std::printf("\n     -log2 P :");
    for (unsigned k = 1; k <= last; ++k) std::printf(" %6.2f", bits(k));
    std::printf("\n  local slope :      -");
    for (unsigned k = 2; k <= last; ++k) std::printf(" %6.2f", bits(k) - bits(k - 1));
    std::printf("   (window %u..%u)\n", w.k0, w.k1);
  }
}


void PrintRowHeader(const Row& row, Workload workload, size_t seeds,
                    const std::string& ops) {
  const sim::Geometry g = row.geometry();
  const uint64_t n = row.n();
  std::printf(
      "\n=== %s | lambda %u  fold %u  P %u  path lanes %u  A %u  |  N %s  "
      "slots/entry %.2f  load %.3f  |  %s  |  %zu seeds x %s ops  |  "
      "leftover lanes %u\n",
      row.label.c_str(), g.leaf_bits, g.fold, g.path_levels, g.path_lanes(),
      g.stash_registers, Commas(n).c_str(), g.slots_per_entry(n), g.load(n),
      WorkloadName(workload), seeds, ops.c_str(), g.leftover_lanes());
}

// Everything after the seeds have run.  `secs` < 0 means the runs were loaded
// by `--merge`, so there is no wall time to report.
void ReportRow(const Row& row, const std::vector<SeedRun>& runs,
               const Options& o, const std::vector<uint64_t>& occupancy,
               double secs, unsigned threads) {
  const sim::Geometry g = row.geometry();
  const unsigned lanes = g.leftover_lanes();
  uint64_t total_ops = 0, total_passes = 0;
  bool diverged = false;
  for (const SeedRun& r : runs) {
    total_ops += r.operations;
    for (unsigned p = 0; p < kPhases; ++p) {
      total_passes += r.at(static_cast<Phase>(p), kAccessPass).samples;
    }
    if (r.diverged) {
      diverged = true;
      std::printf("  DIVERGED (seed %llu): %s\n",
                  static_cast<unsigned long long>(r.seed), r.note.c_str());
    }
  }
  // Fill and warm: the maximum alone, one line each, so a cold-fill failure
  // shows even where those phases are not fitted.
  for (Phase p : {kFill, kWarm}) {
    Hist m;
    for (const SeedRun& r : runs) m.Merge(r.at(p, kOpMax));
    if (m.samples == 0) continue;
    std::printf("  %-6s max leftovers %u  (%s operations)%s\n", PhaseName(p),
                m.max, Commas(m.samples).c_str(),
                m.max > lanes ? "   *** OVER THE LANE COUNT ***" : "");
  }
  if (o.levels && !occupancy.empty()) {
    std::printf("  levels (first seed, after the steady phase), occupancy of each:");
    for (unsigned j = g.fold; j <= g.leaf_bits; ++j) {
      const double cap = static_cast<double>(sim::kZ) * double(uint64_t{1} << j);
      std::printf(" %u:%.0f%%", j, 100.0 * double(occupancy[j]) / cap);
    }
    std::printf("\n");
  }
  const std::string want = o.series;
  for (unsigned q = 0; q < kSeries; ++q) {
    const Series s = static_cast<Series>(q);
    if (want != "all" && want != SeriesName(s)) continue;
    // `--fit-phases` fits the fill and the warm cycle on the same footing as
    // the steady state; each has only `N` samples per seed, which is usually
    // too few for a deep window.
    if (o.fit_phases) {
      PrintSeries(runs, kFill, s, o, lanes);
      PrintSeries(runs, kWarm, s, o, lanes);
    }
    PrintSeries(runs, kSteady, s, o, lanes);
  }
  if (secs < 0) {
    std::printf("  %s steady operations, %s passes (merged from saved seeds)%s\n",
                Commas(total_ops).c_str(), Commas(total_passes).c_str(),
                diverged ? "   [DIVERGED]" : "");
  } else {
    std::printf("  %s steady operations, %s passes, %.1f s wall, %.0f ns per "
                "pass per thread%s\n",
                Commas(total_ops).c_str(), Commas(total_passes).c_str(), secs,
                total_passes == 0 ? 0.0
                                  : secs * 1e9 * threads / double(total_passes),
                diverged ? "   [DIVERGED]" : "");
  }
  std::fflush(stdout);
}

// ---------------------------------------------------------------------------
// --save and --merge: one text file per run, every seed's histograms in it
// ---------------------------------------------------------------------------

constexpr const char* kSaveMagic = "cpu_tree_bucket_shape_benchmark seeds v1";

struct Saved {
  std::string spec;
  Workload workload = kUniform;
  bool seed_mix = false;
  std::vector<SeedRun> runs;
};

// Written to `path.tmp.<pid>` and renamed, so a file that exists is complete
// whenever the process stopped.
void SaveRuns(const std::string& path, const Row& row, Workload workload,
              bool seed_mix, const std::vector<SeedRun>& runs) {
  const std::string tmp = path + ".tmp." + std::to_string(::getpid());
  FILE* f = std::fopen(tmp.c_str(), "w");
  if (f == nullptr) throw std::runtime_error("cannot write " + tmp);
  std::fprintf(f, "%s\nspec %s\nworkload %s\nseed_mix %d\n", kSaveMagic,
               row.spec.c_str(), WorkloadName(workload), seed_mix ? 1 : 0);
  for (const SeedRun& r : runs) {
    std::string note = r.note;
    std::replace(note.begin(), note.end(), '\n', ' ');
    std::fprintf(f, "seed %llu operations %llu diverged %d\nnote %s\n",
                 static_cast<unsigned long long>(r.seed),
                 static_cast<unsigned long long>(r.operations),
                 r.diverged ? 1 : 0, note.empty() ? "-" : note.c_str());
    for (unsigned p = 0; p < kPhases; ++p) {
      for (unsigned q = 0; q < kSeries; ++q) {
        const Hist& h = r.at(static_cast<Phase>(p), static_cast<Series>(q));
        std::fprintf(f, "hist %u %u %llu %u", p, q,
                     static_cast<unsigned long long>(h.samples), h.max);
        for (unsigned k = 0; k < kBins; ++k) {
          if (h.bin[k] != 0) {
            std::fprintf(f, " %u:%llu", k,
                         static_cast<unsigned long long>(h.bin[k]));
          }
        }
        std::fprintf(f, "\n");
      }
    }
  }
  std::fprintf(f, "end\n");
  const bool ok = std::fflush(f) == 0 && ::fsync(::fileno(f)) == 0;
  if (std::fclose(f) != 0 || !ok) throw std::runtime_error("cannot write " + tmp);
  if (std::rename(tmp.c_str(), path.c_str()) != 0) {
    throw std::runtime_error("cannot rename " + tmp + " to " + path);
  }
}

Saved LoadRuns(const std::string& path) {
  FILE* f = std::fopen(path.c_str(), "r");
  if (f == nullptr) throw std::runtime_error("cannot read " + path);
  std::string text;
  char buf[1 << 16];
  for (size_t got; (got = std::fread(buf, 1, sizeof(buf), f)) > 0;) text.append(buf, got);
  std::fclose(f);
  const auto bad = [&](const std::string& why) {
    return std::runtime_error(path + ": " + why);
  };
  Saved out;
  size_t pos = 0;
  const auto line = [&]() -> std::string {
    if (pos >= text.size()) throw bad("truncated");
    size_t nl = text.find('\n', pos);
    if (nl == std::string::npos) throw bad("truncated");
    std::string l = text.substr(pos, nl - pos);
    pos = nl + 1;
    return l;
  };
  const auto field = [&](const std::string& l, const std::string& key) {
    if (l.rfind(key + " ", 0) != 0) throw bad("expected `" + key + "`, got `" + l + "`");
    return l.substr(key.size() + 1);
  };
  if (line() != kSaveMagic) throw bad("not a saved run");
  out.spec = field(line(), "spec");
  out.workload = ParseWorkload(field(line(), "workload"));
  out.seed_mix = field(line(), "seed_mix") == "1";
  for (;;) {
    const std::string l = line();
    if (l == "end") break;
    SeedRun r;
    unsigned long long seed = 0, ops = 0;
    int div = 0;
    if (std::sscanf(l.c_str(), "seed %llu operations %llu diverged %d", &seed,
                    &ops, &div) != 3) {
      throw bad("bad seed line `" + l + "`");
    }
    r.seed = seed;
    r.operations = ops;
    r.diverged = div != 0;
    r.note = field(line(), "note");
    if (r.note == "-") r.note.clear();
    for (unsigned i = 0; i < kPhases * kSeries; ++i) {
      const std::string h = line();
      const char* c = h.c_str();
      unsigned p = 0, q = 0, max = 0;
      unsigned long long samples = 0;
      int used = 0;
      if (std::sscanf(c, "hist %u %u %llu %u%n", &p, &q, &samples, &max, &used) != 4 ||
          p >= kPhases || q >= kSeries) {
        throw bad("bad hist line");
      }
      Hist& dst = r.at(static_cast<Phase>(p), static_cast<Series>(q));
      dst.samples = samples;
      dst.max = max;
      c += used;
      uint64_t sum = 0;
      for (;;) {
        unsigned k = 0;
        unsigned long long v = 0;
        int n = 0;
        if (std::sscanf(c, " %u:%llu%n", &k, &v, &n) != 2) break;
        if (k >= kBins) throw bad("bin out of range");
        dst.bin[k] = v;
        sum += v;
        c += n;
      }
      if (sum != dst.samples) throw bad("histogram does not sum to its samples");
    }
    out.runs.push_back(std::move(r));
  }
  return out;
}

int Merge(const std::vector<std::string>& paths, const Options& o) {
  // Group by (row, workload, seeding), in the order the groups first appear.
  struct Group {
    Saved saved;
    std::vector<std::string> files;
  };
  std::vector<Group> groups;
  for (const std::string& p : paths) {
    Saved s = LoadRuns(p);
    Group* g = nullptr;
    for (Group& x : groups) {
      if (x.saved.spec == s.spec && x.saved.workload == s.workload &&
          x.saved.seed_mix == s.seed_mix) {
        g = &x;
      }
    }
    if (g == nullptr) {
      groups.push_back(Group{});
      g = &groups.back();
      g->saved.spec = s.spec;
      g->saved.workload = s.workload;
      g->saved.seed_mix = s.seed_mix;
    }
    for (SeedRun& r : s.runs) {
      for (const SeedRun& have : g->saved.runs) {
        if (have.seed == r.seed) {
          throw std::runtime_error(p + ": seed " + std::to_string(r.seed) +
                                   " of `" + s.spec + "` is already loaded");
        }
      }
      g->saved.runs.push_back(std::move(r));
    }
    g->files.push_back(p);
  }
  for (Group& g : groups) {
    const Row row = ParseRow(g.saved.spec);
    std::vector<SeedRun>& runs = g.saved.runs;
    std::sort(runs.begin(), runs.end(),
              [](const SeedRun& a, const SeedRun& b) { return a.seed < b.seed; });
    uint64_t lo = UINT64_MAX, hi = 0;
    for (const SeedRun& r : runs) {
      lo = std::min(lo, r.operations);
      hi = std::max(hi, r.operations);
    }
    PrintRowHeader(row, g.saved.workload, runs.size(),
                   lo == hi ? Commas(lo) : Commas(lo) + ".." + Commas(hi));
    std::printf("  merged from %zu file(s); seeds %llu..%llu%s\n",
                g.files.size(),
                static_cast<unsigned long long>(runs.front().seed),
                static_cast<unsigned long long>(runs.back().seed),
                g.saved.seed_mix ? " (mixed)" : " (unmixed: one shifted stream)");
    // The group's own seeding decides whether its seeds give an error bar.
    Options go = o;
    go.seed_mix = g.saved.seed_mix;
    ReportRow(row, runs, go, {}, -1.0, 0);
  }
  return 0;
}

void RunRow(const Row& row, const Options& o) {
  const uint64_t ops = row.ops != 0 ? row.ops : o.ops;
  const unsigned seeds = row.seeds != 0 ? row.seeds : o.seeds;
  PrintRowHeader(row, o.workload, seeds, Commas(ops));

  std::vector<SeedRun> runs(seeds);
  std::vector<uint64_t> occupancy;
  const unsigned threads =
      std::min<unsigned>(seeds, o.threads != 0 ? o.threads
                                               : std::max(1u, std::thread::hardware_concurrency()));
  std::atomic<unsigned> next{0};
  const auto t0 = Clock::now();
  std::vector<std::thread> pool;
  for (unsigned t = 0; t < threads; ++t) {
    pool.emplace_back([&] {
      for (;;) {
        const unsigned i = next.fetch_add(1);
        if (i >= seeds) return;
        runs[i].seed = o.seed_base + i;
        RunSeed(row, ops, o.workload,
                o.seed_mix ? MixSeed(runs[i].seed) : runs[i].seed, &runs[i],
                (o.levels && i == 0) ? &occupancy : nullptr);
      }
    });
  }
  for (std::thread& t : pool) t.join();
  const double secs = std::chrono::duration<double>(Clock::now() - t0).count();
  if (!o.save.empty()) SaveRuns(o.save, row, o.workload, o.seed_mix, runs);
  ReportRow(row, runs, o, occupancy, secs, threads);
}

}  // namespace

int main(int argc, char** argv) {
  Options o;
  std::vector<Row> rows;
  std::vector<std::string> positional;
  bool merge = false;
  try {
    for (int i = 1; i < argc; ++i) {
      const std::string a = argv[i];
      const auto next = [&]() -> std::string {
        if (i + 1 >= argc) throw std::invalid_argument(a + " needs a value");
        return argv[++i];
      };
      if (a == "--ops") o.ops = ParseCount(a, next(), UINT64_MAX);
      else if (a == "--seeds") o.seeds = static_cast<unsigned>(ParseCount(a, next(), UINT_MAX));
      else if (a == "--threads") o.threads = static_cast<unsigned>(ParseCount(a, next(), UINT_MAX));
      else if (a == "--workload") o.workload = ParseWorkload(next());
      else if (a == "--target") o.target_bits = ParseBits(a, next());
      else if (a == "--tail-min") o.tail_min = ParseCount(a, next(), UINT64_MAX);
      else if (a == "--tail-start") o.tail_start = static_cast<unsigned>(ParseCount(a, next(), UINT_MAX));
      else if (a == "--series") o.series = next();
      else if (a == "--detail") o.detail = true;
      else if (a == "--levels") o.levels = true;
      else if (a == "--fit-phases") o.fit_phases = true;
      else if (a == "--seed-base") o.seed_base = ParseCount(a, next(), UINT64_MAX);
      else if (a == "--seed-mix") o.seed_mix = true;
      else if (a == "--no-seed-mix") o.seed_mix = false;
      else if (a == "--save") o.save = next();
      else if (a == "--merge") merge = true;
      else if (a.rfind("--", 0) == 0) throw std::invalid_argument("unknown option: " + a);
      else positional.push_back(a);
    }
    if (o.seeds == 0) throw std::invalid_argument("--seeds must be at least 1");
    bool known_series = o.series == "all";
    for (unsigned q = 0; q < kSeries; ++q) {
      known_series |= o.series == SeriesName(static_cast<Series>(q));
    }
    if (!known_series) throw std::invalid_argument("unknown series: " + o.series);
    if (merge) {
      if (positional.empty()) throw std::invalid_argument("--merge needs files");
      if (!o.save.empty()) throw std::invalid_argument("--merge and --save do not mix");
      return Merge(positional, o);
    }
    for (const std::string& a : positional) rows.push_back(ParseRow(a));
    if (rows.empty()) throw std::invalid_argument("give at least one row");
    if (!o.save.empty() && rows.size() != 1) {
      throw std::invalid_argument("--save takes exactly one row");
    }
  } catch (const std::exception& e) {
    std::fprintf(stderr, "cpu_tree_bucket_shape_benchmark: %s\n", e.what());
    return 2;
  }

  std::printf(
      "cpu_tree_bucket_shape_benchmark: the stash tail of the read-path tree "
      "ORAM.  A scalar simulator of the engine's plan over metadata alone, "
      "checked against CpuReadPathOram slot for slot "
      "(tests/oram/cpu_tree_read_path_oram_test.cpp).\n"
      "Series: access-pass and op-max are the LEFTOVER count of each access "
      "-- the stash entries the plan keeps, which the engine's overflow check "
      "holds to 64 A - 1 -- and the PER-ACCESS failure quantity; after-op is "
      "the stash-region occupancy afterwards.  The lane columns are a "
      "straight line fitted to "
      "the observed tail and CONTINUED to 2^-64, 2^-80 and 2^-%.0f; %s\n",
      o.target_bits,
      o.seed_mix
          ? "the error bar is a jackknife over the seeds, which are the only "
            "independent samples here."
          : "the seeds are unmixed (--no-seed-mix), shifted copies of one "
            "stream, so they give no error bar.");
  int status = 0;
  for (const Row& r : rows) {
    try {
      RunRow(r, o);
    } catch (const std::exception& e) {
      std::printf("\n=== %s: SKIPPED, %s\n", r.label.c_str(), e.what());
      status = 1;
    }
  }
  return status;
}
