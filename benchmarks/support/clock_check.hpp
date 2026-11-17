#pragma once

// `--clock-check`: the TSC against the OS clocks, inside the runtime the
// trials will run in (for a confidential VM, inside the guest): TSC-based
// timing against a monotonic OS clock, migration skew between CPUs, and rate
// consistency over long windows.  `oram_bench doctor` runs it before a
// campaign.
//
// Every latency the harness records is a steady_clock difference, and on
// Linux that is CLOCK_MONOTONIC read through the vDSO from the TSC when the
// clocksource is `tsc`.  What can go wrong is therefore about the TSC and the
// kernel's use of it, and each measurement below targets one failure:
//
//   rate windows    the TSC's rate against CLOCK_MONOTONIC_RAW over several
//                   consecutive windows.  A rate that moves between windows
//                   (a host rescaling a guest's TSC, a clocksource switch) is
//                   a latency error that no single window shows.
//   slew            CLOCK_MONOTONIC against CLOCK_MONOTONIC_RAW: the
//                   frequency correction NTP is applying to steady_clock.
//   per-CPU offset  each allowed CPU's TSC against the first one's.  A thread
//                   that migrates between unsynchronized TSCs sees time jump,
//                   or run backwards.  No OS clock can measure this: the vDSO
//                   computes MONOTONIC_RAW from the LOCAL TSC, so a skew
//                   cancels.  Two threads ping-pong TSC stamps instead, and
//                   causality bounds the offset from both sides: B's stamp
//                   after A's send is at least A's send plus B's offset, and
//                   A's stamp after B's reply at least B's minus it.  An
//                   interval that excludes zero is a proven skew.
//   read cost       one steady_clock::now(): tens of nanoseconds through the
//                   vDSO, a microsecond when the read falls back to a system
//                   call (or, in a guest, traps).
//   NTP state       adjtimex's view: synchronized or not, its frequency
//                   correction and its error bound.  Evidence only.
//
// All five are about the platform, not the library, and all are reported;
// doctor decides what counts as a failure.  The check takes about 1.2 s.

#include <sched.h>
#include <sys/timex.h>
#include <time.h>
#include <x86intrin.h>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

namespace oram_bench {

struct ClockPair {
  uint64_t tsc;
  int64_t raw_ns;
};

inline int64_t ClockNs(clockid_t id) {
  timespec ts{};
  clock_gettime(id, &ts);
  return int64_t{ts.tv_sec} * 1000000000 + ts.tv_nsec;
}

// One MONOTONIC_RAW read bracketed by two TSC reads, the narrowest bracket of
// `tries`, so that an interrupt between the reads cannot pass for an offset.
// The TSC is taken at the bracket's midpoint.
inline ClockPair BestPair(int tries = 64) {
  ClockPair best{0, 0};
  uint64_t narrowest = ~uint64_t{0};
  for (int i = 0; i < tries; ++i) {
    unsigned aux;
    const uint64_t before = __rdtscp(&aux);
    const int64_t raw = ClockNs(CLOCK_MONOTONIC_RAW);
    const uint64_t after = __rdtscp(&aux);
    if (after - before < narrowest) {
      narrowest = after - before;
      best = ClockPair{before + (after - before) / 2, raw};
    }
  }
  return best;
}

inline double TscHz(const ClockPair& a, const ClockPair& b) {
  return double(b.tsc - a.tsc) * 1e9 / double(b.raw_ns - a.raw_ns);
}

// The offset of `cpu`'s TSC from `home`'s, bounded by causality over
// `rounds` ping-pongs: offset in [low, high] ticks.
struct TscOffset {
  int cpu;
  double low_ticks, high_ticks;
  bool placed;
};

inline bool PinTo(int cpu) {
  cpu_set_t one;
  CPU_ZERO(&one);
  CPU_SET(cpu, &one);
  return sched_setaffinity(0, sizeof(one), &one) == 0;
}

inline TscOffset MeasureTscOffset(int home, int cpu, int rounds = 256) {
  struct alignas(64) Stamp {
    std::atomic<uint64_t> round{0};
    uint64_t tsc = 0;
  };
  Stamp ping, pong;
  // Each thread records its own pin; the peer's is read after the join.
  bool peer_placed = false;
  std::thread peer([&] {
    peer_placed = PinTo(cpu);
    for (int r = 1; r <= rounds; ++r) {
      while (ping.round.load(std::memory_order_acquire) != uint64_t(r)) {
      }
      unsigned aux;
      pong.tsc = __rdtscp(&aux);
      pong.round.store(r, std::memory_order_release);
    }
  });
  const bool home_placed = PinTo(home);
  int64_t min_forward = INT64_MAX, min_back = INT64_MAX;
  for (int r = 1; r <= rounds; ++r) {
    unsigned aux;
    const uint64_t sent = __rdtscp(&aux);
    ping.tsc = sent;
    ping.round.store(r, std::memory_order_release);
    while (pong.round.load(std::memory_order_acquire) != uint64_t(r)) {
    }
    const uint64_t back = __rdtscp(&aux);
    min_forward = std::min(min_forward, int64_t(pong.tsc - sent));
    min_back = std::min(min_back, int64_t(back - pong.tsc));
  }
  peer.join();
  return TscOffset{cpu, -double(min_back), double(min_forward), home_placed && peer_placed};
}

inline void SpinFor(std::chrono::nanoseconds span) {
  const auto end = std::chrono::steady_clock::now() + span;
  while (std::chrono::steady_clock::now() < end) {
  }
}

inline bool PrintClockCheck(int argc, char** argv) {
  if (argc != 2 || std::string(argv[1]) != "--clock-check") return false;
  constexpr int kWindows = 5;
  constexpr auto kWindow = std::chrono::milliseconds(200);

  // Rate windows and slew, on the CPU the check starts on.
  std::vector<double> rates;
  const ClockPair first = BestPair();
  const int64_t mono0 = ClockNs(CLOCK_MONOTONIC);
  ClockPair previous = first;
  for (int w = 0; w < kWindows; ++w) {
    SpinFor(kWindow);
    const ClockPair now = BestPair();
    rates.push_back(TscHz(previous, now));
    previous = now;
  }
  const int64_t mono1 = ClockNs(CLOCK_MONOTONIC);
  const double hz = TscHz(first, previous);
  std::vector<double> sorted = rates;
  std::sort(sorted.begin(), sorted.end());
  const double median = sorted[sorted.size() / 2];
  const double spread_ppm = (sorted.back() - sorted.front()) / median * 1e6;
  const double slew_ppm =
      (double(mono1 - mono0) / double(previous.raw_ns - first.raw_ns) - 1.0) * 1e6;

  // Read cost of the clock the harness uses.
  constexpr int kReads = 1 << 20;
  const auto r0 = std::chrono::steady_clock::now();
  int64_t sink = 0;
  for (int i = 0; i < kReads; ++i) {
    sink += std::chrono::steady_clock::now().time_since_epoch().count() & 1;
  }
  const auto r1 = std::chrono::steady_clock::now();
  volatile int64_t keep = sink;  // the reads are not dead code
  (void)keep;
  const double read_ns =
      double(std::chrono::duration_cast<std::chrono::nanoseconds>(r1 - r0).count()) /
      kReads;

  // Per-CPU offsets, every allowed CPU against the first, by ping-pong; and
  // the first read after each migration against the last read before it.
  cpu_set_t original;
  CPU_ZERO(&original);
  sched_getaffinity(0, sizeof(original), &original);
  std::vector<int> cpus;
  for (int cpu = 0; cpu < CPU_SETSIZE; ++cpu) {
    if (CPU_ISSET(cpu, &original)) cpus.push_back(cpu);
  }
  std::vector<TscOffset> offsets;
  unsigned backwards = 0, unplaced = 0;
  uint64_t last_tsc = 0;
  for (int cpu : cpus) {
    if (!PinTo(cpu)) {
      ++unplaced;
      continue;
    }
    unsigned aux;
    const uint64_t arrived = __rdtscp(&aux);
    if (last_tsc != 0 && arrived < last_tsc) ++backwards;
    last_tsc = __rdtscp(&aux);
  }
  for (size_t i = 1; i < cpus.size(); ++i) {
    const TscOffset o = MeasureTscOffset(cpus[0], cpus[i]);
    if (!o.placed) ++unplaced;
    offsets.push_back(o);
  }
  sched_setaffinity(0, sizeof(original), &original);
  // The largest offset the bounds allow, and whether any interval excludes
  // zero (a proven skew).
  double max_offset_ns = 0;
  unsigned proven_skews = 0;
  for (const TscOffset& o : offsets) {
    max_offset_ns = std::max(max_offset_ns,
                             std::max(std::abs(o.low_ticks), std::abs(o.high_ticks)) *
                                 1e9 / hz);
    if (o.low_ticks > 0 || o.high_ticks < 0) ++proven_skews;
  }

  timex tx{};
  const int state = ntp_adjtime(&tx);
  const char* state_name = state == TIME_OK ? "ok" : state == TIME_INS ? "insert"
                         : state == TIME_DEL ? "delete" : state == TIME_OOP ? "in_progress"
                         : state == TIME_WAIT ? "wait" : "error";

  // Every real number is printed with a decimal point: the reader's schema
  // tells integers from reals by their spelling.
  std::printf("{\"schema\":\"clock-check-v1\",\"tsc_hz\":%.1f,\"window_ms\":%d,"
              "\"window_hz\":[",
              hz, int(kWindow.count()));
  for (size_t i = 0; i < rates.size(); ++i) std::printf("%s%.1f", i ? "," : "", rates[i]);
  std::printf("],\"rate_spread_ppm\":%.3f,\"monotonic_slew_ppm\":%.3f,"
              "\"read_ns\":%.2f,\"cpu_offsets_ns\":[",
              spread_ppm, slew_ppm, read_ns);
  for (size_t i = 0; i < offsets.size(); ++i) {
    std::printf("%s{\"cpu\":%d,\"low_ns\":%.1f,\"high_ns\":%.1f}", i ? "," : "",
                offsets[i].cpu, offsets[i].low_ticks * 1e9 / hz,
                offsets[i].high_ticks * 1e9 / hz);
  }
  std::printf("],\"reference_cpu\":%d,\"max_cpu_offset_ns\":%.1f,"
              "\"proven_skews\":%u,\"backwards_on_migration\":%u,"
              "\"unplaced_cpus\":%u,"
              "\"ntp\":{\"state\":\"%s\",\"synchronized\":%s,\"frequency_ppm\":%.3f,"
              "\"max_error_us\":%ld,\"estimated_error_us\":%ld}}\n",
              cpus.empty() ? 0 : cpus[0], max_offset_ns, proven_skews, backwards,
              unplaced, state_name,
              (state != TIME_ERROR && (tx.status & STA_UNSYNC) == 0) ? "true" : "false",
              double(tx.freq) / 65536.0, std::max(0L, long(tx.maxerror)),
              std::max(0L, long(tx.esterror)));
  return true;
}

}  // namespace oram_bench
