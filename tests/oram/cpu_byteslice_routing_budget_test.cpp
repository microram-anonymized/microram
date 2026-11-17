// Routing work has one shared, nonrefundable allowance. Count every padded
// message and repeated evaluation, including work concurrent with a refusal.
// `max_routing_evaluations` bounds how many routing-tag (AES) evaluations one
// instance key may perform (src/oram/levelarena/DESIGN.md, "Routing
// budget"); the bound only means something if no evaluation escapes the
// count, so this checks the counter itself (RoutingEvaluationBudget) and the
// tag routines' reservations.

#include "src/oram/table/cpu_byteslice_routing_budget.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <thread>
#include <vector>

namespace {
namespace bs = microram::byteslice;
namespace crypto = microram::crypto;

int failures = 0;
constexpr uint64_t kCanary = 0x7dd2b584a1936cefull;

void Expect(bool condition, const char* message) {
  if (!condition) {
    std::fprintf(stderr, "test failed: %s\n", message);
    ++failures;
  }
}

template <class Fn>
bool Refuses(Fn&& fn) {
  try {
    fn();
  } catch (const std::overflow_error&) {
    return true;
  }
  return false;
}

void TestReservationBoundaries() {
  bs::RoutingEvaluationBudget zero(0);
  Expect(zero.limit() == 0 && zero.count() == 0 && !zero.exhausted(),
         "a zero allowance starts without a failure");
  zero.Reserve(0);
  zero.RequireAvailable();
  Expect(Refuses([&] { zero.Reserve(1); }) && zero.count() == 0 &&
             zero.exhausted(),
         "a zero allowance refuses and latches without spending");
  Expect(Refuses([&] { zero.RequireAvailable(); }),
         "a refused budget reports its terminal state");

  bs::RoutingEvaluationBudget short_budget(7);
  short_budget.Reserve(3);
  Expect(Refuses([&] { short_budget.Reserve(5); }) &&
             short_budget.count() == 3,
         "a refused reservation preserves the spent count");
  Expect(Refuses([&] { short_budget.Reserve(1); }) &&
             short_budget.count() == 3,
         "the terminal latch rejects smaller work after a refusal");

  const uint64_t maximum = std::numeric_limits<uint64_t>::max();
  bs::RoutingEvaluationBudget large(maximum);
  large.Reserve(maximum - 1);
  large.Reserve(1);
  Expect(large.count() == maximum && !large.exhausted(),
         "the exact uint64 limit is representable and does not wrap");
  Expect(Refuses([&] { large.Reserve(1); }) && large.count() == maximum &&
             large.exhausted(),
         "reservation past uint64 maximum refuses without wrapping");

  bs::RoutingEvaluationBudget oversized(4);
  Expect(Refuses([&] { oversized.Reserve(maximum); }) &&
             oversized.count() == 0,
         "a maximal request cannot wrap into a small allowance");
}

void TestConcurrentReservations() {
  constexpr uint64_t allowance = 10003;
  bs::RoutingEvaluationBudget budget(allowance);
  std::atomic<bool> start{false};
  std::atomic<uint64_t> accepted{0};
  std::atomic<unsigned> refused{0};
  std::vector<std::thread> threads;
  for (unsigned worker = 0; worker < 8; ++worker) {
    threads.emplace_back([&] {
      while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
      for (;;) {
        try {
          budget.Reserve(1);
          accepted.fetch_add(1, std::memory_order_relaxed);
        } catch (const std::overflow_error&) {
          refused.fetch_add(1, std::memory_order_relaxed);
          break;
        }
      }
    });
  }
  start.store(true, std::memory_order_release);
  for (auto& thread : threads) thread.join();
  Expect(accepted.load() == allowance && budget.count() == allowance &&
             refused.load() == threads.size() && budget.exhausted(),
         "concurrent reservations neither lose charges nor exceed the limit");
}

// The default (UINT64_MAX) budget counts small reservations per thread; the
// total must stay exact, and a reservation above the sharded maximum must
// switch the budget to the exact counter without losing a concurrent charge.
void TestUnlimitedSharding() {
  constexpr unsigned kThreads = 8;
  constexpr uint64_t kPerThread = 20000;
  bs::RoutingEvaluationBudget budget(std::numeric_limits<uint64_t>::max());
  {
    std::vector<std::thread> threads;
    for (unsigned worker = 0; worker < kThreads; ++worker)
      threads.emplace_back([&] {
        for (uint64_t i = 0; i < kPerThread; ++i) budget.Reserve(32);
      });
    for (auto& thread : threads) thread.join();
  }
  Expect(budget.count() == kThreads * kPerThread * 32 && !budget.exhausted(),
         "unlimited reservations from many threads keep an exact count");

  // Race small reservations against one that leaves 1000 evaluations: the
  // admitted total may not exceed the limit, and the count must equal it.
  const uint64_t maximum = std::numeric_limits<uint64_t>::max();
  for (int trial = 0; trial < 20; ++trial) {
    bs::RoutingEvaluationBudget racing(maximum);
    std::atomic<bool> start{false};
    std::atomic<uint64_t> accepted{0};
    std::vector<std::thread> threads;
    for (unsigned worker = 0; worker < kThreads; ++worker)
      threads.emplace_back([&] {
        while (!start.load(std::memory_order_acquire)) std::this_thread::yield();
        for (;;) {
          try {
            racing.Reserve(1);
          } catch (const std::overflow_error&) {
            break;
          }
          accepted.fetch_add(1, std::memory_order_relaxed);
        }
      });
    start.store(true, std::memory_order_release);
    uint64_t large = 0;
    while (large == 0) {
      const uint64_t seen = racing.count();
      try {
        racing.Reserve(maximum - 1000 - seen);
        large = maximum - 1000 - seen;
      } catch (const std::overflow_error&) {
        break;  // only if the threads' reservations raced past `seen`
      }
    }
    for (auto& thread : threads) thread.join();
    Expect(large != 0, "the exact reservation was admitted");
    Expect(racing.exhausted() && racing.count() == large + accepted.load() &&
               racing.count() <= maximum && maximum - racing.count() < kThreads,
           "switching to the exact counter loses no charge and never exceeds the limit");
  }
}

crypto::AesRoundKeys Keys() {
  return crypto::DeriveRoutingAesRoundKeys(
      crypto::SecretKeySeed::Fixed(0xaed736902b41));
}

void FillMessages(uint64_t* messages, size_t count) {
  for (size_t i = 0; i < count; ++i) {
    messages[4 * i] = crypto::PackAesCtrHighWord(
        (i * 7) | ((i & 1) ? crypto::kAesCtrDomainBit : 0), 31 * i + 1);
    messages[4 * i + 1] = crypto::kAesRoutingLabel;
    messages[4 * i + 2] = 0x0706050403020100ull ^ (i * 0x9e3779b97f4a7c15ull);
    messages[4 * i + 3] = (i & 2) ? i * 0xd1b54a32d192ed03ull : 0;
  }
}

void TestInterleavedPadding() {
  const auto raw = Keys();
  const auto unrestricted = bs::MakeAesTagKeys(raw);
  alignas(64) uint64_t messages[4 * 36];
  FillMessages(messages, 36);
  uint64_t expected[36];
  bs::AesTagsInterleaved(messages, 36, expected, *unrestricted);
  for (size_t count = 0; count <= 35; ++count) {
    const uint64_t padded = (count + 3) & ~uint64_t{3};
    bs::RoutingEvaluationBudget budget(padded);
    const auto limited = bs::MakeAesTagKeys(raw, &budget);
    std::array<uint64_t, 40> output;
    output.fill(kCanary);
    bs::AesTagsInterleaved(messages, count, output.data(), *limited);
    Expect(budget.count() == padded && !budget.exhausted(),
           "interleaved routing charges the complete padded SIMD group");
    for (size_t i = 0; i < padded; ++i) {
      Expect(output[i] == expected[i],
             "budgeting preserves every real and padded routing output");
    }
    for (size_t i = padded; i < output.size(); ++i) {
      Expect(output[i] == kCanary,
             "interleaved routing preserves output beyond its padded tail");
    }
    if (padded != 0) {
      bs::RoutingEvaluationBudget too_small(padded - 1);
      const auto refusing = bs::MakeAesTagKeys(raw, &too_small);
      output.fill(kCanary);
      Expect(Refuses([&] {
        bs::AesTagsInterleaved(messages, count, output.data(), *refusing);
      }) && too_small.count() == 0 && too_small.exhausted(),
             "interleaved admission includes padding before any evaluation");
      Expect(std::all_of(output.begin(), output.end(),
                         [](uint64_t x) { return x == kCanary; }),
             "a refused interleaved leaf leaves all output untouched");
    }
  }

  bs::RoutingEvaluationBudget repeated(8);
  const auto limited = bs::MakeAesTagKeys(raw, &repeated);
  std::array<uint64_t, 4> output;
  bs::AesTagsInterleaved(messages, 1, output.data(), *limited);
  bs::AesTagsInterleaved(messages, 1, output.data(), *limited);
  Expect(repeated.count() == 8,
         "repeated routing inputs spend their padded evaluations again");
  output.fill(kCanary);
  Expect(Refuses([&] {
    bs::AesTagsInterleaved(nullptr, 1, output.data(), *limited);
  }) && std::all_of(output.begin(), output.end(),
                    [](uint64_t x) { return x == kCanary; }),
         "interleaved refusal occurs before reading message storage");

  // Neither padded-count arithmetic nor a default standalone schedule may
  // turn an unrepresentable request into a small successful loop.
  for (size_t extra = 0; extra < 3; ++extra) {
    const size_t count = std::numeric_limits<size_t>::max() - extra;
    bs::RoutingEvaluationBudget overflow(std::numeric_limits<uint64_t>::max());
    const auto overflow_keys = bs::MakeAesTagKeys(raw, &overflow);
    Expect(Refuses([&] {
      bs::AesTagsInterleaved(nullptr, count, nullptr, *overflow_keys);
    }) && overflow.count() == 0 && overflow.exhausted(),
           "padded-count overflow latches before touching input or output");
    Expect(Refuses([&] {
      bs::AesTagsInterleaved(nullptr, count, nullptr, *unrestricted);
    }), "standalone routing also rejects padded-count overflow");
  }
}

void TestBucketLeaves() {
  const auto raw = Keys();
  const auto unrestricted = bs::MakeAesTagKeys(raw);
  alignas(64) uint64_t low[64], high[64];
  alignas(64) __m512i low_regs[8], high_regs[8], expected[8], output[8];
  for (size_t i = 0; i < 64; ++i) {
    low[i] = i * 0x9e3779b97f4a7c15ull;
    high[i] = (i + 19) * 0xd1b54a32d192ed03ull;
  }
  for (size_t i = 0; i < 8; ++i) {
    low_regs[i] = _mm512_load_si512(low + 8 * i);
    high_regs[i] = _mm512_load_si512(high + 8 * i);
  }
  const uint64_t packed = crypto::PackAesCtrHighWord(17, 0x123456789);
  for (bool wide : {false, true}) {
    bs::AesBatch64Regs(low_regs, wide ? high_regs : nullptr, packed, expected,
                       *unrestricted);
    bs::RoutingEvaluationBudget budget(64);
    const auto limited = bs::MakeAesTagKeys(raw, &budget);
    bs::AesBatch64Regs(low_regs, wide ? high_regs : nullptr, packed, output,
                       *limited);
    Expect(budget.count() == 64 && !budget.exhausted(),
           "one full bucket charges two 32-message leaves exactly once");
    Expect(std::memcmp(output, expected, sizeof(output)) == 0,
           "a bucket's routing tags are unchanged by its allowance");

    bs::RoutingEvaluationBudget leaf(32);
    const auto leaf_keys = bs::MakeAesTagKeys(raw, &leaf);
    bs::AesBatch32Regs(low_regs, wide ? high_regs : nullptr, packed, output,
                       *leaf_keys);
    Expect(leaf.count() == 32 &&
               std::memcmp(output, expected, 4 * sizeof(__m512i)) == 0,
           "the half-bucket leaf charges and preserves its 32 outputs");

    bs::RoutingEvaluationBudget refused(31);
    const auto refused_keys = bs::MakeAesTagKeys(raw, &refused);
    std::memset(output, 0xa5, sizeof(output));
    std::array<uint8_t, sizeof(output)> saved;
    std::memcpy(saved.data(), output, sizeof(output));
    Expect(Refuses([&] {
      bs::AesBatch32Regs(nullptr, nullptr, packed, output, *refused_keys);
    }) && refused.count() == 0 && refused.exhausted(),
           "a refused bucket leaf reads no keys and spends no evaluations");
    Expect(std::memcmp(output, saved.data(), sizeof(output)) == 0,
           "a refused bucket leaf leaves its output untouched");
  }
}

void TestKeyIsolation() {
  const auto raw = Keys();
  bs::RoutingEvaluationBudget first(4), second(4);
  const auto a = bs::MakeAesTagKeys(raw, &first);
  const auto b = bs::MakeAesTagKeys(raw, &second);
  const auto unrestricted = bs::MakeAesTagKeys(raw);
  alignas(64) uint64_t messages[16];
  FillMessages(messages, 4);
  uint64_t output[4], expected[4];
  bs::AesTagsInterleaved(messages, 4, expected, *unrestricted);
  bs::AesTagsInterleaved(messages, 4, output, *a);
  Expect(first.count() == 4 && second.count() == 0,
         "independent schedules charge only their own allowance");
  Expect(Refuses([&] {
    bs::AesTagsInterleaved(messages, 4, output, *a);
  }), "the first schedule can exhaust independently");
  bs::AesTagsInterleaved(messages, 4, output, *b);
  bs::AesTagsInterleaved(messages, 4, output, *unrestricted);
  Expect(second.count() == 4 && !second.exhausted() &&
             std::memcmp(output, expected, sizeof(output)) == 0,
         "one schedule's refusal does not affect another or a standalone key");

  bs::RoutingEvaluationBudget shared(8);
  const auto left = bs::MakeAesTagKeys(raw, &shared);
  const auto right = bs::MakeAesTagKeys(raw, &shared);
  bs::AesTagsInterleaved(messages, 4, output, *left);
  bs::AesTagsInterleaved(messages, 4, output, *right);
  Expect(shared.count() == 8,
         "multiple schedules may deliberately share one allowance");
}
}  // namespace

int main() {
  TestReservationBoundaries();
  TestConcurrentReservations();
  TestUnlimitedSharding();
  TestInterleavedPadding();
  TestBucketLeaves();
  TestKeyIsolation();
  if (failures != 0) return 1;
  std::printf("routing evaluation budget tests passed (%s)\n",
              MICRORAM_BYTESLICE_USE_VAES ? "VAES" : "AES-NI");
  return 0;
}
