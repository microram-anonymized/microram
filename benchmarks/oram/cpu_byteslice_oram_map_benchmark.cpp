// End-to-end benchmark of the public byte and typed map adapters.
//
// Usage:
//   cpu_byteslice_oram_map_benchmark [entries] [operations]
//
// The fill inserts `entries` distinct keys, by DIRECT INITIALIZATION
// (the largest level built straight from the input, see
// src/oram/rebuild/cpu_byteslice_initialization.hpp) on the adapters that
// offer one and by
// one insert per key on the rest -- the typed `Map` is the hybrid, which may
// select the tree engine and therefore has no largest level to build, so its
// rows keep the insert loop.  Which one a row used is a column, because the
// two are not the same measurement: one is a bulk construction, the other is
// `entries` online writes.  The measured phase is the same either way: a
// deterministic hit-only workload with one update for every seven reads.

#include <cpu_byteslice_oram/oram.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"

#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <type_traits>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;
using Clock = std::chrono::steady_clock;

uint64_t Mix(uint64_t value) {
  value += 0x9E3779B97F4A7C15ull;
  value = (value ^ (value >> 30)) * 0xBF58476D1CE4E5B9ull;
  value = (value ^ (value >> 27)) * 0x94D049BB133111EBull;
  return value ^ (value >> 31);
}

// A single-pass generator of the typed fill's {key, value} records: exactly
// the pairs the insert loop below writes, one at a time.
class TypedRecords {
 public:
  explicit TypedRecords(uint64_t key) : key_(key) {}
  std::pair<uint64_t, uint64_t> operator*() const { return {key_, Mix(key_)}; }
  TypedRecords& operator++() {
    ++key_;
    return *this;
  }

 private:
  uint64_t key_;
};

template <typename Map>
void RunTyped(const char* name, size_t entries, size_t operations,
              typename Map::options_type options) {
  Map map(entries, options);
  const auto fill_begin = Clock::now();
  if constexpr (Map::supports_initialize) {
    map.initialize(TypedRecords(1), entries);
  } else {
    for (size_t i = 0; i < entries; ++i) {
      map.insert_or_assign(static_cast<uint64_t>(i + 1), Mix(i + 1));
    }
  }
  map.drain_rebuilds();
  const double fill_seconds =
      std::chrono::duration<double>(Clock::now() - fill_begin).count();

  uint64_t checksum = 0;
  const auto begin = Clock::now();
  for (size_t i = 0; i < operations; ++i) {
    const uint64_t key = (Mix(i) % entries) + 1;
    if (i % 8 == 0) {
      uint64_t old_value = 0;
      (void)map.exchange(key, Mix(key + i), &old_value, true);
    } else {
      uint64_t value = 0;
      if (!map.find(key, &value)) {
        std::fprintf(stderr, "%s: lookup missed\n", name);
        std::exit(1);
      }
      checksum ^= value;
    }
  }
  const double seconds =
      std::chrono::duration<double>(Clock::now() - begin).count();
  std::printf("%-25s %9zu %7s %9.1f %9.1f %10.3f %16llu\n", name,
              map.capacity(), Map::supports_initialize ? "direct" : "online",
              fill_seconds * 1e9 / entries, seconds * 1e9 / operations,
              operations / (seconds * 1e6),
              static_cast<unsigned long long>(checksum));
}

template <typename ByteMap>
void RunBytes(const char* name, size_t entries, size_t operations,
              typename ByteMap::options_type options) {
  ByteMap map(entries, sizeof(uint64_t), sizeof(uint64_t), options);
  std::array<uint8_t, 16> key_bytes{};
  const auto fill_begin = Clock::now();
  if constexpr (ByteMap::supports_initialize) {
    map.initialize(
        microram::byteslice::benchmark_support::MakeGeneratedRecords(
            1, sizeof(uint64_t), sizeof(uint64_t),
            [](uint64_t key, uint8_t* out) {
              std::memcpy(out, &key, sizeof(key));
            },
            [](uint64_t key, uint8_t* out, size_t) {
              const uint64_t value = Mix(key);
              std::memcpy(out, &value, sizeof(value));
            }),
        entries);
  } else {
    for (size_t i = 0; i < entries; ++i) {
      const uint64_t key = i + 1;
      const uint64_t value = Mix(key);
      std::memcpy(key_bytes.data(), &key, sizeof(key));
      map.insert_or_assign(key_bytes.data(),
                           reinterpret_cast<const uint8_t*>(&value));
    }
  }
  map.drain_rebuilds();
  const double fill_seconds =
      std::chrono::duration<double>(Clock::now() - fill_begin).count();

  uint64_t checksum = 0;
  const auto begin = Clock::now();
  for (size_t i = 0; i < operations; ++i) {
    const uint64_t key = (Mix(i) % entries) + 1;
    std::memcpy(key_bytes.data(), &key, sizeof(key));
    if (i % 8 == 0) {
      const uint64_t value = Mix(key + i);
      uint64_t old_value = 0;
      (void)map.exchange(key_bytes.data(),
                         reinterpret_cast<const uint8_t*>(&value),
                         reinterpret_cast<uint8_t*>(&old_value), true);
    } else {
      uint64_t value = 0;
      if (!map.find(key_bytes.data(), reinterpret_cast<uint8_t*>(&value))) {
        std::fprintf(stderr, "%s: lookup missed\n", name);
        std::exit(1);
      }
      checksum ^= value;
    }
  }
  const double seconds =
      std::chrono::duration<double>(Clock::now() - begin).count();
  std::printf("%-25s %9zu %7s %9.1f %9.1f %10.3f %16llu\n", name,
              map.capacity(),
              ByteMap::supports_initialize ? "direct" : "online",
              fill_seconds * 1e9 / entries, seconds * 1e9 / operations,
              operations / (seconds * 1e6),
              static_cast<unsigned long long>(checksum));
}

}  // namespace

int main(int argc, char** argv) {
  const size_t entries =
      argc > 1 ? static_cast<size_t>(std::strtoull(argv[1], nullptr, 10))
               : 4096;
  const size_t operations =
      argc > 2 ? static_cast<size_t>(std::strtoull(argv[2], nullptr, 10))
               : 65536;
  if (entries == 0 || operations == 0) {
    std::fprintf(stderr, "entries and operations must be nonzero\n");
    return 2;
  }

  oram::Options options;

  std::printf("%-25s %9s %7s %9s %9s %10s %16s\n", "adapter", "capacity",
              "fill", "fill ns", "op ns", "Mops/s", "checksum");
  RunBytes<oram::ByteMap<false>>("synchronous bytes", entries, operations,
                                  options);
  RunTyped<oram::Map<uint64_t, uint64_t, false>>(
      "synchronous typed", entries, operations, options);
  RunBytes<oram::ByteMap<>>("deamortized bytes", entries, operations,
                            options);
  RunTyped<oram::Map<uint64_t, uint64_t>>(
      "deamortized typed", entries, operations, options);
  return 0;
}
