#pragma once

// Common assertions and deterministic fixtures for the standalone test
// executables. Tests that intentionally accumulate multiple failures keep
// their local reporter instead.

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <utility>
#include <vector>

namespace microram {
namespace byteslice {
namespace test_support {

inline void Expect(bool condition, const char* message) {
  if (!condition) {
    std::fprintf(stderr, "test failed: %s\n", message);
    std::exit(1);
  }
}

inline std::vector<uint8_t> Value(uint64_t key, size_t bytes = 16,
                                  uint8_t version = 0) {
  std::vector<uint8_t> out(bytes);
  uint64_t state = key ^ (uint64_t{version} << 56);
  for (size_t i = 0; i < out.size(); ++i) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    out[i] = static_cast<uint8_t>(state >> 32);
  }
  return out;
}

// A user key derived from an index. The low bytes retain the index while the
// remaining bytes exercise wide-key hashing with deterministic data.
inline std::vector<uint8_t> WideKey(uint64_t index, size_t key_bytes) {
  std::vector<uint8_t> key(key_bytes);
  uint64_t state = index * 0x9E3779B97F4A7C15ull + 0xABCD;
  for (size_t i = 0; i < key_bytes; ++i) {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    key[i] = static_cast<uint8_t>(state >> 33);
  }
  for (size_t i = 0; i < 8 && i < key_bytes; ++i) {
    key[i] = static_cast<uint8_t>(index >> (8 * i));
  }
  return key;
}

template <typename Fn>
inline void ExpectThrows(Fn&& fn, const char* message) {
  bool threw = false;
  try {
    std::forward<Fn>(fn)();
  } catch (const std::exception&) {
    threw = true;
  }
  Expect(threw, message);
}

// The same, but on the exception TYPE.  Worth the extra word wherever the
// call could also fail for an unrelated reason -- a rejected configuration
// whose arena would be enormous passes `ExpectThrows` on a failed allocation
// without ever reaching the check under test.
template <class E, class Fn>
inline void ExpectThrowsAs(Fn&& fn, const char* message) {
  bool threw_expected = false;
  bool threw_other = false;
  try {
    std::forward<Fn>(fn)();
  } catch (const E&) {
    threw_expected = true;
  } catch (const std::exception&) {
    threw_other = true;
  }
  Expect(!threw_other, message);
  Expect(threw_expected, message);
}

}  // namespace test_support
}  // namespace byteslice
}  // namespace microram
