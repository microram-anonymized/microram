#pragma once

// A stash-simulator ROW: the tree shape and load that
// `cpu_tree_bucket_shape_benchmark` measures, parsed from a `key=value,...`
// spec, and the seed mixing (`MixSeed`) its runs share.

#include "benchmarks/oram/cpu_tree_stash_sim.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"

#include <cctype>
#include <cerrno>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <stdexcept>
#include <string>

namespace microram {
namespace tree {
namespace stash_sim {

// A whole number at most `max`: decimal digits, or an integral float such as
// `5e8` (as analysis/run_stash_tail_long.py accepts it).  A sign, a fraction
// or a trailing character is refused rather than read as a prefix.
inline uint64_t ParseCount(const std::string& what, const std::string& text,
                           uint64_t max) {
  const auto bad = [&](const char* why) {
    return std::invalid_argument(what + " " + why + ": `" + text + "`");
  };
  if (text.empty() || !std::isdigit(static_cast<unsigned char>(text[0])) ||
      text.find_first_not_of("0123456789.eE+") != std::string::npos) {
    throw bad("is not a whole number");
  }
  char* end = nullptr;
  errno = 0;
  uint64_t v = 0;
  if (text.find_first_not_of("0123456789") == std::string::npos) {
    const unsigned long long x = std::strtoull(text.c_str(), &end, 10);
    if (errno == ERANGE) throw bad("is out of range");
    v = x;
  } else {
    const double x = std::strtod(text.c_str(), &end);
    if (*end != '\0' || errno == ERANGE || !(x >= 0) || x != std::floor(x)) {
      throw bad("is not a whole number");
    }
    if (x >= 18446744073709551616.0) throw bad("is out of range");
    v = static_cast<uint64_t>(x);
  }
  if (v > max) throw bad("is out of range");
  return v;
}

struct Row {
  std::string spec;  // the `key=value,...` it was parsed from, for --save
  std::string label;
  unsigned leaf_bits = 0;
  unsigned fold = 1;
  unsigned log2_n = 18;
  uint64_t entries = 0;  // 0: 2^log2_n.  A row may name any N, so the load can
                         // be swept between the powers of two.
  // A, the stash registers: the lane count the tail is held to.  0 is the
  // default rule's for the depth and fold (cpu_tree_layout.hpp's
  // DefaultStashRegisters).
  unsigned stash_registers = 0;
  uint64_t ops = 0;     // 0: the global default
  unsigned seeds = 0;   // 0: the global default

  Geometry geometry() const {
    return MakeGeometry(
        leaf_bits, fold,
        stash_registers != 0 ? stash_registers
                             : DefaultStashRegisters(fold, leaf_bits));
  }
  uint64_t n() const { return entries != 0 ? entries : (uint64_t{1} << log2_n); }
};

inline Row ParseRow(const std::string& spec) {
  Row r;
  r.spec = spec;
  unsigned path_registers = 0;
  size_t pos = 0;
  // The engine's shape is fixed; a spec may still name it, and then must
  // name it as it is.
  const auto fixed = [](const std::string& key, const std::string& value,
                        const char* want) {
    if (value != want) {
      throw std::invalid_argument(key + " must be " + want +
                                  " (the read-path engine's shape)");
    }
  };
  while (pos < spec.size()) {
    size_t comma = spec.find(',', pos);
    if (comma == std::string::npos) comma = spec.size();
    const std::string kv = spec.substr(pos, comma - pos);
    pos = comma + 1;
    const size_t eq = kv.find('=');
    if (eq == std::string::npos) throw std::invalid_argument("bad row field: " + kv);
    const std::string key = kv.substr(0, eq), value = kv.substr(eq + 1);
    if (key == "z") fixed(key, value, "4");
    else if (key == "b") fixed(key, value, "2");
    else if (key == "sched") fixed(key, value, "readpath");
    else if (key == "plan") fixed(key, value, "inplace");
    else if (key == "lam") r.leaf_bits = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "fold") r.fold = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "logn") r.log2_n = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "n") r.entries = ParseCount(key, value, UINT64_MAX);
    else if (key == "a") r.stash_registers = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "preg") path_registers = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "ops") r.ops = ParseCount(key, value, UINT64_MAX);
    else if (key == "seeds") r.seeds = static_cast<unsigned>(ParseCount(key, value, UINT_MAX));
    else if (key == "label") r.label = value;
    else throw std::invalid_argument("unknown row field: " + key);
  }
  if (r.leaf_bits == 0) throw std::invalid_argument("a row needs lam=");
  // Block ids are `int32_t`, so a row holds at most 2^31 entries.
  if ((r.entries == 0 && r.log2_n > 31) || r.n() > kMaxEntries) {
    throw std::invalid_argument(
        "a row holds at most 2^31 entries (logn <= 31): block ids are int32_t");
  }
  if (r.stash_registers != 0 &&
      (r.stash_registers < kMinStashRegisters || r.stash_registers > kMaxStashRegisters)) {
    throw std::invalid_argument("a must be 3 or 4");
  }
  // `preg` is implied by the path; a spec that names it is checked.
  if (path_registers != 0 && path_registers != r.geometry().path_registers()) {
    throw std::invalid_argument("preg does not match the path's registers");
  }
  if (r.label.empty()) {
    r.label = "lam" + std::to_string(r.leaf_bits) + "-f" + std::to_string(r.fold);
  }
  return r;
}

// The SplitMix64 finalizer, so `--seed-mix` seeds land at unrelated points of
// the simulator's one 2^64 cycle rather than one draw apart.
inline uint64_t MixSeed(uint64_t seed) {
  uint64_t z = seed + 0x9E3779B97F4A7C15ull;
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

}  // namespace stash_sim
}  // namespace tree
}  // namespace microram
