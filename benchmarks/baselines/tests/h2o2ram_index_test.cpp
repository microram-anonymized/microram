// H2O2RAM indices (h2o2ram_index.hpp; comparison rule 4 in README.md) and
// patch P-H2, without constructing a map.
#include "benchmarks/baselines/h2o2ram_index.hpp"
#include <hash_planner.hpp>
#include <oram.hpp>
#include <cstdio>
#include <iostream>
#include <unistd.h>

namespace {
using namespace oram_bench;
using namespace oram_bench::h2o2ram;
void Check(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error(message);
}

// (8, 48): an 8-byte key with bit 63 cleared is injective on the generator's
// keys, bit-63 keys included; it would not be for IDs 2^63 apart.
void TestEightByteIndexIsInjective() {
  WorkloadSpec spec; spec.key_bytes = 8; spec.live_entries = uint64_t{1} << 20; spec.seed = 11;
  WorkloadGenerator generator(spec);
  std::vector<uint64_t> indices(spec.live_entries);
  uint64_t top_bit = 0;
  uint8_t key[8];
  for (uint64_t id = 0; id < spec.live_entries; ++id) {
    generator.Key(id, key, 8);
    top_bit += LoadLe(key, 8) >> 63;
    indices[id] = ValueIndex(key, 8, ModeFor(spec));
    Check(indices[id] >> 63 == 0, "an index has H2O2RAM's dummy bit");
  }
  Check(ModeFor(spec) == IndexMode::kValueBit63Cleared, "8-byte permuted keys clear bit 63");
  Check(top_bit > spec.live_entries / 3 && top_bit < 2 * spec.live_entries / 3,
        "the fixture lacks keys whose bit 63 is set");
  Check(CountCollisions(indices) == 0, "8-byte indices collide on the generator's keys");
  // The bound is tight: IDs 2^63 apart differ only in bit 63.
  WorkloadSpec wide = spec; wide.live_entries = ~uint64_t{0};
  WorkloadGenerator all(wide);
  uint8_t a[8], b[8];
  all.Key(5, a, 8); all.Key(5 + (uint64_t{1} << 63), b, 8);
  Check(ValueIndex(a, 8, ModeFor(wide)) == ValueIndex(b, 8, ModeFor(wide)), "IDs 2^63 apart should alias");
  // Dense and narrow keys are their value.
  WorkloadSpec dense = spec; dense.key_bytes = 4; dense.key_layout = KeyLayout::kDense; dense.live_entries = 1000;
  WorkloadGenerator d(dense);
  uint8_t k4[4];
  d.Key(999, k4, 4);
  Check(ModeFor(dense) == IndexMode::kValue && ValueIndex(k4, 4, IndexMode::kValue) == 999, "dense index");
}

std::vector<uint8_t> Hex(const std::string& text) {
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i + 1 < text.size(); i += 2) bytes.push_back(std::stoi(text.substr(i, 2), nullptr, 16));
  return bytes;
}
// RFC 4493 section 4: AES-128 CMAC known answers.
void TestCmacKnownAnswers() {
  const auto key = Hex("2b7e151628aed2a6abf7158809cf4f3c");
  Digest digest(63, key.data());
  const std::pair<std::string, std::string> cases[] = {
      {"", "bb1d6929e95937287fa37d129b756746"},
      {"6bc1bee22e409f96e93d7e117393172a", "070a16b46b4d4144f79bdd9dd04a287c"},
      {"6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411",
       "dfa66747de9ae63030ca32611497c827"}};
  for (const auto& [message, tag] : cases) {
    const auto m = Hex(message), t = Hex(tag);
    unsigned char out[16];
    digest.Tag(m.data(), m.size(), out);
    Check(std::equal(t.begin(), t.end(), out), "AES-CMAC differs from RFC 4493 for message " + message);
    Check(digest(m.data(), m.size()) == (LoadLe(t.data(), 8) & ~(uint64_t{1} << 63)), "63-bit truncation");
  }
}

// The (32, 1024) fill check counts shared digests; fewer bits plant them.
void TestDigestCollisions() {
  Check(CountCollisions({5, 1, 5, 9, 1, 5}) == 3, "collision count");
  Check(CountCollisions({1, 2, 3}) == 0, "no collisions");
  WorkloadSpec spec; spec.key_bytes = 32; spec.value_bytes = 1024; spec.live_entries = 1 << 16;
  WorkloadGenerator generator(spec);
  Check(ModeFor(spec) == IndexMode::kDigest, "32-byte keys take the digest");
  Digest full(63), planted(12);
  std::vector<uint64_t> a(spec.live_entries), b(spec.live_entries);
  uint8_t key[32];
  for (uint64_t id = 0; id < spec.live_entries; ++id) {
    generator.Key(id, key, 32);
    a[id] = full(key, 32); b[id] = planted(key, 32);
    Check(b[id] < (1u << 12) && a[id] >> 63 == 0, "digest width");
  }
  Check(CountCollisions(a) == 0, "63-bit digests collide on 2^16 keys (probability about 2^-32)");
  Check(CountCollisions(b) >= spec.live_entries - (1u << 12), "a 12-bit digest must collide");
}

// P-H2: under its flag a planner-cache miss throws, and prints nothing to the
// worker's JSON channel.
void TestFrozenPlannerMiss() {
  char path[] = "/tmp/h2o2ram-stdout-XXXXXX";
  const int file = mkstemp(path);
  std::cout.flush(); std::fflush(stdout);
  const int saved = dup(1);
  dup2(file, 1);
  bool threw = false;
  std::string message;
  try {
    delete ORAM::determine_hash<uint64_t, 16>(128, 7, 64);  // op_num 7 is never planned
  } catch (const std::runtime_error& error) {
    threw = true; message = error.what();
  }
  std::cout.flush(); std::fflush(stdout);
  dup2(saved, 1); close(saved);
  const off_t printed = lseek(file, 0, SEEK_END);
  close(file); unlink(path);
  Check(threw && message.find("planner cache miss") != std::string::npos, "a cache miss did not throw");
  Check(printed == 0, "a cache miss printed to stdout");
}
}  // namespace

int main() {
  try {
    TestEightByteIndexIsInjective();
    TestCmacKnownAnswers();
    TestDigestCollisions();
    TestFrozenPlannerMiss();
    std::cout << "h2o2ram index tests passed\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
