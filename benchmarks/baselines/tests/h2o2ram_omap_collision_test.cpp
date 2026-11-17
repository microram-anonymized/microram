// H2O2RAM's map aliases keys (README.md, "H2O2RAM's map truncates keys to 63
// bits"), checked against the pinned H2O2RAM: its ObliviousMap indexes the
// ORAM by std::hash with bit 63 cleared and stores no key, so two keys whose
// hashes agree in 63 bits share one record. libstdc++'s std::hash is unkeyed,
// so such a pair can be found offline by a generic collision search (about
// 2^32 hash calls); the pair below is one. This test passes when the aliasing
// reproduces.
#include <hash_planner.hpp>
#include <omap.hpp>
#include <cstring>
#include <iostream>
#include <string>

namespace {
std::string Bytes(uint64_t value) {  // 8 little-endian bytes, as the search took them
  std::string key(8, '\0');
  std::memcpy(key.data(), &value, 8);
  return key;
}
void Check(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(message);
}
}  // namespace

int main() {
  try {
    const std::string first = Bytes(0x584e722ec163d652), second = Bytes(0x6cdc205c23ab1dc5);
    const size_t a = std::hash<std::string>{}(first), b = std::hash<std::string>{}(second);
    Check(a == 0x1ef0dfb841b0ea0cull && b == 0x9ef0dfb841b0ea0cull, "std::hash values differ from the documented pair");
    Check((a ^ b) == (size_t{1} << 63), "the pair should differ only in bit 63");
    ORAM::ObliviousMap<std::string, uint64_t> map;
    map.insert(first, 111);            // only the first key is inserted
    Check(map[second] == 111, "reading the second key should return the first key's value");
    map[second] = 222;                 // writing the second key overwrites the first
    Check(map[first] == 222, "writing the second key should overwrite the first");
    std::cout << "ObliviousMap aliases the chosen pair (aliasing reproduced)\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
