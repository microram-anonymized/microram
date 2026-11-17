// Minimal consumer of the installed library: construct a Map, write, update
// in place with access(), and read back with find().

#include <cpu_byteslice_oram/oram.hpp>

#include <cstdint>
#include <iostream>

int main() {
  // Map<Key, T> is deamortized by default. Pass false as the third template
  // argument to select the synchronous mode, which rebuilds on the calling
  // thread in about half the memory.
  cpu_byteslice_oram::Map<uint64_t, uint64_t> map(4096);
  map.write(7, 41);
  map.access(7, [](uint64_t& value) { ++value; });

  const auto value = map.find(7);
  if (!value) return 1;
  std::cout << *value << '\n';
  return 0;
}
