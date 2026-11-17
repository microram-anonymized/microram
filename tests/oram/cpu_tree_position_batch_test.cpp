// The tree ORAM's hierarchical position map (cpu_tree_position_map.hpp):
// its batched access must give, request for request, the same (position, uid)
// answers as the scalar path and as an unordered-map model, including
// repeated keys inside one batch, misses, erases and non-inserting
// exchanges, at uid widths from 1 to 64 bits, in both storage modes.  A
// wrong position here sends the tree ORAM to the wrong path, so the value
// would be unfindable.  An invalid batch must be refused before it changes
// the access count.
#include "src/oram/tree/cpu_tree_position_map.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"
#include <cstdio>
#include <random>
#include <vector>

using namespace microram::tree;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrows;

template <bool D>
void Exercise(bool key_uid, unsigned bits) {
  cpu_byteslice_oram::Options options;
  options.deamortized_owner_threads = 0;
  HierarchicalPositionMap<D> scalar(512, 8, options, key_uid, bits);
  HierarchicalPositionMap<D> batch(512, 8, options, key_uid, bits);
  UnorderedPositionMap model(512, 8);
  std::mt19937_64 rng(42);
  uint64_t count = 0;
  for (size_t n : {1u, 2u, 15u, 16u, 17u, 65u, 257u}) {
    std::vector<uint64_t> keys(n);
    std::vector<PositionBatchRequest> req(n);
    std::vector<PositionEntry> out(n), expected(n);
    std::vector<uint8_t> found(n), expected_found(n);
    for (unsigned round = 0; round < 12; ++round) {
      for (size_t i = 0; i < n; ++i) {
        // Short repeated-key chains span the cascade's lane boundaries,
        // including key zero, misses, non-inserting exchanges and reinserts.
        keys[i] = round < 6 ? 0 : rng() % 128;
        const unsigned op = (round + i) % 5;
        req[i] = {reinterpret_cast<uint8_t*>(&keys[i]),
                  {rng() & (bits == 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1),
                   key_uid ? 0 : rng()}, op == 0 || op == 4, op == 3};
        const auto& r = req[i];
        expected_found[i] = r.erase ? scalar.Erase(r.key, &expected[i])
            : scalar.Exchange(r.key, r.next, &expected[i], r.insert);
        PositionEntry reference;
        const bool present = r.erase ? model.Erase(r.key, &reference)
            : model.Exchange(r.key, r.next, &reference, r.insert);
        Expect(present == expected_found[i] && reference.position == expected[i].position &&
               reference.uid == expected[i].uid, "scalar disagrees with model");
      }
      batch.AccessBatch(n, req.data(), out.data(), found.data());
      for (size_t i = 0; i < n; ++i)
        Expect(found[i] == expected_found[i] && out[i].position == expected[i].position &&
               out[i].uid == expected[i].uid, "position batch differs from scalar/model");
      count += n;
      Expect(batch.AccessCount() == count && scalar.AccessCount() == count,
             "position access count differs");
    }
  }
  batch.AccessBatch(0, nullptr, nullptr, nullptr);
  PositionBatchRequest invalid[2]{};
  uint64_t key = 999;
  invalid[0] = {reinterpret_cast<uint8_t*>(&key), {1, 2}, true, false};
  PositionEntry out[2]; uint8_t found[2];
  ExpectThrows([&] { batch.AccessBatch(2, invalid, out, found); }, "null key accepted");
  Expect(batch.AccessCount() == count, "invalid adapter batch mutated prefix");
  batch.DrainRebuilds(); scalar.DrainRebuilds();
}
int main() {
  for (bool key_uid : {false, true})
    for (unsigned bits : {1u, 17u, 36u, 64u}) {
      Exercise<false>(key_uid, bits);
      Exercise<true>(key_uid, bits);
    }
  std::puts("cpu_tree_position_batch_test passed");
}
