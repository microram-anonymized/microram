// A radix tuple may shed more than 64 entries into a multi-bucket stash.
// The real aggregate capacity must decide success; every key must survive.
#include <algorithm>
#include <cstdio>
#include <cstring>
#include <set>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_radix_stash.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

namespace {
namespace bs = microram::byteslice;
namespace ts = bs::test_support;

void Check(unsigned r, unsigned records, unsigned to_zero,
           unsigned depth, unsigned occupied) {
  bs::StashLayout layout;
  layout.value_bytes = 2;
  layout.tag_bytes = 1;
  const auto base = layout.Base();
  auto main = ts::ZeroedTable(r, base);
  ts::OwnedLevelStashes stash(1, depth, layout);
  std::set<uint64_t> expected;
  for (unsigned key = 1; key <= records; ++key) {
    const unsigned bucket = (key-1) % r, slot = (key-1) / r;
    ts::PlantEntry(base, main.Bucket(bucket), slot, bs::KeyWords{key}, 1);
    main.Bucket(bucket)[base.DigitLine()*64+slot] = key <= to_zero ? 0 : 1;
    main.masks[bucket] |= uint64_t{1} << slot;
    expected.insert(key);
  }
  for (unsigned i = 0; i < occupied; ++i) {
    const uint64_t key = 100000+i;
    ts::PlantEntry(base, stash.slots[0].Bucket(i/64), i%64, bs::KeyWords{key}, 1);
    stash.slots[0].masks[i/64] |= uint64_t{1} << (i%64);
    expected.insert(key);
  }
  const unsigned shed = (to_zero > 64 ? to_zero-64 : 0) +
      (records-to_zero > 64 ? records-to_zero-64 : 0);
  const bool fits = occupied+shed <= 64*depth;
  const std::vector<uint8_t> before(main.data.get(),
                                  main.data.get()+r*base.BucketBytes());
  const std::vector<uint64_t> masks(main.masks.get(), main.masks.get()+r);
  ts::OwnedLevelStashes pristine(1, depth, layout);
  std::memcpy(pristine.data.get(), stash.data.get(), stash.bytes);
  std::copy_n(stash.slots[0].masks, bs::kMaxResidualStashBuckets,
              pristine.slots[0].masks);
  std::vector<uint8_t*> ptr(r);
  std::vector<uint64_t*> mp(r);
  for (unsigned q = 0; q < r; ++q) {
    ptr[q] = main.Bucket(q);
    mp[q] = &main.masks[q];
  }
  const bool ok = bs::MergeSplitRadixStash<true>(ptr.data(), mp.data(), r,
      base.PayloadLines(), base.DigitLine(), 0, stash.slots[0]);
  ts::Expect(ok == fits, "radix rejected a fitting tuple or accepted overflow");
  if (!fits) {
    ts::Expect(stash.SameAs(pristine), "refused tuple changed the stash");
    ts::Expect(std::memcmp(main.data.get(), before.data(), before.size()) == 0,
               "refused tuple changed input bytes");
    ts::Expect(std::equal(masks.begin(), masks.end(), main.masks.get()),
               "refused tuple changed input masks");
    return;
  }
  ts::Expect(stash.Count() == occupied+shed, "incorrect aggregate shed count");
  std::set<uint64_t> found;
  const auto collect = [&](const uint8_t* bucket, uint64_t mask, int destination) {
    for (unsigned s = 0; s < 64; ++s) {
      if (!(mask & (uint64_t{1} << s))) continue;
      const auto key = bs::ReadSlotKey(bucket, s, 8);
      ts::Expect(found.insert(key.w0).second, "duplicate output key");
      ts::Expect(bucket[base.key_bytes*64+s] == 1, "damaged payload");
      if (destination >= 0)
        ts::Expect(static_cast<unsigned>(destination) == (key.w0 <= to_zero ? 0 : 1),
                   "wrong radix destination");
    }
  };
  for (unsigned q = 0; q < r; ++q) collect(main.Bucket(q), main.masks[q], q);
  for (unsigned b = 0; b < depth; ++b)
    collect(stash.slots[0].Bucket(b), stash.slots[0].masks[b], -1);
  ts::Expect(found == expected, "radix lost or invented a record");
}
}  // namespace

int main() {
  Check(3, 129, 129, 2, 0);    // 65 sheds to a 128-slot stash
  Check(5, 193, 97, 2, 63);    // 33+32 sheds; exactly fills the stash
  Check(5, 193, 97, 2, 64);    // same tuple exceeds remaining capacity by 1
  Check(5, 193, 97, 1, 0);     // genuinely insufficient one-bucket stash
  Check(5, 320, 320, 7, 192);  // dynamic depth; 256 sheds exactly fit
  Check(5, 320, 320, 7, 193);  // dynamic depth refuses one extra record
  std::puts("PASS radix tuple aggregate-capacity checks");
}
