// Patches P-H4, P-H5 and P-H6 (README.md in the parent directory).
//
// P-H4: the shipped constructor merges EVERY linear-scan level into the buffer.
// When the host-timed planner keeps a table below a linear one (a plan that
// times candidates on the host need not be monotone, e.g. bucket at 512,
// linear at 1024), a kept table is smaller than the buffer, and the first
// rebuild into it drops blocks (many reads come back wrong without
// P-H4). A crafted cache for 32-byte blocks, a width no
// campaign uses, reproduces that plan; every read is checked against a reference.
//
// P-H5 (patched build only): a dummy lookup, index -1, in a bucket or cuckoo
// table probes a fresh dummy, as OTwoTierHash does, not the fixed place of -1.
//
// P-H6: OTwoTierHash::extract, which every rebuild of a two-tier level calls,
// dropped blocks: its bin labels bound to oblivious_select's bool overload
// (every overflow block in bin 0 or 1), and its per-bin count restarted within
// a bin rather than at a new one. Without P-H6, extracting a table after
// looking up half its keys can lose blocks, and at the larger size tested it
// loses blocks in every trial.
#include <hash_planner.hpp>
#include <oram.hpp>
#include <cstring>
#include <fstream>
#include <iostream>
#include <random>
#include <set>

namespace {
// White-box access to P-H5's counters: an explicit instantiation may name a
// private member, and the friend it defines hands the pointer out.
template <typename Tag, typename Tag::type Member> struct Expose {
  friend typename Tag::type Get(Tag) { return Member; }
};
#ifdef H2O2RAM_CONSTANT_TIME_CMOV
struct BucketCounter { using type = uint64_t ORAM::OHashBucket<uint64_t, 16>::*; friend type Get(BucketCounter); };
struct BucketPrf { using type = AESPRF<uint32_t> ORAM::OHashBucket<uint64_t, 16>::*; friend type Get(BucketPrf); };
struct CuckooCounter { using type = uint64_t ORAM::OCuckooHash<uint64_t, 16>::*; friend type Get(CuckooCounter); };
template struct Expose<BucketCounter, &ORAM::OHashBucket<uint64_t, 16>::dummy_access_ctr>;
template struct Expose<BucketPrf, &ORAM::OHashBucket<uint64_t, 16>::prf>;
template struct Expose<CuckooCounter, &ORAM::OCuckooHash<uint64_t, 16>::dummy_access_ctr>;
#endif
void Check(bool condition, const std::string& message) {
  if (!condition) throw std::runtime_error(message);
}
struct Value { uint8_t bytes[24]; };  // Block<uint64_t, 32>: hash_map.bin32

void TestLayoutSurvivesANonMonotonePlan() {
  // The bucket parameters are ones a host's planner chose at 16 bytes;
  // the linear scan at 1024 is the choice the shipped constructor mishandles.
  {
    std::ofstream cache(ORAM::getExecutablePath() + CONFIG_FILE "32", std::ios::trunc);
    cache << "128 128 64 linear\n256 256 64 linear\n512 512 64 bucket 21 82\n1024 1024 64 linear\n"
             "2048 2048 64 bucket 31 155\n4096 4096 64 bucket 66 151\n8192 8192 64 bucket 82 209\n"
             "16384 16384 64 bucket 130 248\n32768 32768 64 bucket 191 313\n65536 65536 64 bucket 415 295\n"
             // The two-tier tables' bins (TestTwoTierExtractKeepsEveryBlock).
             "4096 8192 64 bucket 117 106\n8192 16384 64 bucket 211 113\n";
  }
  const uint64_t n = 65536;
  std::vector<Value> initial(n);
  std::vector<uint64_t> reference(n);
  for (uint64_t i = 0; i < n; ++i) {
    reference[i] = i * 0x9e3779b97f4a7c15ull + 1;
    std::memcpy(initial[i].bytes, &reference[i], 8);
  }
  ORAM::ObliviousRAM<uint64_t, Value> oram(initial.begin(), initial.end());
  std::mt19937_64 rng(7);
  uint64_t wrong = 0;
  for (uint64_t access = 0; access < 200000; ++access) {
    const uint64_t index = rng() % n;
    auto& value = oram[index];
    uint64_t stored;
    std::memcpy(&stored, value.bytes, 8);
    wrong += stored != reference[index];
    if (access % 20 == 0) {
      reference[index] = rng();
      std::memcpy(value.bytes, &reference[index], 8);
    }
  }
  Check(wrong == 0, std::to_string(wrong) + " of 200000 reads wrong: the rebuild layout lost blocks");
}

void TestTwoTierExtractKeepsEveryBlock() {
  using Block = ORAM::Block<uint64_t, 32>;
  for (const uint64_t n : {uint64_t{8192}, uint64_t{16384}}) {
    for (int trial = 0; trial < 4; ++trial) {
      std::vector<Block> data(n);
      for (uint64_t i = 0; i < n; ++i) data[i] = Block(i);
      ORAM::OTwoTierHash<uint64_t, 32> table(n, DELTA_INV_LOG2, 2);  // bins of 2048, overflow n / 2
      table.build(data.data());
      for (uint64_t i = 0; i < n; i += 2) Check(!table[i].dummy(), "a two-tier lookup missed its block");
      std::set<uint64_t> left;
      for (const auto& block : table.extract())
        if (!block.dummy()) Check(left.insert(block.id).second, "extract duplicated a block");
      uint64_t lost = 0;
      for (uint64_t i = 1; i < n; i += 2) lost += !left.count(i);
      Check(lost == 0 && left.size() == n / 2, "two-tier extract of " + std::to_string(n) + " lost " +
                                                   std::to_string(lost) + " blocks");
    }
  }
}

void TestDummyLookupsAreFresh() {
#ifdef H2O2RAM_CONSTANT_TIME_CMOV
  using Block = ORAM::Block<uint64_t, 16>;
  std::vector<Block> data(1024);
  for (uint64_t i = 0; i < data.size(); ++i) data[i] = Block(i);
  ORAM::OHashBucket<uint64_t, 16> bucket(512, 21, 82);
  bucket.build(data.data());
  ORAM::OCuckooHash<uint64_t, 16> cuckoo(1024);
  cuckoo.build(data.data());
  std::set<uint64_t> buckets;
  for (uint64_t k = 1; k <= 32; ++k) {
    Check(bucket[uint64_t(-1)].dummy() && cuckoo[uint64_t(-1)].dummy(), "a dummy lookup returned a block");
    Check(bucket.*Get(BucketCounter{}) == uint64_t(0) - k && cuckoo.*Get(CuckooCounter{}) == uint64_t(0) - k,
          "a dummy lookup did not take a fresh dummy");
    buckets.insert((bucket.*Get(BucketPrf{}))(uint32_t(uint64_t(0) - k)));  // the bucket the k-th dummy scanned
  }
  Check(buckets.size() > 10, "fresh dummies probe the same few buckets");
  // Real lookups still find their blocks (a lookup takes the block out of its level).
  const auto five = bucket[5], seven_hundred = cuckoo[700];
  Check(!five.dummy() && five.id == 5, "bucket lookup after dummies");
  Check(!seven_hundred.dummy() && seven_hundred.id == 700, "cuckoo lookup after dummies");
#endif
}
}  // namespace

int main() {
  try {
    TestLayoutSurvivesANonMonotonePlan();
    TestTwoTierExtractKeepsEveryBlock();
    TestDummyLookupsAreFresh();
    std::cout << "h2o2ram layout, two-tier extract and dummy-lookup tests passed\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
