// The tree ORAM's interleaved transposition (cpu_tree_transpose.hpp), the
// sixteen-register network with its exact-P pruning: the VPERMT2B network
// agrees with the scalar reference on random tiles, is its own inverse (so
// one set of tables serves the read and the write-back), and its index
// tables are well formed.  Also the geometry arithmetic of
// cpu_tree_layout.hpp: chunk tiling, bucket addressing in the bit-reversed
// order, checked sizes, and the default rule's fold and stash width per
// capacity.

#include "src/oram/tree/cpu_tree_transpose.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <stdexcept>
#include <vector>

namespace {

namespace tr = microram::tree;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrowsAs;

void TestTablesAreWellFormed() {
  const tr::TransposeTables4 t = tr::MakeTransposeTables4();
  alignas(64) uint8_t bytes[64];
  for (unsigned k = 0; k < tr::kTransposeStages; ++k) {
    for (unsigned rk = 0; rk < 2; ++rk) {
      _mm512_store_si512(reinterpret_cast<void*>(bytes), t.idx[k][rk]);
      for (unsigned q = 0; q < 64; ++q) {
        Expect(bytes[q] < 128, "transpose index out of range");
        // Bit k+2 of the source position is r_k, and the source register is
        // chosen by bit k+2 of the destination position.
        Expect(((bytes[q] >> (k + 2)) & 1u) == rk,
               "transpose index has the wrong source bit");
        Expect(((bytes[q] >> 6) & 1u) == ((q >> (k + 2)) & 1u),
               "transpose index selects the wrong register");
        // The slot bits travel unchanged.
        Expect((bytes[q] & 3u) == (q & 3u), "transpose index moves the slot");
      }
    }
  }
}

// THE EXACT-P NETWORK (cpu_tree_transpose.hpp's "The network pruned to the
// EXACT path length"): for every P in 1..16 the forward network reads
// registers [0, P) only -- the rest are poisoned here and must transpose as
// zero -- and agrees with the reference; the inverse restores [0, P) and
// promises nothing else.  The shuffle count is the table in the header.
void TestExactNetwork() {
  static_assert(tr::ExactNetworkShuffles(8) == 72, "P = 8");
  static_assert(tr::ExactNetworkShuffles(16) == 128, "P = 16 is the full network");
  static_assert(tr::ExactNetworkShuffles(9) == 101, "P = 9");
  static_assert(tr::ExactNetworkShuffles(10) == 102, "P = 10");
  static_assert(tr::ExactNetworkShuffles(12) == 108, "P = 12");
  static_assert(tr::ExactNetworkShuffles(13) == 121, "P = 13");
  static_assert(tr::ExactPrefix(9, 0) == 10 && tr::ExactPrefix(9, 1) == 12 &&
                    tr::ExactPrefix(9, 2) == 16 && tr::ExactPrefix(5, 1) == 8,
                "prefix arithmetic");
  alignas(64) uint8_t in[16 * 64], want[16 * 64];
  alignas(64) __m512i x[16];
  std::mt19937_64 rng(0xE4AC);
  const tr::TransposeTables4& t = tr::DefaultTransposeTables4();
  for (unsigned trial = 0; trial < 60; ++trial) {
    for (unsigned P = 1; P <= 16; ++P) {
      for (auto& b : in) b = static_cast<uint8_t>(rng());
      // Registers [P, 16) are ZERO to the reference and POISON to the
      // kernel, which must not read them.
      std::memset(in + P * 64, 0, (16 - P) * 64);
      tr::TransposeInterleavedReference(in, want);
      std::memcpy(x, in, sizeof(in));
      std::memset(reinterpret_cast<uint8_t*>(x) + P * 64, 0xA5, (16 - P) * 64);
      tr::WithPathBuckets(P, [&](auto p) {
        tr::TransposeToLines4Exact<decltype(p)::value>(x, t);
      });
      Expect(std::memcmp(x, want, sizeof(want)) == 0,
             "the exact forward network disagrees with the reference");
      tr::WithPathBuckets(P, [&](auto p) {
        tr::TransposeToChunks4Exact<decltype(p)::value>(x, t);
      });
      Expect(std::memcmp(x, in, P * 64) == 0,
             "the exact inverse network did not restore the path");
    }
  }
  std::puts("  exact network: P = 1..16 x 60 trials, poisoned tails");
}

// THE BIT REVERSAL (cpu_tree_layout.hpp's reverse_position): every path
// address goes through it, so it is checked exhaustively at the widths a
// test can enumerate and randomly at the rest, against a bit-at-a-time
// loop, and as an involution.
void TestBitReversal() {
  uint64_t state = 0x243F6A8885A308D3ull;
  auto next = [&state] {
    state = state * 6364136223846793005ull + 1442695040888963407ull;
    return state ^ (state >> 29);
  };
  size_t checked = 0;
  for (unsigned bits = 1; bits <= tr::TreeGeometry::max_leaf_bits(); ++bits) {
    tr::TreeGeometry g;
    g.leaf_bits = bits;
    char msg[64];
    std::snprintf(msg, sizeof(msg), "bit reversal at %u leaf bits", bits);
    const uint64_t mask = (uint64_t{1} << bits) - 1;
    const bool exhaustive = bits <= 16;
    const size_t trials = exhaustive ? (size_t{1} << bits) : 4000;
    for (size_t i = 0; i < trials; ++i) {
      const uint64_t v = (exhaustive ? uint64_t{i} : next()) & mask;
      uint64_t loop = 0;
      for (unsigned k = 0; k < bits; ++k) loop |= ((v >> k) & 1) << (bits - 1 - k);
      Expect(g.reverse_position(v) == loop, msg);
      Expect(g.reverse_position(g.reverse_position(v)) == v, msg);
      ++checked;
    }
  }
  Expect(checked > 200000, "the reversal sweep did not run");
  std::printf("  bit reversal: %zu cases, widths 1-%u\n", checked,
              tr::TreeGeometry::max_leaf_bits());
}

// CHECKED SIZE ARITHMETIC (cpu_tree_layout.hpp's ValidateGeometrySizes).
// `kMetaBytes + value_bytes` wraps, and a wrapped entry width would answer
// every later question with a plausible small number.
void TestSizeArithmeticIsChecked() {
  for (double load : {-0.5, 1.0, __builtin_inf(), __builtin_nan("")}) {
    ExpectThrowsAs<std::invalid_argument>(
        [=] {
          tr::TreeShape shape;
          shape.max_load = load;
          (void)tr::TreeGeometry::ForCapacity(128, 1, 16, 0, shape);
        },
        "an invalid custom load was accepted");
  }
  ExpectThrowsAs<std::length_error>(
      [] { tr::TreeGeometry::ForCapacity(4, 1, SIZE_MAX - 15); },
      "a value width that wraps the entry was accepted");
  ExpectThrowsAs<std::length_error>(
      [] { tr::TreeGeometry::ForCapacity(4, 1, SIZE_MAX); },
      "SIZE_MAX value bytes were accepted");
  // A width that does not wrap the ENTRY but wraps the arena.
  ExpectThrowsAs<std::length_error>(
      [] { tr::TreeGeometry::ForCapacity(size_t{1} << 20, 1, size_t{1} << 55); },
      "an arena past the address space was accepted");
  // A hand-built geometry gets the same boundary, and it runs before the
  // arena is asked for.
  ExpectThrowsAs<std::length_error>(
      [] {
        tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, 64);
        g.value_bytes = SIZE_MAX - 15;
        tr::ValidateGeometry(g);
      },
      "a wrapped entry width passed the geometry boundary");
  // A slice naming chunks the entry does not have.
  ExpectThrowsAs<std::invalid_argument>(
      [] {
        const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(1024, 1, 64);
        tr::ValidateGeometry(g.ForSlice(0, static_cast<unsigned>(g.chunks() + 1)));
      },
      "a slice past the entry's chunks was accepted");
  // And the ordinary geometries still pass it.
  for (size_t v : {size_t{1}, size_t{7}, size_t{64}, size_t{1024}}) {
    tr::ValidateGeometry(tr::TreeGeometry::ForCapacity(4096, 1, v));
  }
}

void TestGeometry() {
  // V = 1024: E = 1040, 65 chunks of 16 columns, stride 4160, the last chunk
  // whole.  At fold 1 the load of one half, the 192 stash lanes counted, is
  // 19 leaf bits for 2^21 entries.
  const tr::TreeGeometry g = tr::TreeGeometry::ForCapacity(size_t{1} << 21, 1, 1024);
  Expect(g.leaf_bits == 19, "leaf bits for 2^21 entries");
  Expect(g.shape.stash_registers == 3, "fold 1 takes three stash registers");
  Expect(g.capacity() == (size_t{1} << 21), "capacity is the one requested");
  Expect(g.slots() == 4 * ((size_t{1} << 20) - 1) + 192, "slots");
  Expect(g.entry_bytes() == 1040, "entry bytes");
  Expect(g.chunks() == 65, "chunk count");
  Expect(g.bucket_stride() == 4160, "bucket stride");
  Expect(g.last_chunk_columns() == 16, "last chunk columns");
  Expect(g.path_levels() == 19 && g.path_slots() == 76, "path levels at fold 1");
  Expect(g.num_buckets() == (size_t{1} << 20) - 2, "bucket count");
  Expect(g.stash_bytes() == 192 * 1040, "stash region");
  // Path addressing.  A level is stored BIT-REVERSED and its base carries a
  // one-cache-line skew (cpu_tree_layout.hpp), so level j's slot is the low j
  // bits of the reversed leaf rather than the top j bits of the leaf, and the
  // level bases are not a uniform stride apart.
  const size_t W = g.bucket_stride();
  const size_t K = tr::TreeGeometry::kLevelSkewBytes;
  auto slot_of = [&](unsigned level, uint64_t pos) {
    return (g.bucket_offset(level, pos) - g.level_offset_bytes(level)) / W;
  };
  Expect(g.reverse_position(1) == (uint64_t{1} << 18), "reversal of 1");
  Expect(g.level_offset_bytes(1) == 0, "the first level starts the arena");
  Expect(g.level_offset_bytes(2) == 2 * W + K, "level bases carry the skew");
  Expect(slot_of(1, 0) == 0, "root-level bucket of path 0");
  Expect(slot_of(1, uint64_t{1} << 18) == 1, "root-level bucket of the upper half");
  Expect(slot_of(19, 12345) == g.reverse_position(12345), "leaf bucket slot");
  // Every level is a permutation of its slots, and the tree still nests: the
  // child's slot is the parent's slot plus the next bit of the reversed leaf,
  // weighted 2^level -- the reversed image of "child = 2 * parent + bit".
  for (unsigned level = 1; level < 19; ++level) {
    const uint64_t p = 0x5BCDE;
    const uint64_t rev = g.reverse_position(p);
    const size_t parent = slot_of(level, p);
    const size_t child = slot_of(level + 1, p);
    Expect(parent == (rev & ((uint64_t{1} << level) - 1)),
           "level slot is not the low bits of the reversed leaf");
    Expect(child == parent + (((rev >> level) & 1) << level),
           "path buckets do not nest under the bit-reversed order");
  }
  // The skew must not cost alignment, and the arena must hold it.
  for (unsigned level = 1; level <= 19; ++level) {
    Expect(g.level_offset_bytes(level) % 64 == 0, "level base is not aligned");
  }
  Expect(g.level_offset_bytes(19) + (size_t{1} << 19) * W <=
             g.bucket_bytes_total(),
         "the arena does not hold the skewed levels");

  // The capacity is the one asked for, whatever it is.
  Expect(tr::TreeGeometry::ForCapacity(1000, 1, 8).capacity() == 1000,
         "capacity is not the one requested");
  // A fold needs a stored level beneath it.
  const tr::TreeGeometry tiny = tr::TreeGeometry::ForCapacity(1, 3, 8);
  Expect(tiny.leaf_bits == 3 && tiny.path_levels() == 1,
         "fold 3 on a tiny capacity keeps one stored level");
  // The path bound: 2^34 entries are 32 leaf bits and a 32-bucket path at
  // fold 1, and 2^35 need 33.
  Expect(tr::TreeGeometry::ForCapacity(size_t{1} << 34, 1, 8).path_levels() == 32,
         "2^34 entries at fold 1 are a 32-bucket path");
  ExpectThrowsAs<std::length_error>(
      [] { tr::TreeGeometry::ForCapacity(size_t{1} << 35, 1, 8); },
      "a path past 32 buckets was accepted");
  // The knobs' ranges.
  ExpectThrowsAs<std::invalid_argument>(
      [] { tr::TreeGeometry::ForCapacity(1024, 6, 8); }, "fold 6 was accepted");
  for (unsigned a : {1u, 2u, 5u}) {
    ExpectThrowsAs<std::invalid_argument>(
        [=] {
          tr::TreeShape shape;
          shape.stash_registers = a;
          tr::TreeGeometry::ForCapacity(1024, 0, 8, 0, shape);
        },
        "a stash width other than 3 or 4 was accepted");
  }
  ExpectThrowsAs<std::invalid_argument>(
      [] {
        tr::TreeShape shape;
        shape.max_folded_slots = 192;  // past the 191 of three registers
        tr::TreeGeometry::ForCapacity(1024, 0, 8, 0, shape);
      },
      "a fold budget past the stash lanes was accepted");
  ExpectThrowsAs<std::invalid_argument>(
      [] {
        tr::TreeShape shape;
        shape.max_folded_slots = 12;
        tr::TreeGeometry::ForCapacity(1024, 3, 8, 0, shape);
      },
      "an explicit fold past its budget was accepted");
}

// THE DEFAULT RULE (cpu_tree_layout.hpp): the leaf bits L that hold N at a
// load of one half with the stash lanes counted, fold L - 15 while that is 2
// to 5 and 1 otherwise, three stash registers up to fold 4 and four at
// fold 5 or from 25 leaf bits (2^27 entries) on.  These geometries cost
// nothing to build: nothing is allocated.
void TestDefaultRule() {
  struct Case {
    unsigned log_n, leaf_bits, fold, stash_registers, path_slots;
  };
  const Case cases[] = {
      {10, 8, 1, 3, 32},   {14, 12, 1, 3, 48},  {18, 16, 1, 3, 64},
      {19, 17, 2, 3, 64},  {20, 18, 3, 3, 64},  {21, 19, 4, 3, 64},
      {22, 20, 5, 4, 64},  {23, 21, 1, 3, 84},  {24, 22, 1, 3, 88},
      {25, 23, 1, 3, 92},  {26, 24, 1, 3, 96},  {27, 25, 1, 4, 100},
      {28, 26, 1, 4, 104},
  };
  for (const Case& c : cases) {
    const tr::TreeGeometry g =
        tr::TreeGeometry::ForCapacity(size_t{1} << c.log_n, 0, 1024);
    char msg[96];
    std::snprintf(msg, sizeof(msg), "the default rule at 2^%u", c.log_n);
    Expect(g.leaf_bits == c.leaf_bits, msg);
    Expect(g.fold == c.fold, msg);
    Expect(g.shape.stash_registers == c.stash_registers, msg);
    Expect(g.path_slots() == c.path_slots, msg);
    tr::ValidateGeometry(g);
    std::printf("  2^%u: %u leaf bits, fold %u, A %u, path %u slots\n", c.log_n,
                g.leaf_bits, g.fold, g.shape.stash_registers, g.path_slots());
  }
  // The wide stash starts with the depth: 24 leaf bits hold up to
  // 2^26 + 94 entries with three registers (N <= 2^(L+2) - 2 + 32 A), and
  // one more takes 25 leaf bits and four.
  {
    const size_t last = (size_t{1} << 26) + 94;
    const tr::TreeGeometry g24 = tr::TreeGeometry::ForCapacity(last, 0, 64);
    const tr::TreeGeometry g25 = tr::TreeGeometry::ForCapacity(last + 1, 0, 64);
    Expect(g24.leaf_bits == 24 && g24.shape.stash_registers == 3,
           "2^26 + 94 entries are 24 leaf bits and three stash registers");
    Expect(g25.leaf_bits == 25 && g25.shape.stash_registers == 4,
           "2^26 + 95 entries are 25 leaf bits and four stash registers");
  }
  // A caller's stash width or fold overrides the rule's, and the other one
  // still follows it.
  tr::TreeShape four;
  four.stash_registers = 4;
  Expect(tr::TreeGeometry::ForCapacity(size_t{1} << 20, 0, 64, 0, four).fold == 3,
         "an explicit stash width moved the default fold");
  Expect(tr::TreeGeometry::ForCapacity(size_t{1} << 20, 5, 64).shape.stash_registers == 4,
         "an explicit fold 5 did not take four stash registers");
  Expect(tr::TreeGeometry::ForCapacity(size_t{1} << 22, 4, 64).shape.stash_registers == 3,
         "an explicit fold 4 did not take three stash registers");
  // Fewer than the rule's are refused by depth as by fold.
  ExpectThrowsAs<std::invalid_argument>(
      [] {
        tr::TreeShape three;
        three.stash_registers = 3;
        tr::TreeGeometry::ForCapacity(size_t{1} << 27, 1, 64, 0, three);
      },
      "three stash registers at 25 leaf bits were accepted");
  Expect(tr::TreeGeometry::ForCapacity(size_t{1} << 24, 1, 64, 0, four).shape.stash_registers == 4,
         "an explicit A = 4 below 25 leaf bits was refused");
  // A fold budget lowers the default fold to one it pays for.
  tr::TreeShape budget;
  budget.max_folded_slots = 12;
  const tr::TreeGeometry lowered =
      tr::TreeGeometry::ForCapacity(size_t{1} << 21, 0, 64, 0, budget);
  Expect(lowered.fold == 2 && lowered.path_buckets() == 18,
         "max_folded_slots 12 did not lower 2^21 to fold 2");
}

}  // namespace

int main() {
  TestTablesAreWellFormed();
  TestExactNetwork();
  TestBitReversal();
  TestSizeArithmeticIsChecked();
  TestGeometry();
  TestDefaultRule();
  std::puts("cpu_tree_transpose_test passed");
  return 0;
}
