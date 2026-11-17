// The tree ORAM's planner (cpu_tree_read_path_eviction.hpp) against its
// scalar reference over random working sets that satisfy the path invariant,
// in the shapes the engine builds -- A = 3 and A = 4 behind one or two path
// registers: the routing is identical slot for slot, and the rule's
// three properties hold -- no path entry is dropped, every path entry moves
// down or stays, and path register 1 never takes a source from path
// register 0 -- with the landing lane, the keep masks, the count, the
// occupancy and the overflow all as the reference says.  And the planner's
// byte-sliced field helpers against scalar arithmetic.

#include "src/oram/tree/cpu_tree_read_path_eviction.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <vector>

namespace {

namespace tr = microram::tree;
using microram::byteslice::test_support::Expect;

constexpr unsigned kPathLanes = tr::kReadPathPathRegisters * 64;

// The working set in priority order: `path_lanes` = 64 B path lanes (B =
// ReadPathRegisters(P)), then the stash.  Sized for two path registers.
template <unsigned A>
struct WorkingSet {
  static constexpr unsigned kLanes = kPathLanes + 64 * A;
  unsigned path_lanes = kPathLanes;
  unsigned lanes() const { return path_lanes + 64 * A; }
  uint64_t uid[kLanes];
  uint64_t pos[kLanes];  // as STORED: the leaf, plus the real bit
  alignas(64) uint8_t stash_lines[16 * 64 * A];
  alignas(64) __m512i path_lines[16 * tr::kReadPathPathRegisters];

  bool real(unsigned l) const { return tr::StoredPositionIsReal(pos[l]); }
  uint64_t leaf(unsigned l) const { return tr::StoredPositionLeaf(pos[l]); }

  void Encode() {
    alignas(64) uint8_t path_bytes[16 * kPathLanes] = {};
    for (unsigned line = 0; line < 16; ++line) {
      for (unsigned l = 0; l < lanes(); ++l) {
        const uint64_t word = line < 8 ? uid[l] : pos[l];
        const uint8_t byte = static_cast<uint8_t>(word >> (8 * (line & 7)));
        if (l < path_lanes) {
          // Line `line` of path register `l / 64`.
          path_bytes[64 * (16 * (l / 64) + line) + l % 64] = byte;
        } else {
          stash_lines[line * 64 * A + (l - path_lanes)] = byte;
        }
      }
    }
    std::memcpy(path_lines, path_bytes, sizeof(path_bytes));
  }
};

// Match bits from the leaf up: position `m` shares `leaf_bits - m` bits.
std::vector<uint8_t> MatchBits(unsigned leaf_bits, unsigned path_buckets) {
  std::vector<uint8_t> bits(tr::kMaxPathLevels, 0);
  for (unsigned m = 0; m < path_buckets; ++m) {
    bits[m] = static_cast<uint8_t>(leaf_bits - m);
  }
  return bits;
}

template <unsigned A>
void RunTrial(std::mt19937_64& rng, unsigned* overflowed, unsigned* found_cases,
              unsigned* landed, unsigned* two_registers) {
  WorkingSet<A> w;
  // Both stash widths behind one- and two-register paths, as the engine
  // builds them (four registers from 25 leaf bits at fold 1).
  const unsigned P = 1 + static_cast<unsigned>(rng() % tr::kReadPathMaxBuckets);
  // At least one leaf bit, and at least as many as the levels above the leaf.
  const unsigned leaf_bits =
      (P > 1 ? P - 1 : 1u) + static_cast<unsigned>(rng() % 28);
  const std::vector<uint8_t> match = MatchBits(leaf_bits, P);
  const uint64_t leaf_mask = (uint64_t{1} << leaf_bits) - 1;
  const uint64_t path = rng() & leaf_mask;
  // Densities: an empty-ish stash, a crowded one, and the full one that
  // overflows.
  const unsigned path_density = static_cast<unsigned>(rng() % 101);
  const unsigned stash_mode = static_cast<unsigned>(rng() % 4);
  const unsigned stash_density =
      stash_mode == 0 ? 5 : stash_mode == 1 ? 50 : stash_mode == 2 ? 95 : 100;
  w.path_lanes = 64 * tr::ReadPathRegisters(P);
  for (unsigned l = 0; l < w.lanes(); ++l) {
    // Dummies carry junk uids and leaves sometimes, and real entries a uid of
    // zero sometimes: only the real bit decides.
    w.uid[l] = rng() % 7 == 0 ? 0 : rng();
    const bool on_path = l < w.path_lanes;
    const unsigned m = l / tr::kBucketSlots;
    bool real;
    uint64_t leaf;
    if (on_path) {
      real = m < P && rng() % 100 < path_density;
      // A path entry at position m shares match[m] leading bits of the path.
      const unsigned free_bits = m < P ? leaf_bits - match[m] : 0;
      leaf = path ^ (rng() & ((uint64_t{1} << free_bits) - 1));
    } else {
      real = rng() % 100 < stash_density;
      leaf = rng() & leaf_mask;
    }
    if (!real && rng() % 3 == 0) leaf = rng() & leaf_mask;  // junk
    w.pos[l] = real ? tr::EncodeStoredPosition(leaf) : leaf;
  }
  const bool has_target = rng() % 4 != 0;
  uint64_t target = rng();
  if (has_target && rng() % 3 != 0) {
    // A real lane's uid, so the target is found.
    for (int tries = 0; tries < 64; ++tries) {
      const unsigned l = static_cast<unsigned>(rng() % w.lanes());
      if (w.real(l)) {
        target = w.uid[l];
        break;
      }
    }
  }
  const bool create = rng() % 3 == 0;
  const bool erase = !create && rng() % 5 == 0;
  w.Encode();

  tr::ReadPathEvictionInput in;
  in.stash_meta = w.stash_lines;
  in.path_meta = w.path_lines;
  in.target_uid = target;
  in.has_target = has_target;
  in.create = create;
  in.erase = erase;
  in.path_position = path;
  in.leaf_bits = leaf_bits;
  in.path_buckets = P;
  in.level_match_bits = match.data();
  tr::ReadPathPlan plan;
  const unsigned B = tr::ReadPathRegisters(P);
  if (B == 1) {
    tr::PlanReadPath<A, 1>(in, &plan);
  } else {
    tr::PlanReadPath<A, 2>(in, &plan);
  }
  const tr::ReferenceReadPath ref = tr::ReferenceReadPathEvict(
      w.uid, w.pos, A, target, has_target, create, erase, path, leaf_bits, P,
      match.data());

  Expect(!ref.path_entry_dropped, "the reference dropped a path entry");
  Expect(plan.found == ref.found, "found disagrees with the reference");
  Expect(plan.stash_count == ref.stash_count, "stash count disagrees");
  Expect(plan.overflow == ref.overflow, "overflow disagrees");
  // What the stash would hold: on an overflow that is past its capacity.
  const bool stays = (ref.found || create) && !erase;
  Expect(plan.occupancy == ref.stash_count + (stays ? 1u : 0u),
         "occupancy disagrees");
  Expect(ref.overflow || (ref.landing >= 0) == stays, "the reference lost a landing");
  *overflowed += plan.overflow;
  *found_cases += plan.found;
  *landed += ref.landing >= 0;
  *two_registers += P > tr::kReadPathBucketsPerRegister;

  // The routing, destination by destination.  Destination b's words start
  // at F = ReadPathFirstWord(b), and its pair q is the words (F + 2q, F + 2q
  // + 1) -- or, when F + 2q is the odd last word W - 1, the accumulator and
  // that word, so its lanes must index the second table.  Index bit 6 picks
  // the word, the low six bits its lane; word w's lane l is working-set lane
  // 64 w + l.  Returns -1 for an index into the accumulator.
  const unsigned W = B + A;
  const auto source_of = [&](unsigned F, unsigned q, uint8_t index) {
    const unsigned lo = F + 2 * q;
    const unsigned high = (index >> 6) & 1;
    if (lo + 1 == W && high == 0) return -1;
    return static_cast<int>(64 * (lo + 1 == W ? lo : lo + high) + (index & 63));
  };
  bool used[WorkingSet<A>::kLanes] = {};
  for (unsigned b = 0; b < B; ++b) {
    const unsigned F = tr::ReadPathFirstWord(b);
    const unsigned Q = tr::ReadPathPairs(A, B, b);
    alignas(64) uint8_t index[64];
    _mm512_store_si512(reinterpret_cast<void*>(index), plan.index[b]);
    for (unsigned q = Q; q < tr::kReadPathMaxPairs; ++q) {
      Expect(plan.from[b][q] == 0, "a mask past the destination's pairs");
    }
    for (unsigned lane = 0; lane < 64; ++lane) {
      const unsigned d = 64 * b + lane;
      unsigned pairs = 0, source = tr::ReferenceReadPath::kNone;
      for (unsigned q = 0; q < Q; ++q) {
        if ((plan.from[b][q] >> lane) & 1) {
          ++pairs;
          const int s = source_of(F, q, index[lane]);
          Expect(s >= 0, "a folded word's lane indexes the accumulator");
          source = static_cast<unsigned>(s);
        }
      }
      Expect(pairs <= 1, "a destination names two pairs");
      Expect(source == ref.source[d], "source disagrees with the reference");
      if (source == tr::ReferenceReadPath::kNone) continue;
      Expect(source < w.lanes(), "source out of range");
      Expect(!used[source], "a source was used twice");
      used[source] = true;
      Expect(w.real(source), "a dummy was moved as real");
      Expect(!has_target || !ref.found || static_cast<int>(source) != ref.target,
             "the target was routed onto the path");
      const unsigned m = d / tr::kBucketSlots;
      Expect(m < P, "a destination past the path");
      Expect((w.leaf(source) >> (leaf_bits - match[m])) ==
                 (path >> (leaf_bits - match[m])),
             "an entry was placed off its path");
      if (source < w.path_lanes) {
        Expect(m <= source / tr::kBucketSlots, "a path entry moved up");
        Expect(b == 0 || source >= 64,
               "path register 1 took a source from path register 0");
      }
    }
  }
  // Every path entry but the target was placed; every stash entry is either
  // placed or kept.
  unsigned keep_count = 0;
  for (unsigned l = 0; l < w.lanes(); ++l) {
    const bool target_lane = static_cast<int>(l) == ref.target;
    if (l < w.path_lanes) {
      Expect(used[l] == (w.real(l) && !target_lane), "a path entry was dropped");
      continue;
    }
    const unsigned s = l - w.path_lanes;
    const bool kept = (plan.keep[s / 64] >> (s % 64)) & 1;
    Expect(kept == ref.keep[s], "keep disagrees with the reference");
    Expect(kept + used[l] == (w.real(l) && !target_lane),
           "a stash entry was neither placed nor kept");
    keep_count += kept;
  }
  Expect(keep_count == plan.stash_count, "keep masks and count disagree");
  // The landing lane.
  int landing = -1;
  unsigned land_bits = 0;
  for (unsigned a = 0; a < A; ++a) {
    land_bits += static_cast<unsigned>(_mm_popcnt_u64(plan.land[a]));
    if (plan.land[a] != 0 && landing < 0) {
      landing = static_cast<int>(64 * a + _tzcnt_u64(plan.land[a]));
    }
  }
  if (!plan.overflow) {
    Expect(landing == ref.landing, "landing lane disagrees with the reference");
    Expect(land_bits == (ref.landing >= 0 ? 1u : 0u), "landing is not one-hot");
  }
  // The target's source.
  alignas(64) uint8_t tindex[64];
  _mm512_store_si512(reinterpret_cast<void*>(tindex), plan.target_index);
  int target_lane = -1;
  for (unsigned q = 0; q < tr::ReadPathPairs(A, B, 0); ++q) {
    Expect(plan.target_from[q] == 0 || plan.target_from[q] == ~uint64_t{0},
           "target_from is not all-or-none");
    if (plan.target_from[q] != 0) {
      Expect(target_lane < 0, "the target is in two pairs");
      target_lane = source_of(tr::ReadPathFirstWord(0), q, tindex[0]);
      Expect(target_lane >= 0, "the target's index names the accumulator");
    }
  }
  Expect(target_lane == ref.target, "the target's source disagrees");
  for (unsigned i = 1; i < 64; ++i) {
    Expect(tindex[i] == tindex[0], "target_index is not a broadcast");
  }
}

template <unsigned A>
void TestAgainstReference(unsigned trials, uint64_t seed) {
  std::mt19937_64 rng(seed);
  unsigned overflowed = 0, found = 0, landed = 0, two = 0;
  for (unsigned t = 0; t < trials; ++t) {
    RunTrial<A>(rng, &overflowed, &found, &landed, &two);
  }
  Expect(overflowed > 0, "no trial overflowed: the overflow path is untested");
  Expect(found > 0 && landed > 0, "no trial found or landed its target");
  Expect(two > 0, "no trial used the second path register");
  std::printf("  A = %u: %u trials agreed (%u overflowed, %u found, %u landed, "
              "%u on two path registers)\n",
              A, trials, overflowed, found, landed, two);
}

// The field helpers over lines read in place, a stash line apart: the XOR-OR
// is zero exactly where the field equals the word, and the capped bit length
// is exact below the cap.  At or above the cap the only promise is that the
// answer is also at or above it, which is all the saturating subtract
// downstream needs (both give deepest level 0).
void TestFieldHelpers() {
  constexpr size_t kStride = 64 * 3;
  std::mt19937_64 rng(0xB17);
  alignas(64) uint8_t lines[8 * kStride] = {};
  uint64_t fields[64];
  for (unsigned trial = 0; trial < 200; ++trial) {
    const uint64_t word = trial % 3 == 0 ? 0 : rng();
    for (unsigned lane = 0; lane < 64; ++lane) {
      uint64_t v = rng();
      const unsigned shift = rng() % 65;
      v = shift == 64 ? 0 : (v >> shift);
      fields[lane] = v ^ word;
      for (unsigned b = 0; b < 8; ++b) {
        lines[b * kStride + lane] = static_cast<uint8_t>(fields[lane] >> (8 * b));
      }
    }
    __m512i word_bytes[8];
    for (unsigned b = 0; b < 8; ++b) {
      word_bytes[b] = _mm512_set1_epi8(static_cast<char>(word >> (8 * b)));
    }
    alignas(64) uint8_t eq[64];
    _mm512_store_si512(reinterpret_cast<void*>(eq),
                       tr::detail::FieldXorOr8At<kStride>(lines, word_bytes));
    for (unsigned lane = 0; lane < 64; ++lane) {
      Expect((eq[lane] == 0) == (fields[lane] == word),
             "the field compare is wrong");
    }
    // Every cap the planner can ask for: `leaf_bits + 1` at 1..36 leaf bits,
    // and 64, the uncapped contract.
    for (unsigned cap : {2u, 8u, 16u, 20u, 33u, 37u, 64u}) {
      alignas(64) uint8_t len[64];
      _mm512_store_si512(
          reinterpret_cast<void*>(len),
          tr::detail::BitLengthCappedAt<kStride>(lines, word_bytes, cap));
      for (unsigned lane = 0; lane < 64; ++lane) {
        const uint64_t x = fields[lane] ^ word;
        unsigned exact = 0;
        while (exact < 64 && (x >> exact) != 0) ++exact;
        Expect(exact < cap ? len[lane] == exact : len[lane] >= cap,
               "byte-sliced bit length is wrong");
      }
    }
  }
  std::printf("  field helpers: compare and capped bit length exact\n");
}

}  // namespace

int main() {
  std::printf("cpu_tree_read_path_eviction_test\n");
  TestFieldHelpers();
  TestAgainstReference<3>(6000, 3);
  TestAgainstReference<4>(6000, 4);
  std::printf("cpu_tree_read_path_eviction_test: PASS\n");
  return 0;
}
