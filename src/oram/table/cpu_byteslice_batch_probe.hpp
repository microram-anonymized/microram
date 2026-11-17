#pragma once

// The primitives a BATCH of accesses shares, engine-independent (overview in
// table DESIGN.md, "Probing without revealing the matching slot").
//
// A batch serves independent requests in lane order: a write is visible to
// later reads of its key. Caller buffers cannot carry dependencies between
// requests; this is not a promise of serial program equivalence. Batching buys
// memory-level parallelism: table i's key lines decide table i+1's address,
// so one access is L serially dependent DRAM misses, while B accesses issued
// together are L waves of B overlapped ones.  Three things have to be done
// per batch for that to be both correct and oblivious, and all three live
// here so that the cascade in the engine is a loop over lanes and nothing
// more:
//
//   - DEDUP.  Two equal keys hash to one bucket under one nonce, and a
//     repeated bucket is the statement "these two requests were equal".  So
//     only the FIRST lane holding a key probes for real; every later lane
//     holding it starts out "found" and issues an independent dummy probe at
//     every hashed table, exactly as a lane whose key was found at the top
//     would.  DedupBatchLanes computes, per lane, the set of EARLIER lanes
//     holding the same key -- the whole set, because the forwarding needs the
//     last of them and the insert needs to know which lanes have a successor.
//     Register compares under a public loop; nothing is indexed by a secret.
//
//   - THE ADDRESS PASS OVER ALL LANES.  ResolveHashedProbeAddresses hashes one
//     access's 2h candidate blocks in one AES batch; the batch form hashes all
//     lanes' 2hB blocks in ONE call, which is the width the eight-chain VAES
//     loop was written for and which one access never reaches.
//
//   - FORWARDING.  A lane that repeats an earlier lane's key did not probe, and
//     its answer is not the representative's probe result either once the
//     batch may mix operations: a read after a write of the same key must see
//     the write.  Its answer is the STATE THE PREVIOUS EQUAL-KEY LANE LEFT,
//     which is what the serial sequence would have found in the current
//     stash.  ForwardBatchLane runs that chain in lane order; the state of
//     the lanes already run is kept SLICED -- one 64-byte line per value
//     byte, lane j's byte at column j -- so reading "the state lane p left"
//     with a secret p is one VPERMB per line, a register permute rather than
//     a memory access at a secret address.
//
// Everything below indexes memory by the PUBLIC lane number only.  The secret
// quantities -- which lanes are duplicates, of which earlier lane, whether a
// lane's key was found -- live in registers and drive CMOVs and permute
// controls.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_batch_config.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_probe_addresses.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {

// One request of a batch (the engines' AccessBatch).  `op`
// and `insert` (exchange only) are PUBLIC.  `key` is the engine's user key
// width; `value_in` is read by write and exchange lanes; `value_out`, when
// non-null, receives the key's value BEFORE the lane's own operation -- zeros
// when absent or erased -- for every operation, including write. A write or
// exchange lane may overlap its own value_in and value_out, including partial
// overlap. Buffers must not carry dependencies between different requests.
struct BatchRequest {
  BatchOp op = BatchOp::kRead;
  bool insert = false;
  const uint8_t* key = nullptr;
  const uint8_t* value_in = nullptr;
  uint8_t* value_out = nullptr;
};

// The same with a <= 8-byte key as a word, the Read(uint64_t, ...) form.
struct BatchRequest64 {
  BatchOp op = BatchOp::kRead;
  bool insert = false;
  uint64_t key = 0;
  const uint8_t* value_in = nullptr;
  uint8_t* value_out = nullptr;
};

// ---------------------------------------------------------------------------
// In-batch dedup
// ---------------------------------------------------------------------------

struct BatchDedup {
  // conflicts[j]: bit i set iff i < j and keys[i] == keys[j].  Secret words at
  // public indices.
  uint64_t conflicts[kMaxBatchLanes];
  // The last earlier lane holding lane j's key, or j itself when there is
  // none.  Secret; used only as a register permute control.
  uint8_t prev[kMaxBatchLanes];
  // bit j: lane j repeats some earlier lane (conflicts[j] != 0).
  uint64_t duplicates = 0;
  // bit i: some later lane repeats lane i, so the entry lane i inserts is
  // superseded inside this chunk and need not become live.
  uint64_t superseded = 0;
};

#if defined(__AVX512CD__)
// Exact partner bitsets: for 5–8-byte keys, AND the two dword conflict
// vectors BEFORE reducing to duplicate flags. Equal halves must belong to
// the SAME partner. This is exact for arbitrary (nonhashed) caller keys.
// Memory indices and loop bounds depend only on public lane/group numbers.
template <unsigned Fields>
inline void DedupBatchLanesD(const KeyWords* keys, size_t m, BatchDedup* out) {
  static_assert(Fields == 1 || Fields == 2, "one or two dword fields");
  alignas(64) uint32_t packed[Fields][kMaxBatchLanes] = {};
  for (size_t j = 0; j < m; ++j) {
    for (unsigned f = 0; f < Fields; ++f)
      packed[f][j] = static_cast<uint32_t>(keys[j].w0 >> (32 * f));
  }
  uint64_t duplicates = 0, superseded = 0;
  for (size_t base = 0; base < m; base += 16) {
    alignas(64) uint32_t local[16];
    __m512i conflicts = _mm512_conflict_epi32(_mm512_load_si512(packed[0] + base));
    if constexpr (Fields == 2) {
      conflicts = _mm512_and_si512(conflicts,
          _mm512_conflict_epi32(_mm512_load_si512(packed[1] + base)));
    }
    _mm512_store_si512(local, conflicts);
    const size_t end = std::min<size_t>(base + 16, m);
    for (size_t j = base; j < end; ++j) {
      uint64_t conf = static_cast<uint64_t>(local[j - base]) << base;
      const __m512i low = _mm512_set1_epi32(static_cast<int>(packed[0][j]));
      __m512i high;
      if constexpr (Fields == 2)
        high = _mm512_set1_epi32(static_cast<int>(packed[1][j]));
      for (size_t earlier = 0; earlier < base; earlier += 16) {
        uint64_t matches = core::obliCmpEqMask32(
            _mm512_load_si512(packed[0] + earlier), low);
        if constexpr (Fields == 2) {
          matches &= core::obliCmpEqMask32(
              _mm512_load_si512(packed[1] + earlier), high);
        }
        conf |= matches << earlier;
      }
      out->conflicts[j] = conf;
      const bool dup = conf != 0;
      const uint64_t last = 63 - static_cast<uint64_t>(_lzcnt_u64(conf));
      out->prev[j] = static_cast<uint8_t>(
          core::obliSelectU64(static_cast<uint64_t>(j), last, dup));
      duplicates |= static_cast<uint64_t>(dup) << j;
      superseded |= conf;
    }
  }
  out->duplicates = duplicates;
  out->superseded = superseded;
}

#endif

// Fills `out` for `m <= kMaxBatchLanes` stored keys.  `key_bytes` is the
// STORED width (1..8 or 16): at <=8 the high word is zero and only
// the low words are compared.  Cost: m broadcasts and ceil(m/8)*m compares
// per key word on the general path. Keys up to eight bytes with more than
// eight lanes use exact dword partner bitsets when AVX512CD is available.
inline void DedupBatchLanes(const KeyWords* keys, size_t m, size_t key_bytes,
                            BatchDedup* out) {
  assert(m <= kMaxBatchLanes);
  if (m <= 1) {
    if (m == 1) {
      out->conflicts[0] = 0;
      out->prev[0] = 0;
    }
    out->duplicates = out->superseded = 0;
    return;
  }
  // For <=8 lanes the single-qword-vector path is cheaper.
#if defined(__AVX512CD__)
  if (key_bytes <= 8 && m > 8) {
    if (key_bytes <= 4) DedupBatchLanesD<1>(keys, m, out);
    else DedupBatchLanesD<2>(keys, m, out);
    return;
  }
#endif
  // The lane keys as two qword arrays so a group of eight lanes is one zmm
  // compare.  Padding lanes hold zeros; every comparison below is masked to
  // lanes before the lane under test, so padding never counts.
  alignas(64) uint64_t lo[kMaxBatchLanes] = {};
  alignas(64) uint64_t hi[kMaxBatchLanes] = {};
  for (size_t j = 0; j < m; ++j) {
    lo[j] = keys[j].w0;
    hi[j] = keys[j].w1;
  }
  const size_t groups = (m + 7) / 8;
  const bool wide = key_bytes > 8;
  uint64_t duplicates = 0;
  uint64_t superseded = 0;
  for (size_t j = 0; j < m; ++j) {
    const __m512i bl = _mm512_set1_epi64(static_cast<long long>(lo[j]));
    const __m512i bh = _mm512_set1_epi64(static_cast<long long>(hi[j]));
    uint64_t eq = 0;
    for (size_t g = 0; g < groups; ++g) {
      uint64_t bits = core::obliCmpEqMask64(
          _mm512_load_si512(reinterpret_cast<const void*>(lo + 8 * g)), bl);
      if (wide) {
        bits &= core::obliCmpEqMask64(
            _mm512_load_si512(reinterpret_cast<const void*>(hi + 8 * g)), bh);
      }
      eq |= bits << (8 * g);
    }
    // Only the lanes BEFORE j: a lane never conflicts with itself or with a
    // later lane.  LowMask64(j) is all-ones below bit j (zero at j = 0).
    const uint64_t conf = eq & LowMask64(static_cast<unsigned>(j));
    out->conflicts[j] = conf;
    const bool dup = conf != 0;
    // 63 - lzcnt(conf) is the highest set bit, i.e. the LAST earlier equal
    // lane; the value is garbage when conf == 0 and is then selected away.
    const uint64_t last = 63 - static_cast<uint64_t>(_lzcnt_u64(conf));
    out->prev[j] = static_cast<uint8_t>(
        core::obliSelectU64(static_cast<uint64_t>(j), last, dup));
    duplicates |= static_cast<uint64_t>(dup) << j;
    superseded |= conf;
  }
  out->duplicates = duplicates;
  out->superseded = superseded;
}

// ---------------------------------------------------------------------------
// The address pass over a batch
// ---------------------------------------------------------------------------

// Per-lane candidate scratch: lane j's [real, dummy] pair for cascade entry i
// is at bucket[j * cand_stride + 2i + half], the layout ProbeScratch has per
// access.  The AES blocks are lane-major and contiguous so that one
// AesTagsInterleaved call covers every lane.
struct BatchProbeScratch {
  std::vector<uint64_t> blocks;   // lanes x block_words qwords
  std::vector<uint64_t> tags;     // lanes x (block_words / 4)
  std::vector<uint8_t*> bucket;   // lanes x cand_stride
  std::vector<uint64_t*> mask;
  size_t lanes = 0;
  size_t cand_stride = 0;   // 2 * tables
  size_t block_words = 0;   // qwords of AES input per lane, whole zmm

  // `tables` is the longest cascade and `hashed_tables` the most hashed
  // tables in one; both are public bounds, sized once so a plan change never
  // reallocates on the access path.
  void Resize(size_t max_lanes, size_t tables, size_t hashed_tables) {
    lanes = max_lanes;
    cand_stride = 2 * tables;
    // The same rounding ProbeAddressing::Begin applies: whole zmm registers
    // of four two-block CBC messages (sixteen qwords) per lane.
    block_words = ((2 * hashed_tables + 3) / 4) * 16;
    blocks.assign(max_lanes * block_words, 0);
    tags.assign(max_lanes * (block_words / 4), 0);
    bucket.assign(max_lanes * cand_stride, nullptr);
    mask.assign(max_lanes * cand_stride, nullptr);
  }

  // What Resize above allocates, for a caller reporting a participant's
  // storage rather than sizing it.  Beside Resize so the two cannot drift.
  static size_t Bytes(size_t max_lanes, size_t tables, size_t hashed_tables) {
    const size_t block_words = ((2 * hashed_tables + 3) / 4) * 16;
    const size_t cand_stride = 2 * tables;
    return max_lanes * (block_words + block_words / 4) * sizeof(uint64_t) +
           max_lanes * cand_stride * (sizeof(uint8_t*) + sizeof(uint64_t*));
  }

  uint8_t** LaneBuckets(size_t lane) { return bucket.data() + lane * cand_stride; }
  uint64_t** LaneMasks(size_t lane) { return mask.data() + lane * cand_stride; }
  const uint8_t* const* LaneBuckets(size_t lane) const {
    return bucket.data() + lane * cand_stride;
  }
  const uint64_t* const* LaneMasks(size_t lane) const {
    return mask.data() + lane * cand_stride;
  }
};

// ResolveHashedProbeAddresses for `m` lanes at once: the same block assembly
// per lane, ONE AES call over all lanes, the same two index-map loops with the
// lane innermost.  Lane j's dummy counters start at
// `dummy_base + j * dummy_stride`, so every lane's are distinct and the
// caller's counter advance (m * dummy_stride) is a public amount.
//
// The candidates of DENSE tables are not written here (a dense table has no
// hashed candidate); the engine fills them from the plan, once per chunk.
INLINE void ResolveHashedProbeAddressesBatch(
    const ProbeAddressing& a, const KeyWords* keys, size_t m,
    uint64_t dummy_base, uint64_t dummy_stride, size_t bucket_bytes,
    const AesTagKeys& aes_keys, BatchProbeScratch& out) {
  const size_t h = a.hashed;
  if (h == 0 || m == 0) return;
  assert(m <= out.lanes);
  // The plan's own block width: whole zmm registers, possibly fewer than the
  // scratch was sized for.  Lanes are packed at THIS stride so the AES call
  // sees one contiguous run of m * words / 4 messages, a multiple of four.
  const size_t words = a.aes_template.size();
  assert(words <= out.block_words && words % 16 == 0);
  const uint64_t* const tmpl = a.aes_template.data();
  const uint64_t* const idx = a.aes_index.data();
  uint64_t* const blocks = out.blocks.data();
  for (size_t j = 0; j < m; ++j) {
    const uint64_t lane_dummy = dummy_base + j * dummy_stride;
    const __m512i bp = _mm512_set_epi64(
        0, static_cast<long long>(lane_dummy), 0, 0,
        static_cast<long long>(keys[j].w1), static_cast<long long>(keys[j].w0),
        0, 0);
    uint64_t* const lane_blocks = blocks + j * words;
    for (size_t w = 0; w < words; w += 8) {
      const __m512i v = _mm512_add_epi64(
          _mm512_loadu_si512(reinterpret_cast<const void*>(idx + w)), bp);
      _mm512_storeu_si512(
          reinterpret_cast<void*>(lane_blocks + w),
          _mm512_xor_si512(
              v, _mm512_loadu_si512(reinterpret_cast<const void*>(tmpl + w))));
    }
  }
  const size_t lane_tags = words / 4;  // tags per lane (messages per lane)
  AesTagsInterleaved(blocks, m * lane_tags, out.tags.data(), aes_keys);
  const uint64_t* const tags = out.tags.data();
  const size_t stride = out.cand_stride;
  for (const HashedProbeGeometry& g : a.hashed_pow2) {
    const uint64_t low = LowMask64(g.index_bits);
    for (size_t j = 0; j < m; ++j) {
      const uint64_t* t = tags + j * lane_tags + 2 * g.slot;
      uint8_t** bucket = out.bucket.data() + j * stride + 2 * g.table;
      uint64_t** mask = out.mask.data() + j * stride + 2 * g.table;
      for (unsigned half = 0; half < 2; ++half) {
        const size_t b = static_cast<size_t>(t[half] & low);
        bucket[half] = g.data + b * bucket_bytes;
        mask[half] = g.masks + b;
      }
    }
  }
  for (const HashedProbeGeometry& g : a.hashed_mixed) {
    for (size_t j = 0; j < m; ++j) {
      const uint64_t* t = tags + j * lane_tags + 2 * g.slot;
      uint8_t** bucket = out.bucket.data() + j * stride + 2 * g.table;
      uint64_t** mask = out.mask.data() + j * stride + 2 * g.table;
      for (unsigned half = 0; half < 2; ++half) {
        const size_t b = static_cast<size_t>(
            ApplyRadixIndexMap(t[half], g.index_bits, g.radix, g.index_bits));
        bucket[half] = g.data + b * bucket_bytes;
        mask[half] = g.masks + b;
      }
    }
  }
}

// One lane's chosen candidate for cascade entry `table`: SelectProbeTarget over
// the lane's own pair.
INLINE ProbeTarget SelectLaneProbeTarget(const BatchProbeScratch& s,
                                         size_t lane, size_t table,
                                         bool use_dummy) {
  const uint8_t* const* bucket = s.LaneBuckets(lane) + 2 * table;
  const uint64_t* const* mask = s.LaneMasks(lane) + 2 * table;
  ProbeTarget t;
  t.bucket = reinterpret_cast<uint8_t*>(core::obliSelectU64(
      reinterpret_cast<uintptr_t>(bucket[0]),
      reinterpret_cast<uintptr_t>(bucket[1]), use_dummy));
  t.mask = reinterpret_cast<uint64_t*>(core::obliSelectU64(
      reinterpret_cast<uintptr_t>(mask[0]),
      reinterpret_cast<uintptr_t>(mask[1]), use_dummy));
  return t;
}

// ---------------------------------------------------------------------------
// The dense wave
// ---------------------------------------------------------------------------
//
// Every lane of a chunk scans the SAME dense bucket, so the work a dense table
// costs a chunk need not be m times the work it costs one access.  The key
// lines are loaded once and matched against every lane from registers, and the
// value lines are extracted for ALL lanes at once: one VPERMB per value line
// with the lanes' matched slots as the index vector yields one byte per lane,
// which is blended into a SLICED accumulator (line v, lane j at byte j) under
// the lanes' take mask.  Seventeen permutes and blends per bucket for a whole
// chunk, where the per-lane extract costs about nine permutes per lane.
//
// The slot vector and the take mask are secrets in registers; the slot array
// is written and read at PUBLIC lane indices; every line of the bucket and of
// the accumulator is loaded and stored whole.

// XorOrTree8 over key lines already in registers.
INLINE __m512i XorOrTree8Regs(const __m512i* lines, uint64_t word) {
  __m512i x[8];
  for (int i = 0; i < 8; ++i) {
    x[i] = _mm512_xor_si512(
        lines[i], _mm512_set1_epi8(static_cast<char>(word >> (8 * i))));
  }
  const __m512i t0 = _mm512_ternarylogic_epi64(x[0], x[1], x[2], 0xFE);
  const __m512i t1 = _mm512_ternarylogic_epi64(x[3], x[4], x[5], 0xFE);
  const __m512i t2 = _mm512_ternarylogic_epi64(x[6], x[7], t0, 0xFE);
  return _mm512_or_si512(t1, t2);
}

// MatchMaskByteSlicedTree with the bucket's key lines in `lines` (key_bytes of
// them). Narrow widths compare only their actual bytes.
INLINE uint64_t MatchMaskFromKeyLines(const __m512i* lines, size_t key_bytes,
                                      uint64_t real_mask, KeyWords key) {
  if (key_bytes == 4) {
    __m512i x[4];
    for (size_t i = 0; i < 4; ++i) {
      x[i] = _mm512_xor_si512(lines[i],
          _mm512_set1_epi8(static_cast<char>(key.w0 >> (8 * i))));
    }
    const __m512i o = _mm512_or_si512(x[3],
        _mm512_ternarylogic_epi64(x[0], x[1], x[2], 0xFE));
    return real_mask & core::obliTestNMask8(o, o);
  }
  if (key_bytes != 8 && key_bytes != 16) {
    uint64_t match = real_mask;
    for (size_t b = 0; b < key_bytes; ++b) {
      const uint64_t word = b < 8 ? key.w0 : key.w1;
      match &= core::obliCmpEqMask8(
          lines[b], _mm512_set1_epi8(static_cast<char>(word >> (8 * (b % 8)))));
    }
    return match;
  }
  __m512i o = XorOrTree8Regs(lines, key.w0);
  if (key_bytes == 16) o = _mm512_or_si512(o, XorOrTree8Regs(lines + 8, key.w1));
  return real_mask & core::obliTestNMask8(o, o);
}

// Extracts `value_lines` lines of `bucket` for every lane at once into
// `sliced` (value_lines x kMaxBatchLanes bytes, 64-byte aligned): byte j of
// line v becomes value byte v of lane j's matched slot `slots[j]`, blended in
// where bit j of `take` is set and left alone otherwise.  `slots` is 64 bytes
// (lanes past the chunk hold anything; `take` excludes them).  Value lines
// start at `key_bytes` lines into the bucket.
INLINE void ExtractDenseWave(const uint8_t* bucket, size_t key_bytes,
                             size_t value_lines, const uint8_t* slots,
                             uint64_t take, uint8_t* sliced) {
  const __m512i idx = core::obliLoad512(slots);
  const __mmask64 k = _cvtu64_mask64(take);
  const uint8_t* value = bucket + key_bytes * kBucketCapacity;
  for (size_t v = 0; v < value_lines; ++v) {
    const __m512i line = core::obliLoad512(value + v * kBucketCapacity);
    const __m512i p = _mm512_permutexvar_epi8(idx, line);
    uint8_t* const acc = sliced + v * kMaxBatchLanes;
    const __m512i cur = core::obliLoad512(acc);
    _mm512_store_si512(reinterpret_cast<void*>(acc),
                       core::obliPin512(_mm512_mask_mov_epi8(cur, k, p)));
  }
}

// ---------------------------------------------------------------------------
// Forwarding
// ---------------------------------------------------------------------------

// Byte `lane` of one sliced 64-byte line, read with a REGISTER permute so the
// secret lane index never addresses memory.  `line` must be 64-byte aligned.
INLINE uint8_t SlicedLaneByte(const uint8_t* line, uint64_t lane) {
  const __m512i l = core::obliLoad512(line);
  const __m512i p = _mm512_permutexvar_epi8(
      _mm512_set1_epi8(static_cast<char>(lane)), l);
  return static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(p)));
}

// The sliced state of the lanes already run: `Lines()` 64-byte lines, one per
// user value byte, then the meta byte (kMetaErased and kMetaUnshadowed), then
// a found byte.  Lane
// j's state occupies column j of every line and is written by public index
// once lane j has run; a lane only ever reads columns of EARLIER lanes (its
// `prev`), so nothing needs clearing between chunks.
struct BatchForwardState {
  Aligned64Ptr lines;
  Aligned64Ptr proposed;  // one lane's value input, saved before its output
  size_t user_value_bytes = 0;

  // One line per user value byte, then the meta line, then the found line.
  // The static form is for a byte bill that prices a state it has not built.
  static size_t Lines(size_t value_bytes) { return value_bytes + 2; }
  size_t Lines() const { return Lines(user_value_bytes); }
  size_t MetaLine() const { return user_value_bytes; }
  size_t FoundLine() const { return user_value_bytes + 1; }
  uint8_t* Line(size_t l) { return lines.get() + l * kMaxBatchLanes; }
  const uint8_t* Line(size_t l) const { return lines.get() + l * kMaxBatchLanes; }

  void Resize(size_t value_bytes) {
    user_value_bytes = value_bytes;
    const size_t bytes = CheckedSizeMul(
        CheckedSizeAdd(value_bytes, 2, "forward lines"), kMaxBatchLanes,
        "forward bytes");
    lines = AllocateAligned64(bytes);
    std::memset(lines.get(), 0, bytes);
    proposed = AllocateAligned64(value_bytes);
  }
};

// What one lane hands to the insert phase: the entry it leaves behind.
struct BatchLaneInsert {
  uint8_t* value = nullptr;   // user_value_bytes, caller-owned scratch
  bool erased = false;        // the tombstone bit of the entry
  // The unshadowed qualifier the serial access would give it
  // (kMetaUnshadowed): a tombstone, and the state the lane saw was no copy at
  // all or an unshadowed tombstone.  Only a tombstone carries it.
  bool unshadowed = false;
};

// Runs lane j of the forwarding chain.
//
// `probe` is the lane's own probe result -- `user_value_bytes` value bytes
// followed by the meta byte, zeros throughout on a miss -- with byte v at
// `probe[v * probe_stride]`: stride 1 reads a contiguous row, stride
// kMaxBatchLanes reads column j of a sliced accumulator (`probe` then points
// at the lane's column of line 0; j is public, so the byte loads are at
// public addresses either way).  `probe_found` is its found flag; both are
// garbage for a duplicate lane, whose state comes from `state` column `prev`
// instead.  `dup` and `prev` are secret; `op`, `insert`, `value_in`,
// `value_out` and `j` are public.
//
// Writes the lane's answer -- the value BEFORE its own operation, zeros when
// absent or erased -- into `value_out` when that is non-null, returns whether
// the key was present and not erased before the lane ran, fills `insert`
// with the entry the lane leaves (exactly what ReadStored / WriteStored /
// EraseStored / ExchangeStored would insert), and records that entry as
// column j of `state`.  Every byte is written whatever the secrets say; the
// choices are CMOVs and byte blends.
INLINE bool ForwardBatchLane(BatchOp op, bool insert_if_absent,
                             const uint8_t* probe, size_t probe_stride,
                             uint64_t probe_found, bool dup, uint64_t prev,
                             const uint8_t* value_in, uint8_t* value_out,
                             size_t j, BatchForwardState& state,
                             BatchLaneInsert* out) {
  const size_t n = state.user_value_bytes;
  // The operation is public. Snapshot before writing value_out so a write
  // or exchange can return the old value through its own input buffer, even
  // with partial overlap. One allocation at construction, no per-lane growth.
  if (op == BatchOp::kWrite || op == BatchOp::kReadThenWrite ||
      op == BatchOp::kExchange) {
    std::memcpy(state.proposed.get(), value_in, n);
  }
  // S: the state this lane sees.  Its own probe unless it repeats an earlier
  // lane, in which case the entry that lane left.
  const uint64_t forwarded_found =
      SlicedLaneByte(state.Line(state.FoundLine()), prev) & 1u;
  const uint64_t s_found =
      core::obliSelectU64(probe_found & 1u, forwarded_found, dup);
  const uint64_t forwarded_meta = SlicedLaneByte(state.Line(state.MetaLine()), prev);
  const uint64_t s_meta =
      core::obliSelectU64(probe[n * probe_stride], forwarded_meta, dup);
  const uint64_t s_erased = static_cast<uint64_t>((s_meta & kMetaErased) != 0);
  const uint64_t s_unshadowed =
      static_cast<uint64_t>((s_meta & kMetaUnshadowed) != 0);
  // Present iff found and not a tombstone.  Bitwise: both flags are secret.
  const uint64_t present = s_found & (s_erased ^ 1u);

  uint8_t* const a = out->value;
  for (size_t v = 0; v < n; ++v) {
    const uint64_t forwarded = SlicedLaneByte(state.Line(v), prev);
    a[v] = static_cast<uint8_t>(
        core::obliSelectU64(probe[v * probe_stride], forwarded, dup));
  }
  // a[] now holds S.value: the found value, or zeros for a miss or a
  // tombstone (a tombstone stores zeros, and a probe row is zeros on a miss).
  if (value_out != nullptr) std::memcpy(value_out, a, n);

  uint64_t a_erased = 0;
  switch (op) {
    case BatchOp::kRead:
      // ReadStored: re-insert what was found, as a tombstone when the key was
      // absent or already erased.
      a_erased = s_erased | (s_found ^ 1u);
      break;
    case BatchOp::kWrite:
    case BatchOp::kReadThenWrite:
      std::memcpy(a, state.proposed.get(), n);
      a_erased = 0;
      break;
    case BatchOp::kErase:
      std::memset(a, 0, n);
      a_erased = 1;
      break;
    case BatchOp::kExchange: {
      // ExchangeStored: the proposed value iff present or inserting,
      // otherwise what the probe left (zeros) as a tombstone.
      const uint64_t store = present | static_cast<uint64_t>(insert_if_absent);
      core::obliAssignBytes(a, state.proposed.get(), n, store);
      a_erased = store ^ 1u;
      break;
    }
  }
  // The serial access's qualifier (the level arena engine's NoOlderLiveCopy):
  // a tombstone over no copy, or over an unshadowed tombstone.  Forwarded with
  // the entry, so a repeated key inherits it lane by lane exactly as repeated
  // serial accesses do.
  const uint64_t a_unshadowed =
      a_erased & ((s_found ^ 1u) | (s_erased & s_unshadowed));
  out->erased = a_erased != 0;
  out->unshadowed = a_unshadowed != 0;
  // Column j of the state, by PUBLIC index: what the next equal-key lane sees.
  for (size_t v = 0; v < n; ++v) state.Line(v)[j] = a[v];
  state.Line(state.MetaLine())[j] = static_cast<uint8_t>(
      ((0u - static_cast<unsigned>(a_erased)) & kMetaErased) |
      ((0u - static_cast<unsigned>(a_unshadowed)) & kMetaUnshadowed));
  state.Line(state.FoundLine())[j] = 1;  // an entry now exists, tombstone or not
  return present != 0;
}

// The contiguous-row form: `probe_row` is value bytes then meta.
INLINE bool ForwardBatchLane(BatchOp op, bool insert_if_absent,
                             const uint8_t* probe_row, uint64_t probe_found,
                             bool dup, uint64_t prev, const uint8_t* value_in,
                             uint8_t* value_out, size_t j,
                             BatchForwardState& state, BatchLaneInsert* out) {
  return ForwardBatchLane(op, insert_if_absent, probe_row, 1, probe_found, dup,
                          prev, value_in, value_out, j, state, out);
}

}  // namespace byteslice
}  // namespace microram
