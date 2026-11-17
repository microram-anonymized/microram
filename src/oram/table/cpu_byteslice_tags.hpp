#pragma once

// Routing tags: the AES-128 PRF that decides where an entry goes, and the
// register-resident gather that feeds it.
//
// A rebuild assigns each entry the low 64 bits of fixed two-block CBC-MAC over
// its labeled routing identity and complete stored key. The butterfly routes
// on that tag's bits. Re-hashing under a fresh nonce
// at every rebuild is what stops a bucket index from meaning anything across
// rebuilds.
//
// The expensive half is not the AES.  Byte line l of a bucket holds key byte l
// of all 64 entries, so assembling 64 contiguous AES inputs is an 8x64 byte
// TRANSPOSE.  Doing it the obvious way -- 64 strided 8-byte scalar loads --
// dominates the tag phase, more than the AES itself, because of the
// store-to-load forwarding it puts on the critical path.  The code therefore
// uses a register-resident transpose (Transpose8x8Index and a fixed permute
// sequence, no memory round trip) and runs eight independent AES chains.
//
// Eight chains, not four, because VAESENC is latency-bound at one chain and
// its throughput keeps rising up to about eight independent chains; four
// leaves the pipeline about half idle.  Two code paths exist -- VAES with 512-bit registers, 4 blocks per
// instruction (Ice Lake+ / Zen 4+), and an 8-way pipelined xmm AES-NI fallback
// -- and they produce bit-identical tags.  Both go through one interleave step
// so the wide path can consume the same block layout as the narrow one.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>

#include "src/core/mov_intrinsics.hpp"
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_budget.hpp"

// VAES with 512-bit registers (4 AES blocks per instruction). GCC defines
// __VAES__ when -mvaes is passed (or -march=native finds it). Override with
// -DMICRORAM_BYTESLICE_USE_VAES=0 to force the 8-way pipelined xmm AES-NI
// fallback.
#ifndef MICRORAM_BYTESLICE_USE_VAES
#if defined(__VAES__)
#define MICRORAM_BYTESLICE_USE_VAES 1
#else
#define MICRORAM_BYTESLICE_USE_VAES 0
#endif
#endif

namespace microram {
namespace byteslice {

// vpermb index that transposes an 8x8 byte matrix held in one zmm register
// (row-major 8 rows of 8 bytes -> column-major).  Used by
// dense key matching; the tag phase's own gather is GatherBucketKeys below.
inline __m512i Transpose8x8Index() {
  alignas(64) uint8_t idx[64];
  for (int e = 0; e < 8; ++e) {
    for (int l = 0; l < 8; ++l) {
      idx[e * 8 + l] = static_cast<uint8_t>(l * 8 + e);
    }
  }
  return _mm512_load_si512(reinterpret_cast<const void*>(idx));
}

// ---------------------------------------------------------------------------
// Key gather: 8 key byte lines -> 64 packed keys, entirely in registers
// ---------------------------------------------------------------------------
//
// Byte line l of a bucket holds key byte l of all 64 entries, so building the
// AES inputs is an 8x64 byte transpose.  Doing it with strided 8-byte scalar
// loads into a stack buffer (one VPERMB per 8 entries) costs ~72 loads and
// ~72 stores per bucket and puts store-to-load forwarding on the critical
// path, which costs more than the AES itself.  Three lane-local unpack stages plus a 4x4 128-bit-lane transpose
// do the same job in 8 loads and 40 shuffles with nothing touching memory.
//
// keys_out[m] receives entries 8m..8m+7 as eight qwords, so the pipeline
// downstream (AES, tag scatter) keeps its natural entry order.  Key bytes
// past key_bytes are zero, matching a scalar gather.
// The shuffle half of GatherBucketKeys, on eight already-loaded key byte lines
// (l[i] = key byte i of all 64 entries; lines past key_bytes must be zero).
// Split out so callers that have to preprocess the lines first -- the
// cross-source dedup zeroes the key bytes of dummy slots -- reuse the network
// instead of round-tripping keys through memory.
//
// The three unpack stages alone leave d[j] lane q holding entries 16q+2j and
// 16q+2j+1 (qword 2q+t of d[j] is slot 16q+2j+t).  That is all a side needs
// when it is only read as a set, or when its answer is placed back in slot
// order by that map (AllPairsMatchMaskQ), so it is split out as well.
INLINE void UnpackKeyLinesToQwords(const __m512i* l, __m512i* d) {
  // Stage 1: pair key bytes (l0,l1), (l2,l3), (l4,l5), (l6,l7).  Each 128-bit
  // lane covers 16 entries; lo takes the lane's first 8, hi its last 8.
  const __m512i b0 = _mm512_unpacklo_epi8(l[0], l[1]);
  const __m512i b1 = _mm512_unpackhi_epi8(l[0], l[1]);
  const __m512i b2 = _mm512_unpacklo_epi8(l[2], l[3]);
  const __m512i b3 = _mm512_unpackhi_epi8(l[2], l[3]);
  const __m512i b4 = _mm512_unpacklo_epi8(l[4], l[5]);
  const __m512i b5 = _mm512_unpackhi_epi8(l[4], l[5]);
  const __m512i b6 = _mm512_unpacklo_epi8(l[6], l[7]);
  const __m512i b7 = _mm512_unpackhi_epi8(l[6], l[7]);
  // Stage 2: quads (l0..l3) and (l4..l7).
  const __m512i c0 = _mm512_unpacklo_epi16(b0, b2);
  const __m512i c1 = _mm512_unpackhi_epi16(b0, b2);
  const __m512i c2 = _mm512_unpacklo_epi16(b1, b3);
  const __m512i c3 = _mm512_unpackhi_epi16(b1, b3);
  const __m512i c4 = _mm512_unpacklo_epi16(b4, b6);
  const __m512i c5 = _mm512_unpackhi_epi16(b4, b6);
  const __m512i c6 = _mm512_unpacklo_epi16(b5, b7);
  const __m512i c7 = _mm512_unpackhi_epi16(b5, b7);
  // Stage 3: whole keys.
  d[0] = _mm512_unpacklo_epi32(c0, c4);
  d[1] = _mm512_unpackhi_epi32(c0, c4);
  d[2] = _mm512_unpacklo_epi32(c1, c5);
  d[3] = _mm512_unpackhi_epi32(c1, c5);
  d[4] = _mm512_unpacklo_epi32(c2, c6);
  d[5] = _mm512_unpackhi_epi32(c2, c6);
  d[6] = _mm512_unpacklo_epi32(c3, c7);
  d[7] = _mm512_unpackhi_epi32(c3, c7);
}

INLINE void TransposeKeyLinesToQwords(const __m512i* l, __m512i* keys_out) {
  __m512i d[8];
  UnpackKeyLinesToQwords(l, d);
  // The unpacks are lane-local, so entries are still interleaved across the
  // four 128-bit lanes: a 4x4 lane transpose of {d0..d3} and of {d4..d7}
  // (two VSHUFI64X2 stages each) puts entry 8m+i back in keys_out[m] qword i.
  const __m512i e0 = _mm512_shuffle_i64x2(d[0], d[1], 0x88);
  const __m512i e1 = _mm512_shuffle_i64x2(d[0], d[1], 0xDD);
  const __m512i e2 = _mm512_shuffle_i64x2(d[2], d[3], 0x88);
  const __m512i e3 = _mm512_shuffle_i64x2(d[2], d[3], 0xDD);
  const __m512i e4 = _mm512_shuffle_i64x2(d[4], d[5], 0x88);
  const __m512i e5 = _mm512_shuffle_i64x2(d[4], d[5], 0xDD);
  const __m512i e6 = _mm512_shuffle_i64x2(d[6], d[7], 0x88);
  const __m512i e7 = _mm512_shuffle_i64x2(d[6], d[7], 0xDD);
  keys_out[0] = _mm512_shuffle_i64x2(e0, e2, 0x88);
  keys_out[2] = _mm512_shuffle_i64x2(e1, e3, 0x88);
  keys_out[4] = _mm512_shuffle_i64x2(e0, e2, 0xDD);
  keys_out[6] = _mm512_shuffle_i64x2(e1, e3, 0xDD);
  keys_out[1] = _mm512_shuffle_i64x2(e4, e6, 0x88);
  keys_out[3] = _mm512_shuffle_i64x2(e5, e7, 0x88);
  keys_out[5] = _mm512_shuffle_i64x2(e4, e6, 0xDD);
  keys_out[7] = _mm512_shuffle_i64x2(e5, e7, 0xDD);
}

// Eight consecutive key byte lines starting at `first_line`, transposed.  A
// stored key of at most 8 bytes needs only first_line = 0; a 16-byte one is two
// calls, the second producing the key's high words (see kMaxKeyBytes).  Lines
// past key_bytes read as zero, so a width that is not a multiple of 8 needs no
// special case anywhere downstream.
//
// The loads are pinned (obliLoad512) only to keep them loads: plain ones let
// GCC turn the loop into a memcpy@PLT of the present lines into a zeroed
// stack buffer and reload all eight from it.
inline void GatherBucketKeyLines(const uint8_t* bucket, size_t first_line,
                                 size_t key_bytes, __m512i* keys_out) {
  __m512i l[8];
  for (size_t i = 0; i < 8; ++i) {
    const size_t line = first_line + i;
    l[i] = line < key_bytes
               ? core::obliLoad512(bucket + line * kBucketCapacity)
               : _mm512_setzero_si512();
  }
  TransposeKeyLinesToQwords(l, keys_out);
}

inline void GatherBucketKeys(const uint8_t* bucket, size_t key_bytes,
                             __m512i* keys_out) {
  GatherBucketKeyLines(bucket, 0, key_bytes, keys_out);
}

// The round keys in the form each AES path wants them, built once per ORAM
// (the PRF key is per-instance and secret, so it cannot be a file-scope
// constant folded into the kernels).  Under VAES the round keys are
// memory operands of the VAESENC, so they are pre-broadcast to zmm here rather
// than four times per bucket.
//
// 64-byte aligned and heap-allocated by MakeAesTagKeys: an object with __m512i
// members must not land on a stack slot the ABI only guarantees to 16 bytes
// (see the MinGW note in CMakeLists.txt).
struct alignas(64) AesTagKeys {
  __m128i rk[11];
#if MICRORAM_BYTESLICE_USE_VAES
  __m512i rk512[11];
#endif
  // Null for standalone kernels; every hierarchy schedule shares its engine's
  // allowance across requester, value, batch and rebuild threads.
  RoutingEvaluationBudget* budget = nullptr;

  AesTagKeys() : AesTagKeys(crypto::FixedAesRoundKeys()) {}
  explicit AesTagKeys(const crypto::AesRoundKeys& keys,
                      RoutingEvaluationBudget* allowance = nullptr)
      : budget(allowance) {
    for (int r = 0; r < 11; ++r) {
      rk[r] = keys.rk[r];
#if MICRORAM_BYTESLICE_USE_VAES
      rk512[r] = _mm512_broadcast_i32x4(keys.rk[r]);
#endif
    }
  }

  void ReserveEvaluations(uint64_t count) const {
    if (budget != nullptr) budget->Reserve(count);
  }

  size_t ReserveInterleaved(size_t count) const {
    if (count > std::numeric_limits<size_t>::max() - 3) {
      if (budget != nullptr) budget->Refuse();
      throw std::overflow_error("routing: padded evaluation count overflow");
    }
    const size_t rounded = (count + 3) & ~size_t{3};
    ReserveEvaluations(rounded);
    return rounded;
  }
};

// The fixed-key schedule, for every caller that has not been given one: the
// standalone rebuild kernels and their tests and benchmarks.
inline const AesTagKeys& DefaultAesTagKeys() {
  static const AesTagKeys keys;
  return keys;
}

inline std::unique_ptr<AesTagKeys> MakeAesTagKeys(
    const crypto::AesRoundKeys& keys,
    RoutingEvaluationBudget* budget = nullptr) {
  return std::make_unique<AesTagKeys>(keys, budget);
}

#if MICRORAM_BYTESLICE_USE_VAES
// Second CBC blocks, 4 blocks per zmm register, EIGHT independent chains
// (32 stored keys) in flight. The first CBC state is shared by the group. Tag
// register m holds the low 8 bytes of the ciphertext for entries 8m..8m+7,
// matching crypto::AesCtrTagU128WordsHost.
//
// `keys_hi` is the stored key's high words, or null when the key fits 8 bytes
// -- both forms use the same two-block message format.
//
// Eight chains, not four: one VAESENC zmm chain is latency-bound (several
// cycles per round), throughput scales with independent chains up to about
// eight, four chains leave it well short of peak, and more chains add only
// register pressure, so eight is the knee.  The round keys stay memory
// operands of the VAESENC so all eight states fit comfortably in registers.
// 32 keys (4 registers) -> 32 tags (4 registers), 8 chains.  Half a bucket at
// a time, because GCC hoists all 11 round keys into registers: with all 8 tag
// registers live across the whole bucket that costs 8 spill-stores and 16
// reloads per bucket, and halving the tag live range removes them.
inline void AesBatch32Regs(const __m512i* keys, const __m512i* keys_hi,
                           uint64_t high_word, __m512i* tags,
                           const AesTagKeys& rks = DefaultAesTagKeys()) {
  rks.ReserveEvaluations(32);
  const __m512i prefix = _mm512_broadcast_i32x4(
      crypto::AesRoutingPrefixHost(high_word, rks.rk));
  // permutex2var qword selectors: 0-7 pick from the key register, 8-15 from
  // the block's high halves. A 128-bit AES lane is (low qword = entry key's low
  // word, high qword = key's high word). interleave_hi takes indices
  // 12-15 rather than 8-11 because the high halves are per-entry once the key
  // is wide; against a broadcast the two spellings are the same permutation.
  const __m512i interleave_lo = _mm512_set_epi64(11, 3, 10, 2, 9, 1, 8, 0);
  const __m512i interleave_hi = _mm512_set_epi64(15, 7, 14, 6, 13, 5, 12, 4);
  const __m512i gather_tags = _mm512_set_epi64(14, 12, 10, 8, 6, 4, 2, 0);
  __m512i s[8];
  for (int j = 0; j < 4; ++j) {
    const __m512i hx = keys_hi != nullptr ? keys_hi[j] : _mm512_setzero_si512();
    s[2 * j] = _mm512_permutex2var_epi64(keys[j], interleave_lo, hx);
    s[2 * j + 1] = _mm512_permutex2var_epi64(keys[j], interleave_hi, hx);
  }
  const __m512i initial = _mm512_xor_si512(prefix, rks.rk512[0]);
  for (int j = 0; j < 8; ++j) s[j] = _mm512_xor_si512(s[j], initial);
  for (int r = 1; r < 10; ++r) {
    for (int j = 0; j < 8; ++j) s[j] = _mm512_aesenc_epi128(s[j], rks.rk512[r]);
  }
  for (int j = 0; j < 8; ++j) {
    s[j] = _mm512_aesenclast_epi128(s[j], rks.rk512[10]);
  }
  for (int j = 0; j < 4; ++j) {
    tags[j] = _mm512_permutex2var_epi64(s[2 * j], gather_tags, s[2 * j + 1]);
  }
}

inline void AesBatch64Regs(const __m512i* keys, const __m512i* keys_hi,
                           uint64_t high_word, __m512i* tags,
                           const AesTagKeys& rks = DefaultAesTagKeys()) {
  AesBatch32Regs(keys, keys_hi, high_word, tags, rks);
  AesBatch32Regs(keys + 4, keys_hi != nullptr ? keys_hi + 4 : nullptr,
                 high_word, tags + 4, rks);
}

// Variable-identity routing messages: four qwords each, containing
// [packed identity, kAesRoutingLabel, stored low, stored high]. Every message
// has exactly two CBC blocks, including narrow keys and dummy counters.
// tags[j] receives the low 8 final ciphertext bytes, matching the scalar
// AesCtrTagU128WordsHost. The message bytes are independent of the secret key.
//
// The caller must round `blocks` up to a multiple of 4 messages (16 qwords)
// and size `tags` to that same multiple; padding messages may hold anything.
inline void AesTagsInterleaved(const uint64_t* blocks, size_t num_blocks,
                               uint64_t* tags,
                               const AesTagKeys& rks = DefaultAesTagKeys()) {
  // Even qwords of a pair of ciphertext registers = eight consecutive tags.
  const __m512i gather = _mm512_set_epi64(14, 12, 10, 8, 6, 4, 2, 0);
  const size_t nz = rks.ReserveInterleaved(num_blocks) / 4;
  const __m512i first = _mm512_set_epi64(13, 12, 9, 8, 5, 4, 1, 0);
  const __m512i second = _mm512_set_epi64(15, 14, 11, 10, 7, 6, 3, 2);
  size_t z = 0;
  // Eight chains is the VAESENC throughput knee (see AesBatch32Regs).
  for (; z + 8 <= nz; z += 8) {
    __m512i s[8];
    for (int j = 0; j < 8; ++j) {
      const uint64_t* m = blocks + 16 * (z + j);
      s[j] = _mm512_xor_si512(_mm512_permutex2var_epi64(
          _mm512_loadu_si512(m), first, _mm512_loadu_si512(m + 8)),
          rks.rk512[0]);
    }
    for (int r = 1; r < 10; ++r) {
      for (int j = 0; j < 8; ++j) {
        s[j] = _mm512_aesenc_epi128(s[j], rks.rk512[r]);
      }
    }
    for (int j = 0; j < 8; ++j) {
      s[j] = _mm512_aesenclast_epi128(s[j], rks.rk512[10]);
      const uint64_t* m = blocks + 16 * (z + j);
      s[j] = _mm512_xor_si512(s[j], _mm512_xor_si512(rks.rk512[0],
          _mm512_permutex2var_epi64(_mm512_loadu_si512(m), second,
                                    _mm512_loadu_si512(m + 8))));
    }
    for (int r = 1; r < 10; ++r) {
      for (int j = 0; j < 8; ++j) {
        s[j] = _mm512_aesenc_epi128(s[j], rks.rk512[r]);
      }
    }
    for (int j = 0; j < 8; ++j) {
      s[j] = _mm512_aesenclast_epi128(s[j], rks.rk512[10]);
    }
    for (int j = 0; j < 4; ++j) {
      _mm512_storeu_si512(
          reinterpret_cast<void*>(tags + 4 * (z + 2 * j)),
          _mm512_permutex2var_epi64(s[2 * j], gather, s[2 * j + 1]));
    }
  }
  // Tail: independent single-register chains, so out-of-order still overlaps
  // them even though each is latency-bound on its own.
  const __m512i gather4 = _mm512_set_epi64(0, 0, 0, 0, 6, 4, 2, 0);
  for (; z < nz; ++z) {
    const __m512i a = _mm512_loadu_si512(blocks + 16 * z);
    const __m512i b = _mm512_loadu_si512(blocks + 16 * z + 8);
    __m512i s = _mm512_xor_si512(
        _mm512_permutex2var_epi64(a, first, b), rks.rk512[0]);
    for (int r = 1; r < 10; ++r) s = _mm512_aesenc_epi128(s, rks.rk512[r]);
    s = _mm512_aesenclast_epi128(s, rks.rk512[10]);
    s = _mm512_xor_si512(s, _mm512_xor_si512(rks.rk512[0],
        _mm512_permutex2var_epi64(a, second, b)));
    for (int r = 1; r < 10; ++r) s = _mm512_aesenc_epi128(s, rks.rk512[r]);
    s = _mm512_aesenclast_epi128(s, rks.rk512[10]);
    _mm256_storeu_si256(
        reinterpret_cast<__m256i*>(tags + 4 * z),
        _mm512_castsi512_si256(_mm512_permutexvar_epi64(gather4, s)));
  }
}
#else
// Variable-nonce tags, xmm fallback: four independent chains, which is all the
// compatibility path needs (see the VAES version for the contract).
inline void AesTagsInterleaved(const uint64_t* blocks, size_t num_blocks,
                               uint64_t* tags,
                               const AesTagKeys& rks = DefaultAesTagKeys()) {
  const __m128i* rk = rks.rk;
  const size_t rounded = rks.ReserveInterleaved(num_blocks);
  for (size_t g = 0; g < rounded; g += 4) {
    __m128i s[4];
    for (int j = 0; j < 4; ++j) {
      s[j] = _mm_xor_si128(
          _mm_loadu_si128(
              reinterpret_cast<const __m128i*>(blocks + 4 * (g + j))),
          rk[0]);
    }
    for (int r = 1; r < 10; ++r) {
      for (int j = 0; j < 4; ++j) s[j] = _mm_aesenc_si128(s[j], rk[r]);
    }
    for (int j = 0; j < 4; ++j) {
      s[j] = _mm_aesenclast_si128(s[j], rk[10]);
      s[j] = _mm_xor_si128(s[j], _mm_xor_si128(rk[0], _mm_loadu_si128(
          reinterpret_cast<const __m128i*>(blocks + 4 * (g + j) + 2))));
    }
    for (int r = 1; r < 10; ++r) {
      for (int j = 0; j < 4; ++j) s[j] = _mm_aesenc_si128(s[j], rk[r]);
    }
    for (int j = 0; j < 4; ++j) {
      s[j] = _mm_aesenclast_si128(s[j], rk[10]);
      tags[g + j] = static_cast<uint64_t>(_mm_cvtsi128_si64(s[j]));
    }
  }
}

// Register-form wrappers over the xmm fallback: the compatibility path is not
// worth vectorizing further, so it round-trips through the stack.  `keys_hi`
// is the stored key's high words, or null when the key fits 8 bytes.
inline void AesBatch32Regs(const __m512i* keys, const __m512i* keys_hi,
                           uint64_t high_word, __m512i* tags,
                           const AesTagKeys& rks = DefaultAesTagKeys()) {
  rks.ReserveEvaluations(32);
  alignas(64) uint64_t k[kBucketCapacity / 2];
  alignas(64) uint64_t kh[kBucketCapacity / 2] = {};
  alignas(64) uint64_t t[kBucketCapacity / 2];
  for (int i = 0; i < 4; ++i) {
    _mm512_store_si512(reinterpret_cast<void*>(k + 8 * i), keys[i]);
    if (keys_hi != nullptr) {
      _mm512_store_si512(reinterpret_cast<void*>(kh + 8 * i), keys_hi[i]);
    }
  }
  const __m128i* rk = rks.rk;
  const __m128i initial = _mm_xor_si128(
      crypto::AesRoutingPrefixHost(high_word, rk), rk[0]);
  for (int g = 0; g < 32; g += 8) {
    __m128i s[8];
    for (int j = 0; j < 8; ++j) {
      s[j] = _mm_xor_si128(
          _mm_set_epi64x(static_cast<long long>(kh[g + j]),
                         static_cast<long long>(k[g + j])),
          initial);
    }
    for (int r = 1; r < 10; ++r) {
      for (int j = 0; j < 8; ++j) s[j] = _mm_aesenc_si128(s[j], rk[r]);
    }
    for (int j = 0; j < 8; ++j) {
      s[j] = _mm_aesenclast_si128(s[j], rk[10]);
      t[g + j] = static_cast<uint64_t>(_mm_cvtsi128_si64(s[j]));
    }
  }
  for (int i = 0; i < 4; ++i) {
    tags[i] = _mm512_load_si512(reinterpret_cast<const void*>(t + 8 * i));
  }
}

inline void AesBatch64Regs(const __m512i* keys, const __m512i* keys_hi,
                           uint64_t high_word, __m512i* tags,
                           const AesTagKeys& rks = DefaultAesTagKeys()) {
  AesBatch32Regs(keys, keys_hi, high_word, tags, rks);
  AesBatch32Regs(keys + 4, keys_hi != nullptr ? keys_hi + 4 : nullptr,
                 high_word, tags + 4, rks);
}
#endif  // MICRORAM_BYTESLICE_USE_VAES

}  // namespace byteslice
}  // namespace microram
