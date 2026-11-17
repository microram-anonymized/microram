#pragma once

// Value-plane primitives (table DESIGN.md, "Scalar value columns"): extract a
// public [begin, end) range of a bucket's value byte lines for a secret slot
// (used only as a register permute index), or write such a range to a public
// stash slot, so the work on a wide value can be split across value workers
// by column range.
// Fixed public column ranges. Secret slot/take operands stay in registers;
// in particular an unsuccessful take must never suppress a memory load.
#include "src/oram/table/cpu_byteslice_probe.hpp"

namespace microram::byteslice {

enum class ValueKernel { kAuto, kAccumulate, kPermute };

INLINE void ExtractValueRange(const uint8_t* bucket, size_t key_bytes,
                              size_t begin, size_t end, unsigned slot,
                              uint8_t* out) {
  uint64_t sink = 0;
  const Layout range{0, end - begin, 0};
  // The permute primitive only uses tzcnt(match), and writes its
  // public number of output bytes. A dummy match names slot zero as usual.
  ExtractValueAndClearRealMaskByteSlicedPermute<false>(
      const_cast<uint8_t*>(bucket + (key_bytes + begin) * kBucketCapacity),
      &sink, range, uint64_t{1} << slot, out);
}

INLINE uint8_t ExtractMeta(const uint8_t* bucket, const Layout& layout,
                           uint64_t match) {
  const __m512i line = _mm512_load_si512(bucket + layout.MetaLine() * 64);
  const __m512i index = _mm512_set1_epi8(static_cast<char>(_tzcnt_u64(match)));
  return static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(
      _mm512_permutexvar_epi8(index, line))));
}

INLINE void WriteValueRange(uint8_t* bucket, size_t key_bytes, size_t slot,
                            size_t begin, size_t end, const uint8_t* bytes) {
  for (size_t l = begin; l < end; ++l)
    bucket[(key_bytes + l) * 64 + slot] = bytes[l - begin];
}

template <size_t Lines>
struct ValueAccumulator {
  __m512i line[Lines == 0 ? 1 : Lines];
  // Unrolled before scalar replacement, so `line` lives in registers rather
  // than in a stack array reloaded around every blend.
  ValueAccumulator() {
#pragma GCC unroll 32
    for (size_t l = 0; l < Lines; ++l) line[l] = _mm512_setzero_si512();
  }
  INLINE void Blend(const uint8_t* values, uint64_t take) {
#pragma GCC unroll 32
    for (size_t l = 0; l < Lines; ++l) {
      const __m512i loaded = _mm512_load_si512(values + l * 64);
      line[l] = core::obliMaskMov8(line[l], 0 - take, loaded);
    }
  }
  INLINE void Finish(unsigned slot, uint8_t* out) {
    const __m512i idx = _mm512_add_epi8(_mm512_set1_epi16(0x4000),
        _mm512_set1_epi8(static_cast<char>(slot)));
    size_t l = 0;
#pragma GCC unroll 32
    for (; l + 1 < Lines; l += 2) {
      const __m512i p = _mm512_permutex2var_epi8(line[l], idx, line[l + 1]);
      const uint32_t bytes = _mm_cvtsi128_si32(_mm512_castsi512_si128(p));
      std::memcpy(out + l, &bytes, 2);
    }
    if (l < Lines) out[l] = static_cast<uint8_t>(_mm_cvtsi128_si32(
        _mm512_castsi512_si128(_mm512_permutexvar_epi8(idx, line[l]))));
  }
};

}  // namespace microram::byteslice
