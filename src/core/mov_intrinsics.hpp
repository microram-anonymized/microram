#pragma once

// Register-only selection for oblivious access kernels.
//
// The ORAM's obliviousness argument requires that the instruction and memory
// trace of an access be a function of public data alone.  A branch on a secret
// -- "is this the real probe or a dummy?", "did the key match?" -- breaks that
// through the branch predictor, so scalar choices use a register CMOV. This
// fixes the instruction and memory-address sequence; instruction timing is a
// host assumption checked by tests/timing, not a guarantee supplied by C++.
//
// The asm is written by hand rather than left to the compiler because a plain
// ternary is under no obligation to compile to CMOV; at -O2 GCC routinely turns
// one back into a branch when it thinks the condition is predictable.
//
// The vector primitives below exist for the same reason one level up: an
// AVX-512 masked move with a load feeding it is a pattern the compiler is free
// to fuse into ONE masked load, and then the bytes fetched from memory depend
// on the mask.  Where the mask is secret that is a leak, so the loads that
// feed secret masks go through obliLoad512 / obliPin512, which force the value
// into a register first. The secret-masked consumer must also use the
// register-only wrappers below, because GCC may spill a pinned value.

// GCC ONLY: everything below relies on GNU inline-asm register constraints,
// and tests/timing checks only the code GCC emits (CMakeLists.txt).
#if !defined(__GNUC__) || defined(__clang__)
#error "cpu_byteslice_oram builds only with GCC"
#endif

#include <immintrin.h>

#include <cstddef>
#include <cstdint>

namespace microram {
namespace core {

// Forced inlining for the register-only primitives and the kernels built on
// them.  The name is generic, so it is defined here unconditionally (and
// with the same text in monitor_wait.hpp): an INLINE macro the including
// code already has, or an empty -DINLINE=, must not turn these header
// functions into ordinary definitions that collide at link time.  That
// macro is replaced for the rest of the translation unit.
#undef INLINE
#define INLINE inline __attribute__((always_inline))

// val1 = cond ? val2 : val1, without branching on `cond`.
INLINE void CMOV8(const bool& cond, uint64_t& val1, const uint64_t& val2) {
  const uint64_t wide = static_cast<uint64_t>(cond);
  asm volatile(
      "test %[mcond], %[mcond]\n\t"
      "cmovnz %[i2], %[i1]\n\t"
      : [i1] "=r"(val1)
      : [mcond] "r"(wide), "[i1]"(val1), [i2] "r"(val2)
      :);
}

// cond ? take : keep, as an expression.
INLINE uint64_t obliSelectU64(const uint64_t keep, const uint64_t take,
                              const bool cond) {
  uint64_t out = keep;
  CMOV8(cond, out, take);
  return out;
}

// Pins a vector in a register.  An empty asm statement with the value as an
// in/out register operand: the compiler must have the whole vector in a
// register at this point and cannot see through the statement. The original
// load must therefore fetch the whole vector before any later selection.
// The assembly statement emits no instruction.
//
// A pin guarantees that the value was once whole in a register, NOT that a
// later consumer reads a register: GCC may still spill the pinned value and
// fold the reload into the consumer's memory operand.  Where a secret mask
// meets an operand, use the register-only forms below.
INLINE __m512i obliPin512(__m512i v) {
  asm("" : "+v"(v));
  return v;
}

// Secret-masked instructions whose operands are registers BY CONSTRAINT.
//
// GCC turns `secret & _mm512_cmpeq_epi8_mask(x, y)` into one compare with the
// secret as its write mask, and folds whichever operand it has in memory -- a
// bucket line, a set1 constant, a spill slot -- into that compare; a masked
// move, broadcast or expand takes its source from memory the same way.  With a
// secret mask the bytes then read depend on the secret (EVEX fault
// suppression), which src/core/DESIGN.md forbids.  Pinning does not stop it:
// GCC can spill a value pinned right before a VPEXPANDB and fold the reload
// into the VPEXPANDB's memory operand.  Whether the fusion happens depends on
// the caller the function is inlined into, the optimization level and the
// target, so a clean build is no evidence for the next one; the instruction
// census in tests/timing checks the compiled library.  An asm operand
// constrained to "v" must be a register, so a spilled value is first reloaded
// whole by a plain load, and an asm compare is opaque, so a caller's AND
// stays an AND.
//
// LIBRARY CODE WRITES EVERY COMPARE AND TEST THROUGH THESE, never through the
// mask-producing intrinsics.  Each returns its mask as a plain word (bits past
// the lane count are zero); each move merges `a` into `src` under `k`.
#define MICRORAM_OBLI_COMPARE(name, insn)                                    \
  INLINE uint64_t name(__m512i a, __m512i b) {                               \
    __mmask64 k;                                                             \
    asm(insn " %[b], %[a], %[k]" : [k] "=k"(k) : [a] "v"(a), [b] "v"(b));    \
    return _cvtmask64_u64(k);                                                \
  }
MICRORAM_OBLI_COMPARE(obliCmpEqMask8, "vpcmpeqb")
MICRORAM_OBLI_COMPARE(obliCmpEqMask32, "vpcmpeqd")
MICRORAM_OBLI_COMPARE(obliCmpEqMask64, "vpcmpeqq")
MICRORAM_OBLI_COMPARE(obliCmpGtU8Mask, "vpcmpub $6,")  // a > b, unsigned
MICRORAM_OBLI_COMPARE(obliCmpGeU8Mask, "vpcmpub $5,")  // a >= b, unsigned
MICRORAM_OBLI_COMPARE(obliTestMask8, "vptestmb")       // (a & b) != 0
MICRORAM_OBLI_COMPARE(obliTestMask32, "vptestmd")
MICRORAM_OBLI_COMPARE(obliTestMask64, "vptestmq")
MICRORAM_OBLI_COMPARE(obliTestNMask8, "vptestnmb")     // (a & b) == 0
MICRORAM_OBLI_COMPARE(obliTestNMask32, "vptestnmd")
MICRORAM_OBLI_COMPARE(obliTestNMask64, "vptestnmq")
#undef MICRORAM_OBLI_COMPARE

#define MICRORAM_OBLI_MASKED_MOVE(name, insn)                                \
  INLINE __m512i name(__m512i src, uint64_t k, __m512i a) {                  \
    asm(insn " %[a], %[dst]%{%[k]%}"                                         \
        : [dst] "+v"(src)                                                    \
        : [a] "v"(a), [k] "Yk"(_cvtu64_mask64(k)));                          \
    return src;                                                              \
  }
MICRORAM_OBLI_MASKED_MOVE(obliMaskMov8, "vmovdqu8")
MICRORAM_OBLI_MASKED_MOVE(obliMaskMov32, "vmovdqa32")
MICRORAM_OBLI_MASKED_MOVE(obliMaskMov64, "vmovdqa64")
MICRORAM_OBLI_MASKED_MOVE(obliMaskExpand8, "vpexpandb")
#undef MICRORAM_OBLI_MASKED_MOVE

// A whole 64-byte aligned line, loaded UNMASKED into a register.
//
// Every AVX-512 move and permute has a masked form whose memory operand is
// read element-wise under the mask, and GCC (15.2, -O3) fuses
//   _mm512_maskz_mov_epi8(k, _mm512_load_si512(p))
// into exactly that -- one VMOVDQU8 zmm{k}{z}, [p].  With a secret `k` the
// bytes fetched, and on some microarchitectures the time taken, then depend
// on the secret (Intel's data-operand-independent-timing guidance lists masked
// memory operations for this reason).  The pattern arises naturally in key
// loaders and in blends such as obliAssignBytes below.  Load through this
// wherever the value is about to meet a secret mask.
INLINE __m512i obliLoad512(const void* p) {
  return obliPin512(_mm512_load_si512(p));
}

// Assigns `source[0..n)` to `dest[0..n)` iff take == 1, without changing the
// instruction or memory-address trace with `take`. `n` is public; callers use
// this to blend a probe's candidate value into the access result.
//
// The lane mask is PUBLIC (it is the tail length) and may drive the loads and
// the store; the `select` mask is SECRET and may only ever touch registers.
// Public tail masks bound both loads and the store. The register-only blend
// prevents a secret selection from being folded into a memory operand.
INLINE void obliAssignBytes(uint8_t* dest, const uint8_t* source, size_t n,
                            uint64_t take) {
  const uint64_t select = uint64_t{0} - take;
  size_t off = 0;
  while (off < n) {
    const unsigned chunk = static_cast<unsigned>(n - off < 64 ? n - off : 64);
    const uint64_t lane_bits = _bzhi_u64(~uint64_t{0}, chunk);
    const __mmask64 lane = _cvtu64_mask64(lane_bits);
    const __m512i current =
        obliPin512(_mm512_maskz_loadu_epi8(lane, dest + off));
    const __m512i incoming =
        obliPin512(_mm512_maskz_loadu_epi8(lane, source + off));
    const __m512i blended = obliMaskMov8(current, lane_bits & select, incoming);
    _mm512_mask_storeu_epi8(dest + off, lane, blended);
    off += chunk;
  }
}

}  // namespace core
}  // namespace microram
