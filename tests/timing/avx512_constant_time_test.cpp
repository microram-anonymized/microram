// Empirical constant-time test for the instructions the library applies to
// secret operands.
//
// The obliviousness argument (src/core/DESIGN.md) assumes that a secret
// selection mask, permutation index, occupancy mask or key never changes how
// long an instruction takes.  This test measures that assumption on the host
// it runs on, instruction by instruction.
//
// Every instruction the library emits on secret data (the census in
// instruction_census.py lists the mnemonics from the compiled binaries) has
// one entry per secret operand role: the index vector of a permute, the mask
// of a compress or a masked move, the data of a compare, the count of a
// variable shift.  An entry measures one operand form of its mnemonic; the
// census does not tell forms apart (README.md, "Operand forms").  Each entry
// has operand CLASSES -- hardcoded special cases
// (identity and reverse permutations, the clear-all zero mask, all-ones,
// single-bit, alternating and half masks, out-of-range counts, all-equal and
// all-distinct conflict inputs, ...) and random operands redrawn every round.
//
// How one sample is taken.  A hand-written asm block, so the compiler cannot
// fold an identity permutation or rewrite a masked move, runs the instruction
// 128 (latency form) or 192 (throughput form) times between LFENCE-fenced TSC
// reads, with every operand held at the class's value for the whole block:
//   latency     one dependency chain through the operand under test.  After
//               each instruction the operand is XORed twice with the result,
//               which leaves its value unchanged but makes the next
//               instruction wait for this one.
//   throughput  twelve (vector) or four (mask, scalar) independent copies per
//               step, so the block is limited by issue ports, not latency.
// A latency difference would show in the first form, a uop-count or port
// difference in the second.
//
// How a verdict is reached.  Each round times every class once in a fresh
// random order, so drift, frequency changes and interrupts fall on every
// class alike.  The first class, a random operand, is the reference; a NULL
// class drawn independently from the same distribution is added to every
// entry and must come out indistinguishable, which validates the instrument
// on that very entry.  Per class (constant_time_stats.hpp):
//   LEAK        the mean paired difference or the outlier rate differs from
//               the reference beyond a threshold chosen so the whole run's
//               family-wise false-alarm rate is alpha (default 1e-3).
//   CERTIFIED   not a leak, and the bound |mean| + z * SE on any difference
//               is below the tolerance (default 0.05 core cycles per
//               instruction -- far below the one-cycle quantum in which an
//               operand-dependent latency would appear).
//   INCONCLUSIVE neither yet.  Certify mode keeps adding rounds until every
//               class is certified or the budget runs out.
// Two positive controls check the instrument itself: a kernel pair whose ADD
// chains differ by one ADD per loop iteration must be detected, measured near
// that many cycles, and with a standard error small enough that a difference
// of one cycle per sample would be flagged; and 64-bit DIV, whose latency
// depends on the dividend on current x86 cores, is expected to be flagged.
//
// Scope.  The measured quantity is core timing of register operands on this
// host.  It does not cover memory operands (their addresses are public by
// construction), data-dependent power or frequency effects over milliseconds,
// or other hosts: re-run on every target (README.md).

#include <cpuid.h>
#include <immintrin.h>
#include <sched.h>
#include <sys/utsname.h>
#include <time.h>
#include <unistd.h>
#include <x86intrin.h>

#include <algorithm>
#include <cinttypes>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "constant_time_stats.hpp"

namespace microram {
namespace timing {
namespace {

// ---------------------------------------------------------------------------
// Operands and timed kernels
// ---------------------------------------------------------------------------

struct alignas(64) Operands {
  uint8_t v[3][64];  // vector operands v0 (usually the control), v1, v2
  uint64_t k[2];     // mask operands k0, k1
  uint64_t g[3];     // general-purpose operands g0, g1, g2
};

using Kernel = uint64_t (*)(const Operands*, uint64_t iters);

constexpr unsigned kLatOps = 16;   // instructions per loop iteration, latency
constexpr unsigned kTputOps = 24;  // instructions per loop iteration, throughput

// The clock.  MFENCE drains the store buffer (LFENCE alone does not, and a
// store still draining into a class-specific address slowed the block that
// followed it) and LFENCE waits for the operand loads, so neither is timed;
// RDTSCP + LFENCE stops the clock after the block has executed.  RAX is the
// kernel's return value and RDX/RCX are clobbered, so a body may use all
// three as scratch (DIV and MUL do).
#define CT_BEGIN                                                         \
  "mfence\n\tlfence\n\trdtsc\n\tlfence\n\tshlq $32, %%rdx\n\t"           \
  "orq %%rdx, %%rax\n\tmovq %%rax, %[t0]\n\t"
#define CT_LOOP ".p2align 5\n1:\n\t"
#define CT_END                                                            \
  "decq %[cnt]\n\tjnz 1b\n\trdtscp\n\tlfence\n\tshlq $32, %%rdx\n\t"      \
  "orq %%rdx, %%rax\n\tsubq %[t0], %%rax\n\t"
#define CT_ASM(pre, reps, body) \
  CT_BEGIN pre CT_LOOP ".rept " #reps "\n\t" body ".endr\n\t" CT_END

#define CT_LOAD_VECTORS                                   \
  __m512i v0 = _mm512_load_si512(op->v[0]);               \
  __m512i v1 = _mm512_load_si512(op->v[1]);               \
  __m512i v2 = _mm512_load_si512(op->v[2]);               \
  __mmask64 k0 = _cvtu64_mask64(op->k[0]);                \
  uint64_t g0 = op->g[0];                                 \
  uint64_t ticks, t0, cnt = iters

// Four register shapes.  Every template may name every operand of its shape;
// the in/out operands let a latency chain run through whichever one is under
// test.  Operand counts stay within GCC's limit of 30.
//
// VEC: zmm outputs o0..o11 and scratch t, inputs v0..v2 (any of zmm0-31),
// mask k0 (k1-k7, so usable as a write mask) and scratch kt, GPR g0.
#define CT_VEC_FN(fn, pre, reps, body)                                        \
  __attribute__((noinline)) uint64_t fn(const Operands* op, uint64_t iters) { \
    CT_LOAD_VECTORS;                                                          \
    __m512i o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, t;              \
    __mmask64 kt;                                                             \
    asm volatile(CT_ASM(pre, reps, body)                                      \
                 : "=&a"(ticks), [t0] "=&r"(t0), [cnt] "+r"(cnt),             \
                   [o0] "=&v"(o0), [o1] "=&v"(o1), [o2] "=&v"(o2),            \
                   [o3] "=&v"(o3), [o4] "=&v"(o4), [o5] "=&v"(o5),            \
                   [o6] "=&v"(o6), [o7] "=&v"(o7), [o8] "=&v"(o8),            \
                   [o9] "=&v"(o9), [o10] "=&v"(o10), [o11] "=&v"(o11),        \
                   [t] "=&v"(t), [kt] "=&Yk"(kt), [v0] "+v"(v0),              \
                   [v1] "+v"(v1), [v2] "+v"(v2), [k0] "+Yk"(k0),              \
                   [g0] "+r"(g0)                                              \
                 :                                                            \
                 : "rdx", "rcx", "cc", "memory");                             \
    return ticks;                                                             \
  }

// VEX: the VEC shape restricted to xmm0-15, for instructions with no EVEX
// encoding (vpblendw, vperm2i128, vptest, 128-bit AES, ...).  Eight outputs.
#define CT_VEX_FN(fn, pre, reps, body)                                        \
  __attribute__((noinline)) uint64_t fn(const Operands* op, uint64_t iters) { \
    CT_LOAD_VECTORS;                                                          \
    (void)k0;                                                                 \
    __m512i o0, o1, o2, o3, o4, o5, o6, o7, t;                                \
    asm volatile(CT_ASM(pre, reps, body)                                      \
                 : "=&a"(ticks), [t0] "=&r"(t0), [cnt] "+r"(cnt),             \
                   [o0] "=&x"(o0), [o1] "=&x"(o1), [o2] "=&x"(o2),            \
                   [o3] "=&x"(o3), [o4] "=&x"(o4), [o5] "=&x"(o5),            \
                   [o6] "=&x"(o6), [o7] "=&x"(o7), [t] "=&x"(t),              \
                   [v0] "+x"(v0), [v1] "+x"(v1), [v2] "+x"(v2), [g0] "+r"(g0) \
                 :                                                            \
                 : "rdx", "rcx", "cc", "memory");                             \
    return ticks;                                                             \
  }

// MASK: mask outputs m0..m3 and scratch kt, inputs v0..v2, k0, k1, g0.
#define CT_MASK_FN(fn, pre, reps, body)                                       \
  __attribute__((noinline)) uint64_t fn(const Operands* op, uint64_t iters) { \
    CT_LOAD_VECTORS;                                                          \
    __mmask64 k1 = _cvtu64_mask64(op->k[1]);                                  \
    __mmask64 m0, m1, m2, m3, kt;                                             \
    __m512i t;                                                                \
    asm volatile(CT_ASM(pre, reps, body)                                      \
                 : "=&a"(ticks), [t0] "=&r"(t0), [cnt] "+r"(cnt),             \
                   [m0] "=&k"(m0), [m1] "=&k"(m1), [m2] "=&k"(m2),            \
                   [m3] "=&k"(m3), [kt] "=&k"(kt), [t] "=&v"(t),              \
                   [v0] "+v"(v0), [v1] "+v"(v1), [v2] "+v"(v2),               \
                   [k0] "+Yk"(k0), [k1] "+Yk"(k1), [g0] "+r"(g0)              \
                 :                                                            \
                 : "rdx", "rcx", "cc", "memory");                             \
    return ticks;                                                             \
  }

// GPR: GPR outputs r0..r3, inputs g0..g2, v0, v1, k0, scratch t and kt.
#define CT_GPR_FN(fn, pre, reps, body)                                        \
  __attribute__((noinline)) uint64_t fn(const Operands* op, uint64_t iters) { \
    CT_LOAD_VECTORS;                                                          \
    (void)v2;                                                                 \
    uint64_t g1 = op->g[1], g2 = op->g[2];                                    \
    uint64_t r0, r1, r2, r3;                                                  \
    __m512i t;                                                                \
    __mmask64 kt;                                                             \
    asm volatile(CT_ASM(pre, reps, body)                                      \
                 : "=&a"(ticks), [t0] "=&r"(t0), [cnt] "+r"(cnt),             \
                   [r0] "=&r"(r0), [r1] "=&r"(r1), [r2] "=&r"(r2),            \
                   [r3] "=&r"(r3), [t] "=&v"(t), [kt] "=&Yk"(kt),             \
                   [v0] "+v"(v0), [v1] "+v"(v1), [k0] "+Yk"(k0),              \
                   [g0] "+r"(g0), [g1] "+r"(g1), [g2] "+r"(g2)                \
                 :                                                            \
                 : "rdx", "rcx", "cc", "memory");                             \
    return ticks;                                                             \
  }

// P2I: VP2INTERSECT writes an even/odd mask register PAIR, which no operand
// constraint expresses, so its kernels name k0..k7 explicitly.
#define CT_P2I_FN(fn, reps, body)                                              \
  __attribute__((noinline)) uint64_t fn(const Operands* op, uint64_t iters) {  \
    CT_LOAD_VECTORS;                                                           \
    (void)v2;                                                                  \
    (void)k0;                                                                  \
    (void)g0;                                                                  \
    __m512i t;                                                                 \
    asm volatile(CT_ASM("", reps, body)                                        \
                 : "=&a"(ticks), [t0] "=&r"(t0), [cnt] "+r"(cnt),              \
                   [t] "=&v"(t), [v0] "+v"(v0), [v1] "+v"(v1)                  \
                 :                                                             \
                 : "rdx", "rcx", "cc", "memory", "k0", "k1", "k2", "k3", "k4", \
                   "k5", "k6", "k7");                                          \
    return ticks;                                                              \
  }

// Write-mask decorations, AT&T syntax (braces are escaped in GCC asm).
#define KM "%{%[k0]%}"
#define KZ "%{%[k0]%}%{z%}"

// Latency-chain restores: XOR the operand under test with the result twice.
#define XOR2(src, dst) \
  "vpxorq " src ", " dst ", " dst "\n\tvpxorq " src ", " dst ", " dst "\n\t"
#define V0_O XOR2("%[o0]", "%[v0]")
#define V1_O XOR2("%[o0]", "%[v1]")
#define K0_O \
  "vpmovb2m %[o0], %[kt]\n\tkxorq %[kt], %[k0], %[k0]\n\tkxorq %[kt], %[k0], %[k0]\n\t"
#define G0_O "vmovq %x[o0], %%rdx\n\txorq %%rdx, %[g0]\n\txorq %%rdx, %[g0]\n\t"
#define V1_M "vpmovm2b %[m0], %[t]\n\t" XOR2("%[t]", "%[v1]")
#define K0_M "kxorq %[m0], %[k0], %[k0]\n\tkxorq %[m0], %[k0], %[k0]\n\t"
#define G0_R "xorq %[r0], %[g0]\n\txorq %[r0], %[g0]\n\t"
#define G1_R "xorq %[r0], %[g1]\n\txorq %[r0], %[g1]\n\t"
#define V0_R "vmovq %[r0], %x[t]\n\t" XOR2("%[t]", "%[v0]")

#define X12(F, mn)                                                        \
  F(mn, "o0") F(mn, "o1") F(mn, "o2") F(mn, "o3") F(mn, "o4") F(mn, "o5") \
  F(mn, "o6") F(mn, "o7") F(mn, "o8") F(mn, "o9") F(mn, "o10") F(mn, "o11")
#define X8(F, mn)                                                         \
  F(mn, "o0") F(mn, "o1") F(mn, "o2") F(mn, "o3") F(mn, "o4") F(mn, "o5") \
  F(mn, "o6") F(mn, "o7")
#define X4M(F, mn) F(mn, "m0") F(mn, "m1") F(mn, "m2") F(mn, "m3")
#define X4R(F, mn) F(mn, "r0") F(mn, "r1") F(mn, "r2") F(mn, "r3")

// One latency and one throughput kernel from a form F(mnemonic, output).
#define VEC(name, F, mn, chain)                       \
  CT_VEC_FN(name##_lat, "", 16, F(mn, "o0") chain) \
  CT_VEC_FN(name##_tput, "", 2, X12(F, mn))
#define VEX(name, F, mn, chain)                       \
  CT_VEX_FN(name##_lat, "", 16, F(mn, "o0") chain) \
  CT_VEX_FN(name##_tput, "", 3, X8(F, mn))
#define MSK(name, F, mn, chain)                        \
  CT_MASK_FN(name##_lat, "", 16, F(mn, "m0") chain) \
  CT_MASK_FN(name##_tput, "", 6, X4M(F, mn))
#define GPR(name, F, mn, chain)                       \
  CT_GPR_FN(name##_lat, "", 16, F(mn, "r0") chain) \
  CT_GPR_FN(name##_tput, "", 6, X4R(F, mn))

#define O(o) "%[" o "]"
#define OX(o) "%x[" o "]"
#define OY(o) "%t[" o "]"
#define OE(o) "%k[" o "]"

// --- operand forms (AT&T order: sources first, destination last) ----------
#define F_BIN(mn, o) mn " %[v2], %[v1], " O(o) "\n\t"
#define F_BIN_XC(mn, o) mn " %x[v2], %[v1], " O(o) "\n\t"
#define F_BINI(mn, o) mn ", %[v2], %[v1], " O(o) "\n\t"
#define F_UN(mn, o) mn " %[v1], " O(o) "\n\t"
#define F_UNI(mn, o) mn ", %[v1], " O(o) "\n\t"
#define F_UN_X(mn, o) mn " %[v1], " OX(o) "\n\t"
#define F_UN_Y(mn, o) mn " %[v1], " OY(o) "\n\t"
#define F_UNI_X(mn, o) mn ", %[v1], " OX(o) "\n\t"
#define F_UNI_Y(mn, o) mn ", %[v1], " OY(o) "\n\t"
#define F_UNY(mn, o) mn " %t[v1], " O(o) "\n\t"
#define F_UNX(mn, o) mn " %x[v1], " O(o) "\n\t"
#define F_INSX(mn, o) mn ", %x[v2], %[v1], " O(o) "\n\t"
#define F_INSY(mn, o) mn ", %t[v2], %[v1], " O(o) "\n\t"
// v1 permuted by index v0 (vpermb/d/q), v1 shuffled by v0 (vpshufb), v1
// shifted by counts v0 (vpsllvq)
#define F_IDX(mn, o) mn " %[v1], %[v0], " O(o) "\n\t"
#define F_CTL(mn, o) mn " %[v0], %[v1], " O(o) "\n\t"
// Two-table permutes: tables v1, v2, index v0.  The destination is also an
// input, so a copy puts the right operand there first; the copy is the same
// for every class.
#define F_T2(mn, o) "vmovdqa64 %[v1], " O(o) "\n\t" mn " %[v2], %[v0], " O(o) "\n\t"
#define F_I2(mn, o) "vmovdqa64 %[v0], " O(o) "\n\t" mn " %[v2], %[v1], " O(o) "\n\t"
#define F_TERN(mn, o) "vmovdqa64 %[v1], " O(o) "\n\t" mn ", %[v2], %[v0], " O(o) "\n\t"
#define F_AES(mn, o) mn " %[v0], %[v1], " O(o) "\n\t"
#define F_BCG(mn, o) mn " %[g0], " O(o) "\n\t"
#define F_BCE(mn, o) mn " %k[g0], " O(o) "\n\t"
#define F_INSG(mn, o) mn ", %[g0], %x[v1], " OX(o) "\n\t"
#define F_INSE(mn, o) mn ", %k[g0], %x[v1], " OX(o) "\n\t"
// masked (mask role: the chain runs through k0)
#define F_KZ_IDX(mn, o) mn " %[v1], %[v0], " O(o) KZ "\n\t"
#define F_KM_IDX(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %[v1], %[v0], " O(o) KM "\n\t"
#define F_KZ_T2(mn, o) "vmovdqa64 %[v1], " O(o) "\n\t" mn " %[v2], %[v0], " O(o) KZ "\n\t"
#define F_KM_T2(mn, o) "vmovdqa64 %[v1], " O(o) "\n\t" mn " %[v2], %[v0], " O(o) KM "\n\t"
#define F_KZ_I2(mn, o) "vmovdqa64 %[v0], " O(o) "\n\t" mn " %[v2], %[v1], " O(o) KZ "\n\t"
#define F_KM_CTL(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %[v0], %[v1], " O(o) KM "\n\t"
#define F_KZ_CTL(mn, o) mn " %[v0], %[v1], " O(o) KZ "\n\t"
#define F_KZ_UN(mn, o) mn " %[v1], " O(o) KZ "\n\t"
#define F_KM_UN(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %[v1], " O(o) KM "\n\t"
#define F_KM_BIN(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %[v1], %[v0], " O(o) KM "\n\t"
#define F_KM_BLEND(mn, o) mn " %[v2], %[v1], " O(o) KM "\n\t"
#define F_KZ_BINI(mn, o) mn ", %[v2], %[v1], " O(o) KZ "\n\t"
#define F_KM_UNI(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn ", %[v1], " O(o) KM "\n\t"
#define F_KZ_UNI(mn, o) mn ", %[v1], " O(o) KZ "\n\t"
#define F_KM_BCG(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %[g0], " O(o) KM "\n\t"
#define F_KZ_BCG(mn, o) mn " %[g0], " O(o) KZ "\n\t"
#define F_KM_BCE(mn, o) "vmovdqa64 %[v2], " O(o) "\n\t" mn " %k[g0], " O(o) KM "\n\t"
#define F_KZ_BCE(mn, o) mn " %k[g0], " O(o) KZ "\n\t"
#define F_M2V(mn, o) mn " %[k0], " O(o) "\n\t"
// VEX shape
#define F_XBIN(mn, o) mn " %x[v2], %x[v1], " OX(o) "\n\t"
#define F_YBIN(mn, o) mn " %t[v2], %t[v1], " OY(o) "\n\t"
#define F_XBINI(mn, o) mn ", %x[v2], %x[v1], " OX(o) "\n\t"
#define F_XBLENDV(mn, o) mn " %x[v0], %x[v2], %x[v1], " OX(o) "\n\t"
#define F_YBCX(mn, o) mn " %x[v1], " OY(o) "\n\t"
#define F_YEXTX(mn, o) mn ", %t[v1], " OX(o) "\n\t"
#define F_YBINI(mn, o) mn ", %t[v2], %t[v1], " OY(o) "\n\t"
#define F_YINSX(mn, o) mn ", %x[v2], %t[v1], " OY(o) "\n\t"
#define F_XAES(mn, o) mn " %x[v0], %x[v1], " OX(o) "\n\t"
#define F_XUNI(mn, o) mn ", %x[v1], " OX(o) "\n\t"
#define F_YTEST(mn, o) mn " %t[v2], %t[v1]\n\t"
// MASK shape
#define F_CMP(mn, o) mn " %[v2], %[v1], " O(o) "\n\t"
#define F_CMPI(mn, o) mn ", %[v2], %[v1], " O(o) "\n\t"
#define F_CMPK(mn, o) mn " %[v2], %[v1], " O(o) KM "\n\t"
#define F_CMPIK(mn, o) mn ", %[v2], %[v1], " O(o) KM "\n\t"
#define F_V2M(mn, o) mn " %[v1], " O(o) "\n\t"
#define F_K2(mn, o) mn " %[k1], %[k0], " O(o) "\n\t"
#define F_K1(mn, o) mn " %[k0], " O(o) "\n\t"
#define F_K1I(mn, o) mn ", %[k0], " O(o) "\n\t"
#define F_KTEST(mn, o) mn " %[k1], %[k0]\n\t"
// GPR shape
#define F_G1(mn, o) mn " %[g0], " O(o) "\n\t"
#define F_G2(mn, o) mn " %[g1], %[g0], " O(o) "\n\t"
#define F_PDEP(mn, o) mn " %[g0], %[g1], " O(o) "\n\t"
#define F_IMUL(mn, o) "movq %[g0], " O(o) "\n\t" mn " %[g1], " O(o) "\n\t"
#define F_CMOVT(mn, o) \
  "testq %[g0], %[g0]\n\tmovq %[g1], " O(o) "\n\t" mn " %[g2], " O(o) "\n\t"
#define F_CMOVC(mn, o) \
  "cmpq %[g1], %[g0]\n\tmovq %[g1], " O(o) "\n\t" mn " %[g2], " O(o) "\n\t"
#define F_KMOVQ(mn, o) "kmovq %[g0], %[kt]\n\tkmovq %[kt], " O(o) "\n\t"
#define F_KMOVE(mn, o) mn " %k[g0], %[kt]\n\t" mn " %[kt], " OE(o) "\n\t"
#define F_EXTRE(mn, o) mn ", %x[v0], " OE(o) "\n\t"
#define F_EXTRQ(mn, o) mn ", %x[v0], " O(o) "\n\t"
#define F_MULQ(mn, o) "movq %[g0], %%rax\n\t" mn " %[g1]\n\t"

// ---- permutes and shuffles: control role (chain through the index) -------
VEC(vpermb_ctrl, F_IDX, "vpermb", V0_O)
VEC(vpermb_data, F_IDX, "vpermb", V1_O)
VEC(vpermb_km, F_KM_IDX, "vpermb", K0_O)
VEC(vpermb_kz, F_KZ_IDX, "vpermb", K0_O)
VEC(vpermt2b_ctrl, F_T2, "vpermt2b", V0_O)
VEC(vpermt2b_data, F_T2, "vpermt2b", V1_O)
VEC(vpermt2b_kz, F_KZ_T2, "vpermt2b", K0_O)
VEC(vpermt2b_km, F_KM_T2, "vpermt2b", K0_O)
VEC(vpermi2b_ctrl, F_I2, "vpermi2b", V0_O)
VEC(vpermi2b_kz, F_KZ_I2, "vpermi2b", K0_O)
VEC(vpermt2w_ctrl, F_T2, "vpermt2w", V0_O)
VEC(vpermi2w_ctrl, F_I2, "vpermi2w", V0_O)
VEC(vpermt2d_ctrl, F_T2, "vpermt2d", V0_O)
VEC(vpermi2d_ctrl, F_I2, "vpermi2d", V0_O)
VEC(vpermd_ctrl, F_IDX, "vpermd", V0_O)
VEC(vpermt2q_ctrl, F_T2, "vpermt2q", V0_O)
VEC(vpermi2q_ctrl, F_I2, "vpermi2q", V0_O)
VEC(vpermq_ctrl, F_IDX, "vpermq", V0_O)
VEC(vpshufb_ctrl, F_CTL, "vpshufb", V0_O)
VEC(vpshufb_km, F_KM_CTL, "vpshufb", K0_O)
VEC(vpsllvq_count, F_CTL, "vpsllvq", V0_O)
VEC(vpsrlvq_count, F_CTL, "vpsrlvq", V0_O)
VEC(vpsllvq_kz, F_KZ_CTL, "vpsllvq", K0_O)

// ---- mask role (chain through k0) ----------------------------------------
VEC(vpcompressb_kz, F_KZ_UN, "vpcompressb", K0_O)
VEC(vpexpandb_km, F_KM_UN, "vpexpandb", K0_O)
VEC(vmovdqu8_km, F_KM_UN, "vmovdqu8", K0_O)
VEC(vmovdqu8_kz, F_KZ_UN, "vmovdqu8", K0_O)
VEC(vmovdqa32_km, F_KM_UN, "vmovdqa32", K0_O)
VEC(vmovdqa32_kz, F_KZ_UN, "vmovdqa32", K0_O)
VEC(vmovdqa64_km, F_KM_UN, "vmovdqa64", K0_O)
VEC(vmovdqa64_kz, F_KZ_UN, "vmovdqa64", K0_O)
VEC(vpblendmb_km, F_KM_BLEND, "vpblendmb", K0_O)
VEC(vpblendmd_km, F_KM_BLEND, "vpblendmd", K0_O)
VEC(vpblendmq_km, F_KM_BLEND, "vpblendmq", K0_O)
VEC(vpaddb_km, F_KM_BIN, "vpaddb", K0_O)
VEC(vpaddq_km, F_KM_BIN, "vpaddq", K0_O)
VEC(vpabsb_kz, F_KZ_UN, "vpabsb", K0_O)
VEC(vshufi64x2_kz, F_KZ_BINI, "vshufi64x2 $0x4e", K0_O)
VEC(vpsrld_km, F_KM_UNI, "vpsrld $3", K0_O)
VEC(vpsrld_kz, F_KZ_UNI, "vpsrld $3", K0_O)
VEC(vpbroadcastq_km, F_KM_BCG, "vpbroadcastq", K0_O)
VEC(vpbroadcastq_kz, F_KZ_BCG, "vpbroadcastq", K0_O)
VEC(vpbroadcastd_km, F_KM_BCE, "vpbroadcastd", K0_O)
VEC(vpbroadcastd_kz, F_KZ_BCE, "vpbroadcastd", K0_O)
VEC(vpbroadcastb_km, F_KM_BCE, "vpbroadcastb", K0_O)
VEC(vpbroadcastb_kz, F_KZ_BCE, "vpbroadcastb", K0_O)
VEC(vpmovm2b_mask, F_M2V, "vpmovm2b", K0_O)
VEC(vpmovm2q_mask, F_M2V, "vpmovm2q", K0_O)

// ---- data role (chain through v1) ----------------------------------------
VEC(vpaddq_data, F_BIN, "vpaddq", V1_O)
VEC(vpaddd_data, F_BIN, "vpaddd", V1_O)
VEC(vpaddb_data, F_BIN, "vpaddb", V1_O)
VEC(vpsubq_data, F_BIN, "vpsubq", V1_O)
VEC(vpsubd_data, F_BIN, "vpsubd", V1_O)
VEC(vpsubb_data, F_BIN, "vpsubb", V1_O)
VEC(vpsubusb_data, F_BIN, "vpsubusb", V1_O)
VEC(vpxord_data, F_BIN, "vpxord", V1_O)
VEC(vpxorq_data, F_BIN, "vpxorq", V1_O)
VEC(vpandd_data, F_BIN, "vpandd", V1_O)
VEC(vpandq_data, F_BIN, "vpandq", V1_O)
VEC(vpandnd_data, F_BIN, "vpandnd", V1_O)
VEC(vpandnq_data, F_BIN, "vpandnq", V1_O)
VEC(vpord_data, F_BIN, "vpord", V1_O)
VEC(vporq_data, F_BIN, "vporq", V1_O)
VEC(vpmaxuq_data, F_BIN, "vpmaxuq", V1_O)
VEC(vpmaxud_data, F_BIN, "vpmaxud", V1_O)
VEC(vpmaxub_data, F_BIN, "vpmaxub", V1_O)
VEC(vpminuq_data, F_BIN, "vpminuq", V1_O)
VEC(vpminud_data, F_BIN, "vpminud", V1_O)
VEC(vpmullq_data, F_BIN, "vpmullq", V1_O)
VEC(vpmulld_data, F_BIN, "vpmulld", V1_O)
VEC(vpmuludq_data, F_BIN, "vpmuludq", V1_O)
VEC(vpackusdw_data, F_BIN, "vpackusdw", V1_O)
VEC(vpackuswb_data, F_BIN, "vpackuswb", V1_O)
VEC(vpunpcklbw_data, F_BIN, "vpunpcklbw", V1_O)
VEC(vpunpckhbw_data, F_BIN, "vpunpckhbw", V1_O)
VEC(vpunpcklwd_data, F_BIN, "vpunpcklwd", V1_O)
VEC(vpunpckhwd_data, F_BIN, "vpunpckhwd", V1_O)
VEC(vpunpckldq_data, F_BIN, "vpunpckldq", V1_O)
VEC(vpunpckhdq_data, F_BIN, "vpunpckhdq", V1_O)
VEC(vpunpcklqdq_data, F_BIN, "vpunpcklqdq", V1_O)
VEC(vpunpckhqdq_data, F_BIN, "vpunpckhqdq", V1_O)
VEC(vpternlogq_xor3, F_TERN, "vpternlogq $0x96", V1_O)
VEC(vpternlogq_select, F_TERN, "vpternlogq $0xca", V1_O)
VEC(vpternlogd_select, F_TERN, "vpternlogd $0xca", V1_O)
VEC(vpabsb_data, F_UN, "vpabsb", V1_O)
VEC(vpopcntq_data, F_UN, "vpopcntq", V1_O)
VEC(vpconflictd_data, F_UN, "vpconflictd", V1_O)
VEC(vpconflictq_data, F_UN, "vpconflictq", V1_O)
VEC(vpshufd_data, F_UNI, "vpshufd $0x1b", V1_O)
VEC(vpslldq_data, F_UNI, "vpslldq $4", V1_O)
VEC(vpsrldq_data, F_UNI, "vpsrldq $4", V1_O)
VEC(vpsrlw_data, F_UNI, "vpsrlw $3", V1_O)
VEC(vpsrld_data, F_UNI, "vpsrld $3", V1_O)
VEC(vpsrlq_data, F_UNI, "vpsrlq $3", V1_O)
VEC(vpsraq_data, F_UNI, "vpsraq $3", V1_O)
VEC(vpsllw_data, F_UNI, "vpsllw $3", V1_O)
VEC(vpslld_data, F_UNI, "vpslld $3", V1_O)
VEC(vpsllq_data, F_UNI, "vpsllq $3", V1_O)
// The same shifts with the (public) count in an xmm register, a different uop
// mix: the radix digits and routing tags shift secret data this way.
VEC(vpsrlw_xcount_data, F_BIN_XC, "vpsrlw", V1_O)
VEC(vpsrlq_xcount_data, F_BIN_XC, "vpsrlq", V1_O)
VEC(vpsllq_xcount_data, F_BIN_XC, "vpsllq", V1_O)
VEC(vpmovqb_data, F_UN_X, "vpmovqb", V1_O)
VEC(vpmovdb_data, F_UN_X, "vpmovdb", V1_O)
VEC(vpmovqd_data, F_UN_Y, "vpmovqd", V1_O)
VEC(vpmovzxdq_data, F_UNY, "vpmovzxdq", V1_O)
VEC(vpmovzxwd_data, F_UNY, "vpmovzxwd", V1_O)
VEC(vpmovzxbw_data, F_UNY, "vpmovzxbw", V1_O)
VEC(vpmovzxbq_data, F_UNX, "vpmovzxbq", V1_O)
VEC(vextracti64x2_data, F_UNI_X, "vextracti64x2 $1", V1_O)
VEC(vextracti32x4_data, F_UNI_X, "vextracti32x4 $1", V1_O)
VEC(vextracti64x4_data, F_UNI_Y, "vextracti64x4 $1", V1_O)
VEC(vextracti32x8_data, F_UNI_Y, "vextracti32x8 $1", V1_O)
VEC(vinserti64x2_data, F_INSX, "vinserti64x2 $1", V1_O)
VEC(vinserti32x4_data, F_INSX, "vinserti32x4 $1", V1_O)
VEC(vinserti64x4_data, F_INSY, "vinserti64x4 $1", V1_O)
VEC(vinserti32x8_data, F_INSY, "vinserti32x8 $1", V1_O)
VEC(vshufi64x2_data, F_BINI, "vshufi64x2 $0x4e", V1_O)
VEC(vshufi32x4_data, F_BINI, "vshufi32x4 $0xb1", V1_O)
VEC(valignq_data, F_BINI, "valignq $3", V1_O)
VEC(valignd_data, F_BINI, "valignd $5", V1_O)
VEC(vpalignr_data, F_BINI, "vpalignr $5", V1_O)
VEC(vaesenc_state, F_AES, "vaesenc", V1_O)
VEC(vaesenc_key, F_AES, "vaesenc", V0_O)
VEC(vaesenclast_state, F_AES, "vaesenclast", V1_O)
VEC(vaesenclast_key, F_AES, "vaesenclast", V0_O)
VEC(vpbroadcastq_data, F_BCG, "vpbroadcastq", G0_O)
VEC(vpbroadcastd_data, F_BCE, "vpbroadcastd", G0_O)
VEC(vpbroadcastb_data, F_BCE, "vpbroadcastb", G0_O)
VEC(vpbroadcastw_data, F_BCE, "vpbroadcastw", G0_O)
VEC(vpinsrq_data, F_INSG, "vpinsrq $1", G0_O)
VEC(vpinsrd_data, F_INSE, "vpinsrd $1", G0_O)
VEC(vpinsrw_data, F_INSE, "vpinsrw $1", G0_O)
VEC(vpinsrb_data, F_INSE, "vpinsrb $1", G0_O)
// The re-tag's vector modulus (ModSmallLanes,
// src/oram/table/cpu_byteslice_routing_map.hpp): byte sums
// and multiply-adds of secret tag words.
VEC(vpsadbw_data, F_BIN, "vpsadbw", V1_O)
VEC(vpmaddubsw_data, F_BIN, "vpmaddubsw", V1_O)
VEC(vpmaddwd_data, F_BIN, "vpmaddwd", V1_O)

// ---- VEX-only encodings ----------------------------------------------------
VEX(vpxor_data, F_XBIN, "vpxor", V1_O)
VEX(vpand_data, F_XBIN, "vpand", V1_O)
// GCC 13 emits these VEX forms in the worker benchmark and its shared kernels.
VEX(vpor_x_data, F_XBIN, "vpor", V1_O)
VEX(vpor_y_data, F_YBIN, "vpor", V1_O)
VEX(vpcmpgtq_x_data, F_XBIN, "vpcmpgtq", V1_O)
VEX(vpcmpgtq_y_data, F_YBIN, "vpcmpgtq", V1_O)
VEX(vextracti128_data, F_YEXTX, "vextracti128 $1", V1_O)
VEX(vpblendw_data, F_YBINI, "vpblendw $0xaa", V1_O)
VEX(vperm2i128_data, F_YBINI, "vperm2i128 $0x21", V1_O)
VEX(vinserti128_data, F_YINSX, "vinserti128 $1", V1_O)
VEX(vaesenc_state_x, F_XAES, "vaesenc", V1_O)
VEX(vaesenc_key_x, F_XAES, "vaesenc", V0_O)
VEX(vaesenclast_state_x, F_XAES, "vaesenclast", V1_O)
VEX(vaeskeygenassist_data, F_XUNI, "vaeskeygenassist $1", V1_O)
// The tree read path's `valid & ~match` over secret lane masks, vectorized.
VEX(vpandn_x_data, F_XBIN, "vpandn", V1_O)
VEX(vpandn_y_data, F_YBIN, "vpandn", V1_O)
// FP-domain shuffles and bitwise operations.  GCC uses vshufps in the
// popcount reductions of secret occupancy masks and vinsertps to merge secret
// value bytes; the others appear in public scheduling arithmetic.
VEX(vshufps_data, F_XBINI, "vshufps $0x88", V1_O)
VEX(vinsertps_data, F_XBINI, "vinsertps $0x10", V1_O)
VEX(vunpcklpd_data, F_XBIN, "vunpcklpd", V1_O)
VEX(vxorps_data, F_XBIN, "vxorps", V1_O)
VEX(vxorpd_data, F_XBIN, "vxorpd", V1_O)
VEX(vandpd_data, F_XBIN, "vandpd", V1_O)
VEX(vbroadcastsd_data, F_YBCX, "vbroadcastsd", V1_O)
VEX(vblendvpd_mask, F_XBLENDV, "vblendvpd", V0_O)
CT_VEX_FN(vptest_data_lat, "", 16,
          "vptest %t[v2], %t[v1]\n\tsbbq %%rdx, %%rdx\n\tvmovq %%rdx, %x[t]\n\t"
          XOR2("%[t]", "%[v1]"))
CT_VEX_FN(vptest_data_tput, "", 3, X8(F_YTEST, "vptest"))

// ---- mask-producing and mask-register instructions ------------------------
MSK(vpcmpeqb_data, F_CMP, "vpcmpeqb", V1_M)
MSK(vpcmpeqd_data, F_CMP, "vpcmpeqd", V1_M)
MSK(vpcmpeqq_data, F_CMP, "vpcmpeqq", V1_M)
MSK(vpcmpub_data, F_CMPI, "vpcmpub $1", V1_M)
MSK(vpcmpud_data, F_CMPI, "vpcmpud $1", V1_M)
MSK(vpcmpuq_data, F_CMPI, "vpcmpuq $1", V1_M)
MSK(vpcmpb_data, F_CMPI, "vpcmpb $1", V1_M)
MSK(vpcmpd_data, F_CMPI, "vpcmpd $1", V1_M)
MSK(vpcmpq_data, F_CMPI, "vpcmpq $1", V1_M)
MSK(vptestmb_data, F_CMP, "vptestmb", V1_M)
MSK(vptestnmb_data, F_CMP, "vptestnmb", V1_M)
MSK(vptestmd_data, F_CMP, "vptestmd", V1_M)
MSK(vptestnmd_data, F_CMP, "vptestnmd", V1_M)
MSK(vptestmq_data, F_CMP, "vptestmq", V1_M)
MSK(vptestnmq_data, F_CMP, "vptestnmq", V1_M)
MSK(vpmovb2m_data, F_V2M, "vpmovb2m", V1_M)
MSK(vpcmpeqb_km, F_CMPK, "vpcmpeqb", K0_M)
MSK(vpcmpeqd_km, F_CMPK, "vpcmpeqd", K0_M)
MSK(vpcmpeqq_km, F_CMPK, "vpcmpeqq", K0_M)
MSK(vpcmpub_km, F_CMPIK, "vpcmpub $1", K0_M)
MSK(vpcmpd_km, F_CMPIK, "vpcmpd $1", K0_M)
MSK(vptestmb_km, F_CMPK, "vptestmb", K0_M)
MSK(vptestnmb_km, F_CMPK, "vptestnmb", K0_M)
MSK(korq_data, F_K2, "korq", K0_M)
MSK(kord_data, F_K2, "kord", K0_M)
MSK(korw_data, F_K2, "korw", K0_M)
MSK(korb_data, F_K2, "korb", K0_M)
MSK(kandq_data, F_K2, "kandq", K0_M)
MSK(kandnq_data, F_K2, "kandnq", K0_M)
MSK(kxorq_data, F_K2, "kxorq", K0_M)
MSK(kxord_data, F_K2, "kxord", K0_M)
MSK(kxorw_data, F_K2, "kxorw", K0_M)
MSK(kxorb_data, F_K2, "kxorb", K0_M)
MSK(kxnorq_data, F_K2, "kxnorq", K0_M)
MSK(kxnorb_data, F_K2, "kxnorb", K0_M)
MSK(kandb_data, F_K2, "kandb", K0_M)
MSK(kunpckbw_data, F_K2, "kunpckbw", K0_M)
MSK(knotq_data, F_K1, "knotq", K0_M)
MSK(knotb_data, F_K1, "knotb", K0_M)
MSK(kshiftrq_data, F_K1I, "kshiftrq $5", K0_M)
MSK(kshiftlq_data, F_K1I, "kshiftlq $5", K0_M)
MSK(kshiftld_data, F_K1I, "kshiftld $5", K0_M)
MSK(kshiftrw_data, F_K1I, "kshiftrw $5", K0_M)
MSK(kshiftrb_data, F_K1I, "kshiftrb $5", K0_M)
MSK(kshiftlb_data, F_K1I, "kshiftlb $5", K0_M)
#define KORTEST_LAT(mn)                                            \
  mn " %[k1], %[k0]\n\tsbbq %%rdx, %%rdx\n\tkmovq %%rdx, %[kt]\n\t" \
  "kxorq %[kt], %[k0], %[k0]\n\tkxorq %[kt], %[k0], %[k0]\n\t"
CT_MASK_FN(kortestq_data_lat, "", 16, KORTEST_LAT("kortestq"))
CT_MASK_FN(kortestq_data_tput, "", 6, X4M(F_KTEST, "kortestq"))
CT_MASK_FN(kortestd_data_lat, "", 16, KORTEST_LAT("kortestd"))
CT_MASK_FN(kortestd_data_tput, "", 6, X4M(F_KTEST, "kortestd"))
CT_MASK_FN(kortestw_data_lat, "", 16, KORTEST_LAT("kortestw"))
CT_MASK_FN(kortestw_data_tput, "", 6, X4M(F_KTEST, "kortestw"))
CT_MASK_FN(kortestb_data_lat, "", 16, KORTEST_LAT("kortestb"))
CT_MASK_FN(kortestb_data_tput, "", 6, X4M(F_KTEST, "kortestb"))

// ---- scalar and cross-domain ----------------------------------------------
GPR(kmovq_data, F_KMOVQ, "kmovq", G0_R)
GPR(kmovd_data, F_KMOVE, "kmovd", G0_R)
GPR(kmovw_data, F_KMOVE, "kmovw", G0_R)
GPR(kmovb_data, F_KMOVE, "kmovb", G0_R)
GPR(vpextrb_data, F_EXTRE, "vpextrb $5", V0_R)
GPR(vpextrw_data, F_EXTRE, "vpextrw $3", V0_R)
GPR(vpextrd_data, F_EXTRE, "vpextrd $1", V0_R)
GPR(vpextrq_data, F_EXTRQ, "vpextrq $1", V0_R)
GPR(pdep_mask, F_PDEP, "pdep", G0_R)
GPR(pdep_source, F_PDEP, "pdep", G1_R)
GPR(pext_mask, F_PDEP, "pext", G0_R)
GPR(pext_source, F_PDEP, "pext", G1_R)
GPR(popcnt_data, F_G1, "popcntq", G0_R)
GPR(lzcnt_data, F_G1, "lzcntq", G0_R)
GPR(tzcnt_data, F_G1, "tzcntq", G0_R)
GPR(blsr_data, F_G1, "blsrq", G0_R)
GPR(blsi_data, F_G1, "blsiq", G0_R)
GPR(bzhi_index, F_G2, "bzhi", G1_R)
GPR(andn_data, F_G2, "andn", G0_R)
GPR(shlx_count, F_G2, "shlx", G1_R)
GPR(shrx_count, F_G2, "shrx", G1_R)
GPR(sarx_count, F_G2, "sarx", G1_R)
GPR(imul_data, F_IMUL, "imulq", G0_R)
GPR(cmov_zf, F_CMOVT, "cmovnzq", G0_R)
GPR(cmov_cf_zf, F_CMOVC, "cmovbeq", G0_R)
GPR(cmov_sf, F_CMOVT, "cmovsq", G0_R)
CT_GPR_FN(mul_data_lat, "", 16,
          F_MULQ("mulq", "") "xorq %%rdx, %[g0]\n\txorq %%rdx, %[g0]\n\t")
CT_GPR_FN(mul_data_tput, "", 6, X4R(F_MULQ, "mulq"))
CT_GPR_FN(mulx_data_lat, "", 16,
          "movq %[g0], %%rdx\n\tmulxq %[g1], %[r0], %[r1]\n\t"
          "xorq %[r1], %[g0]\n\txorq %[r1], %[g0]\n\t")
CT_GPR_FN(mulx_data_tput, "", 12,
          "movq %[g0], %%rdx\n\tmulxq %[g1], %[r0], %[r1]\n\t"
          "mulxq %[g1], %[r2], %[r3]\n\t")

// ---- VP2INTERSECT ------------------------------------------------------------
CT_P2I_FN(vp2intersectd_data_lat, 16,
          "vp2intersectd %[v1], %[v0], %%k2\n\tvpmovm2d %%k2, %[t]\n\t"
          XOR2("%[t]", "%[v0]"))
CT_P2I_FN(vp2intersectd_data_tput, 6,
          "vp2intersectd %[v1], %[v0], %%k0\n\tvp2intersectd %[v1], %[v0], %%k2\n\t"
          "vp2intersectd %[v1], %[v0], %%k4\n\tvp2intersectd %[v1], %[v0], %%k6\n\t")
CT_P2I_FN(vp2intersectq_data_lat, 16,
          "vp2intersectq %[v1], %[v0], %%k2\n\tvpmovm2q %%k2, %[t]\n\t"
          XOR2("%[t]", "%[v0]"))
CT_P2I_FN(vp2intersectq_data_tput, 6,
          "vp2intersectq %[v1], %[v0], %%k0\n\tvp2intersectq %[v1], %[v0], %%k2\n\t"
          "vp2intersectq %[v1], %[v0], %%k4\n\tvp2intersectq %[v1], %[v0], %%k6\n\t")

// ---- instrument controls ---------------------------------------------------
// A chain of one-cycle ADDs: the cycle ruler, and (with one more chained ADD
// in every loop iteration) a known difference of `iters` cycles per sample.
// 64-bit DIV: a real operand-dependent latency on current x86 cores.
//
// The known difference lies inside the steady-state chain, where one more
// chained ADD costs one cycle.  An extra instruction next to the fences does
// not: the chain's first cycles overlap the clock reads, and how much of an
// ADD placed there is absorbed depends on the core (on Ice Lake-SP one ADD
// ahead of the loop read -0.4 to +0.3 cycles).  The pair compares two
// different kernels, so they share their layout: the base runs the same ADD
// off the chain, and both start on a 64-byte line.
CT_GPR_FN(ruler_add, "", 16, "addq %[g1], %[r0]\n\t")
__attribute__((aligned(64)))
CT_GPR_FN(ruler_add_off_chain, "", 1,
          ".rept 16\n\taddq %[g1], %[r0]\n\t.endr\n\taddq %[g1], %[r1]\n\t")
__attribute__((aligned(64)))
CT_GPR_FN(ruler_add_plus_one, "", 1,
          ".rept 16\n\taddq %[g1], %[r0]\n\t.endr\n\taddq %[g1], %[r0]\n\t")
CT_GPR_FN(div64_lat, "", 16,
          "movq %[g0], %%rax\n\txorl %%edx, %%edx\n\tdivq %[g1]\n\t"
          "xorq %%rdx, %[g0]\n\txorq %%rdx, %[g0]\n\t")

// ---------------------------------------------------------------------------
// Operand classes
// ---------------------------------------------------------------------------

class Rng {
 public:
  explicit Rng(uint64_t seed) {
    for (uint64_t& w : s_) {
      seed += 0x9E3779B97F4A7C15ull;
      uint64_t z = seed;
      z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
      z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
      w = z ^ (z >> 31);
    }
  }
  uint64_t Next() {  // xoshiro256**
    const uint64_t result = Rotl(s_[1] * 5, 7) * 9;
    const uint64_t t = s_[1] << 17;
    s_[2] ^= s_[0];
    s_[3] ^= s_[1];
    s_[1] ^= s_[2];
    s_[0] ^= s_[3];
    s_[2] ^= t;
    s_[3] = Rotl(s_[3], 45);
    return result;
  }
  uint64_t Below(uint64_t n) {
    return static_cast<uint64_t>((static_cast<unsigned __int128>(Next()) * n) >> 64);
  }

 private:
  static uint64_t Rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
  uint64_t s_[4];
};

using Fill = std::function<void(Operands&, Rng&)>;

struct OperandClass {
  std::string name;
  Fill fill;
  bool fresh = false;        // redrawn every round (otherwise one fixed value)
  Kernel kernel = nullptr;   // overrides the entry's kernel (controls only)
};
using ClassList = std::vector<OperandClass>;  // [0] is the reference

uint64_t LowBits(unsigned n) { return n >= 64 ? ~uint64_t{0} : (uint64_t{1} << n) - 1; }

// 1..3 distinct random bit positions below `width`.
uint64_t Sparse(Rng& r, unsigned width) {
  uint64_t m = 0;
  const unsigned bits = 1 + static_cast<unsigned>(r.Below(3));
  for (unsigned i = 0; i < bits; ++i) m |= uint64_t{1} << r.Below(width);
  return m;
}

using LaneFn = std::function<uint64_t(unsigned lane, Rng&)>;

void SetLanes(uint8_t* dst, unsigned lane_bytes, const LaneFn& f, Rng& r) {
  for (unsigned i = 0; i < 64 / lane_bytes; ++i) {
    const uint64_t x = f(i, r);
    std::memcpy(dst + i * lane_bytes, &x, lane_bytes);
  }
}

OperandClass Lanes(std::string name, int slot, unsigned lane_bytes, bool fresh,
                   LaneFn f) {
  return {std::move(name),
          [=](Operands& o, Rng& r) { SetLanes(o.v[slot], lane_bytes, f, r); },
          fresh};
}
OperandClass Bytes(std::string name, int slot, bool fresh, LaneFn f) {
  return Lanes(std::move(name), slot, 1, fresh, std::move(f));
}
OperandClass MaskValue(std::string name, int slot, bool fresh,
                       std::function<uint64_t(Rng&)> f) {
  return {std::move(name), [=](Operands& o, Rng& r) { o.k[slot] = f(r); }, fresh};
}
OperandClass GprValue(std::string name, int slot, bool fresh,
                      std::function<uint64_t(Rng&)> f) {
  return {std::move(name), [=](Operands& o, Rng& r) { o.g[slot] = f(r); }, fresh};
}
OperandClass Pair(std::string name, int a, int b, unsigned lane_bytes, bool fresh,
                  std::function<std::pair<uint64_t, uint64_t>(unsigned, Rng&)> f) {
  return {std::move(name),
          [=](Operands& o, Rng& r) {
            for (unsigned i = 0; i < 64 / lane_bytes; ++i) {
              const auto xy = f(i, r);
              std::memcpy(o.v[a] + i * lane_bytes, &xy.first, lane_bytes);
              std::memcpy(o.v[b] + i * lane_bytes, &xy.second, lane_bytes);
            }
          },
          fresh};
}

// Permutation index for vpermb (64 entries, bits 6-7 ignored).
ClassList ByteIndex64(int s) {
  return {
      Bytes("random", s, true, [](unsigned, Rng& r) { return r.Next(); }),
      Bytes("identity", s, false, [](unsigned i, Rng&) { return i; }),
      Bytes("zero", s, false, [](unsigned, Rng&) { return 0; }),
      Bytes("last", s, false, [](unsigned, Rng&) { return 63; }),
      Bytes("reverse", s, false, [](unsigned i, Rng&) { return 63 - i; }),
      Bytes("rotate1", s, false, [](unsigned i, Rng&) { return (i + 1) & 63; }),
      Bytes("swap-halves", s, false, [](unsigned i, Rng&) { return i ^ 32; }),
      Bytes("ignored-bits", s, false, [](unsigned i, Rng&) { return i | 0xC0; }),
      Bytes("in-range", s, true, [](unsigned, Rng& r) { return r.Next() & 63; }),
  };
}

// Two-table byte index for vpermt2b/vpermi2b (bit 6 picks the table, bit 7
// ignored).
ClassList ByteIndex128(int s) {
  return {
      Bytes("random", s, true, [](unsigned, Rng& r) { return r.Next(); }),
      Bytes("identity-a", s, false, [](unsigned i, Rng&) { return i; }),
      Bytes("identity-b", s, false, [](unsigned i, Rng&) { return i | 64; }),
      Bytes("zero", s, false, [](unsigned, Rng&) { return 0; }),
      Bytes("last", s, false, [](unsigned, Rng&) { return 127; }),
      Bytes("alternate-ab", s, false,
            [](unsigned i, Rng&) { return i ^ ((i & 1) << 6); }),
      Bytes("reverse", s, false, [](unsigned i, Rng&) { return 127 - i; }),
      Bytes("interleave", s, false,
            [](unsigned i, Rng&) { return (i >> 1) | ((i & 1) << 6); }),
      Bytes("bit7-set", s, false, [](unsigned i, Rng&) { return i | 0x80; }),
      Bytes("in-range", s, true, [](unsigned, Rng& r) { return r.Next() & 127; }),
  };
}

// vpshufb control: low 4 bits index the 128-bit lane, bit 7 zeroes the byte.
ClassList ShufbIndex(int s) {
  return {
      Bytes("random", s, true, [](unsigned, Rng& r) { return r.Next(); }),
      Bytes("identity", s, false, [](unsigned i, Rng&) { return i & 15; }),
      Bytes("clear-all", s, false, [](unsigned, Rng&) { return 0x80; }),
      Bytes("zero", s, false, [](unsigned, Rng&) { return 0; }),
      Bytes("reverse", s, false, [](unsigned i, Rng&) { return 15 - (i & 15); }),
      Bytes("clear-half", s, false,
            [](unsigned i, Rng&) { return (i & 1) ? 0x80u : (i & 15); }),
      Bytes("no-clear", s, true, [](unsigned, Rng& r) { return r.Next() & 15; }),
  };
}

// Word/dword/qword permutation index over `entries` selectable elements
// (2 x lanes for the two-table forms); the bits above are ignored.
ClassList LaneIndex(int s, unsigned lane_bytes, unsigned entries) {
  const unsigned lanes = 64 / lane_bytes;
  const uint64_t width = LowBits(8 * lane_bytes);
  ClassList c = {
      Lanes("random", s, lane_bytes, true, [](unsigned, Rng& r) { return r.Next(); }),
      Lanes("identity", s, lane_bytes, false, [](unsigned i, Rng&) { return i; }),
      Lanes("zero", s, lane_bytes, false, [](unsigned, Rng&) { return 0; }),
      Lanes("reverse", s, lane_bytes, false,
            [=](unsigned i, Rng&) { return entries - 1 - i; }),
      Lanes("rotate1", s, lane_bytes, false,
            [=](unsigned i, Rng&) { return (i + 1) % entries; }),
      Lanes("ignored-bits", s, lane_bytes, false,
            [=](unsigned i, Rng&) { return (i | ~uint64_t{entries - 1}) & width; }),
      Lanes("in-range", s, lane_bytes, true,
            [=](unsigned, Rng& r) { return r.Below(entries); }),
  };
  if (entries > lanes) {
    c.push_back(Lanes("identity-b", s, lane_bytes, false,
                      [=](unsigned i, Rng&) { return i + lanes; }));
  }
  return c;
}

// Write/zeroing masks over `lanes` elements.  "clear-all" is the zero mask.
ClassList Masks(int s, unsigned lanes) {
  const uint64_t low = LowBits(lanes);
  const uint64_t half = LowBits(lanes / 2);
  return {
      MaskValue("random", s, true, [=](Rng& r) { return r.Next() & low; }),
      MaskValue("clear-all", s, false, [](Rng&) { return uint64_t{0}; }),
      MaskValue("all", s, false, [=](Rng&) { return low; }),
      MaskValue("lowest", s, false, [](Rng&) { return uint64_t{1}; }),
      MaskValue("highest", s, false, [=](Rng&) { return uint64_t{1} << (lanes - 1); }),
      MaskValue("even", s, false, [=](Rng&) { return 0x5555555555555555ull & low; }),
      MaskValue("odd", s, false, [=](Rng&) { return 0xAAAAAAAAAAAAAAAAull & low; }),
      MaskValue("low-half", s, false, [=](Rng&) { return half; }),
      MaskValue("high-half", s, false, [=](Rng&) { return low & ~half; }),
      MaskValue("sparse", s, true, [=](Rng& r) { return Sparse(r, lanes); }),
      MaskValue("dense", s, true, [=](Rng& r) { return low & ~Sparse(r, lanes); }),
  };
}

// Mask-register operands of k-instructions: the full 64 bits are data.
ClassList MaskData(int s) { return Masks(s, 64); }

// Generic secret vector data.
ClassList Data(int s) {
  return {
      Lanes("random", s, 8, true, [](unsigned, Rng& r) { return r.Next(); }),
      Lanes("zero", s, 8, false, [](unsigned, Rng&) { return 0; }),
      Lanes("ones", s, 8, false, [](unsigned, Rng&) { return ~uint64_t{0}; }),
      Bytes("iota", s, false, [](unsigned i, Rng&) { return i; }),
      Bytes("sign", s, false, [](unsigned, Rng&) { return 0x80; }),
      Lanes("alternate", s, 8, false,
            [](unsigned i, Rng&) { return (i & 1) ? ~uint64_t{0} : 0; }),
      {"sparse",
       [s](Operands& o, Rng& r) {
         std::memset(o.v[s], 0, 64);
         const uint64_t bits = Sparse(r, 64);
         for (unsigned i = 0; i < 64; ++i) {
           if ((bits >> i) & 1) o.v[s][r.Below(64)] |= uint8_t(1u << r.Below(8));
         }
       },
       true},
      {"dense",
       [s](Operands& o, Rng& r) {
         std::memset(o.v[s], 0xFF, 64);
         const uint64_t bits = Sparse(r, 64);
         for (unsigned i = 0; i < 64; ++i) {
           if ((bits >> i) & 1) o.v[s][r.Below(64)] &= uint8_t(~(1u << r.Below(8)));
         }
       },
       true},
  };
}

// Two secret data vectors compared or combined lane by lane.
ClassList DataPair(int a, int b, unsigned lane_bytes) {
  const uint64_t width = LowBits(8 * lane_bytes);
  const uint64_t top = uint64_t{1} << (8 * lane_bytes - 1);
  using P = std::pair<uint64_t, uint64_t>;
  return {
      Pair("random", a, b, lane_bytes, true,
           [](unsigned, Rng& r) { return P{r.Next(), r.Next()}; }),
      Pair("equal", a, b, lane_bytes, true, [](unsigned, Rng& r) {
        const uint64_t x = r.Next();
        return P{x, x};
      }),
      Pair("zero", a, b, lane_bytes, false, [](unsigned, Rng&) { return P{0, 0}; }),
      Pair("ones", a, b, lane_bytes, false,
           [](unsigned, Rng&) { return P{~uint64_t{0}, ~uint64_t{0}}; }),
      Pair("a<b", a, b, lane_bytes, true, [=](unsigned, Rng& r) {
        const uint64_t x = r.Next() & (top - 1);
        return P{x, x | top};
      }),
      Pair("a>b", a, b, lane_bytes, true, [=](unsigned, Rng& r) {
        const uint64_t x = r.Next() & (top - 1);
        return P{x | top, x};
      }),
      Pair("complement", a, b, lane_bytes, true, [=](unsigned, Rng& r) {
        const uint64_t x = r.Next();
        return P{x, ~x & width};
      }),
      Pair("half-equal", a, b, lane_bytes, true, [](unsigned, Rng& r) {
        const uint64_t x = r.Next();
        return P{x, (r.Next() & 1) ? x : r.Next()};
      }),
  };
}

// Per-lane shift counts; counts >= the lane width shift everything out.
ClassList ShiftCounts(int s, unsigned lane_bits) {
  const unsigned lb = lane_bits / 8;
  const uint64_t w = lane_bits;
  return {
      Lanes("in-range", s, lb, true, [=](unsigned, Rng& r) { return r.Below(w); }),
      Lanes("zero", s, lb, false, [](unsigned, Rng&) { return 0; }),
      Lanes("one", s, lb, false, [](unsigned, Rng&) { return 1; }),
      Lanes("max", s, lb, false, [=](unsigned, Rng&) { return w - 1; }),
      Lanes("width", s, lb, false, [=](unsigned, Rng&) { return w; }),
      Lanes("byte-max", s, lb, false, [](unsigned, Rng&) { return 255; }),
      Lanes("huge", s, lb, false, [=](unsigned, Rng&) { return uint64_t{1} << (w - 1); }),
      Lanes("any", s, lb, true, [](unsigned, Rng& r) { return r.Next(); }),
  };
}

// VPCONFLICT inputs, from no duplicates to all duplicates.
ClassList ConflictInputs(int s, unsigned lane_bytes) {
  const unsigned lanes = 64 / lane_bytes;
  return {
      Lanes("random", s, lane_bytes, true, [](unsigned, Rng& r) { return r.Next(); }),
      Lanes("distinct", s, lane_bytes, false, [](unsigned i, Rng&) { return i; }),
      Lanes("all-zero", s, lane_bytes, false, [](unsigned, Rng&) { return 0; }),
      {"all-equal",
       [=](Operands& o, Rng& r) {
         const uint64_t x = r.Next();
         SetLanes(o.v[s], lane_bytes, [=](unsigned, Rng&) { return x; }, r);
       },
       true},
      Lanes("pairs", s, lane_bytes, false, [](unsigned i, Rng&) { return i / 2; }),
      Lanes("halves", s, lane_bytes, false,
            [=](unsigned i, Rng&) { return i % (lanes / 2); }),
      Lanes("small-alphabet", s, lane_bytes, true,
            [](unsigned, Rng& r) { return r.Next() & 3; }),
  };
}

// VP2INTERSECT operand pairs, from no matches to all pairs matching.
ClassList IntersectInputs(int a, int b, unsigned lane_bytes) {
  const unsigned lanes = 64 / lane_bytes;
  using P = std::pair<uint64_t, uint64_t>;
  return {
      Pair("random", a, b, lane_bytes, true,
           [](unsigned, Rng& r) { return P{r.Next(), r.Next()}; }),
      Pair("identical", a, b, lane_bytes, false,
           [](unsigned i, Rng&) { return P{i + 1000, i + 1000}; }),
      Pair("disjoint", a, b, lane_bytes, false,
           [=](unsigned i, Rng&) { return P{i, i + lanes}; }),
      Pair("all-equal", a, b, lane_bytes, false, [](unsigned, Rng&) { return P{0, 0}; }),
      Pair("reversed", a, b, lane_bytes, false,
           [=](unsigned i, Rng&) { return P{i, lanes - 1 - i}; }),
      {"one-match",
       [=](Operands& o, Rng& r) {
         for (unsigned i = 0; i < lanes; ++i) {
           const uint64_t x = i, y = i + lanes;
           std::memcpy(o.v[a] + i * lane_bytes, &x, lane_bytes);
           std::memcpy(o.v[b] + i * lane_bytes, &y, lane_bytes);
         }
         const uint64_t j = r.Below(lanes), k = r.Below(lanes);
         std::memcpy(o.v[b] + j * lane_bytes, o.v[a] + k * lane_bytes, lane_bytes);
       },
       true},
      Pair("small-alphabet", a, b, lane_bytes, true,
           [](unsigned, Rng& r) { return P{r.Next() & 3, r.Next() & 3}; }),
  };
}

// AES state or round key.
ClassList AesBlock(int s) {
  return {
      Lanes("random", s, 8, true, [](unsigned, Rng& r) { return r.Next(); }),
      Lanes("zero", s, 8, false, [](unsigned, Rng&) { return 0; }),
      Lanes("ones", s, 8, false, [](unsigned, Rng&) { return ~uint64_t{0}; }),
      Bytes("iota", s, false, [](unsigned i, Rng&) { return i; }),
  };
}

// 64-bit scalar data: occupancy masks, popcount/tzcnt inputs.
ClassList Gpr64(int s) {
  return {
      GprValue("random", s, true, [](Rng& r) { return r.Next(); }),
      GprValue("zero", s, false, [](Rng&) { return uint64_t{0}; }),
      GprValue("ones", s, false, [](Rng&) { return ~uint64_t{0}; }),
      GprValue("lowest", s, false, [](Rng&) { return uint64_t{1}; }),
      GprValue("highest", s, false, [](Rng&) { return uint64_t{1} << 63; }),
      GprValue("even", s, false, [](Rng&) { return 0x5555555555555555ull; }),
      GprValue("odd", s, false, [](Rng&) { return 0xAAAAAAAAAAAAAAAAull; }),
      GprValue("sparse", s, true, [](Rng& r) { return Sparse(r, 64); }),
      GprValue("dense", s, true, [](Rng& r) { return ~Sparse(r, 64); }),
  };
}

// PDEP source operand: the library deposits LowMask64(count).
ClassList LowMasks(int s) {
  return {
      GprValue("random", s, true, [](Rng& r) { return r.Next(); }),
      GprValue("zero", s, false, [](Rng&) { return uint64_t{0}; }),
      GprValue("ones", s, false, [](Rng&) { return ~uint64_t{0}; }),
      GprValue("low-1", s, false, [](Rng&) { return uint64_t{1}; }),
      GprValue("low-32", s, false, [](Rng&) { return LowBits(32); }),
      GprValue("low-63", s, false, [](Rng&) { return LowBits(63); }),
      GprValue("low-random", s, true,
               [](Rng& r) { return LowBits(static_cast<unsigned>(r.Below(65))); }),
  };
}

// Scalar shift counts and BZHI indices (SHLX masks to 6 bits, BZHI reads 8).
ClassList Counts(int s) {
  return {
      GprValue("in-range", s, true, [](Rng& r) { return r.Next() & 63; }),
      GprValue("zero", s, false, [](Rng&) { return uint64_t{0}; }),
      GprValue("one", s, false, [](Rng&) { return uint64_t{1}; }),
      GprValue("max", s, false, [](Rng&) { return uint64_t{63}; }),
      GprValue("width", s, false, [](Rng&) { return uint64_t{64}; }),
      GprValue("byte-max", s, false, [](Rng&) { return uint64_t{255}; }),
      GprValue("garbage-high", s, true,
               [](Rng& r) { const uint64_t x = r.Next(); return (x & 63) | (x & ~uint64_t{0xFF}); }),
  };
}

// CMOVNZ condition input.
ClassList Conditions(int s) {
  return {
      GprValue("random-bit", s, true, [](Rng& r) { return r.Next() & 1; }),
      GprValue("zero", s, false, [](Rng&) { return uint64_t{0}; }),
      GprValue("one", s, false, [](Rng&) { return uint64_t{1}; }),
      GprValue("nonzero", s, true, [](Rng& r) { return r.Next() | 1; }),
  };
}

// CMOVBE after CMP g1, g0: g0 below, equal to or above g1.
ClassList Orderings(int s, int other) {
  return {
      GprValue("random", s, true, [](Rng& r) { return r.Next(); }),
      {"below", [=](Operands& o, Rng&) { o.g[s] = o.g[other] - 1; }, false},
      {"equal", [=](Operands& o, Rng&) { o.g[s] = o.g[other]; }, false},
      {"above", [=](Operands& o, Rng&) { o.g[s] = o.g[other] + 1; }, false},
  };
}

ClassList Dividends(int s) {
  return {
      GprValue("random", s, true, [](Rng& r) { return r.Next(); }),
      GprValue("one", s, false, [](Rng&) { return uint64_t{1}; }),
      GprValue("small", s, true, [](Rng& r) { return r.Next() & 0xFF; }),
      GprValue("two-pow-32", s, false, [](Rng&) { return uint64_t{1} << 32; }),
      GprValue("max", s, false, [](Rng&) { return ~uint64_t{0}; }),
  };
}

// ---------------------------------------------------------------------------
// The instruction table
// ---------------------------------------------------------------------------

enum class Feature {
  kAvx512, kVbmi, kVbmi2, kCd, kVpopcntdq, kVp2intersect, kVaes, kAes, kBmi1,
  kBmi2, kLzcnt, kPopcnt,
};

const char* FeatureName(Feature f) {
  switch (f) {
    case Feature::kAvx512: return "avx512f/bw/dq/vl";
    case Feature::kVbmi: return "avx512vbmi";
    case Feature::kVbmi2: return "avx512vbmi2";
    case Feature::kCd: return "avx512cd";
    case Feature::kVpopcntdq: return "avx512vpopcntdq";
    case Feature::kVp2intersect: return "avx512vp2intersect";
    case Feature::kVaes: return "vaes";
    case Feature::kAes: return "aes";
    case Feature::kBmi1: return "bmi";
    case Feature::kBmi2: return "bmi2";
    case Feature::kLzcnt: return "lzcnt";
    case Feature::kPopcnt: return "popcnt";
  }
  return "?";
}

bool Supported(Feature f) {
  __builtin_cpu_init();
  switch (f) {
    case Feature::kAvx512:
      return __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512bw") &&
             __builtin_cpu_supports("avx512dq") && __builtin_cpu_supports("avx512vl");
    case Feature::kVbmi: return __builtin_cpu_supports("avx512vbmi");
    case Feature::kVbmi2: return __builtin_cpu_supports("avx512vbmi2");
    case Feature::kCd: return __builtin_cpu_supports("avx512cd");
    case Feature::kVpopcntdq: return __builtin_cpu_supports("avx512vpopcntdq");
    case Feature::kVp2intersect: return __builtin_cpu_supports("avx512vp2intersect");
    case Feature::kVaes: return __builtin_cpu_supports("vaes");
    case Feature::kAes: return __builtin_cpu_supports("aes");
    case Feature::kBmi1: return __builtin_cpu_supports("bmi");
    case Feature::kBmi2: return __builtin_cpu_supports("bmi2");
    case Feature::kLzcnt: return __builtin_cpu_supports("lzcnt");
    case Feature::kPopcnt: return __builtin_cpu_supports("popcnt");
  }
  return false;
}

enum class Kind {
  kConstant,     // must be operand-independent
  kCalibration,  // known difference of `iters` cycles per sample: must be
                 // detected, measured near it, and with an error small
                 // enough to resolve one cycle per sample
  kVariable,     // known operand-dependent instruction: expected to be flagged
};

struct Entry {
  std::string key;   // census key: mnemonic, plus {k} / {k}{z} when masked
  std::string role;  // which operand the classes vary
  Feature feature;
  Kernel lat;
  Kernel tput;       // null: latency form only
  ClassList classes;
  Fill base;         // fixes the operands the classes do not vary
  Kind kind = Kind::kConstant;
};

#define KP(name) name##_lat, name##_tput

std::vector<Entry> BuildEntries() {
  using F = Feature;
  std::vector<Entry> e;
  auto add = [&](const char* key, const char* role, F f, Kernel lat, Kernel tput,
                 ClassList classes, Fill base = nullptr) {
    e.push_back({key, role, f, lat, tput, std::move(classes), std::move(base)});
  };
  // Operands the classes leave alone stay at one random value per entry.  A
  // few masked forms fix their data so the mask decides the result: equal
  // inputs for an equality compare, disjoint bits for a test-not.
  auto equal_v1_v2 = [](Operands& o, Rng&) { std::memcpy(o.v[2], o.v[1], 64); };
  auto disjoint_v1_v2 = [](Operands& o, Rng&) {
    for (int i = 0; i < 64; ++i) o.v[2][i] = static_cast<uint8_t>(~o.v[1][i]);
  };
  auto below_v1_v2 = [](Operands& o, Rng&) {
    for (int i = 0; i < 64; ++i) {
      o.v[1][i] &= 0x7F;
      o.v[2][i] = o.v[1][i] | 0x80;
    }
  };
  auto in_range_counts = [](Operands& o, Rng&) {
    for (int i = 0; i < 64; i += 8) {
      const uint64_t count = o.v[0][i] & 63;
      std::memcpy(o.v[0] + i, &count, 8);
    }
  };

  // Permutes and shuffles: the routing index is the secret.
  add("vpermb", "ctrl", F::kVbmi, KP(vpermb_ctrl), ByteIndex64(0));
  add("vpermb", "data", F::kVbmi, KP(vpermb_data), Data(1));
  add("vpermb{k}", "mask", F::kVbmi, KP(vpermb_km), Masks(0, 64));
  add("vpermb{k}{z}", "mask", F::kVbmi, KP(vpermb_kz), Masks(0, 64));
  add("vpermt2b", "ctrl", F::kVbmi, KP(vpermt2b_ctrl), ByteIndex128(0));
  add("vpermt2b", "data", F::kVbmi, KP(vpermt2b_data), Data(1));
  add("vpermt2b{k}{z}", "mask", F::kVbmi, KP(vpermt2b_kz), Masks(0, 64));
  // Merge-masked, the first table the merge source (the tree ORAM's fold of
  // an odd last source word into its accumulator).
  add("vpermt2b{k}", "mask", F::kVbmi, KP(vpermt2b_km), Masks(0, 64));
  add("vpermi2b", "ctrl", F::kVbmi, KP(vpermi2b_ctrl), ByteIndex128(0));
  add("vpermi2b{k}{z}", "mask", F::kVbmi, KP(vpermi2b_kz), Masks(0, 64));
  add("vpermt2w", "ctrl", F::kAvx512, KP(vpermt2w_ctrl), LaneIndex(0, 2, 64));
  add("vpermi2w", "ctrl", F::kAvx512, KP(vpermi2w_ctrl), LaneIndex(0, 2, 64));
  add("vpermt2d", "ctrl", F::kAvx512, KP(vpermt2d_ctrl), LaneIndex(0, 4, 32));
  add("vpermi2d", "ctrl", F::kAvx512, KP(vpermi2d_ctrl), LaneIndex(0, 4, 32));
  add("vpermd", "ctrl", F::kAvx512, KP(vpermd_ctrl), LaneIndex(0, 4, 16));
  add("vpermt2q", "ctrl", F::kAvx512, KP(vpermt2q_ctrl), LaneIndex(0, 8, 16));
  add("vpermi2q", "ctrl", F::kAvx512, KP(vpermi2q_ctrl), LaneIndex(0, 8, 16));
  add("vpermq", "ctrl", F::kAvx512, KP(vpermq_ctrl), LaneIndex(0, 8, 8));
  add("vpshufb", "ctrl", F::kAvx512, KP(vpshufb_ctrl), ShufbIndex(0));
  add("vpshufb{k}", "mask", F::kAvx512, KP(vpshufb_km), Masks(0, 64));
  add("vpsllvq", "count", F::kAvx512, KP(vpsllvq_count), ShiftCounts(0, 64));
  add("vpsrlvq", "count", F::kAvx512, KP(vpsrlvq_count), ShiftCounts(0, 64));
  add("vpsllvq{k}{z}", "mask", F::kAvx512, KP(vpsllvq_kz), Masks(0, 8), in_range_counts);

  // Secret masks selecting, compressing and merging lanes.
  add("vpcompressb{k}{z}", "mask", F::kVbmi2, KP(vpcompressb_kz), Masks(0, 64));
  add("vpexpandb{k}", "mask", F::kVbmi2, KP(vpexpandb_km), Masks(0, 64));
  add("vmovdqu8{k}", "mask", F::kAvx512, KP(vmovdqu8_km), Masks(0, 64));
  add("vmovdqu8{k}{z}", "mask", F::kAvx512, KP(vmovdqu8_kz), Masks(0, 64));
  add("vmovdqa32{k}", "mask", F::kAvx512, KP(vmovdqa32_km), Masks(0, 16));
  add("vmovdqa32{k}{z}", "mask", F::kAvx512, KP(vmovdqa32_kz), Masks(0, 16));
  add("vmovdqa64{k}", "mask", F::kAvx512, KP(vmovdqa64_km), Masks(0, 8));
  add("vmovdqa64{k}{z}", "mask", F::kAvx512, KP(vmovdqa64_kz), Masks(0, 8));
  add("vpblendmb{k}", "mask", F::kAvx512, KP(vpblendmb_km), Masks(0, 64));
  add("vpblendmd{k}", "mask", F::kAvx512, KP(vpblendmd_km), Masks(0, 16));
  add("vpblendmq{k}", "mask", F::kAvx512, KP(vpblendmq_km), Masks(0, 8));
  add("vpaddb{k}", "mask", F::kAvx512, KP(vpaddb_km), Masks(0, 64));
  add("vpaddq{k}", "mask", F::kAvx512, KP(vpaddq_km), Masks(0, 8));
  add("vpabsb{k}{z}", "mask", F::kAvx512, KP(vpabsb_kz), Masks(0, 64));
  add("vshufi64x2{k}{z}", "mask", F::kAvx512, KP(vshufi64x2_kz), Masks(0, 8));
  add("vpsrld{k}", "mask", F::kAvx512, KP(vpsrld_km), Masks(0, 16));
  add("vpsrld{k}{z}", "mask", F::kAvx512, KP(vpsrld_kz), Masks(0, 16));
  add("vpbroadcastq{k}", "mask", F::kAvx512, KP(vpbroadcastq_km), Masks(0, 8));
  add("vpbroadcastq{k}{z}", "mask", F::kAvx512, KP(vpbroadcastq_kz), Masks(0, 8));
  add("vpbroadcastd{k}", "mask", F::kAvx512, KP(vpbroadcastd_km), Masks(0, 16));
  add("vpbroadcastd{k}{z}", "mask", F::kAvx512, KP(vpbroadcastd_kz), Masks(0, 16));
  add("vpbroadcastb{k}", "mask", F::kAvx512, KP(vpbroadcastb_km), Masks(0, 64));
  add("vpbroadcastb{k}{z}", "mask", F::kAvx512, KP(vpbroadcastb_kz), Masks(0, 64));
  add("vpmovm2b", "mask", F::kAvx512, KP(vpmovm2b_mask), Masks(0, 64));
  add("vpmovm2q", "mask", F::kAvx512, KP(vpmovm2q_mask), Masks(0, 8));

  // Compares and tests producing masks from secret data.
  add("vpcmpeqb", "data", F::kAvx512, KP(vpcmpeqb_data), DataPair(1, 2, 1));
  add("vpcmpeqd", "data", F::kAvx512, KP(vpcmpeqd_data), DataPair(1, 2, 4));
  add("vpcmpeqq", "data", F::kAvx512, KP(vpcmpeqq_data), DataPair(1, 2, 8));
  add("vpcmpub", "data", F::kAvx512, KP(vpcmpub_data), DataPair(1, 2, 1));
  add("vpcmpud", "data", F::kAvx512, KP(vpcmpud_data), DataPair(1, 2, 4));
  add("vpcmpuq", "data", F::kAvx512, KP(vpcmpuq_data), DataPair(1, 2, 8));
  add("vpcmpb", "data", F::kAvx512, KP(vpcmpb_data), DataPair(1, 2, 1));
  add("vpcmpd", "data", F::kAvx512, KP(vpcmpd_data), DataPair(1, 2, 4));
  add("vpcmpq", "data", F::kAvx512, KP(vpcmpq_data), DataPair(1, 2, 8));
  add("vptestmb", "data", F::kAvx512, KP(vptestmb_data), DataPair(1, 2, 1));
  add("vptestnmb", "data", F::kAvx512, KP(vptestnmb_data), DataPair(1, 2, 1));
  add("vptestmd", "data", F::kAvx512, KP(vptestmd_data), DataPair(1, 2, 4));
  add("vptestnmd", "data", F::kAvx512, KP(vptestnmd_data), DataPair(1, 2, 4));
  add("vptestmq", "data", F::kAvx512, KP(vptestmq_data), DataPair(1, 2, 8));
  add("vptestnmq", "data", F::kAvx512, KP(vptestnmq_data), DataPair(1, 2, 8));
  add("vpmovb2m", "data", F::kAvx512, KP(vpmovb2m_data), Data(1));
  add("vpcmpeqb{k}", "mask", F::kAvx512, KP(vpcmpeqb_km), Masks(0, 64), equal_v1_v2);
  add("vpcmpeqd{k}", "mask", F::kAvx512, KP(vpcmpeqd_km), Masks(0, 16), equal_v1_v2);
  add("vpcmpeqq{k}", "mask", F::kAvx512, KP(vpcmpeqq_km), Masks(0, 8), equal_v1_v2);
  add("vpcmpub{k}", "mask", F::kAvx512, KP(vpcmpub_km), Masks(0, 64), below_v1_v2);
  add("vpcmpd{k}", "mask", F::kAvx512, KP(vpcmpd_km), Masks(0, 16),
      [](Operands& o, Rng&) {  // signed v1 < v2 in every dword lane
        for (int i = 0; i < 64; i += 4) {
          uint32_t a;
          std::memcpy(&a, o.v[1] + i, 4);
          a &= 0x3FFFFFFFu;
          const uint32_t b = a + 1;
          std::memcpy(o.v[1] + i, &a, 4);
          std::memcpy(o.v[2] + i, &b, 4);
        }
      });
  add("vptestmb{k}", "mask", F::kAvx512, KP(vptestmb_km), Masks(0, 64), equal_v1_v2);
  add("vptestnmb{k}", "mask", F::kAvx512, KP(vptestnmb_km), Masks(0, 64), disjoint_v1_v2);

  // Mask-register instructions on secret masks.
  add("korq", "data", F::kAvx512, KP(korq_data), MaskData(0));
  add("kord", "data", F::kAvx512, KP(kord_data), MaskData(0));
  add("korw", "data", F::kAvx512, KP(korw_data), MaskData(0));
  add("korb", "data", F::kAvx512, KP(korb_data), MaskData(0));
  add("kandq", "data", F::kAvx512, KP(kandq_data), MaskData(0));
  add("kandnq", "data", F::kAvx512, KP(kandnq_data), MaskData(0));
  add("kxorq", "data", F::kAvx512, KP(kxorq_data), MaskData(0));
  add("kxord", "data", F::kAvx512, KP(kxord_data), MaskData(0));
  add("kxorw", "data", F::kAvx512, KP(kxorw_data), MaskData(0));
  add("kxorb", "data", F::kAvx512, KP(kxorb_data), MaskData(0));
  add("kxnorq", "data", F::kAvx512, KP(kxnorq_data), MaskData(0));
  add("kxnorb", "data", F::kAvx512, KP(kxnorb_data), MaskData(0));
  add("kandb", "data", F::kAvx512, KP(kandb_data), MaskData(0));
  add("kunpckbw", "data", F::kAvx512, KP(kunpckbw_data), MaskData(0));
  add("knotq", "data", F::kAvx512, KP(knotq_data), MaskData(0));
  add("knotb", "data", F::kAvx512, KP(knotb_data), MaskData(0));
  add("kshiftrq", "data", F::kAvx512, KP(kshiftrq_data), MaskData(0));
  add("kshiftlq", "data", F::kAvx512, KP(kshiftlq_data), MaskData(0));
  add("kshiftld", "data", F::kAvx512, KP(kshiftld_data), MaskData(0));
  add("kshiftrw", "data", F::kAvx512, KP(kshiftrw_data), MaskData(0));
  add("kshiftrb", "data", F::kAvx512, KP(kshiftrb_data), MaskData(0));
  add("kshiftlb", "data", F::kAvx512, KP(kshiftlb_data), MaskData(0));
  add("kortestq", "data", F::kAvx512, KP(kortestq_data), MaskData(0));
  add("kortestd", "data", F::kAvx512, KP(kortestd_data), MaskData(0));
  add("kortestw", "data", F::kAvx512, KP(kortestw_data), MaskData(0));
  add("kortestb", "data", F::kAvx512, KP(kortestb_data), MaskData(0));
  add("kmovq", "data", F::kAvx512, KP(kmovq_data), Gpr64(0));
  add("kmovd", "data", F::kAvx512, KP(kmovd_data), Gpr64(0));
  add("kmovw", "data", F::kAvx512, KP(kmovw_data), Gpr64(0));
  add("kmovb", "data", F::kAvx512, KP(kmovb_data), Gpr64(0));

  // Vector arithmetic and data movement on secret data.
  const std::pair<const char*, std::pair<Kernel, Kernel>> binary[] = {
      {"vpaddq", {KP(vpaddq_data)}},       {"vpaddd", {KP(vpaddd_data)}},
      {"vpaddb", {KP(vpaddb_data)}},       {"vpsubq", {KP(vpsubq_data)}},
      {"vpsubd", {KP(vpsubd_data)}},       {"vpsubb", {KP(vpsubb_data)}},
      {"vpsubusb", {KP(vpsubusb_data)}},
      {"vpxord", {KP(vpxord_data)}},       {"vpxorq", {KP(vpxorq_data)}},
      {"vpandd", {KP(vpandd_data)}},       {"vpandq", {KP(vpandq_data)}},
      {"vpandnd", {KP(vpandnd_data)}},     {"vpandnq", {KP(vpandnq_data)}},
      {"vpord", {KP(vpord_data)}},
      {"vporq", {KP(vporq_data)}},         {"vpmaxuq", {KP(vpmaxuq_data)}},
      {"vpmaxud", {KP(vpmaxud_data)}},     {"vpmaxub", {KP(vpmaxub_data)}},
      {"vpminuq", {KP(vpminuq_data)}},     {"vpminud", {KP(vpminud_data)}},
      {"vpmullq", {KP(vpmullq_data)}},     {"vpmulld", {KP(vpmulld_data)}},
      {"vpmuludq", {KP(vpmuludq_data)}},   {"vpackusdw", {KP(vpackusdw_data)}},
      {"vpackuswb", {KP(vpackuswb_data)}}, {"vpunpcklbw", {KP(vpunpcklbw_data)}},
      {"vpunpckhbw", {KP(vpunpckhbw_data)}}, {"vpunpcklwd", {KP(vpunpcklwd_data)}},
      {"vpunpckhwd", {KP(vpunpckhwd_data)}}, {"vpunpckldq", {KP(vpunpckldq_data)}},
      {"vpunpckhdq", {KP(vpunpckhdq_data)}}, {"vpunpcklqdq", {KP(vpunpcklqdq_data)}},
      {"vpunpckhqdq", {KP(vpunpckhqdq_data)}},
  };
  for (const auto& b : binary) {
    const std::string mn = b.first;
    const unsigned lane = mn.back() == 'q' ? 8 : mn.back() == 'd' ? 4 : 1;
    add(b.first, "data", F::kAvx512, b.second.first, b.second.second,
        DataPair(1, 2, lane));
  }
  add("vpternlogq", "data-xor3", F::kAvx512, KP(vpternlogq_xor3), Data(1));
  add("vpternlogq", "data-select", F::kAvx512, KP(vpternlogq_select), Data(1));
  add("vpternlogd", "data-select", F::kAvx512, KP(vpternlogd_select), Data(1));
  add("vpconflictd", "data", F::kCd, KP(vpconflictd_data), ConflictInputs(1, 4));
  add("vpconflictq", "data", F::kCd, KP(vpconflictq_data), ConflictInputs(1, 8));
  add("vp2intersectd", "data", F::kVp2intersect, KP(vp2intersectd_data),
      IntersectInputs(0, 1, 4));
  add("vp2intersectq", "data", F::kVp2intersect, KP(vp2intersectq_data),
      IntersectInputs(0, 1, 8));
  add("vpopcntq", "data", F::kVpopcntdq, KP(vpopcntq_data), Data(1));
  const std::pair<const char*, std::pair<Kernel, Kernel>> unary[] = {
      {"vpabsb", {KP(vpabsb_data)}},           {"vpshufd", {KP(vpshufd_data)}},
      {"vpslldq", {KP(vpslldq_data)}},         {"vpsrldq", {KP(vpsrldq_data)}},
      {"vpsrlw", {KP(vpsrlw_data)}},           {"vpsrld", {KP(vpsrld_data)}},
      {"vpsrlq", {KP(vpsrlq_data)}},           {"vpsraq", {KP(vpsraq_data)}},
      {"vpsllw", {KP(vpsllw_data)}},
      {"vpslld", {KP(vpslld_data)}},           {"vpsllq", {KP(vpsllq_data)}},
      {"vpmovqb", {KP(vpmovqb_data)}},         {"vpmovdb", {KP(vpmovdb_data)}},
      {"vpmovqd", {KP(vpmovqd_data)}},         {"vpmovzxdq", {KP(vpmovzxdq_data)}},
      {"vpmovzxwd", {KP(vpmovzxwd_data)}},     {"vpmovzxbw", {KP(vpmovzxbw_data)}},
      {"vpmovzxbq", {KP(vpmovzxbq_data)}},     {"vextracti64x2", {KP(vextracti64x2_data)}},
      {"vextracti32x4", {KP(vextracti32x4_data)}}, {"vextracti64x4", {KP(vextracti64x4_data)}},
      {"vextracti32x8", {KP(vextracti32x8_data)}}, {"vinserti64x2", {KP(vinserti64x2_data)}},
      {"vinserti32x4", {KP(vinserti32x4_data)}}, {"vinserti64x4", {KP(vinserti64x4_data)}},
      {"vinserti32x8", {KP(vinserti32x8_data)}}, {"vshufi64x2", {KP(vshufi64x2_data)}},
      {"vshufi32x4", {KP(vshufi32x4_data)}},   {"valignq", {KP(valignq_data)}},
      {"valignd", {KP(valignd_data)}},         {"vpalignr", {KP(vpalignr_data)}},
  };
  for (const auto& u : unary) {
    add(u.first, "data", F::kAvx512, u.second.first, u.second.second, Data(1));
  }
  auto count3_v2 = [](Operands& o, Rng&) {
    std::memset(o.v[2], 0, 64);
    o.v[2][0] = 3;
  };
  add("vpsrlw", "data-xcount", F::kAvx512, KP(vpsrlw_xcount_data), Data(1), count3_v2);
  add("vpsrlq", "data-xcount", F::kAvx512, KP(vpsrlq_xcount_data), Data(1), count3_v2);
  add("vpsllq", "data-xcount", F::kAvx512, KP(vpsllq_xcount_data), Data(1), count3_v2);
  add("vpxor", "data", F::kAvx512, KP(vpxor_data), DataPair(1, 2, 8));
  add("vpand", "data", F::kAvx512, KP(vpand_data), DataPair(1, 2, 8));
  add("vpblendw", "data", F::kAvx512, KP(vpblendw_data), Data(1));
  add("vperm2i128", "data", F::kAvx512, KP(vperm2i128_data), Data(1));
  add("vinserti128", "data", F::kAvx512, KP(vinserti128_data), Data(1));
  add("vptest", "data", F::kAvx512, KP(vptest_data), DataPair(1, 2, 8));
  add("vpandn", "data-xmm", F::kAvx512, KP(vpandn_x_data), DataPair(1, 2, 8));
  add("vpandn", "data-ymm", F::kAvx512, KP(vpandn_y_data), DataPair(1, 2, 8));
  add("vshufps", "data", F::kAvx512, KP(vshufps_data), DataPair(1, 2, 8));
  add("vinsertps", "data", F::kAvx512, KP(vinsertps_data), DataPair(1, 2, 8));
  add("vunpcklpd", "data", F::kAvx512, KP(vunpcklpd_data), DataPair(1, 2, 8));
  add("vxorps", "data", F::kAvx512, KP(vxorps_data), DataPair(1, 2, 8));
  add("vxorpd", "data", F::kAvx512, KP(vxorpd_data), DataPair(1, 2, 8));
  add("vandpd", "data", F::kAvx512, KP(vandpd_data), DataPair(1, 2, 8));
  add("vbroadcastsd", "data", F::kAvx512, KP(vbroadcastsd_data), Data(1));
  add("vblendvpd", "mask", F::kAvx512, KP(vblendvpd_mask), Data(0));  // sign bits select
  // The re-tag's vector modulus reduces secret tag words (ModSmallLanes).
  add("vpsadbw", "data", F::kAvx512, KP(vpsadbw_data), DataPair(1, 2, 8));
  add("vpmaddubsw", "data", F::kAvx512, KP(vpmaddubsw_data), DataPair(1, 2, 2));
  add("vpmaddwd", "data", F::kAvx512, KP(vpmaddwd_data), DataPair(1, 2, 4));

  // Cross-domain moves of secret values.
  add("vpbroadcastq", "data", F::kAvx512, KP(vpbroadcastq_data), Gpr64(0));
  add("vpbroadcastd", "data", F::kAvx512, KP(vpbroadcastd_data), Gpr64(0));
  add("vpbroadcastb", "data", F::kAvx512, KP(vpbroadcastb_data), Gpr64(0));
  add("vpbroadcastw", "data", F::kAvx512, KP(vpbroadcastw_data), Gpr64(0));
  add("vpor", "data-xmm", F::kAvx512, KP(vpor_x_data), DataPair(1, 2, 8));
  add("vpor", "data-ymm", F::kAvx512, KP(vpor_y_data), DataPair(1, 2, 8));
  add("vpcmpgtq", "data-xmm", F::kAvx512, KP(vpcmpgtq_x_data), DataPair(1, 2, 8));
  add("vpcmpgtq", "data-ymm", F::kAvx512, KP(vpcmpgtq_y_data), DataPair(1, 2, 8));
  add("vextracti128", "data", F::kAvx512, KP(vextracti128_data), Data(1));
  add("vpinsrq", "data", F::kAvx512, KP(vpinsrq_data), Gpr64(0));
  add("vpinsrd", "data", F::kAvx512, KP(vpinsrd_data), Gpr64(0));
  add("vpinsrw", "data", F::kAvx512, KP(vpinsrw_data), Gpr64(0));
  add("vpinsrb", "data", F::kAvx512, KP(vpinsrb_data), Gpr64(0));
  add("vpextrb", "data", F::kAvx512, KP(vpextrb_data), Data(0));
  add("vpextrw", "data", F::kAvx512, KP(vpextrw_data), Data(0));
  add("vpextrd", "data", F::kAvx512, KP(vpextrd_data), Data(0));
  add("vpextrq", "data", F::kAvx512, KP(vpextrq_data), Data(0));

  // AES on secret keys and states.
  add("vaesenc", "state", F::kVaes, KP(vaesenc_state), AesBlock(1));
  add("vaesenc", "key", F::kVaes, KP(vaesenc_key), AesBlock(0));
  add("vaesenclast", "state", F::kVaes, KP(vaesenclast_state), AesBlock(1));
  add("vaesenclast", "key", F::kVaes, KP(vaesenclast_key), AesBlock(0));
  add("vaesenc", "state-xmm", F::kAes, KP(vaesenc_state_x), AesBlock(1));
  add("vaesenc", "key-xmm", F::kAes, KP(vaesenc_key_x), AesBlock(0));
  add("vaesenclast", "state-xmm", F::kAes, KP(vaesenclast_state_x), AesBlock(1));
  add("vaeskeygenassist", "data", F::kAes, KP(vaeskeygenassist_data), AesBlock(1));

  // Scalar bit manipulation on occupancy masks, counts and conditions.
  add("pdep", "mask", F::kBmi2, KP(pdep_mask), Gpr64(0));
  add("pdep", "source", F::kBmi2, KP(pdep_source), LowMasks(1));
  // The dedup nests deposit arbitrary match bits (PlaceMatchesQ / D) and
  // gather secret occupancy with PEXT (CrossBucketClassFieldMasks), both
  // under public constant masks.
  add("pdep", "source-bits", F::kBmi2, KP(pdep_source), Gpr64(1));
  add("pext", "mask", F::kBmi2, KP(pext_mask), Gpr64(0));
  add("pext", "source", F::kBmi2, KP(pext_source), Gpr64(1));
  add("popcnt", "data", F::kPopcnt, KP(popcnt_data), Gpr64(0));
  add("lzcnt", "data", F::kLzcnt, KP(lzcnt_data), Gpr64(0));
  add("tzcnt", "data", F::kBmi1, KP(tzcnt_data), Gpr64(0));
  add("blsr", "data", F::kBmi1, KP(blsr_data), Gpr64(0));
  add("blsi", "data", F::kBmi1, KP(blsi_data), Gpr64(0));
  add("andn", "data", F::kBmi1, KP(andn_data), Gpr64(0));
  add("bzhi", "index", F::kBmi2, KP(bzhi_index), Counts(1));
  add("shlx", "count", F::kBmi2, KP(shlx_count), Counts(1));
  add("shrx", "count", F::kBmi2, KP(shrx_count), Counts(1));
  add("sarx", "count", F::kBmi2, KP(sarx_count), Counts(1));
  add("imul", "data", F::kAvx512, KP(imul_data), Gpr64(0));
  add("mul", "data", F::kAvx512, KP(mul_data), Gpr64(0));
  add("mulx", "data", F::kBmi2, KP(mulx_data), Gpr64(0));
  add("cmovcc", "zf", F::kAvx512, KP(cmov_zf), Conditions(0));
  add("cmovcc", "cf-zf", F::kAvx512, KP(cmov_cf_zf), Orderings(0, 1),
      [](Operands& o, Rng&) { o.g[1] = uint64_t{1} << 62; });
  add("cmovcc", "sf", F::kAvx512, KP(cmov_sf), Gpr64(0));

  // Instrument controls.
  e.push_back({"control", "one-cycle", F::kAvx512, ruler_add_off_chain, nullptr,
               {{"base", [](Operands&, Rng&) {}, false, ruler_add_off_chain},
                {"plus-add-per-iter", [](Operands&, Rng&) {}, false, ruler_add_plus_one}},
               nullptr, Kind::kCalibration});
  e.push_back({"control", "div64", F::kAvx512, div64_lat, nullptr, Dividends(0),
               [](Operands& o, Rng&) { o.g[1] = 3; }, Kind::kVariable});
  return e;
}

// ---------------------------------------------------------------------------
// Measurement
// ---------------------------------------------------------------------------

struct Config {
  bool certify = false;
  uint64_t iters = 8;
  size_t min_rounds = 4000;
  size_t max_rounds = 4000;
  size_t batch = 4000;
  size_t pool = 4096;
  double tolerance = 0.05;  // core cycles per instruction
  double alpha = 1e-3;      // family-wise false-alarm rate
  double max_seconds = 60;  // per variant
  uint64_t seed = 0;
  int cpu = -1;
  std::vector<std::string> only;
  std::string json;
  bool verbose = false;
  bool null_test = false;   // every class drawn like the reference
};

struct Clock {
  double tsc_ghz = 0;
  double quantum = 1;         // smallest TSC step seen between two reads
  double ticks_per_cycle = 1; // from the ADD ruler
  double overhead = 0;        // ticks per sample outside the timed loop
  double ruler_start = 0, ruler_end = 0;
};

enum class Verdict { kCertified, kInconclusive, kLeak };

const char* VerdictName(Verdict v) {
  switch (v) {
    case Verdict::kCertified: return "certified";
    case Verdict::kInconclusive: return "inconclusive";
    case Verdict::kLeak: return "LEAK";
  }
  return "?";
}

struct ClassResult {
  std::string name;
  double mean = 0;      // ticks per sample, outliers excluded
  double cut = 0;       // outlier threshold
  uint64_t outliers = 0;
  PairedTest pair;      // against the reference
  double tail_p = 1;
  double bound = 0;     // |mean diff| + z * SE, ticks per sample
  Verdict verdict = Verdict::kCertified;
};

struct VariantResult {
  std::string name, key, role, form, status;
  Kind kind = Kind::kConstant;
  size_t rounds = 0;
  double seconds = 0;
  unsigned ops = 0;     // instructions per sample
  double ref_cycles_per_op = 0;
  double expected_cycles = 0;        // calibration: the known difference per sample
  double resolution_cycles = 0;      // calibration: z * SE of that difference
  std::vector<ClassResult> classes;  // [0] reference, last is the null class
  size_t worst = 0;                  // index of the worst class (0: none)
};

struct Variant {
  const Entry* entry;
  bool latency;
  std::string name;
  Kernel kernel;
  unsigned ops_per_iter;
};

double CensoredMean(const std::vector<uint32_t>& x, double cut) {
  double sum = 0;
  size_t n = 0;
  for (uint32_t v : x) {
    if (v <= cut) {
      sum += v;
      ++n;
    }
  }
  return n ? sum / static_cast<double>(n) : 0.0;
}

double OutlierMargin(double median, const Clock& clock) {
  return std::max(0.25 * median, 8.0 * clock.quantum);
}

class Runner {
 public:
  Runner(const Config& cfg, const Clock& clock, double z, double per_alpha)
      : cfg_(cfg), clock_(clock), z_(z), per_alpha_(per_alpha) {}

  VariantResult Run(const Variant& v) {
    const Entry& e = *v.entry;
    VariantResult res;
    res.name = v.name;
    res.key = e.key;
    res.role = e.role;
    res.form = v.latency ? "lat" : "tput";
    res.kind = e.kind;
    res.ops = static_cast<unsigned>(cfg_.iters) * v.ops_per_iter;

    // Operand pools: one random base per variant, then each class overwrites
    // the operand it varies.  The null class repeats the reference with its
    // own draws.
    ClassList classes = e.classes;
    classes.push_back(classes[0]);
    classes.back().name = classes[0].name + "#null";
    if (cfg_.null_test && e.kind == Kind::kConstant) {
      for (size_t c = 1; c < classes.size(); ++c) {
        classes[c].fill = classes[0].fill;
        classes[c].fresh = classes[0].fresh;
      }
    }
    Rng rng(cfg_.seed ^ std::hash<std::string>()(v.name));
    Operands base;
    for (auto& row : base.v) {
      for (auto& b : row) b = static_cast<uint8_t>(rng.Next());
    }
    for (auto& k : base.k) k = rng.Next();
    for (auto& g : base.g) g = rng.Next();
    if (e.base) e.base(base, rng);
    const size_t n_classes = classes.size();

    // Nothing the harness does may depend on which class a sample belongs
    // to, including the addresses it touches outside the timed region.  An
    // operand's address alone can move the block that follows its load: with
    // each class in its own pool, or at a fixed offset of a shared row,
    // classes can differ by a hundredth of a cycle per instruction -- highly
    // significant at certify-mode round counts -- whatever their operand
    // values.  So every pool row places the classes at a fresh random
    // permutation of its slots, fixed classes as identical copies, and
    // samples are stored in execution order next to the class that produced
    // them.
    const size_t pool = cfg_.pool;
    std::vector<Operands> ops(pool * n_classes, base);
    std::vector<uint8_t> slot(pool * n_classes);  // slot[row * n + class]
    std::vector<Operands> fixed(n_classes, base);
    for (size_t c = 0; c < n_classes; ++c) {
      if (!classes[c].fresh) classes[c].fill(fixed[c], rng);
    }
    for (size_t row = 0; row < pool; ++row) {
      uint8_t* perm = &slot[row * n_classes];
      for (size_t c = 0; c < n_classes; ++c) perm[c] = static_cast<uint8_t>(c);
      for (size_t i = n_classes - 1; i > 0; --i) std::swap(perm[i], perm[rng.Below(i + 1)]);
      for (size_t c = 0; c < n_classes; ++c) {
        Operands& op = ops[row * n_classes + perm[c]];
        if (classes[c].fresh) {
          classes[c].fill(op, rng);
        } else {
          op = fixed[c];
        }
      }
    }
    std::vector<Kernel> kernels(n_classes);
    for (size_t c = 0; c < n_classes; ++c) {
      kernels[c] = classes[c].kernel ? classes[c].kernel : v.kernel;
    }

    std::vector<uint32_t> ticks;  // in execution order
    std::vector<uint8_t> who;     // the class of each sample
    std::vector<uint8_t> order(n_classes);
    for (size_t c = 0; c < n_classes; ++c) order[c] = static_cast<uint8_t>(c);

    // Warm-up: frequency, caches, the vector unit's power state.
    for (size_t r = 0; r < 300; ++r) {
      for (size_t c = 0; c < n_classes; ++c) {
        kernels[c](&ops[(r % pool) * n_classes + c], cfg_.iters);
      }
    }

    // The control must resolve one cycle per sample (a 0.7-tick shift) under
    // a TSC that may step in tens of ticks; it needs ~100k rounds whatever
    // the mode, and it stops only once its difference is clearly detected
    // and its standard error resolves one cycle.
    const bool calibration = e.kind == Kind::kCalibration;
    const size_t min_rounds = calibration ? std::max<size_t>(cfg_.min_rounds, 100000)
                                          : cfg_.min_rounds;
    const size_t max_rounds = calibration ? std::max<size_t>(cfg_.max_rounds, 1000000)
                                          : cfg_.max_rounds;
    const size_t batch = calibration ? std::max<size_t>(cfg_.batch, 50000) : cfg_.batch;

    const double t_start = Now();
    size_t rounds = 0;
    while (true) {
      const size_t target = std::min(max_rounds, rounds + batch);
      ticks.resize(target * n_classes);
      who.resize(target * n_classes);
      for (; rounds < target; ++rounds) {
        for (size_t i = n_classes - 1; i > 0; --i) {
          std::swap(order[i], order[rng.Below(i + 1)]);
        }
        const size_t row = rounds % pool;
        const Operands* ops_row = &ops[row * n_classes];
        const uint8_t* perm = &slot[row * n_classes];
        uint32_t* out = &ticks[rounds * n_classes];
        uint8_t* out_class = &who[rounds * n_classes];
        for (size_t j = 0; j < n_classes; ++j) {
          const uint8_t c = order[j];
          out[j] = static_cast<uint32_t>(kernels[c](ops_row + perm[c], cfg_.iters));
          out_class[j] = c;
        }
      }
      res.seconds = Now() - t_start;
      if (rounds < min_rounds) continue;
      std::vector<std::vector<uint32_t>> samples(n_classes, std::vector<uint32_t>(rounds));
      for (size_t r = 0; r < rounds; ++r) {
        for (size_t j = 0; j < n_classes; ++j) {
          samples[who[r * n_classes + j]][r] = ticks[r * n_classes + j];
        }
      }
      Analyze(samples, classes, res);
      if (rounds >= max_rounds || res.seconds >= cfg_.max_seconds) break;
      bool all_certified = true, clear_leak = false;
      for (size_t c = 1; c < res.classes.size(); ++c) {
        const ClassResult& cr = res.classes[c];
        if (cr.verdict != Verdict::kCertified) all_certified = false;
        if (std::fabs(cr.pair.t) > std::max(10.0, 2.0 * z_)) clear_leak = true;
      }
      if (calibration ? clear_leak && Resolves(res.classes[1]) : clear_leak || all_certified) {
        break;
      }
    }
    res.rounds = rounds;
    Finish(res);
    return res;
  }

 private:
  static double Now() {
    timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return static_cast<double>(ts.tv_sec) + 1e-9 * static_cast<double>(ts.tv_nsec);
  }

  double CyclesPerOp(double ticks, const VariantResult& res) const {
    return ticks / res.ops / clock_.ticks_per_cycle;
  }

  // z * SE of a paired difference, in core cycles per sample.
  double ResolutionCycles(const ClassResult& c) const {
    return z_ * c.pair.se / clock_.ticks_per_cycle;
  }

  // A difference of one cycle per sample would be flagged with |t| >= 2z.
  bool Resolves(const ClassResult& c) const {
    return c.pair.n >= 2 && ResolutionCycles(c) <= 0.5;
  }

  void Analyze(const std::vector<std::vector<uint32_t>>& samples,
               const ClassList& classes, VariantResult& res) const {
    // One outlier cut for every class, from the pooled median.  Per-class
    // cuts sit on the TSC's lattice: two identical classes a step apart
    // censored a cluster of samples in one and not the other, which the
    // tail test read as p = 1e-54 in a null test.
    const size_t n = samples.size();
    res.classes.assign(n, ClassResult{});
    std::vector<uint32_t> pooled;
    pooled.reserve(n * samples[0].size());
    for (const auto& s : samples) pooled.insert(pooled.end(), s.begin(), s.end());
    const double median = Median(std::move(pooled));
    const double cut = median + OutlierMargin(median, clock_);
    for (size_t c = 0; c < n; ++c) {
      ClassResult& cr = res.classes[c];
      cr.name = classes[c].name;
      cr.cut = cut;
      cr.mean = CensoredMean(samples[c], cr.cut);
      cr.outliers = static_cast<uint64_t>(std::count_if(
          samples[c].begin(), samples[c].end(), [&](uint32_t x) { return x > cr.cut; }));
    }
    const ClassResult& ref = res.classes[0];
    for (size_t c = 1; c < n; ++c) {
      ClassResult& cr = res.classes[c];
      cr.pair = CensoredPairedMean(samples[c], samples[0], cr.cut, ref.cut);
      cr.tail_p = BinomialHalfTwoSidedP(cr.outliers, ref.outliers);
      cr.bound = std::fabs(cr.pair.mean) + z_ * cr.pair.se;
      if (std::fabs(cr.pair.t) > z_ || cr.tail_p < per_alpha_) {
        cr.verdict = Verdict::kLeak;
      } else if (CyclesPerOp(cr.bound, res) <= cfg_.tolerance) {
        cr.verdict = Verdict::kCertified;
      } else {
        cr.verdict = Verdict::kInconclusive;
      }
    }
    res.ref_cycles_per_op =
        std::max(0.0, ref.mean - clock_.overhead) / res.ops / clock_.ticks_per_cycle;
  }

  void Finish(VariantResult& res) const {
    // The worst class: any leak first, then the largest bound.
    res.worst = 0;
    for (size_t c = 1; c < res.classes.size(); ++c) {
      const ClassResult& cr = res.classes[c];
      if (res.worst == 0) {
        res.worst = c;
        continue;
      }
      const ClassResult& w = res.classes[res.worst];
      const bool leak = cr.verdict == Verdict::kLeak;
      const bool worst_leak = w.verdict == Verdict::kLeak;
      if (leak != worst_leak ? leak
                             : (leak ? std::fabs(cr.pair.t) > std::fabs(w.pair.t)
                                     : cr.bound > w.bound)) {
        res.worst = c;
      }
    }
    const ClassResult& null_class = res.classes.back();
    bool any_leak = false, all_certified = true;
    for (size_t c = 1; c + 1 < res.classes.size(); ++c) {
      if (res.classes[c].verdict == Verdict::kLeak) any_leak = true;
      if (res.classes[c].verdict != Verdict::kCertified) all_certified = false;
    }
    switch (res.kind) {
      case Kind::kConstant:
        if (null_class.verdict == Verdict::kLeak) {
          res.status = "INVALID";  // the null test failed: noise, not signal
        } else if (any_leak) {
          res.status = "LEAK";
        } else if (all_certified && null_class.verdict == Verdict::kCertified) {
          res.status = "certified";
        } else {
          res.status = "inconclusive";
        }
        break;
      case Kind::kCalibration: {
        // One more chained ADD per loop iteration: `iters` cycles per sample.
        const ClassResult& plus = res.classes[1];
        const double cycles = plus.pair.mean / clock_.ticks_per_cycle;
        res.expected_cycles = static_cast<double>(cfg_.iters);
        res.resolution_cycles = ResolutionCycles(plus);
        if (plus.verdict != Verdict::kLeak || plus.pair.mean <= 0) {
          res.status = "NOT-DETECTED";
        } else if (cycles < 0.5 * res.expected_cycles || cycles > 1.5 * res.expected_cycles) {
          res.status = "MISCALIBRATED";
        } else if (!Resolves(plus)) {
          res.status = "UNRESOLVED";
        } else {
          res.status = "detected";
        }
        break;
      }
      case Kind::kVariable:
        res.status = any_leak ? "detected" : "not-detected";
        break;
    }
  }

  const Config& cfg_;
  const Clock& clock_;
  double z_, per_alpha_;
};

// ---------------------------------------------------------------------------
// Host facts, clock calibration
// ---------------------------------------------------------------------------

struct Platform {
  std::string vendor, brand, microcode, kernel, hypervisor, guest_flags;
  unsigned family = 0, model = 0, stepping = 0;
  int cpu = -1;
};

std::string Trim(std::string s) {
  const auto b = s.find_first_not_of(" \t");
  const auto e = s.find_last_not_of(" \t\n");
  return b == std::string::npos ? std::string() : s.substr(b, e - b + 1);
}

Platform ReadPlatform() {
  Platform p;
  unsigned a = 0, b = 0, c = 0, d = 0;
  char vendor[13] = {};
  __get_cpuid(0, &a, &b, &c, &d);
  std::memcpy(vendor, &b, 4);
  std::memcpy(vendor + 4, &d, 4);
  std::memcpy(vendor + 8, &c, 4);
  p.vendor = vendor;
  __get_cpuid(1, &a, &b, &c, &d);
  const unsigned base_family = (a >> 8) & 0xF, base_model = (a >> 4) & 0xF;
  p.family = base_family == 0xF ? base_family + ((a >> 20) & 0xFF) : base_family;
  p.model = (base_family == 0x6 || base_family == 0xF) ? base_model | (((a >> 16) & 0xF) << 4)
                                                       : base_model;
  p.stepping = a & 0xF;
  const bool under_hypervisor = (c >> 31) & 1;
  char brand[49] = {};
  for (unsigned i = 0; i < 3; ++i) {
    __get_cpuid(0x80000002 + i, &a, &b, &c, &d);
    std::memcpy(brand + 16 * i, &a, 4);
    std::memcpy(brand + 16 * i + 4, &b, 4);
    std::memcpy(brand + 16 * i + 8, &c, 4);
    std::memcpy(brand + 16 * i + 12, &d, 4);
  }
  p.brand = Trim(brand);
  if (under_hypervisor) {
    char hv[13] = {};
    __cpuid(0x40000000, a, b, c, d);
    std::memcpy(hv, &b, 4);
    std::memcpy(hv + 4, &c, 4);
    std::memcpy(hv + 8, &d, 4);
    p.hypervisor = hv;
  } else {
    p.hypervisor = "none";
  }
  std::ifstream info("/proc/cpuinfo");
  std::string line;
  while (std::getline(info, line)) {
    if (p.microcode.empty() && line.rfind("microcode", 0) == 0) {
      p.microcode = Trim(line.substr(line.find(':') + 1));
    }
    if (p.guest_flags.empty() && line.rfind("flags", 0) == 0) {
      std::istringstream flags(line.substr(line.find(':') + 1));
      std::string f;
      while (flags >> f) {
        if (f.find("tdx") != std::string::npos || f.find("sev") != std::string::npos) {
          p.guest_flags += (p.guest_flags.empty() ? "" : " ") + f;
        }
      }
      if (p.guest_flags.empty()) p.guest_flags = "none";
    }
  }
  utsname u;
  if (uname(&u) == 0) p.kernel = std::string(u.sysname) + " " + u.release;
  return p;
}

double NowSeconds() {
  timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return static_cast<double>(ts.tv_sec) + 1e-9 * static_cast<double>(ts.tv_nsec);
}

uint64_t Tsc() {
  unsigned aux;
  _mm_lfence();
  const uint64_t t = __rdtscp(&aux);
  _mm_lfence();
  return t;
}

// Ticks per core cycle from the slope of the one-cycle ADD chain between two
// block lengths, and the per-sample overhead from its intercept.  Means over
// interleaved samples below the outlier cut: the TSC may be too coarse for a
// median to resolve a fraction of a tick.
std::pair<double, double> MeasureRuler(uint64_t iters, Rng& rng) {
  Operands op{};
  op.g[1] = 1;
  const uint64_t long_iters = 8 * iters;
  std::vector<uint32_t> short_s, long_s;
  for (int w = 0; w < 2000; ++w) ruler_add(&op, long_iters);
  for (int r = 0; r < 40000; ++r) {
    if (rng.Next() & 1) {
      short_s.push_back(static_cast<uint32_t>(ruler_add(&op, iters)));
      long_s.push_back(static_cast<uint32_t>(ruler_add(&op, long_iters)));
    } else {
      long_s.push_back(static_cast<uint32_t>(ruler_add(&op, long_iters)));
      short_s.push_back(static_cast<uint32_t>(ruler_add(&op, iters)));
    }
  }
  const double ms = Median(short_s), ml = Median(long_s);
  const double s = CensoredMean(short_s, ms * 1.25 + 64), l = CensoredMean(long_s, ml * 1.25 + 64);
  const double ops_short = static_cast<double>(iters * kLatOps);
  const double ops_long = static_cast<double>(long_iters * kLatOps);
  const double tpc = (l - s) / (ops_long - ops_short);
  return {tpc, s - tpc * ops_short};
}

Clock CalibrateClock(uint64_t iters, Rng& rng) {
  Clock c;
  const double t0 = NowSeconds();
  const uint64_t c0 = Tsc();
  while (NowSeconds() - t0 < 0.2) {
  }
  c.tsc_ghz = static_cast<double>(Tsc() - c0) / (NowSeconds() - t0) / 1e9;
  uint64_t q = ~uint64_t{0};
  for (int i = 0; i < 100000; ++i) {
    const uint64_t a = Tsc(), b = Tsc();
    if (b > a) q = std::min(q, b - a);
  }
  // Back-to-back reads cost more than one step on a fine TSC, so this
  // overstates a fine quantum; it is only used to floor the outlier margin.
  c.quantum = static_cast<double>(q);
  const auto ruler = MeasureRuler(iters, rng);
  c.ticks_per_cycle = ruler.first;
  c.overhead = ruler.second;
  c.ruler_start = ruler.first;
  return c;
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

std::string JsonEscape(const std::string& s) {
  std::string out;
  for (char ch : s) {
    if (ch == '"' || ch == '\\') out += '\\';
    if (static_cast<unsigned char>(ch) >= 0x20) out += ch;
  }
  return out;
}

void PrintVariant(const VariantResult& r, const Clock& clock, bool verbose) {
  const ClassResult* w = r.worst ? &r.classes[r.worst] : nullptr;
  const double bound_cyc = w ? w->bound / r.ops / clock.ticks_per_cycle : 0;
  std::printf("%-28s %-4s %7zu %6.2f  %-18s %+7.2f %8.4f %8.2g  %s\n", (r.key + "." + r.role).c_str(),
              r.form.c_str(), r.rounds, r.ref_cycles_per_op, w ? w->name.c_str() : "-",
              w ? w->pair.t : 0.0, bound_cyc, w ? w->tail_p : 1.0, r.status.c_str());
  if (r.kind == Kind::kCalibration && r.classes.size() > 1) {
    const ClassResult& plus = r.classes[1];
    std::printf("    measured %+.3f +- %.3f cycles per sample (expected %+.0f, within "
                "50%%); z * SE %.3f cycles (at most 0.5 resolves one cycle per sample)\n",
                plus.pair.mean / clock.ticks_per_cycle,
                plus.pair.se / clock.ticks_per_cycle, r.expected_cycles,
                r.resolution_cycles);
  }
  if (!verbose) return;
  for (const ClassResult& c : r.classes) {
    std::printf("    %-18s mean %9.1f ticks  diff %+8.3f cyc/op  t %+7.2f  bound %.4f  "
                "outliers %6" PRIu64 "  tail-p %.2g  %s\n",
                c.name.c_str(), c.mean, c.pair.mean / r.ops / clock.ticks_per_cycle,
                c.pair.t, c.bound / r.ops / clock.ticks_per_cycle, c.outliers, c.tail_p,
                &c == &r.classes[0] ? "reference" : VerdictName(c.verdict));
  }
}

void WriteJson(const std::string& path, const Config& cfg, const Platform& p,
               const Clock& clock, double z, size_t comparisons,
               const std::vector<VariantResult>& results,
               const std::vector<std::string>& skipped, const std::string& verdict) {
  std::ofstream f(path);
  f << "{\n  \"platform\": {\"vendor\": \"" << JsonEscape(p.vendor) << "\", \"brand\": \""
    << JsonEscape(p.brand) << "\", \"family\": " << p.family << ", \"model\": " << p.model
    << ", \"stepping\": " << p.stepping << ", \"microcode\": \"" << JsonEscape(p.microcode)
    << "\", \"kernel\": \"" << JsonEscape(p.kernel) << "\", \"hypervisor\": \""
    << JsonEscape(p.hypervisor) << "\", \"guest_flags\": \"" << JsonEscape(p.guest_flags)
    << "\", \"cpu\": " << p.cpu << "},\n";
  f << "  \"config\": {\"mode\": \"" << (cfg.certify ? "certify" : "smoke")
    << "\", \"iters\": " << cfg.iters << ", \"min_rounds\": " << cfg.min_rounds
    << ", \"max_rounds\": " << cfg.max_rounds << ", \"tolerance_cycles_per_op\": "
    << cfg.tolerance << ", \"alpha\": " << cfg.alpha << ", \"seed\": " << cfg.seed
    << ", \"comparisons\": " << comparisons << ", \"z\": " << z << "},\n";
  f << "  \"clock\": {\"tsc_ghz\": " << clock.tsc_ghz << ", \"tsc_quantum\": " << clock.quantum
    << ", \"ticks_per_cycle_start\": " << clock.ruler_start
    << ", \"ticks_per_cycle_end\": " << clock.ruler_end
    << ", \"sample_overhead_ticks\": " << clock.overhead << "},\n";
  f << "  \"verdict\": \"" << verdict << "\",\n  \"skipped\": [";
  for (size_t i = 0; i < skipped.size(); ++i) {
    f << (i ? ", " : "") << "\"" << JsonEscape(skipped[i]) << "\"";
  }
  f << "],\n  \"variants\": [\n";
  for (size_t i = 0; i < results.size(); ++i) {
    const VariantResult& r = results[i];
    f << "    {\"name\": \"" << JsonEscape(r.name) << "\", \"key\": \"" << JsonEscape(r.key)
      << "\", \"role\": \"" << JsonEscape(r.role) << "\", \"form\": \"" << r.form
      << "\", \"status\": \"" << r.status << "\", \"rounds\": " << r.rounds
      << ", \"seconds\": " << r.seconds << ", \"ops_per_sample\": " << r.ops
      << ", \"ref_cycles_per_op\": " << r.ref_cycles_per_op << ", \"classes\": [\n";
    for (size_t c = 0; c < r.classes.size(); ++c) {
      const ClassResult& cr = r.classes[c];
      const double to_cyc = 1.0 / r.ops / clock.ticks_per_cycle;
      f << "      {\"name\": \"" << JsonEscape(cr.name) << "\", \"mean_ticks\": " << cr.mean
        << ", \"diff_cycles_per_op\": " << cr.pair.mean * to_cyc
        << ", \"se_cycles_per_op\": " << cr.pair.se * to_cyc << ", \"t\": " << cr.pair.t
        << ", \"bound_cycles_per_op\": " << cr.bound * to_cyc
        << ", \"diff_cycles_per_sample\": " << cr.pair.mean / clock.ticks_per_cycle
        << ", \"rounds_kept\": " << cr.pair.n << ", \"outliers\": " << cr.outliers
        << ", \"tail_p\": " << cr.tail_p << ", \"verdict\": \""
        << (c == 0 ? "reference" : VerdictName(cr.verdict)) << "\"}"
        << (c + 1 < r.classes.size() ? "," : "") << "\n";
    }
    f << "    ]}" << (i + 1 < results.size() ? "," : "") << "\n";
  }
  f << "  ]\n}\n";
}

// ---------------------------------------------------------------------------
// Driver
// ---------------------------------------------------------------------------

void Usage() {
  std::puts(
      "usage: avx512_constant_time_test [options]\n"
      "  --certify          run until every class is certified (or the budget ends)\n"
      "                     and fail on anything short of that; default is a quick\n"
      "                     smoke run that fails only on a leak or a broken instrument\n"
      "  --only A,B         run variants whose name (key.role.form) contains any of\n"
      "                     the substrings; each must match some variant\n"
      "  --list             print the covered instruction keys and exit\n"
      "  --json PATH        write every statistic to PATH\n"
      "  --cpu N            pin to CPU N (default: the CPU the test starts on)\n"
      "  --seed S           operand and order seed (default: from the clock)\n"
      "  --iters N          loop iterations per sample (default 8)\n"
      "  --min-rounds N, --max-rounds N, --batch N, --max-seconds S (per variant)\n"
      "  --tolerance C      certification bound, core cycles per instruction (0.05)\n"
      "  --alpha A          family-wise false-alarm rate (1e-3)\n"
      "  --null-test        validate the instrument: every class is drawn like the\n"
      "                     reference, so nothing may be flagged and the t spread\n"
      "                     must be close to 1\n"
      "  --verbose          print every class");
}

bool Matches(const std::string& name, const std::vector<std::string>& only) {
  if (only.empty()) return true;
  for (const auto& s : only) {
    if (name.find(s) != std::string::npos) return true;
  }
  return false;
}

int Main(int argc, char** argv) {
  Config cfg;
  bool list = false, rounds_set = false;
  cfg.seed = static_cast<uint64_t>(NowSeconds() * 1e6);
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    auto next = [&]() -> std::string {
      if (i + 1 >= argc) {
        std::fprintf(stderr, "missing value for %s\n", a.c_str());
        std::exit(2);
      }
      return argv[++i];
    };
    if (a == "--certify") {
      cfg.certify = true;
    } else if (a == "--only") {
      std::stringstream ss(next());
      std::string part;
      while (std::getline(ss, part, ',')) cfg.only.push_back(part);
    } else if (a == "--list") {
      list = true;
    } else if (a == "--json") {
      cfg.json = next();
    } else if (a == "--cpu") {
      cfg.cpu = std::stoi(next());
    } else if (a == "--seed") {
      cfg.seed = std::stoull(next(), nullptr, 0);
    } else if (a == "--iters") {
      cfg.iters = std::stoull(next());
    } else if (a == "--min-rounds") {
      cfg.min_rounds = std::stoull(next());
      rounds_set = true;
    } else if (a == "--max-rounds") {
      cfg.max_rounds = std::stoull(next());
      rounds_set = true;
    } else if (a == "--batch") {
      cfg.batch = std::stoull(next());
    } else if (a == "--max-seconds") {
      cfg.max_seconds = std::stod(next());
    } else if (a == "--tolerance") {
      cfg.tolerance = std::stod(next());
    } else if (a == "--alpha") {
      cfg.alpha = std::stod(next());
    } else if (a == "--verbose") {
      cfg.verbose = true;
    } else if (a == "--null-test") {
      cfg.null_test = true;
    } else {
      Usage();
      return a == "--help" || a == "-h" ? 0 : 2;
    }
  }
  if (cfg.certify && !rounds_set) {
    // 100k rounds = 12.8M timed executions per class in the latency form and
    // 19.2M in the throughput form, before any extension.
    cfg.min_rounds = 100000;
    cfg.max_rounds = 2000000;
    cfg.batch = 100000;
  }
  cfg.max_rounds = std::max(cfg.max_rounds, cfg.min_rounds);

  const std::vector<Entry> entries = BuildEntries();
  if (list) {
    std::set<std::string> keys;
    for (const Entry& e : entries) {
      if (e.kind == Kind::kConstant) keys.insert(e.key);
    }
    std::puts("# instruction keys measured by avx512_constant_time_test");
    for (const auto& k : keys) std::puts(k.c_str());
    return 0;
  }

  Platform platform = ReadPlatform();
  if (cfg.cpu < 0) cfg.cpu = sched_getcpu();
  cpu_set_t set;
  CPU_ZERO(&set);
  CPU_SET(cfg.cpu, &set);
  if (sched_setaffinity(0, sizeof(set), &set) != 0) {
    std::fprintf(stderr, "warning: could not pin to CPU %d\n", cfg.cpu);
  }
  platform.cpu = cfg.cpu;

  // A pattern that names no variant (a typo) is a usage error, not a run
  // that measured nothing and passed.
  for (const auto& s : cfg.only) {
    bool any = false;
    for (const Entry& e : entries) {
      for (int form = 0; form < 2; ++form) {
        if (!(form == 0 ? e.lat : e.tput)) continue;
        any = any || Matches(e.key + "." + e.role + (form == 0 ? ".lat" : ".tput"), {s});
      }
    }
    if (!any) {
      std::fprintf(stderr, "--only %s matches no variant (names are key.role.form, "
                   "e.g. vpermb.ctrl.lat)\n", s.c_str());
      return 2;
    }
  }

  std::vector<Variant> variants;
  std::vector<std::string> skipped;
  for (const Entry& e : entries) {
    for (int form = 0; form < 2; ++form) {
      const Kernel k = form == 0 ? e.lat : e.tput;
      if (!k) continue;
      const std::string name = e.key + "." + e.role + (form == 0 ? ".lat" : ".tput");
      if (!Matches(name, cfg.only)) continue;
      if (!Supported(e.feature)) {
        skipped.push_back(name + " (no " + FeatureName(e.feature) + ")");
        continue;
      }
      variants.push_back({&e, form == 0, name, k, form == 0 ? kLatOps : kTputOps});
    }
  }
  // Two tests per non-reference class (location and tail), null class
  // included.
  size_t comparisons = 0;
  for (const Variant& v : variants) comparisons += 2 * v.entry->classes.size();
  comparisons = std::max<size_t>(comparisons, 1);
  const double per_alpha = cfg.alpha / static_cast<double>(comparisons);
  const double z = TwoSidedNormalThreshold(per_alpha);

  Rng rng(cfg.seed);
  Clock clock = CalibrateClock(cfg.iters, rng);
  std::printf("avx512_constant_time_test (%s mode)\n", cfg.certify ? "certify" : "smoke");
  std::printf("host: %s | %s family %u model %u stepping %u | microcode %s\n",
              platform.brand.c_str(), platform.vendor.c_str(), platform.family,
              platform.model, platform.stepping, platform.microcode.c_str());
  std::printf("      %s | hypervisor %s | guest flags %s | pinned to CPU %d\n",
              platform.kernel.c_str(), platform.hypervisor.c_str(),
              platform.guest_flags.c_str(), cfg.cpu);
  std::printf("clock: TSC %.3f GHz, step %.0f ticks, %.3f ticks per core cycle "
              "(core ~%.2f GHz), %.0f ticks overhead per sample\n",
              clock.tsc_ghz, clock.quantum, clock.ticks_per_cycle,
              clock.tsc_ghz / clock.ticks_per_cycle, clock.overhead);
  std::printf("test: %zu variants, %zu comparisons, |t| > %.2f flags a leak "
              "(family-wise alpha %.0e), certify below %.3f cycles/instruction\n",
              variants.size(), comparisons, z, cfg.alpha, cfg.tolerance);
  std::printf("      %zu..%zu rounds of %" PRIu64 " x (%u or %u) instructions per class, "
              "seed %" PRIu64 "\n\n",
              cfg.min_rounds, cfg.max_rounds, cfg.iters, kLatOps, kTputOps, cfg.seed);
  std::printf("%-28s %-4s %7s %6s  %-18s %7s %8s %8s  %s\n", "instruction.role", "form",
              "rounds", "cyc/op", "worst class", "t", "bound", "tail-p", "status");

  Runner runner(cfg, clock, z, per_alpha);
  std::vector<VariantResult> results;
  results.reserve(variants.size());
  for (const Variant& v : variants) {
    results.push_back(runner.Run(v));
    PrintVariant(results.back(), clock, cfg.verbose);
    std::fflush(stdout);
  }
  clock.ruler_end = MeasureRuler(cfg.iters, rng).first;

  // Spread of every constant-kind t statistic.  When nothing leaks each is
  // close to standard normal, so a standard deviation well above 1 means the
  // standard errors are too small for this host's noise.
  double t_sum = 0, t_sq = 0, t_max = 0, bound_max = 0;
  size_t t_n = 0;
  std::string bound_max_at;
  for (const VariantResult& r : results) {
    if (r.kind != Kind::kConstant) continue;
    for (size_t c = 1; c < r.classes.size(); ++c) {
      const ClassResult& cr = r.classes[c];
      t_sum += cr.pair.t;
      t_sq += cr.pair.t * cr.pair.t;
      t_max = std::max(t_max, std::fabs(cr.pair.t));
      ++t_n;
      const double b = cr.bound / r.ops / clock.ticks_per_cycle;
      if (b > bound_max) {
        bound_max = b;
        bound_max_at = r.name + " / " + cr.name;
      }
    }
  }
  size_t certified = 0, inconclusive = 0, leak = 0, invalid = 0;
  bool controls_ok = true, calibration_ran = false;
  std::vector<std::string> notes;
  for (const VariantResult& r : results) {
    if (r.kind == Kind::kConstant) {
      if (r.status == "certified") ++certified;
      if (r.status == "inconclusive") ++inconclusive;
      if (r.status == "LEAK") ++leak;
      if (r.status == "INVALID") ++invalid;
    } else if (r.kind == Kind::kCalibration) {
      calibration_ran = true;
      if (r.status != "detected") controls_ok = false;
      notes.push_back(r.name + ": " + r.status);
    } else {
      notes.push_back(r.name + ": " + r.status +
                      (r.status == "detected" ? " (as expected)"
                                              : " (DIV looks constant-time on this CPU)"));
    }
  }
  // A run that measured nothing (every selected variant skipped) does not
  // pass, and neither does a certify run that measured no instruction.
  const size_t measured = certified + inconclusive + leak + invalid;
  const bool pass = !results.empty() && (!cfg.certify || measured > 0) &&
                    leak == 0 && invalid == 0 && controls_ok &&
                    (!cfg.certify || inconclusive == 0) &&
                    (!cfg.certify || calibration_ran || !cfg.only.empty());
  std::printf("\n== summary ==\n");
  std::printf("clock drift: %.3f -> %.3f ticks per cycle\n", clock.ruler_start, clock.ruler_end);
  std::printf("variants: %zu certified, %zu inconclusive, %zu LEAK, %zu INVALID, %zu skipped%s\n",
              certified, inconclusive, leak, invalid, skipped.size(),
              cfg.null_test ? " (null test: every class drawn like the reference)" : "");
  if (t_n > 1) {
    const double mean = t_sum / static_cast<double>(t_n);
    const double sd = std::sqrt(std::max(0.0, (t_sq - t_n * mean * mean) / (t_n - 1.0)));
    std::printf("t statistics: %zu comparisons, mean %+.2f, sd %.2f, max |t| %.2f "
                "(expected about 0, 1, and below %.2f when nothing leaks)\n",
                t_n, mean, sd, t_max, z);
    std::printf("largest bound: %.4f cycles/instruction (%s)\n", bound_max,
                bound_max_at.c_str());
  }
  for (const auto& s : skipped) std::printf("  skipped %s\n", s.c_str());
  for (const auto& n : notes) std::printf("  control %s\n", n.c_str());
  if (!cfg.certify && inconclusive > 0) {
    std::printf("  (smoke mode: inconclusive variants need --certify for a bound)\n");
  }
  if (results.empty()) {
    std::printf("  nothing was measured: every selected variant was skipped\n");
  } else if (cfg.certify && measured == 0) {
    std::printf("  nothing was certified: the run measured no instruction\n");
  }
  std::printf("VERDICT: %s\n", pass ? "PASS" : "FAIL");
  if (!cfg.json.empty()) {
    WriteJson(cfg.json, cfg, platform, clock, z, comparisons, results, skipped,
              pass ? "PASS" : "FAIL");
  }
  return pass ? 0 : 1;
}

}  // namespace
}  // namespace timing
}  // namespace microram

int main(int argc, char** argv) { return microram::timing::Main(argc, argv); }
