#pragma once

// Secret-keyed AES-128 fixed two-block CBC-MAC used to derive routing tags,
// plus the AES key schedules and the wide-key normalization (AesHashKey128)
// the ORAMs build on.  Only the AES-NI host path lives here: the scalar
// reference that the table layer's VAES / AES-NI vector kernels
// (src/oram/table/) must match bit for bit.  AES rounds use the AES-NI
// instructions, so no secret-indexed lookup table is involved.
//
// Every routing message has two complete 128-bit blocks:
//   B0 = (packed public identity, ASCII "oram-rt1")
//   B1 = (stored key low word, stored key high word)
// and tag = low64 AES(AES(B0) XOR B1). Narrow keys and dummy counters use
// a zero high key word. The packed identity separates real/dummy domains.
// See DESIGN.md for the fixed-length CBC reduction and its query budget.
//
// The round keys are a RUNTIME object (AesRoundKeys), not a global constant,
// and that follows from how the nonce is chosen.  Each hierarchy
// ALLOCATES the identity above -- monotone epoch, explicit domain bit,
// explicit level -- instead of sampling it, so that two rebuilds can never
// collide into one hash function.  But that layout is then entirely public, so
// a hardcoded AES key would make tag(key) computable by anyone, and the probe
// position IS tag(key) mod |table|, read straight off the memory trace.  The
// two halves are a package: an allocated nonce is only safe under a secret
// key.  Every entry point here
// therefore takes `const AesRoundKeys&`, defaulting to a fixed public key
// (FixedAesRoundKeys) so the standalone rebuild kernels, their tests and their
// benchmarks stay bit-reproducible; the ORAMs pass their own per-instance keys.

#include <wmmintrin.h>

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <random>
#include <stdexcept>

#if defined(__linux__)
#if __has_include(<sys/random.h>)
#include <sys/random.h>
#define MICRORAM_CRYPTO_HAVE_GETRANDOM 1
#endif
#endif

namespace microram {
namespace crypto {

constexpr unsigned kAesCtrLevelBits = 15;
constexpr unsigned kAesCtrCounterBits = 48;
constexpr uint64_t kAesCtrLevelMask = (uint64_t{1} << kAesCtrLevelBits) - 1;
constexpr uint64_t kAesCtrCounterMask =
    (uint64_t{1} << kAesCtrCounterBits) - 1;
constexpr uint64_t kAesCtrDomainBit = uint64_t{1} << 63;
// Little-endian bytes spell "oram-rt1" in the second half of block zero.
constexpr uint64_t kAesRoutingLabel = 0x3174722d6d61726full;

// Packs a public routing identity into the low word of block B0:
//   bit 63          real/dummy domain bit (taken from nonce_lo)
//   bits 15..62     48-bit family counter (nonce_hi, masked)
//   bits 0..14      15-bit level (nonce_lo, masked)
// The masks truncate silently: callers must keep counters and levels in range
// and never reuse an identity, or two routing functions coincide.
inline uint64_t PackAesCtrHighWord(uint64_t nonce_lo, uint64_t nonce_hi) {
  const uint64_t domain = nonce_lo & kAesCtrDomainBit;
  const uint64_t level = nonce_lo & kAesCtrLevelMask;
  const uint64_t counter = nonce_hi & kAesCtrCounterMask;
  return domain | (counter << kAesCtrLevelBits) | level;
}

// The bytes of the fixed, public AES-128 schedule behind
// FixedAesRoundKeys below: a reproducible key for kernel fixtures, never an
// ORAM's (an ORAM derives its own from a SecretKeySeed).
inline uint8_t FixedAesRoundKeyByte(unsigned i) {
  constexpr uint8_t round_key[176] = {
      0x8d, 0x6e, 0x21, 0x0b, 0x81, 0x62, 0x15, 0xff,
      0x75, 0x56, 0x09, 0xf3, 0x69, 0x4a, 0xfd, 0xe7,
      0x5a, 0x3a, 0xb5, 0xf2, 0xdb, 0x58, 0xa0, 0x0d,
      0xae, 0x0e, 0xa9, 0xfe, 0xc7, 0x44, 0x54, 0x19,
      0x43, 0x1a, 0x61, 0x34, 0x98, 0x42, 0xc1, 0x39,
      0x36, 0x4c, 0x68, 0xc7, 0xf1, 0x08, 0x3c, 0xde,
      0x77, 0xf1, 0x7c, 0x95, 0xef, 0xb3, 0xbd, 0xac,
      0xd9, 0xff, 0xd5, 0x6b, 0x28, 0xf7, 0xe9, 0xb5,
      0x17, 0xef, 0xa9, 0xa1, 0xf8, 0x5c, 0x14, 0x0d,
      0x21, 0xa3, 0xc1, 0x66, 0x09, 0x54, 0x28, 0xd3,
      0x27, 0xdb, 0xcf, 0xa0, 0xdf, 0x87, 0xdb, 0xad,
      0xfe, 0x24, 0x1a, 0xcb, 0xf7, 0x70, 0x32, 0x18,
      0x56, 0xf8, 0x62, 0xc8, 0x89, 0x7f, 0xb9, 0x65,
      0x77, 0x5b, 0xa3, 0xae, 0x80, 0x2b, 0x91, 0xb6,
      0xe7, 0x79, 0x2c, 0x05, 0x6e, 0x06, 0x95, 0x60,
      0x19, 0x5d, 0x36, 0xce, 0x99, 0x76, 0xa7, 0x78,
      0x5f, 0x25, 0x90, 0xeb, 0x31, 0x23, 0x05, 0x8b,
      0x28, 0x7e, 0x33, 0x45, 0xb1, 0x08, 0x94, 0x3d,
      0x74, 0x07, 0xb7, 0x23, 0x45, 0x24, 0xb2, 0xa8,
      0x6d, 0x5a, 0x81, 0xed, 0xdc, 0x52, 0x15, 0xd0,
      0x42, 0x5e, 0xc7, 0xa5, 0x07, 0x7a, 0x75, 0x0d,
      0x6a, 0x20, 0xf4, 0xe0, 0xb6, 0x72, 0xe1, 0x30};
  return round_key[i];
}

// One AES-128 key schedule, passed by reference wherever a tag is derived.
struct AesRoundKeys {
  __m128i rk[11];
};

// AES-128 key expansion.  The round constant is an immediate, so the ten steps
// are written out rather than looped.
inline __m128i AesKeyExpandStep(__m128i key, __m128i assist) {
  assist = _mm_shuffle_epi32(assist, 0xFF);  // broadcast the rotated word
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  key = _mm_xor_si128(key, _mm_slli_si128(key, 4));
  return _mm_xor_si128(key, assist);
}

inline AesRoundKeys ExpandAesKey128(__m128i key) {
  AesRoundKeys out;
  out.rk[0] = key;
#define MICRORAM_AES_KEY_STEP(r, rcon)                     \
  out.rk[r] = AesKeyExpandStep(                            \
      out.rk[r - 1], _mm_aeskeygenassist_si128(out.rk[r - 1], rcon))
  MICRORAM_AES_KEY_STEP(1, 0x01);
  MICRORAM_AES_KEY_STEP(2, 0x02);
  MICRORAM_AES_KEY_STEP(3, 0x04);
  MICRORAM_AES_KEY_STEP(4, 0x08);
  MICRORAM_AES_KEY_STEP(5, 0x10);
  MICRORAM_AES_KEY_STEP(6, 0x20);
  MICRORAM_AES_KEY_STEP(7, 0x40);
  MICRORAM_AES_KEY_STEP(8, 0x80);
  MICRORAM_AES_KEY_STEP(9, 0x1B);
  MICRORAM_AES_KEY_STEP(10, 0x36);
#undef MICRORAM_AES_KEY_STEP
  return out;
}

// The fixed public schedule.  The default for the standalone
// rebuild kernels, whose tests compare tags against a reference computation and
// whose benchmarks want a run to reproduce; NOT for an ORAM.
inline const AesRoundKeys& FixedAesRoundKeys() {
  static const AesRoundKeys keys = [] {
    AesRoundKeys k;
    alignas(16) uint8_t bytes[16];
    for (unsigned round = 0; round <= 10; ++round) {
      for (unsigned i = 0; i < 16; ++i) {
        bytes[i] = FixedAesRoundKeyByte(round * 16 + i);
      }
      k.rk[round] = _mm_load_si128(reinterpret_cast<const __m128i*>(bytes));
    }
    return k;
  }();
  return keys;
}

// A per-ORAM master seed. Random() is the production default -- the nonce
// layout is public, so the key is what stops an adversary recomputing probe
// positions from the memory trace.  Fixed(seed) is for tests and benchmarks
// that need a run to reproduce bit for bit.
//
// WHERE Random() GETS ITS 16 BYTES: the kernel's generator, getrandom(2),
// which blocks only until the kernel pool is first initialized and carries
// the kernel's workarounds for faulty CPU generators; std::random_device
// only where that call is unavailable (not Linux, a kernel without it, or a
// sandbox that refuses it).  An
// all-zero seed -- the all-zero AES master key, which no healthy source
// produces but a failing hardware generator can -- is refused with
// std::runtime_error.  It runs once per map, at construction.
struct SecretKeySeed {
  uint64_t lo = 0;
  uint64_t hi = 0;

  static SecretKeySeed Fixed(uint64_t seed) {
    uint64_t state = seed;
    SecretKeySeed out;
    out.lo = Mix(&state);
    out.hi = Mix(&state);
    return out;
  }

  static SecretKeySeed Random() {
    uint8_t bytes[16];
    if (!KernelRandom(bytes, sizeof(bytes))) {
      std::random_device rd;
      for (size_t i = 0; i < sizeof(bytes); i += 4) {
        const uint32_t word = static_cast<uint32_t>(rd());
        std::memcpy(bytes + i, &word, sizeof(word));
      }
    }
    SecretKeySeed out;
    std::memcpy(&out.lo, bytes, sizeof(out.lo));
    std::memcpy(&out.hi, bytes + sizeof(out.lo), sizeof(out.hi));
    if (out.lo == 0 && out.hi == 0) {
      throw std::runtime_error(
          "secret seed: the random source returned sixteen zero bytes");
    }
    return out;
  }

  bool operator==(const SecretKeySeed& other) const {
    return lo == other.lo && hi == other.hi;
  }

 private:
  // Fills `bytes` from getrandom(2), retrying on EINTR and short reads;
  // false where the call is unavailable (missing, or refused by a sandbox),
  // so the caller falls back.
  static bool KernelRandom(uint8_t* bytes, size_t n) {
#ifdef MICRORAM_CRYPTO_HAVE_GETRANDOM
    size_t filled = 0;
    while (filled < n) {
      const ssize_t got = getrandom(bytes + filled, n - filled, 0);
      if (got > 0) {
        filled += static_cast<size_t>(got);
      } else if (!(got < 0 && errno == EINTR)) {
        return false;
      }
    }
    return true;
#else
    (void)bytes;
    (void)n;
    return false;
#endif
  }

  static uint64_t Mix(uint64_t* state) {
    uint64_t z = (*state += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
  }
};

// Raw expansion: fixtures and the separately seeded tree use this directly.
// The hierarchy uses the two labeled derivations below instead.
inline AesRoundKeys DeriveAesRoundKeys(const SecretKeySeed& seed) {
  return ExpandAesKey128(_mm_set_epi64x(static_cast<long long>(seed.hi),
                                        static_cast<long long>(seed.lo)));
}

inline uint64_t LoadLe64Host(const uint8_t* p) {
  uint64_t v = 0;
  std::memcpy(&v, p, sizeof(v));
  return v;
}

// One AES-128 block, scalar.  The tag PRF, its wide-key form and the key
// rehash below all reduce to this; the vector paths spell it out again only to
// keep several blocks in flight.
inline __m128i AesEncryptBlockHost(__m128i state, const __m128i* rk) {
  state = _mm_xor_si128(state, rk[0]);
  for (unsigned round = 1; round < 10; ++round) {
    state = _mm_aesenc_si128(state, rk[round]);
  }
  return _mm_aesenclast_si128(state, rk[10]);
}

inline __m128i AesEncryptBlockHost(__m128i state, const AesRoundKeys& rk) {
  return AesEncryptBlockHost(state, rk.rk);
}

// The first CBC state depends only on the public identity and routing key.
// Bulk re-tagging can share it across all stored keys under one identity.
inline __m128i AesRoutingPrefixHost(uint64_t packed_identity,
                                   const __m128i* rk) {
  return AesEncryptBlockHost(
      _mm_set_epi64x(static_cast<long long>(kAesRoutingLabel),
                    static_cast<long long>(packed_identity)), rk);
}

// Hierarchy subkeys: the master seed is used only to encrypt these two fixed,
// distinct labels. Each resulting block is expanded as an ordinary AES key.
// The labels are ASCII, zero-padded to 16 bytes, with no integer encoding.
// Keeping raw DeriveAesRoundKeys separate preserves low-level fixture keys.
// See DESIGN.md for the two-query PRP reduction and its 2^-128 switching cost;
// this does not establish the downstream routing or normalization word laws.
inline AesRoundKeys DeriveRoutingAesRoundKeys(const SecretKeySeed& seed) {
  constexpr char label[16] = "oram-routing-v1";
  return ExpandAesKey128(AesEncryptBlockHost(
      _mm_loadu_si128(reinterpret_cast<const __m128i*>(label)),
      DeriveAesRoundKeys(seed)));
}

inline AesRoundKeys DeriveStoredKeyAesRoundKeys(const SecretKeySeed& seed) {
  constexpr char label[16] = "oram-stored-v1";
  return ExpandAesKey128(AesEncryptBlockHost(
      _mm_loadu_si128(reinterpret_cast<const __m128i*>(label)),
      DeriveAesRoundKeys(seed)));
}

// The routing tag: the two-block CBC routing function described at the top of
// this file.  (The "AesCtr" in the name refers to the nonce/counter identity
// it is keyed by.)  Its message includes the full stored key and packed
// identity separately;
// the fixed-length encoding is injective within the identity field limits.
// This is a PRF construction, not an assertion that AES outputs are independent.
inline uint64_t AesCtrTagU128WordsHost(
    uint64_t nonce_lo, uint64_t nonce_hi, uint64_t key_lo, uint64_t key_hi,
    const AesRoundKeys& rk = FixedAesRoundKeys()) {
  const __m128i state = AesEncryptBlockHost(
      _mm_xor_si128(
          AesRoutingPrefixHost(PackAesCtrHighWord(nonce_lo, nonce_hi), rk.rk),
          _mm_set_epi64x(static_cast<long long>(key_hi),
                        static_cast<long long>(key_lo))),
      rk);
  alignas(16) uint8_t encrypted[16];
  _mm_store_si128(reinterpret_cast<__m128i*>(encrypted), state);
  return LoadLe64Host(encrypted);
}

inline uint64_t AesCtrTagU64WordsHost(
    uint64_t nonce_lo, uint64_t nonce_hi, uint64_t entry_key,
    const AesRoundKeys& rk = FixedAesRoundKeys()) {
  return AesCtrTagU128WordsHost(nonce_lo, nonce_hi, entry_key, 0, rk);
}

// Rehashes a user key of ANY width to the 16-byte key the buckets store
// (out[0] = bytes 0..7, out[1] = bytes 8..15, little-endian), under a secret
// AES-128 key.
//
// Why the ORAMs need it at all: a key of 16 bytes or more has to become a fixed
// 16-byte stored key (narrower keys are stored verbatim), and a TRUNCATION of the user key would not do -- two
// distinct keys sharing 16 bytes would become one entry, and an adversary
// choosing the keys controls whether that happens. For fixed widths through
// sixteen bytes, the padded AES input is injective. Wider keys are compressed;
// an ideal 128-bit output model gives a per-pair collision probability of
// 2^-128, not an unconditional guarantee for this construction. Rebuild and
// online matching compare the complete stored key exactly; that does not
// distinguish user keys that normalize to the same stored representation.
//
//  - len <= 16: ONE block, the key zero-padded.  An ORAM fixes `len` for its
//    lifetime, so zero padding is injective and a length block would buy
//    nothing but a second serial AES on every access.
//  - len  > 16: CBC-MAC with the length as block 0. The encoding retains the
//    length and every input byte before compression. The hierarchy fixes len;
//    its CBC reduction uses that fixed block count. This helper as a whole
//    makes no mixed-width security claim (the short branch aliases lengths).
inline void AesHashKey128(const uint8_t* key_in, size_t len,
                          const AesRoundKeys& rk, uint64_t out[2]) {
  // `key` points to `len` bytes by contract, but the ONE caller that reaches
  // here (EncodeStoredKey) reaches it only on the `user_key_bytes >= 16` branch
  // of a runtime width it cannot constant-fold.  Inlined into a call site whose
  // key object really is a `uint64_t`, GCC therefore sees a (dead) path that
  // copies 9..16 bytes out of an 8-byte object and reports
  // -Wstringop-overread against glibc's fortified memcpy.  Laundering the
  // pointer through an empty asm drops the object-size deduction -- the
  // optimizer no longer knows which object this points into -- without adding
  // an instruction or changing the code that is generated.
  const uint8_t* key = key_in;
  asm("" : "+r"(key));
  alignas(16) uint8_t block[16];
  __m128i state;
  if (len <= 16) {
    std::memset(block, 0, sizeof(block));
    std::memcpy(block, key, len);
    state = AesEncryptBlockHost(
        _mm_load_si128(reinterpret_cast<const __m128i*>(block)), rk);
  } else {
    state = AesEncryptBlockHost(
        _mm_set_epi64x(0, static_cast<long long>(static_cast<uint64_t>(len))),
        rk);
    for (size_t off = 0; off < len; off += 16) {
      const size_t chunk = len - off < 16 ? len - off : 16;
      std::memset(block, 0, sizeof(block));
      std::memcpy(block, key + off, chunk);
      state = AesEncryptBlockHost(
          _mm_xor_si128(state,
                        _mm_load_si128(reinterpret_cast<const __m128i*>(block))),
          rk);
    }
  }
  alignas(16) uint8_t digest[16];
  _mm_store_si128(reinterpret_cast<__m128i*>(digest), state);
  out[0] = LoadLe64Host(digest);
  out[1] = LoadLe64Host(digest + 8);
}

}  // namespace crypto
}  // namespace microram
