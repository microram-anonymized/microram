// Key derivation for the hierarchy's AES-based hashing.  One secret seed is
// separated into two AES keys by fixed labels -- one for the ROUTING tags that
// decide which bucket an entry lives in at a given level and epoch, one for
// the STORED form of user keys of 16 bytes or more (narrower keys are stored
// verbatim) -- so the two uses never share a key.  The labels are exactly 16
// bytes: "oram-routing-v1\0" and "oram-stored-v1\0\0".  Routing tags must
// also separate level, epoch (nonce) and real/dummy probes, since a collision
// between those domains would make two independent probes land on related
// buckets.  Checked here: fixed known-answer vectors, and every scalar and
// vector consumer of the derived routing schedule against a byte-level
// reference.
//
// The AES primitive vector is the FIPS 197 AES-128 example. All other fixed
// vectors were generated independently with OpenSSL 3.0.13:
//   openssl enc -aes-128-ecb -K <key hex> -nosalt -nopad
// Inputs/outputs below are byte strings, not host-endian printed integers.
// For normalization >16, encrypt LE128(length), then CBC the zero-padded
// message blocks. For routing, CBC the two blocks LE64(family)||"oram-rt1"
// and the zero-padded stored key. These checks establish implementation
// consistency, not a cryptographic security bound.

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/table/cpu_byteslice_stored_key.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <set>
#include <utility>

namespace {

namespace crypto = microram::crypto;
namespace bs = microram::byteslice;
using bs::test_support::Expect;
using Block = std::array<uint8_t, 16>;

Block Hex(const char* text) {
  Expect(std::strlen(text) == 32, "bad known-answer vector length");
  Block out{};
  for (size_t i = 0; i < out.size(); ++i) {
    unsigned byte = 0;
    Expect(std::sscanf(text + 2 * i, "%2x", &byte) == 1,
           "bad known-answer vector byte");
    out[i] = static_cast<uint8_t>(byte);
  }
  return out;
}

Block Bytes(__m128i word) {
  Block out{};
  _mm_storeu_si128(reinterpret_cast<__m128i*>(out.data()), word);
  return out;
}

Block Encrypt(const crypto::AesRoundKeys& keys, const Block& plaintext) {
  return Bytes(crypto::AesEncryptBlockHost(
      _mm_loadu_si128(reinterpret_cast<const __m128i*>(plaintext.data())),
      keys));
}

// Byte-level reference, independent of the routing message helpers and the
// scalar/vector tag entry points. The primitive itself has the FIPS check.
uint64_t RoutingReference(const crypto::AesRoundKeys& keys, uint64_t family,
                          uint64_t low, uint64_t high) {
  Block prefix{};
  constexpr char label[] = "oram-rt1";
  for (size_t i = 0; i < 8; ++i) {
    prefix[i] = static_cast<uint8_t>(family >> (8 * i));
    prefix[i + 8] = static_cast<uint8_t>(label[i]);
  }
  Block state = Encrypt(keys, prefix);
  for (size_t i = 0; i < 8; ++i) {
    state[i] ^= static_cast<uint8_t>(low >> (8 * i));
    state[i + 8] ^= static_cast<uint8_t>(high >> (8 * i));
  }
  state = Encrypt(keys, state);
  uint64_t tag = 0;
  for (size_t i = 0; i < 8; ++i) tag |= uint64_t{state[i]} << (8 * i);
  return tag;
}

crypto::SecretKeySeed Seed(const Block& bytes) {
  crypto::SecretKeySeed seed;
  std::memcpy(&seed.lo, bytes.data(), 8);
  std::memcpy(&seed.hi, bytes.data() + 8, 8);
  return seed;
}

void TestAesKnownAnswer() {
  const auto seed = Seed(Hex("000102030405060708090a0b0c0d0e0f"));
  const auto keys = crypto::DeriveAesRoundKeys(seed);
  Expect(Bytes(keys.rk[0]) == Hex("000102030405060708090a0b0c0d0e0f"),
         "raw AES expansion changed its key bytes");
  Expect(Bytes(keys.rk[10]) == Hex("13111d7fe3944a17f307a78b4d2b30c5"),
         "AES-128 final round key differs from FIPS 197");
  Expect(Encrypt(keys, Hex("00112233445566778899aabbccddeeff")) ==
             Hex("69c4e0d86a7b0430d8cdb78070b4c55a"),
         "AES-128 encryption differs from FIPS 197");
}

void TestDerivedKnownAnswers() {
  struct Vector {
    const char* seed;
    const char* routing;
    const char* stored;
    const char* routing_ciphertext;
    const char* stored_ciphertext;
  };
  const Vector vectors[] = {
      {"000102030405060708090a0b0c0d0e0f",
       "e7cc11e31c74d2351808e05ab0879868",
       "9911caba0c8c4eb9685cfbdb555a9ed1",
       "cc0b31e8143ea941052e878e2fe02b7d",
       "2dee19e3e9da4aac23fb3c7cddee3c64"},
      {"00000000000000000000000000000000",
       "19d6e6ceeddac300ce15514385d7023a",
       "b3dab712db8b6b15bd7327476e15b5e5",
       "ab8446922ba6cb87814856f3c6c512cf",
       "5d3fd292275edb4612dd7849adf44ed1"},
      {"ffffffffffffffffffffffffffffffff",
       "661f2cef1bdb0141d859c61c3ddf3137",
       "76cbe750211f49cae33d49f849763ece",
       "bda99eef435ffa7eea42ce3d38815fee",
       "e9759775a7487c0406a55b037a77e92f"}};
  const Block plaintext = Hex("00112233445566778899aabbccddeeff");
  for (const Vector& v : vectors) {
    const auto seed = Seed(Hex(v.seed));
    const auto routing = crypto::DeriveRoutingAesRoundKeys(seed);
    const auto stored = crypto::DeriveStoredKeyAesRoundKeys(seed);
    const auto wrapper = bs::DeriveStoredKeyHashKeys(seed);
    Expect(Bytes(routing.rk[0]) == Hex(v.routing),
           "routing label/key bytes differ from OpenSSL");
    Expect(Bytes(stored.rk[0]) == Hex(v.stored),
           "stored-key label/key bytes differ from OpenSSL");
    Expect(Encrypt(routing, plaintext) == Hex(v.routing_ciphertext),
           "derived routing schedule differs from OpenSSL");
    Expect(Encrypt(stored, plaintext) == Hex(v.stored_ciphertext),
           "derived stored-key schedule differs from OpenSSL");
    for (size_t r = 0; r < 11; ++r) {
      Expect(Bytes(wrapper.rk[r]) == Bytes(stored.rk[r]),
             "stored-key wrapper uses the wrong derivation");
    }
  }
}

void TestRoutingIdentityMasks() {
  // Probe every raw nonce bit, both alone and cleared from all ones. This
  // checks retained fields and discarded bits independently of the message
  // consumers. Injectivity requires the bounded fields of FamilyId; the
  // masked primitive deliberately does not validate arbitrary raw nonces.
  constexpr uint64_t full = ~uint64_t{0};
  for (unsigned bit = 0; bit < 64; ++bit) {
    const uint64_t input = uint64_t{1} << bit;
    const uint64_t from_low = (bit < 15 || bit == 63) ? input : 0;
    const uint64_t from_high = bit < 48 ? uint64_t{1} << (bit + 15) : 0;
    Expect(crypto::PackAesCtrHighWord(input, 0) == from_low &&
               crypto::PackAesCtrHighWord(full ^ input, full) ==
                   (full ^ from_low),
           "routing low nonce bit is misplaced or incorrectly retained");
    Expect(crypto::PackAesCtrHighWord(0, input) == from_high &&
               crypto::PackAesCtrHighWord(full, full ^ input) ==
                   (full ^ from_high),
           "routing high nonce bit is misplaced or incorrectly retained");
  }
  Expect(crypto::PackAesCtrHighWord(1, 1) ==
             crypto::PackAesCtrHighWord(1 | (uint64_t{1} << 15), 1),
         "out-of-range level alias witness changed");
  Expect(crypto::PackAesCtrHighWord(1, 1) ==
             crypto::PackAesCtrHighWord(1, 1 | (uint64_t{1} << 48)),
         "out-of-range counter alias witness changed");
}

void TestRoutingConsumers() {
  const auto keys = crypto::DeriveRoutingAesRoundKeys(
      Seed(Hex("000102030405060708090a0b0c0d0e0f")));
  const auto vector_keys = bs::MakeAesTagKeys(keys);
  const uint64_t expected[2][2] = {
      {0xd04d1242a54d4d6bull, 0x7f29afa10ece95abull},
      {0x46ab096abf11f62eull, 0xb0e28929e3425800ull}};
  alignas(64) uint64_t low[64], high[64], result[64];
  alignas(64) __m512i low_regs[8], high_regs[8], tag_regs[8];
  for (size_t i = 0; i < 64; ++i) {
    low[i] = 0x0706050403020100ull ^ (i * 0x9e3779b97f4a7c15ull);
    high[i] = 0x0f0e0d0c0b0a0908ull ^ (i * 0xd1b54a32d192ed03ull);
  }
  for (size_t i = 0; i < 8; ++i) {
    low_regs[i] = _mm512_load_si512(low + 8 * i);
    high_regs[i] = _mm512_load_si512(high + 8 * i);
  }
  for (unsigned dummy = 0; dummy < 2; ++dummy) {
    const uint64_t nonce_lo = 0x1234 | (dummy ? crypto::kAesCtrDomainBit : 0);
    const uint64_t nonce_hi = 0x112233445566;
    const uint64_t packed = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
    for (unsigned wide = 0; wide < 2; ++wide) {
      bs::AesBatch64Regs(low_regs, wide ? high_regs : nullptr, packed,
                          tag_regs, *vector_keys);
      for (size_t i = 0; i < 8; ++i) {
        _mm512_store_si512(result + 8 * i, tag_regs[i]);
      }
      Expect(result[0] == expected[dummy][wide],
             "derived-key batch tag differs from OpenSSL");
      for (size_t i = 0; i < 64; ++i) {
        const uint64_t scalar = crypto::AesCtrTagU128WordsHost(
            nonce_lo, nonce_hi, low[i], wide ? high[i] : 0, keys);
        Expect(result[i] == scalar,
               "derived-key batch and scalar routing disagree");
        Expect(scalar == RoutingReference(keys, packed, low[i],
                                           wide ? high[i] : 0),
               "routing differs from the byte-level CBC reference");
      }
    }
  }

  // Online probes interleave per-input key/nonce words, and may leave a
  // partial final SIMD group. Exercise every public count and padded tail.
  alignas(64) uint64_t blocks[256];
  uint64_t oracle[64];
  for (size_t i = 0; i < 64; ++i) {
    const uint64_t nonce_lo = (i * 13) | ((i & 1) ? crypto::kAesCtrDomainBit : 0);
    const uint64_t nonce_hi = crypto::kAesCtrCounterMask - i;
    const uint64_t key_high = (i & 2) ? high[i] : 0;
    blocks[4 * i] = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
    blocks[4 * i + 1] = crypto::kAesRoutingLabel;
    blocks[4 * i + 2] = low[i];
    blocks[4 * i + 3] = key_high;
    oracle[i] = RoutingReference(keys, blocks[4 * i], low[i], key_high);
  }
  constexpr uint64_t canary = 0x5a43c217e96db80full;
  for (size_t count = 0; count <= 64; ++count) {
    uint64_t tags[68];
    for (auto& tag : tags) tag = canary;
    bs::AesTagsInterleaved(blocks, count, tags, *vector_keys);
    const size_t padded = (count + 3) & ~size_t{3};
    for (size_t i = 0; i < padded; ++i) {
      Expect(tags[i] == oracle[i],
             "derived-key interleaved routing disagrees with scalar");
    }
    for (size_t i = padded; i < 68; ++i) {
      Expect(tags[i] == canary, "interleaved routing writes past padded tail");
    }
  }
}

void TestRoutingLaneLayouts() {
  const auto keys = crypto::DeriveRoutingAesRoundKeys(
      Seed(Hex("102132435465768798a9bacbdcedfe0f")));
  const auto vector_keys = bs::MakeAesTagKeys(keys);
  constexpr uint64_t canary = 0x5a43c217e96db80full;
  alignas(64) uint64_t low[64], high[64], expected[64], actual[64], halves[80];
  alignas(64) __m512i low_regs[8], high_regs[8], tag_regs[8], half_tags[10];
  alignas(64) uint64_t messages[100 * 4];
  uint64_t interleaved_expected[100], interleaved[104];
  for (unsigned wide = 0; wide < 2; ++wide) {
    for (unsigned bit = 0; bit < 64; ++bit) {
      // Every lane visits every bit in each word. The one-set/one-cleared
      // patterns distinguish all 64 lanes and the two words. In narrow mode
      // the populated high registers are deliberately not passed to the API.
      const uint64_t family = (uint64_t{bit & 1} << 63) |
                              (uint64_t{bit + 1} << 15) | 0x1234;
      for (size_t i = 0; i < 64; ++i) {
        low[i] = uint64_t{1} << ((bit + i) % 64);
        high[i] = ~(uint64_t{1} << ((bit + i + 17) % 64));
        expected[i] = RoutingReference(keys, family, low[i], wide ? high[i] : 0);
      }
      for (size_t i = 0; i < 8; ++i) {
        low_regs[i] = _mm512_load_si512(low + 8 * i);
        high_regs[i] = _mm512_load_si512(high + 8 * i);
      }
      bs::AesBatch64Regs(low_regs, wide ? high_regs : nullptr, family,
                        tag_regs, *vector_keys);
      for (auto& tag : half_tags) tag = _mm512_set1_epi64(canary);
      bs::AesBatch32Regs(low_regs, wide ? high_regs : nullptr, family,
                        half_tags + 1, *vector_keys);
      bs::AesBatch32Regs(low_regs + 4, wide ? high_regs + 4 : nullptr, family,
                        half_tags + 5, *vector_keys);
      for (size_t i = 0; i < 8; ++i) {
        _mm512_store_si512(actual + 8 * i, tag_regs[i]);
      }
      for (size_t i = 0; i < 10; ++i) {
        _mm512_store_si512(halves + 8 * i, half_tags[i]);
      }
      for (size_t i = 0; i < 64; ++i) {
        Expect(actual[i] == expected[i] && halves[i + 8] == expected[i],
               "shared-family SIMD lane or low-word gather mismatch");
      }
      for (size_t i = 0; i < 8; ++i) {
        Expect(halves[i] == canary && halves[i + 72] == canary,
               "half-bucket routing writes outside its output registers");
      }

      // Independent families exercise both four-message block selectors.
      // 100 messages cross three eight-chain groups and a final tail group.
      for (size_t i = 0; i < 100; ++i) {
        messages[4 * i] = (uint64_t{i & 1} << 63) |
                          ((i + 1) << 15) | (bit + 1);
        messages[4 * i + 1] = crypto::kAesRoutingLabel;
        messages[4 * i + 2] = uint64_t{1} << ((bit + i) % 64);
        messages[4 * i + 3] = wide ? ~(uint64_t{1} << ((bit + i + 17) % 64)) : 0;
        interleaved_expected[i] = RoutingReference(
            keys, messages[4 * i], messages[4 * i + 2], messages[4 * i + 3]);
      }
      for (size_t count : {size_t{0}, size_t{1}, size_t{3}, size_t{4}, size_t{5},
                           size_t{28}, size_t{29}, size_t{31}, size_t{32},
                           size_t{33}, size_t{35}, size_t{36}, size_t{60},
                           size_t{61}, size_t{63}, size_t{64}, size_t{65},
                           size_t{67}, size_t{68}, size_t{95}, size_t{96},
                           size_t{97}, size_t{99}, size_t{100}}) {
        // The full bit sweep needs one long input; boundary cases need only
        // one representative sweep position for each stored-key width.
        if (bit != 0 && count != 100) continue;
        for (auto& tag : interleaved) tag = canary;
        bs::AesTagsInterleaved(messages, count, interleaved, *vector_keys);
        const size_t padded = (count + 3) & ~size_t{3};
        for (size_t i = 0; i < padded; ++i) {
          Expect(interleaved[i] == interleaved_expected[i],
                 "interleaved SIMD lane or low-word gather mismatch");
        }
        for (size_t i = padded; i < 104; ++i) {
          Expect(interleaved[i] == canary,
                 "interleaved SIMD boundary writes past its padded output");
        }
      }
    }
  }
}

void TestRoutingBoundariesAndFormerAliases() {
  const auto keys = crypto::DeriveRoutingAesRoundKeys(
      Seed(Hex("000102030405060708090a0b0c0d0e0f")));
  const auto vector_keys = bs::MakeAesTagKeys(keys);
  alignas(64) uint64_t messages[64 * 4];
  alignas(64) uint64_t low[64], high[64], actual[64], interleaved[64];
  alignas(64) __m512i low_regs[8], high_regs[8], tags[8];
  for (size_t width = 1; width <= 16; ++width) {
    for (unsigned dummy = 0; dummy < 2; ++dummy) {
      for (uint64_t level : {uint64_t{0}, crypto::kAesCtrLevelMask}) {
        for (uint64_t counter : {uint64_t{0}, crypto::kAesCtrCounterMask}) {
          const uint64_t nonce_lo = level | (uint64_t{dummy} << 63);
          const uint64_t packed = (uint64_t{dummy} << 63) | (counter << 15) | level;
          Expect(crypto::PackAesCtrHighWord(nonce_lo, counter) == packed,
                 "routing family fields differ at their boundaries");
          for (size_t i = 0; i < 64; ++i) {
            const auto key = bs::MaskKey(
                bs::KeyWords{i == 0 ? 0 : ~uint64_t{0} - i,
                             i == 0 ? 0 : 0x8f7e6d5c4b3a2918ull + i}, width);
            low[i] = key.w0;
            high[i] = key.w1;
            messages[4 * i] = packed;
            messages[4 * i + 1] = crypto::kAesRoutingLabel;
            messages[4 * i + 2] = key.w0;
            messages[4 * i + 3] = key.w1;
          }
          for (size_t i = 0; i < 8; ++i) {
            low_regs[i] = _mm512_load_si512(low + 8 * i);
            high_regs[i] = _mm512_load_si512(high + 8 * i);
          }
          bs::AesBatch64Regs(low_regs, width > 8 ? high_regs : nullptr,
                              packed, tags, *vector_keys);
          bs::AesTagsInterleaved(messages, 64, interleaved, *vector_keys);
          for (size_t i = 0; i < 8; ++i) {
            _mm512_store_si512(actual + 8 * i, tags[i]);
          }
          for (size_t i = 0; i < 64; ++i) {
            const uint64_t want = RoutingReference(keys, packed, low[i], high[i]);
            Expect(actual[i] == want && interleaved[i] == want &&
                       crypto::AesCtrTagU128WordsHost(
                           nonce_lo, counter, low[i], high[i], keys) == want,
                   "routing boundary/partial-width reference mismatch");
          }
        }
      }
    }
  }

  // These distinct (nonce, key) pairs would produce exactly the same AES
  // input block under an encoding that XORs the nonce family into the key's
  // high word, so they exercise level, epoch and real/dummy separation with
  // controlled high words.  The CBC message encoding keeps them apart.
  // Distinct 64-bit outputs here are fixed known answers, not a claim that a
  // 64-bit tag is an injective function.
  const uint64_t low_word = 0x0706050403020100ull;
  const uint64_t high_word = 0x0f0e0d0c0b0a0908ull;
  const uint64_t nonce_lo = 0x1234;
  const uint64_t nonce_hi = 0x112233445566;
  const uint64_t family = crypto::PackAesCtrHighWord(nonce_lo, nonce_hi);
  const uint64_t first = crypto::AesCtrTagU128WordsHost(
      nonce_lo, nonce_hi, low_word, high_word, keys);
  for (uint64_t changed : {family ^ uint64_t{1}, family ^ (uint64_t{1} << 15),
                          family ^ (uint64_t{1} << 63)}) {
    const uint64_t other_high = high_word ^ family ^ changed;
    Expect((high_word ^ family) == (other_high ^ changed),
           "alias fixture does not collide under the XOR-folded encoding");
    const uint64_t second = crypto::AesCtrTagU128WordsHost(
        changed & (crypto::kAesCtrDomainBit | crypto::kAesCtrLevelMask),
        (changed >> 15) & crypto::kAesCtrCounterMask,
        low_word, other_high, keys);
    Expect(second == RoutingReference(keys, changed, low_word, other_high),
           "alias pair differs from the CBC reference");
    Expect(first != second, "XOR-folded alias pair returned unchanged tags");
  }
}

Block StoredBytes(const uint8_t* input, size_t width,
                  const crypto::AesRoundKeys& keys) {
  const auto actual = bs::EncodeStoredKey(input, width, keys);
  Block bytes{};
  for (size_t i = 0; i < 8; ++i) {
    bytes[i] = static_cast<uint8_t>(actual.w0 >> (8 * i));
    bytes[i + 8] = static_cast<uint8_t>(actual.w1 >> (8 * i));
  }
  return bytes;
}

void TestNormalizationConsumers() {
  const auto keys = bs::DeriveStoredKeyHashKeys(
      Seed(Hex("000102030405060708090a0b0c0d0e0f")));
  // Independently generated OpenSSL answers for each width 16..64. The three
  // inputs are bytes 0..width-1, that input with its last byte XOR 0x80, and
  // that input with its last byte zero. The first byte is always zero; the
  // third input also exercises trailing zero bytes at every block boundary.
  // Narrower keys are stored verbatim at their own width.
  // For width >16, OpenSSL AES-CBC with IV=0 encrypts LE128(width) followed
  // by the input padded with zeros to a multiple of 16; retain its last block.
  const char* vectors[][3] = {
      {"f2265acdf1eb97a7bec0c36201bb7003", "48db5d27caaa2e3af098dc234b911a26",
       "0ffba87b4796118ba2924972a6bde569"},  // 16
      {"a4078aca820e1a732ad098171dc5c9ef", "def8a9e8517647f02d81a987171d4bec",
       "4f8469b4b17cd1b6c62b880c6cb15cb7"},  // 17
      {"11ce7eadaafce1401ad8f86f5d9a09fb", "06dfc85605a5fe7c26908f15f3bf0a89",
       "6e4d58b2253bf616f02fe2f6e6415c15"},  // 18
      {"853908f223bd3b3d3a60c23d4b6bfdd6", "d1265bdb1e147eaa209192162ed75c09",
       "d9ae3c6ded9ec270389ee64474ab5bf7"},  // 19
      {"466a990815fad24dd5fa7b0293712e69", "bd76c9bf0f45eaa8ecd5ffabdbceb437",
       "d4b1163896cb2f86b83f9d4eeb431a69"},  // 20
      {"67a79a20535be2122592a7969f24c833", "c39742cbaef2854e2ca410396c94f1b5",
       "710cd0831e0aa5962fd61903ea58a46d"},  // 21
      {"f10611f0f2f870681423cf4b10387468", "46d50aa34350a15d73c9dcc20cc26c1e",
       "75231aea454362b04e7eca06bd44836f"},  // 22
      {"301d7c5675f5d5b5479ff1c9688063c2", "981d187c55532b26472d022b0f1db7b4",
       "890fc889426f0d7889ee418ee3fa9de5"},  // 23
      {"e09e81c9e86d8def9e9d38191bb10990", "e2e6456f9ac5faa1a3ed6522bf925311",
       "f3e835cba47a3011f8dc2363644eec2d"},  // 24
      {"8f178bdfd6bf94f65df9589dd4b38e3e", "bfc875d9778864108ce986f3f2ab9333",
       "6524d1f15bea9d058eb1fe6d7671313c"},  // 25
      {"779cf532d382cec52b7a34cd8ce0181a", "c884bac8da2d96f8d0306275d8609480",
       "ad86df3f3303415e66009ef38871ba6d"},  // 26
      {"fc00cc60517ebec6daf43eceaa1e4ba4", "0a575740997a8691a1cf0373374d80ca",
       "fd56d1d5e158039f4c979ca54e8415c5"},  // 27
      {"0db7a930c0dcafa81a147b9e1f6c0613", "e3eb11eac5479601f6bddc206ce9bc81",
       "f0a797b2eb09cfd35db5e43bbed36672"},  // 28
      {"3b3d653caeff22341fd9259b6a6b1a46", "e00e716922f25dec93091112fae35919",
       "6749cb7805015508c624959cd597885a"},  // 29
      {"5116ced1efbb90f6e565617212aa42b4", "e25ff06344c778709d2dc547a3919143",
       "9e67e3be3de4e79792d8914a0f8d9834"},  // 30
      {"1ba5a86761258c83fc4df45bfa0f95e7", "1bdc5e7e2add1cf23fc077e8c0f0661a",
       "7dd7248a1dbec91ed642a634cabdf9dc"},  // 31
      {"a32402b410f9ed1480e74488b40c5711", "1636ed16b8aec61caa80b7774e60cd5a",
       "f4f209cbdb749be76e8c7d3e9c0184b0"},  // 32
      {"a1d6d9259338509182fd99672b4646e8", "11ac864be4c7acf8f19077791983d8d5",
       "a1fe474ecfffec4e9b557a021306e1ca"},  // 33
      {"630217609c39451f994069abc0556b17", "df2d02741ff06699d814b2a1bfc0656a",
       "1e8bc4a90c7fa42afaa1c6ecc59b0a07"},  // 34
      {"3c6f979a49898ba0b705920cc1339b35", "c7899f943938d3d9f48fccbc1f1ab6a0",
       "f5327727295b6d6a8b5b75d37ec33680"},  // 35
      {"45ead0ac4c46a15945e7ad1aec86268d", "4fcacca920e84692ac066f2d27ad1afa",
       "3197616613c654307c0f77ddd505a2eb"},  // 36
      {"bf5ecfcacfb883c5f1e8ce527fb4d2a8", "a890db71407107e6e38ced8d1f728f30",
       "3b57ebde0d127a22beb80d991eb47aac"},  // 37
      {"38f1dc5248514a3253c215c5fb180820", "64d0e40559ce37f400cf09a11025a872",
       "cc4f2ef3fca58533779639ffba428d0d"},  // 38
      {"f1799a32e043d414e9aa4f8758bfd6b1", "12f01df34e8f8e193664e2764a0adef3",
       "5a96d7dadd8e7a8a176756804921becd"},  // 39
      {"dad5306a3d1cddf4620306f746ccf271", "0d16467a5e11fdbc7a9e81f1b0d8386d",
       "0037f82a2c7ce07de3a03378e270ffef"},  // 40
      {"8d9eb0f0fb225cbd6495bb34b762826a", "b58826b23e1ed76311b5676d970c4f6b",
       "fc761d7c30f2f8ead1af86d904884b08"},  // 41
      {"0ea8082faee0b93f6b4f616e02a52e3a", "c43966834dca0358e1beada435930fba",
       "825f16a35d8415f837e1e9c11aec2d7d"},  // 42
      {"5aa6eff4b52b84cf2813e069d7421565", "df2cfe536315c2ee22aa2eb8b7c6b0a4",
       "583a91908055b6155ef0fd025f03a431"},  // 43
      {"f351bd716c522ef027da6d14231765e0", "8c05d047fe9c255d8165391a8da9329e",
       "75024a064ab8ffb48285baabb86df50b"},  // 44
      {"fdd1b2835df9ae05020b0f8cf1faaa3b", "0c482a0f667c9fb006e41b8a19f3f090",
       "db598a16fd6a5bc6b88cf08577844763"},  // 45
      {"7b67275fd4fa64d4d96207e5cde21685", "5ef06e2805adeabdbef5c19b724feb9d",
       "a0ab3ede746c0c03033b086dda2e9cc4"},  // 46
      {"eec957c5286fe06bc8fc21a88a3a64d6", "de04ac2ea50e655cd193d056d8f4c3cb",
       "f7a76cfa4226557eee0e79c6c2d70973"},  // 47
      {"6a9ec5ad6306cb34031696e38daa13f6", "42c4b4f92748019c87aa09ec1c3ded11",
       "7cf64f5392ab055ec85751677b966b66"},  // 48
      {"c632647e28fe42c667e8fd4192a7cb84", "2a5b0e768fd4fb5d87b6eb6d1e69dde4",
       "cffa508bd1efb8fabfca6aa2043573cb"},  // 49
      {"518de7e0d9cb54856532b0c64a5c3369", "7721b35f8d13080e30f1e52196d1f56e",
       "84f98dad5ea9a0cb9b9a8b335b20605d"},  // 50
      {"2b68b5007e4c4bfc8fb7d277720f165c", "eb4833a597f599bf7318bb8816c5c522",
       "cc3548f999a9d2c246c14fcb34455768"},  // 51
      {"bc169177396709e3563789920222f7c9", "6b8e04c8cee939011a79cfe2af2c3e48",
       "3ed93959b3d73282704fabc846b8dd19"},  // 52
      {"69f785dde3d47956db4ab3ae480d6700", "784e444bdeecc5d637d1e0ee0833ecb9",
       "14d013215aa93ea8a2695cd755cb5979"},  // 53
      {"a7880d8910b3c91cf5517c933319eb1c", "8b02ff8a14c524bcc69979e049251dce",
       "d6c42cdaacf34aeecf3bc7a8534ef261"},  // 54
      {"6bcbbba5fa4d27061f5aa28aad79d359", "21ec17a1cb936e4562ca71743030f3b9",
       "381cbd716764f895469c0498576aae2b"},  // 55
      {"3c518a079d079dde84bb279ed44eb6c8", "5fc2928b40276720631cf9328f764e5f",
       "266852c87844b78f2a60d32b0e2fe766"},  // 56
      {"f70440827d14b89cbdce52cf372fc8e3", "809f84516a978261b82f9399bd9f8fb6",
       "1c4986f05a702db0f63e5de0c212f879"},  // 57
      {"262fddf14b1b754985e59ef12c0e7e32", "99277358f67a50c1c6a14aebe8db7532",
       "2e77acfa1b0f86f94f44a6d01ce49583"},  // 58
      {"caa1bbd8b2b9931460ebf53a305e167f", "e31c9d7d5e2717b09a17ce8da97209b6",
       "bde7b3548be9834d7d40f5d3342f81f7"},  // 59
      {"35f36b4b08fade2248256e66bda89143", "907108b2f078f893c9c5ef76b1c5c1c8",
       "89803bcc1736436964a748509eb8cf75"},  // 60
      {"331f4055b3c3511acf4b1fd5de18a5f9", "9f9495f4cfe169dbbbc61ed85c6a6dc6",
       "805cfe20483f934fc03a00e11a29d052"},  // 61
      {"557f9a23c07b598d071386820a77a3ed", "ca4b909ec01a8879b78702f81b8cfea4",
       "c20e176a6ca57e82381324ca77380038"},  // 62
      {"be1d4a61d3648436a56306632e192d39", "549610fe0cda317396e8887b5004d760",
       "23d48e7c30f58eb92609b42b9ab709bf"},  // 63
      {"ca763bbcf3ee152ecb7344ffb4c45983", "39806f1eaeab925a7ed096dcbba180bc",
       "977a446685718f03c31e8e0781cc1cad"},  // 64
  };
  static_assert(sizeof(vectors) / sizeof(vectors[0]) == 49,
                "every normalized width needs known answers");
  for (size_t width = 1; width <= 64; ++width) {
    for (unsigned variant = 0; variant < 3; ++variant) {
      std::array<uint8_t, 64> input{};
      // Bytes outside the declared key must not become its zero padding.
      input.fill(0xa5);
      for (size_t i = 0; i < width; ++i) input[i] = static_cast<uint8_t>(i);
      if (variant == 1) input[width - 1] ^= 0x80;
      if (variant == 2) input[width - 1] = 0;
      Block expected{};
      if (width < 16) {
        for (size_t i = 0; i < width; ++i) expected[i] = input[i];
      } else {
        expected = Hex(vectors[width - 16][variant]);
      }
      const Block actual = StoredBytes(input.data(), width, keys);
      if (actual != expected) {
        std::fprintf(stderr, "normalization mismatch: width=%zu variant=%u\n",
                     width, variant);
      }
      Expect(actual == expected,
             "normalization differs from independent byte/OpenSSL answers");
    }
    if (width < 16) {
      Expect(bs::StoredKeyBytes(width) == width,
             "keys narrower than 16 bytes must keep their width");
    }
  }
}

void TestNormalizationFixedWidth() {
  const auto keys = bs::DeriveStoredKeyHashKeys(
      Seed(Hex("000102030405060708090a0b0c0d0e0f")));
  // Finite evidence for exact fixed-width storage: the zero input and every
  // single-byte perturbation stay distinct at each width 1..16. The Lean
  // encoding argument supplies the general injectivity statement.
  for (size_t width = 1; width <= 16; ++width) {
    std::array<uint8_t, 16> input{};
    std::set<Block> outputs{StoredBytes(input.data(), width, keys)};
    for (size_t position = 0; position < width; ++position) {
      for (unsigned value = 1; value <= 255; ++value) {
        input[position] = static_cast<uint8_t>(value);
        Expect(outputs.insert(StoredBytes(input.data(), width, keys)).second,
               "distinct fixed-width normalization fixtures alias");
      }
      input[position] = 0;
    }
    Expect(outputs.size() == 1 + 255 * width,
           "fixed-width normalization fixture coverage changed");
  }

  // Negative witnesses: fixed width is necessary. A trailing zero aliases
  // across widths in verbatim storage, in either stored word, and in the
  // helper's padded one-block AES branch, which stored keys now reach only at
  // sixteen bytes. No hierarchy instance admits these mixed-width comparisons.
  std::array<uint8_t, 16> input{};
  input[0] = 0x37;
  Expect(StoredBytes(input.data(), 1, keys) == StoredBytes(input.data(), 2, keys),
         "verbatim mixed-width alias witness changed");
  input[8] = 0x91;
  Expect(StoredBytes(input.data(), 9, keys) == StoredBytes(input.data(), 15, keys),
         "two-word verbatim mixed-width alias witness changed");
  uint64_t short_block[2], full_block[2];
  crypto::AesHashKey128(input.data(), 9, keys, short_block);
  crypto::AesHashKey128(input.data(), 16, keys, full_block);
  Expect(short_block[0] == full_block[0] && short_block[1] == full_block[1],
         "one-block AES mixed-width alias witness changed");
}

}  // namespace

// The production seed: sixteen bytes from the kernel's generator, never all
// zero, and independent from one draw to the next.
void TestRandomSeeds() {
  std::set<std::pair<uint64_t, uint64_t>> seen;
  for (int i = 0; i < 64; ++i) {
    const crypto::SecretKeySeed seed = crypto::SecretKeySeed::Random();
    Expect(seed.lo != 0 || seed.hi != 0, "a random seed was all zero");
    Expect(seen.insert({seed.lo, seed.hi}).second, "two random seeds repeated");
  }
}

int main() {
  TestRandomSeeds();
  TestAesKnownAnswer();
  TestDerivedKnownAnswers();
  TestRoutingIdentityMasks();
  TestRoutingConsumers();
  TestRoutingLaneLayouts();
  TestRoutingBoundariesAndFormerAliases();
  TestNormalizationConsumers();
  TestNormalizationFixedWidth();
  std::puts("PASS: derived key vectors, routing paths, and normalization");
}
