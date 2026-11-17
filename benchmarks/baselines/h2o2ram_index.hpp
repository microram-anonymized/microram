#pragma once
// The H2O2RAM index of a key. H2O2RAM is an index ORAM: it addresses blocks by
// a number below 2^63 (bit 63 marks a dummy) and stores no key, so every
// backend receives the same key bytes and this adapter turns them into an
// index (README.md, "How each baseline is wrapped"). Dense
// keys and keys narrower than 8 bytes are their value; an 8-byte permuted key
// is its value with bit 63 (H2O2RAM's dummy flag) cleared, which is injective
// on the generator's keys (an odd affine map of IDs below 2^63); a wider key is
// a keyed AES-CMAC digest truncated to 63 bits, whose collisions the adapter
// counts on the fill set.
#include "src/oram/support/benchmark_workload.hpp"
#include <openssl/core_names.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <openssl/rand.h>
#include <algorithm>
#include <cstring>
#include <stdexcept>
#include <vector>

namespace oram_bench::h2o2ram {

enum class IndexMode { kValue, kValueBit63Cleared, kDigest };
inline const char* IndexModeName(IndexMode mode) {
  switch (mode) {
    case IndexMode::kValue: return "key_value";
    case IndexMode::kValueBit63Cleared: return "key_value_bit63_cleared";
    case IndexMode::kDigest: return "aes_cmac_63";
  }
  return "?";
}
inline IndexMode ModeFor(const WorkloadSpec& w) {
  if (w.key_layout == KeyLayout::kDense || w.key_bytes < 8) return IndexMode::kValue;
  return w.key_bytes == 8 ? IndexMode::kValueBit63Cleared : IndexMode::kDigest;
}
inline uint64_t LoadLe(const uint8_t* key, size_t bytes) {
  uint64_t value = 0;
  for (size_t i = 0; i < std::min<size_t>(bytes, 8); ++i) value |= uint64_t{key[i]} << (8 * i);
  return value;
}
inline uint64_t ValueIndex(const uint8_t* key, size_t bytes, IndexMode mode) {
  return mode == IndexMode::kValueBit63Cleared ? LoadLe(key, 8) & ~(uint64_t{1} << 63) : LoadLe(key, bytes);
}

// A keyed PRF of the whole key: AES-CMAC from OpenSSL (AES-NI through EVP),
// the first 8 tag bytes little-endian, truncated to `bits` (63 in campaigns;
// fewer only to plant collisions). The key is fresh per process unless given.
class Digest {
 public:
  explicit Digest(unsigned bits, const unsigned char* fixed_key = nullptr)
      : mask_((uint64_t{1} << std::min(bits, 63u)) - 1) {
    unsigned char key[16];
    if (fixed_key) std::memcpy(key, fixed_key, sizeof(key));
    else if (RAND_bytes(key, sizeof(key)) != 1) throw std::runtime_error("h2o2ram: no random key for the index PRF");
    mac_ = EVP_MAC_fetch(nullptr, "CMAC", nullptr);
    ctx_ = mac_ ? EVP_MAC_CTX_new(mac_) : nullptr;
    char cipher[] = "AES-128-CBC";
    const OSSL_PARAM params[] = {OSSL_PARAM_construct_utf8_string(OSSL_MAC_PARAM_CIPHER, cipher, 0),
                                 OSSL_PARAM_construct_end()};
    const bool keyed = ctx_ && EVP_MAC_init(ctx_, key, sizeof(key), params) == 1;
    OPENSSL_cleanse(key, sizeof(key));
    if (!keyed) throw std::runtime_error("h2o2ram: cannot key AES-CMAC");
  }
  ~Digest() { EVP_MAC_CTX_free(ctx_); EVP_MAC_free(mac_); }
  Digest(const Digest&) = delete;
  Digest& operator=(const Digest&) = delete;
  // The full 16-byte tag, for known-answer tests.
  void Tag(const uint8_t* message, size_t bytes, unsigned char tag[16]) {
    size_t length = 0;
    // A null key re-initializes CMAC with the same key.
    if (EVP_MAC_init(ctx_, nullptr, 0, nullptr) != 1 || EVP_MAC_update(ctx_, message, bytes) != 1 ||
        EVP_MAC_final(ctx_, tag, &length, 16) != 1 || length != 16)
      throw std::runtime_error("h2o2ram: AES-CMAC failed");
  }
  uint64_t operator()(const uint8_t* key, size_t bytes) {
    unsigned char tag[16];
    Tag(key, bytes, tag);
    return LoadLe(tag, 8) & mask_;
  }
 private:
  uint64_t mask_;
  EVP_MAC* mac_ = nullptr;
  EVP_MAC_CTX* ctx_ = nullptr;
};

// Keys beyond the first that share an index: 0 means the fill set is injective.
inline uint64_t CountCollisions(std::vector<uint64_t> indices) {
  std::sort(indices.begin(), indices.end());
  uint64_t collisions = 0;
  for (size_t i = 1; i < indices.size(); ++i) collisions += indices[i] == indices[i - 1];
  return collisions;
}
}  // namespace oram_bench::h2o2ram
