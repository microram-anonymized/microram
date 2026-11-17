#pragma once

// User-key -> stored-key conversion for the hierarchy and standalone callers.
//
// Keys of at most fifteen bytes are stored verbatim at their own width (one
// KeyWords word through eight bytes, two above). Keys of sixteen bytes or more
// are compressed to one AES-128 block under a per-instance key that is
// domain-separated from the routing-tag key. Keeping the conversion here makes
// the representation and its key derivation consistent across callers.

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {

inline crypto::AesRoundKeys DeriveStoredKeyHashKeys(
    const crypto::SecretKeySeed& seed) {
  return crypto::DeriveStoredKeyAesRoundKeys(seed);
}

inline KeyWords EncodeStoredKey(const uint8_t* key, size_t user_key_bytes,
                                const crypto::AesRoundKeys& hash_keys) {
  if (user_key_bytes <= 8) {
    uint64_t low = 0;
    std::memcpy(&low, key, user_key_bytes);
    return KeyWords{low};
  }
  if (user_key_bytes < kMaxKeyBytes) {
    // Verbatim, as StoredKeyBytes keeps the width: zero above the key.  The
    // empty asm hides the source object, as in crypto::AesHashKey128, so a
    // word-key call site's dead path does not warn -Wstringop-overread.
    const uint8_t* bytes = key;
    asm("" : "+r"(bytes));
    uint64_t words[2] = {0, 0};
    std::memcpy(words, bytes, user_key_bytes);
    return KeyWords{words[0], words[1]};
  }
  uint64_t out[2];
  crypto::AesHashKey128(key, user_key_bytes, hash_keys, out);
  return KeyWords{out[0], out[1]};
}

inline KeyWords NarrowStoredKey(uint64_t key, size_t user_key_bytes) {
  if (user_key_bytes > 8) {
    throw std::invalid_argument(
        "this ORAM was configured with a key wider than 8 bytes: pass the "
        "key as bytes (Read/Write/Erase(const uint8_t*, ...))");
  }
  return MaskKey(KeyWords{key}, user_key_bytes);
}

}  // namespace byteslice
}  // namespace microram

