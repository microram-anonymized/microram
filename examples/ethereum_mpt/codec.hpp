// Reference Ethereum encodings used by the public builder, packer and client:
// Keccak-256, RLP, nibble paths and account/storage scalar codecs.

#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace ethereum_mpt {

// Public/reference helpers. These allocate and branch on their inputs and must
// not be used inside the private traversal (see fixed.hpp/fixed_node.hpp).
using Bytes = std::vector<std::uint8_t>;
using Hash = std::array<std::uint8_t, 32>;
using Address = std::array<std::uint8_t, 20>;
using Word = Hash;
using Nibbles = Bytes;

// Ethereum's original Keccak-256 domain, not FIPS SHA3-256.
Hash keccak256(const Bytes& bytes);
Hash keccak256(const std::uint8_t* bytes, std::size_t size);
Hash empty_trie_root();
Hash empty_code_hash();

// Lowercase hexadecimal without a prefix; decoding also accepts 0x or 0X.
std::string hex(const Bytes& bytes);
std::string hex(const Hash& hash);
Bytes from_hex(const std::string& text);
Nibbles nibbles(const Hash& hash);

Bytes rlp_bytes(const Bytes& bytes);
// Each argument is an already encoded item, not an unencoded byte string.
Bytes rlp_list(const std::vector<Bytes>& encoded_items);

struct RlpItem {
  bool is_list;
  Bytes payload;
  Bytes encoded;
};

// Decode exactly one canonical outer item. Opening a list validates its direct
// children; callers must open nested lists to validate their contents too.
RlpItem rlp_decode(const Bytes& encoded);
std::vector<RlpItem> rlp_items(const RlpItem& list);

struct CompactPath {
  bool leaf;
  Nibbles path;
};

// Fixed 64-nibble keys: leaves have 0..64 nibbles, extensions have 1..63.
Bytes compact_encode(const Nibbles& path, bool leaf);
CompactPath compact_decode(const Bytes& encoded);

struct Account {
  std::uint64_t nonce = 0;
  Word balance{};
  Hash storage_root = empty_trie_root();
  Hash code_hash = empty_code_hash();
};

Bytes encode_account(const Account& account);
Account decode_account(const Bytes& encoded);
Bytes encode_storage(const Word& value);
// Zero storage must be absent from the trie and is rejected here.
Word decode_storage(const Bytes& encoded);

}  // namespace ethereum_mpt
