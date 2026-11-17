// Reference (variable-time) Ethereum codecs: Keccak-256 with the original 0x01
// padding, strict canonical RLP, hex-prefix compact paths and account/storage
// value encodings. Used only on public data.

#include "codec.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>

namespace ethereum_mpt {
namespace {

constexpr std::size_t kKeccakRate = 136;
constexpr std::array<std::uint64_t, 24> kRoundConstants{{
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL,
}};
// Indexed as x + 5*y, following Keccak's lane convention.
constexpr std::array<unsigned, 25> kRotation{{
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43,
    25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
}};

std::uint64_t rotate(std::uint64_t value, unsigned shift) {
  return shift == 0 ? value : (value << shift) | (value >> (64 - shift));
}

void keccak_permute(std::array<std::uint64_t, 25>& state) {
  for (const auto round_constant : kRoundConstants) {
    std::array<std::uint64_t, 5> columns{};
    for (std::size_t x = 0; x < 5; ++x) {
      for (std::size_t y = 0; y < 5; ++y) columns[x] ^= state[x + 5 * y];
    }
    for (std::size_t x = 0; x < 5; ++x) {
      const auto delta = columns[(x + 4) % 5] ^ rotate(columns[(x + 1) % 5], 1);
      for (std::size_t y = 0; y < 5; ++y) state[x + 5 * y] ^= delta;
    }
    std::array<std::uint64_t, 25> moved{};
    for (std::size_t x = 0; x < 5; ++x) {
      for (std::size_t y = 0; y < 5; ++y) {
        moved[y + 5 * ((2 * x + 3 * y) % 5)] =
            rotate(state[x + 5 * y], kRotation[x + 5 * y]);
      }
    }
    for (std::size_t x = 0; x < 5; ++x) {
      for (std::size_t y = 0; y < 5; ++y) {
        state[x + 5 * y] = moved[x + 5 * y] ^
            ((~moved[(x + 1) % 5 + 5 * y]) & moved[(x + 2) % 5 + 5 * y]);
      }
    }
    state[0] ^= round_constant;
  }
}

void xor_byte(std::array<std::uint64_t, 25>& state, std::size_t offset,
              std::uint8_t byte) {
  state[offset / 8] ^= std::uint64_t{byte} << (8 * (offset % 8));
}

Bytes minimal_integer(std::uint64_t value) {
  Bytes result;
  while (value != 0) {
    result.push_back(static_cast<std::uint8_t>(value));
    value >>= 8;
  }
  std::reverse(result.begin(), result.end());
  return result;
}

Bytes minimal_word(const Word& word) {
  const auto first = std::find_if(word.begin(), word.end(),
                                [](std::uint8_t byte) { return byte != 0; });
  return Bytes(first, word.end());
}

Bytes with_rlp_prefix(const Bytes& payload, bool list) {
  Bytes result;
  if (payload.size() <= 55) {
    result.push_back(static_cast<std::uint8_t>((list ? 0xc0 : 0x80) + payload.size()));
  } else {
    static_assert(sizeof(std::size_t) <= sizeof(std::uint64_t),
                  "RLP length must fit in 64 bits");
    const auto length = minimal_integer(payload.size());
    result.push_back(static_cast<std::uint8_t>((list ? 0xf7 : 0xb7) + length.size()));
    result.insert(result.end(), length.begin(), length.end());
  }
  result.insert(result.end(), payload.begin(), payload.end());
  return result;
}

RlpItem decode_at(const Bytes& encoded, std::size_t& offset) {
  if (offset >= encoded.size()) throw std::invalid_argument("truncated RLP item");
  const auto start = offset;
  const auto prefix = encoded[offset++];
  bool list = false;
  std::size_t size = 0;
  if (prefix < 0x80) {
    return {false, Bytes{prefix}, Bytes{prefix}};
  }
  if (prefix <= 0xb7) {
    size = prefix - 0x80;
  } else if (prefix <= 0xbf || prefix >= 0xf8) {
    list = prefix >= 0xf8;
    const auto length_bytes = static_cast<std::size_t>(prefix - (list ? 0xf7 : 0xb7));
    if (length_bytes > encoded.size() - offset) {
      throw std::invalid_argument("truncated RLP length");
    }
    if (encoded[offset] == 0) throw std::invalid_argument("nonminimal RLP length");
    for (std::size_t i = 0; i < length_bytes; ++i) {
      const auto byte = encoded[offset++];
      if (size > (std::numeric_limits<std::size_t>::max() - byte) / 256) {
        throw std::invalid_argument("RLP length overflow");
      }
      size = size * 256 + byte;
    }
    if (size <= 55) throw std::invalid_argument("nonminimal long RLP item");
  } else {
    list = true;
    size = prefix - 0xc0;
  }
  if (size > encoded.size() - offset) throw std::invalid_argument("truncated RLP payload");
  if (!list && size == 1 && encoded[offset] < 0x80) {
    throw std::invalid_argument("nonminimal single-byte RLP item");
  }
  const auto end = offset + size;
  RlpItem result{list, Bytes(encoded.data() + offset, encoded.data() + end),
                 Bytes(encoded.data() + start, encoded.data() + end)};
  offset = end;
  return result;
}

void validate_scalar(const RlpItem& item, std::size_t max_bytes) {
  if (item.is_list || item.payload.size() > max_bytes) {
    throw std::invalid_argument("invalid scalar type or width");
  }
  if (!item.payload.empty() && item.payload.front() == 0) {
    throw std::invalid_argument("nonminimal scalar");
  }
}

Word word_from_scalar(const RlpItem& item) {
  validate_scalar(item, 32);
  Word result{};
  std::copy(item.payload.begin(), item.payload.end(), result.end() - item.payload.size());
  return result;
}

Hash hash_from_item(const RlpItem& item) {
  if (item.is_list || item.payload.size() != 32) {
    throw std::invalid_argument("account hash must be exactly 32 bytes");
  }
  Hash result{};
  std::copy(item.payload.begin(), item.payload.end(), result.begin());
  return result;
}

void validate_path(const Nibbles& path, bool leaf) {
  if (path.size() > 64 || (!leaf && (path.empty() || path.size() == 64))) {
    throw std::invalid_argument("compact path length outside secure-trie bounds");
  }
  for (const auto nibble : path) {
    if (nibble > 15) throw std::invalid_argument("invalid path nibble");
  }
}

unsigned hex_digit(char value) {
  if (value >= '0' && value <= '9') return static_cast<unsigned>(value - '0');
  if (value >= 'a' && value <= 'f') return static_cast<unsigned>(value - 'a' + 10);
  if (value >= 'A' && value <= 'F') return static_cast<unsigned>(value - 'A' + 10);
  throw std::invalid_argument("invalid hexadecimal digit");
}

}  // namespace

Hash keccak256(const Bytes& bytes) { return keccak256(bytes.data(), bytes.size()); }

Hash keccak256(const std::uint8_t* bytes, std::size_t size) {
  if (bytes == nullptr && size != 0) throw std::invalid_argument("null Keccak input");
  std::array<std::uint64_t, 25> state{};
  while (size >= kKeccakRate) {
    for (std::size_t i = 0; i < kKeccakRate; ++i) xor_byte(state, i, bytes[i]);
    keccak_permute(state);
    bytes += kKeccakRate;
    size -= kKeccakRate;
  }
  for (std::size_t i = 0; i < size; ++i) xor_byte(state, i, bytes[i]);
  // Original Keccak pad10*1: SHA3's delimited suffix would be 0x06.
  xor_byte(state, size, 0x01);
  xor_byte(state, kKeccakRate - 1, 0x80);
  keccak_permute(state);
  Hash digest{};
  for (std::size_t i = 0; i < digest.size(); ++i) {
    digest[i] = static_cast<std::uint8_t>(state[i / 8] >> (8 * (i % 8)));
  }
  return digest;
}

Hash empty_trie_root() {
  static const Hash result = keccak256(Bytes{0x80});
  return result;
}

Hash empty_code_hash() {
  static const Hash result = keccak256(Bytes{});
  return result;
}

std::string hex(const Bytes& bytes) {
  constexpr char digits[] = "0123456789abcdef";
  std::string result;
  if (bytes.size() > result.max_size() / 2) throw std::length_error("hex input too large");
  result.reserve(bytes.size() * 2);
  for (const auto byte : bytes) {
    result.push_back(digits[byte >> 4]);
    result.push_back(digits[byte & 15]);
  }
  return result;
}

std::string hex(const Hash& hash) { return hex(Bytes(hash.begin(), hash.end())); }

Bytes from_hex(const std::string& text) {
  std::size_t offset = 0;
  if (text.size() >= 2 && text[0] == '0' && (text[1] == 'x' || text[1] == 'X')) offset = 2;
  if ((text.size() - offset) % 2 != 0) throw std::invalid_argument("odd hexadecimal length");
  Bytes result;
  result.reserve((text.size() - offset) / 2);
  for (; offset < text.size(); offset += 2) {
    result.push_back(static_cast<std::uint8_t>((hex_digit(text[offset]) << 4) |
                                             hex_digit(text[offset + 1])));
  }
  return result;
}

Nibbles nibbles(const Hash& hash) {
  Nibbles result;
  result.reserve(64);
  for (const auto byte : hash) {
    result.push_back(byte >> 4);
    result.push_back(byte & 15);
  }
  return result;
}

Bytes rlp_bytes(const Bytes& bytes) {
  if (bytes.size() == 1 && bytes.front() < 0x80) return bytes;
  return with_rlp_prefix(bytes, false);
}

Bytes rlp_list(const std::vector<Bytes>& encoded_items) {
  Bytes payload;
  for (const auto& item : encoded_items) {
    rlp_decode(item);
    if (item.size() > payload.max_size() - payload.size()) {
      throw std::length_error("RLP list too large");
    }
    payload.insert(payload.end(), item.begin(), item.end());
  }
  return with_rlp_prefix(payload, true);
}

RlpItem rlp_decode(const Bytes& encoded) {
  std::size_t offset = 0;
  auto result = decode_at(encoded, offset);
  if (offset != encoded.size()) throw std::invalid_argument("trailing bytes after RLP item");
  return result;
}

std::vector<RlpItem> rlp_items(const RlpItem& list) {
  if (!list.is_list) throw std::invalid_argument("RLP item is not a list");
  const auto outer = rlp_decode(list.encoded);
  if (!outer.is_list || outer.payload != list.payload) {
    throw std::invalid_argument("inconsistent RLP list object");
  }
  std::vector<RlpItem> result;
  std::size_t offset = 0;
  while (offset < list.payload.size()) result.push_back(decode_at(list.payload, offset));
  return result;
}

Bytes compact_encode(const Nibbles& path, bool leaf) {
  validate_path(path, leaf);
  const bool odd = path.size() % 2 != 0;
  Bytes result;
  result.reserve(1 + path.size() / 2);
  result.push_back(static_cast<std::uint8_t>((leaf ? 0x20 : 0) | (odd ? 0x10 : 0) |
                                           (odd ? path.front() : 0)));
  for (std::size_t i = odd ? 1 : 0; i < path.size(); i += 2) {
    result.push_back(static_cast<std::uint8_t>((path[i] << 4) | path[i + 1]));
  }
  return result;
}

CompactPath compact_decode(const Bytes& encoded) {
  if (encoded.empty() || encoded.size() > 33) throw std::invalid_argument("invalid compact path size");
  const auto flags = encoded.front() >> 4;
  if (flags > 3) throw std::invalid_argument("invalid compact path flags");
  const bool odd = (flags & 1) != 0;
  CompactPath result{(flags & 2) != 0, {}};
  if (odd) {
    result.path.push_back(encoded.front() & 15);
  } else if ((encoded.front() & 15) != 0) {
    throw std::invalid_argument("nonzero compact path padding");
  }
  for (std::size_t i = 1; i < encoded.size(); ++i) {
    result.path.push_back(encoded[i] >> 4);
    result.path.push_back(encoded[i] & 15);
  }
  validate_path(result.path, result.leaf);
  return result;
}

Bytes encode_account(const Account& account) {
  return rlp_list({rlp_bytes(minimal_integer(account.nonce)),
                   rlp_bytes(minimal_word(account.balance)),
                   rlp_bytes(Bytes(account.storage_root.begin(), account.storage_root.end())),
                   rlp_bytes(Bytes(account.code_hash.begin(), account.code_hash.end()))});
}

Account decode_account(const Bytes& encoded) {
  if (encoded.size() > 110) throw std::invalid_argument("account exceeds 110-byte bound");
  const auto items = rlp_items(rlp_decode(encoded));
  if (items.size() != 4) throw std::invalid_argument("account must contain four fields");
  validate_scalar(items[0], 8);
  Account result;
  for (const auto byte : items[0].payload) result.nonce = (result.nonce << 8) | byte;
  result.balance = word_from_scalar(items[1]);
  result.storage_root = hash_from_item(items[2]);
  result.code_hash = hash_from_item(items[3]);
  return result;
}

Bytes encode_storage(const Word& value) { return rlp_bytes(minimal_word(value)); }

Word decode_storage(const Bytes& encoded) {
  const auto item = rlp_decode(encoded);
  const auto result = word_from_scalar(item);
  if (item.payload.empty()) throw std::invalid_argument("zero storage must be absent");
  return result;
}

}  // namespace ethereum_mpt
