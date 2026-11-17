// Tests the reference codecs against independent Keccak vectors and canonical
// RLP, compact-path and account/storage encoding rules.

#include "codec.hpp"

#include <limits>
#include <stdexcept>
#include <string>
#include <utility>

namespace ethereum_mpt {
namespace {

void expect(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(std::string("codec test: ") + message);
}

template <typename Function>
void rejects(Function function, const char* message) {
  try {
    function();
  } catch (const std::invalid_argument&) {
    return;
  }
  throw std::runtime_error(std::string("codec test accepted malformed input: ") + message);
}

void test_keccak() {
  // Independent PyCryptodome 3.24.1 Keccak-256 vectors, with input[i] = i % 256.
  // These exercise complete blocks and padding on both sides of the 136-byte rate.
  const std::pair<std::size_t, const char*> vectors[] = {
      {0, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"},
      {1, "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"},
      {31, "3e50547cf72e8583ee91462f9d99fe624f53282f78e1a5ec2347b1d0123d0d9b"},
      {32, "8ae1aa597fa146ebd3aa2ceddf360668dea5e526567e92b0321816a4e895bd2d"},
      {135, "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"},
      {136, "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"},
      {137, "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"},
      {271, "7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191"},
      {272, "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"},
      {407, "c2cf727c5f0699cf15e6f77663dcab48d640afd571abbed9cd29f459b50410d6"},
      {408, "4deeaefc26bf0becc5bf9603551584ca1d514238f2f84d0b6adb4bebde86ce61"},
      {532, "6cec40d944dc321c7811a4768339b0e3a6779b92a33b4b2598731fdb45fcd2a7"},
      {4096, "1c85a3e5666494583f321cd54285cc17276acf9aea34b207d43005bfa69d0a86"},
  };
  for (const auto& vector : vectors) {
    Bytes input(vector.first);
    for (std::size_t i = 0; i < input.size(); ++i) input[i] = static_cast<std::uint8_t>(i);
    expect(hex(keccak256(input)) == vector.second, "independent Keccak digest");
  }
  expect(hex(keccak256(Bytes{'a', 'b', 'c'})) ==
             "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45",
         "Keccak abc vector");
  expect(hex(empty_trie_root()) ==
             "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421",
         "Ethereum empty trie root");
  expect(empty_code_hash() == keccak256(nullptr, 0), "empty code hash");
  expect(hex(empty_code_hash()) !=
             "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
         "Ethereum Keccak differs from SHA3-256");
  rejects([] { keccak256(nullptr, 1); }, "null nonempty Keccak input");
}

void test_hex_and_nibbles() {
  expect(hex(from_hex("0x00aBff")) == "00abff", "hexadecimal normalization");
  expect(from_hex("0X") == Bytes{} && from_hex("") == Bytes{}, "empty hexadecimal");
  rejects([] { from_hex("0x0"); }, "odd hexadecimal input");
  rejects([] { from_hex("ag"); }, "invalid hexadecimal input");
  rejects([] { from_hex(" 0"); }, "hexadecimal whitespace");
  Hash key{};
  key[0] = 0xab;
  key.back() = 0x1f;
  const auto path = nibbles(key);
  expect(path.size() == 64 && path[0] == 10 && path[1] == 11 &&
             path[62] == 1 && path[63] == 15,
         "big-endian nibble expansion");
}

void test_rlp() {
  expect(hex(rlp_bytes({})) == "80", "empty byte string");
  expect(hex(rlp_list({})) == "c0", "empty list");
  expect(hex(rlp_bytes(Bytes{0})) == "00", "single zero byte is not a scalar zero");
  expect(hex(rlp_bytes(Bytes{0x7f})) == "7f", "single-byte short form");
  expect(hex(rlp_bytes(Bytes{0x80})) == "8180", "single-byte prefixed form");
  expect(hex(rlp_list({rlp_bytes(Bytes{'c', 'a', 't'}),
                       rlp_bytes(Bytes{'d', 'o', 'g'})})) == "c88363617483646f67",
         "Ethereum RLP example");

  for (const auto length : std::array<std::size_t, 7>{{0, 1, 55, 56, 255, 256, 532}}) {
    const Bytes payload(length, 0x80);
    const auto encoded = rlp_bytes(payload);
    const auto decoded = rlp_decode(encoded);
    expect(!decoded.is_list && decoded.payload == payload && decoded.encoded == encoded,
           "RLP byte string round trip");
    const auto list = rlp_list(std::vector<Bytes>(length, Bytes{0x80}));
    const auto items = rlp_items(rlp_decode(list));
    expect(items.size() == length, "RLP list round trip");
    if (length == 55) expect(encoded[0] == 0xb7 && list[0] == 0xf7, "55-byte prefixes");
    if (length == 56) {
      expect(encoded[0] == 0xb8 && encoded[1] == 56 && list[0] == 0xf8 && list[1] == 56,
             "56-byte prefixes");
    }
    if (length == 256) {
      expect(encoded[0] == 0xb9 && encoded[1] == 1 && encoded[2] == 0 &&
                 list[0] == 0xf9 && list[1] == 1 && list[2] == 0,
             "256-byte prefixes");
    }
  }
  const auto nested = rlp_decode(from_hex("c7c0c1c0c3c0c1c0"));
  const auto children = rlp_items(nested);
  expect(children.size() == 3 && rlp_items(children[1]).size() == 1 &&
             rlp_items(children[2]).size() == 2,
         "nested RLP lists");

  const char* malformed[] = {
      "", "81", "8100", "817f", "8201", "8080", "b8", "b800",
      "b80100", "b90038", "b838", "bf0100000000000000", "bfffffffffffffffff",
      "f8", "f800", "f80180", "f90038", "f838", "ffffffffffffffffff",
  };
  for (const auto* value : malformed) {
    rejects([&] { rlp_decode(from_hex(value)); }, "RLP length/canonicality");
  }
  expect(rlp_items(rlp_decode(from_hex("c100"))).front().payload == Bytes{0},
         "zero byte is valid RLP string content");
  rejects([] { rlp_items(rlp_decode(from_hex("c28100"))); }, "noncanonical list child");
  rejects([] { rlp_items(rlp_decode(from_hex("c181"))); }, "truncated list child");
  rejects([] { rlp_items(rlp_decode(Bytes{0x80})); }, "opening a byte string as a list");
  rejects([] { rlp_items(RlpItem{true, Bytes{0x80}, Bytes{0xc0}}); }, "inconsistent list object");
  rejects([] { rlp_list({Bytes{0x80, 0x80}}); }, "concatenated list element");
  rejects([] { rlp_list({Bytes{}}); }, "empty encoded list element");
}

void test_compact_paths() {
  expect(hex(compact_encode({}, true)) == "20", "empty leaf suffix");
  expect(hex(compact_encode({1, 2, 3, 4, 5}, false)) == "112345", "odd extension path");
  expect(hex(compact_encode({0, 1, 2, 3, 4, 5}, false)) == "00012345", "even extension path");
  expect(hex(compact_encode({0, 15, 1, 12, 11, 8}, true)) == "200f1cb8", "even leaf path");
  expect(hex(compact_encode({15, 1, 12, 11, 8}, true)) == "3f1cb8", "odd leaf path");
  for (std::size_t length = 0; length <= 64; ++length) {
    Nibbles path(length);
    for (std::size_t i = 0; i < length; ++i) path[i] = static_cast<std::uint8_t>(i % 16);
    for (const bool leaf : {false, true}) {
      if (!leaf && (length == 0 || length == 64)) continue;
      const auto decoded = compact_decode(compact_encode(path, leaf));
      expect(decoded.leaf == leaf && decoded.path == path, "compact path round trip");
    }
  }
  rejects([] { compact_decode({}); }, "missing compact path");
  rejects([] { compact_decode(Bytes{0x40}); }, "invalid compact path flags");
  rejects([] { compact_decode(Bytes{0x21}); }, "nonzero compact padding");
  rejects([] { compact_decode(Bytes{0x00}); }, "empty extension");
  rejects([] { compact_encode({}, false); }, "encoding empty extension");
  rejects([] { compact_encode(Nibbles(64, 0), false); }, "64-nibble extension");
  rejects([] { compact_encode(Nibbles(65, 0), true); }, "65-nibble leaf");
  rejects([] { compact_encode({16}, true); }, "out-of-range nibble");
  rejects([] { compact_decode(Bytes(34, 0x20)); }, "oversized compact path");
  rejects([] {
    Bytes path(33, 0);
    path.front() = 0x30;
    compact_decode(path);
  }, "odd 65-nibble compact path");
  rejects([] { compact_decode(Bytes(33, 0)); }, "decoded 64-nibble extension");
}

void test_account_and_storage() {
  Account account;
  account.nonce = std::numeric_limits<std::uint64_t>::max();
  account.balance.fill(0xff);
  account.storage_root.fill(0x42);
  account.code_hash.fill(0x99);
  const auto encoded = encode_account(account);
  expect(encoded.size() == 110, "maximum account bound");
  const auto decoded = decode_account(encoded);
  expect(decoded.nonce == account.nonce && decoded.balance == account.balance &&
             decoded.storage_root == account.storage_root && decoded.code_hash == account.code_hash,
         "maximum account round trip");
  const auto empty = decode_account(encode_account(Account{}));
  expect(empty.nonce == 0 && empty.balance == Word{} && empty.storage_root == empty_trie_root() &&
             empty.code_hash == empty_code_hash(), "default account round trip");

  auto fields = std::vector<Bytes>{rlp_bytes({}), rlp_bytes({}),
                                 rlp_bytes(Bytes(32, 0)), rlp_bytes(Bytes(32, 0))};
  rejects([&] { decode_account(rlp_list({fields[0], fields[1], fields[2]})); }, "missing account field");
  rejects([&] { decode_account(rlp_list({fields[0], fields[1], fields[2], fields[3], fields[0]})); },
          "extra account field");
  rejects([] { decode_account(Bytes(111)); }, "oversized account");
  rejects([] { decode_account(rlp_bytes(Bytes(70, 1))); }, "account byte string");
  for (std::size_t field = 0; field < 4; ++field) {
    const auto original = fields[field];
    fields[field] = rlp_list({});
    rejects([&] { decode_account(rlp_list(fields)); }, "list in account field");
    fields[field] = original;
  }
  for (std::size_t field = 0; field < 2; ++field) {
    const auto original = fields[field];
    for (const auto& payload : {Bytes{0}, Bytes{0, 1}, Bytes(field == 0 ? 9 : 33, 1)}) {
      fields[field] = rlp_bytes(payload);
      rejects([&] { decode_account(rlp_list(fields)); }, "invalid account scalar");
    }
    fields[field] = original;
  }
  for (std::size_t field = 2; field < 4; ++field) {
    const auto original = fields[field];
    for (const auto length : std::array<std::size_t, 3>{{0, 31, 33}}) {
      fields[field] = rlp_bytes(Bytes(length, 1));
      rejects([&] { decode_account(rlp_list(fields)); }, "invalid account hash width");
    }
    fields[field] = original;
  }

  expect(encode_storage(Word{}) == Bytes{0x80}, "scalar zero encoding");
  for (const auto byte : {1, 127, 128, 255}) {
    Word word{};
    word.back() = static_cast<std::uint8_t>(byte);
    expect(decode_storage(encode_storage(word)) == word, "storage scalar round trip");
  }
  Word word{};
  word.fill(0xff);
  expect(encode_storage(word).size() == 33 && decode_storage(encode_storage(word)) == word,
         "maximum storage scalar");
  for (const auto& bad : {Bytes{0x80}, Bytes{0}, rlp_bytes(Bytes{0, 1}),
                          rlp_bytes(Bytes(33, 1)), rlp_list({}), Bytes{1, 1}}) {
    rejects([&] { decode_storage(bad); }, "zero/noncanonical/oversized storage scalar");
  }
  word.fill(0);
  word.back() = 128;
  const auto leaf = rlp_items(rlp_decode(rlp_list({rlp_bytes(compact_encode({}, true)),
                                                rlp_bytes(encode_storage(word))})));
  expect(hex(leaf[1].encoded) == "828180" && decode_storage(leaf[1].payload) == word,
         "storage scalar nested inside leaf byte string");
}

}  // namespace
}  // namespace ethereum_mpt

void run_codec_tests() {
  ethereum_mpt::test_keccak();
  ethereum_mpt::test_hex_and_nibbles();
  ethereum_mpt::test_rlp();
  ethereum_mpt::test_compact_paths();
  ethereum_mpt::test_account_and_storage();
}
