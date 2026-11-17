// Tests the reference trie: empty and singleton tries, proof failures and
// absence, the 32-byte embedding threshold, maximum depth and malformed nodes.

#include "trie.hpp"

#include <algorithm>
#include <stdexcept>
#include <string>

namespace {

using namespace ethereum_mpt;

void check(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(message);
}

template <class Function>
void rejects(Function&& function, const char* message) {
  try {
    function();
  } catch (const std::invalid_argument&) {
    return;
  }
  throw std::runtime_error(message);
}

Hash key_with_nibble(std::size_t depth, std::uint8_t nibble) {
  Hash key{};
  key[depth / 2] = static_cast<std::uint8_t>(
      nibble << (depth % 2 == 0 ? 4 : 0));
  return key;
}

Bytes storage_value(std::size_t nonzero_bytes) {
  Word value{};
  std::fill(value.end() - nonzero_bytes, value.end(), 1);
  return encode_storage(value);
}

Bytes leaf(const Nibbles& path, const Bytes& value) {
  return rlp_list({rlp_bytes(compact_encode(path, true)), rlp_bytes(value)});
}

Bytes branch(const std::vector<std::pair<std::size_t, Bytes>>& children) {
  std::vector<Bytes> items(17, rlp_bytes({}));
  for (const auto& child : children) items.at(child.first) = child.second;
  return rlp_list(items);
}

void empty_and_singleton() {
  const Trie empty = build_trie(TrieKind::storage, {});
  check(empty.root_hash() == empty_trie_root(), "empty root mismatch");
  check(prove(empty, {}) == Proof{}, "empty trie proof is not empty");
  check(!verify_proof(empty.kind, empty.root_hash(), {}, {}),
        "empty trie absence failed");
  validate_trie(empty);
  rejects([&] { verify_proof(empty.kind, empty.root_hash(), {}, {{0x80}}); },
          "nonempty proof accepted for empty root");

  const auto value = storage_value(1);
  const Trie singleton = build_trie(TrieKind::storage, {{{}, value}});
  check(singleton.root->kind == NodeKind::leaf &&
            singleton.root->path.size() == 64,
        "singleton root is not a full-key leaf");
  check(singleton.root_hash() == keccak256(singleton.root->rlp),
        "singleton root must always be hashed");
  check(verify_proof(singleton.kind, singleton.root_hash(), {},
                     prove(singleton, {})) == value,
        "singleton membership failed");
  const Hash absent = key_with_nibble(63, 1);
  check(!verify_proof(singleton.kind, singleton.root_hash(), absent,
                      prove(singleton, absent)),
        "singleton leaf mismatch did not prove absence");
  validate_trie(singleton);
  rejects([&] { build_trie(TrieKind::storage, {{{}, value}, {{}, value}}); },
          "duplicate keys accepted");
  rejects([&] { build_trie(TrieKind::storage, {{{}, rlp_bytes({})}}); },
          "zero storage accepted");
  rejects([&] { build_trie(TrieKind::account, {{{}, value}}); },
          "storage leaf accepted in account role");

  auto bad_hash = std::make_shared<Node>(*singleton.root);
  bad_hash->hash[0] ^= 1;
  rejects([&] { validate_trie({singleton.kind, bad_hash}); },
          "corrupted cached node hash accepted");
  auto bad_value = std::make_shared<Node>(*singleton.root);
  bad_value->value[0] ^= 1;
  rejects([&] { validate_trie({singleton.kind, bad_value}); },
          "object fields disagreeing with canonical bytes accepted");
}

void proof_failures_and_absence() {
  const auto value = storage_value(1);
  const Trie trie = build_trie(TrieKind::storage,
                               {{{}, value}, {key_with_nibble(0, 1), value}});
  const Proof proof = prove(trie, {});
  check(proof.size() == 2, "expected root and hashed leaf proof");
  check(verify_proof(trie.kind, trie.root_hash(), {}, proof) == value,
        "branch membership failed");
  auto corrupted = proof;
  corrupted.back().back() ^= 1;
  rejects([&] { verify_proof(trie.kind, trie.root_hash(), {}, corrupted); },
          "tampered child proof accepted");
  auto truncated = proof;
  truncated.pop_back();
  rejects([&] { verify_proof(trie.kind, trie.root_hash(), {}, truncated); },
          "missing proof node treated as absence");
  auto excessive = proof;
  excessive.push_back(proof.back());
  rejects([&] { verify_proof(trie.kind, trie.root_hash(), {}, excessive); },
          "superfluous proof node accepted");
  rejects([&] { verify_proof(trie.kind, trie.root_hash(), {}, {}); },
          "missing root treated as absence");
  const Hash absent = key_with_nibble(0, 2);
  check(prove(trie, absent).size() == 1 &&
            !verify_proof(trie.kind, trie.root_hash(), absent,
                          prove(trie, absent)),
        "missing branch child absence failed");

  const Trie common = build_trie(
      TrieKind::storage, {{{}, value}, {key_with_nibble(63, 1), value}});
  check(common.root->kind == NodeKind::extension &&
            common.root->path.size() == 63,
        "shared prefix was not canonically collapsed");
  check(!verify_proof(common.kind, common.root_hash(), absent,
                      prove(common, absent)),
        "extension mismatch absence failed");
  validate_trie(common);
}

void embedding_threshold_and_nested_subtrees() {
  // At incoming depth 64, these canonical storage leaves occupy 31 and 32
  // bytes. Only the latter may appear as a hashed child/proof entry.
  const Trie trie = build_trie(TrieKind::storage,
                               {{{}, storage_value(27)},
                                {key_with_nibble(63, 1), storage_value(28)}});
  const auto& split = trie.root->child;
  check(split->children[0]->rlp.size() == 31 &&
            split->children[1]->rlp.size() == 32,
        "embedding threshold fixture sizes changed");
  const auto decoded = decode_node(split->rlp, TrieKind::storage, 63);
  check(decoded.children[0].embedded == split->children[0]->rlp &&
            decoded.children[1].hash == split->children[1]->hash,
        "31/32-byte embedding rule violated");
  check(prove(trie, {}).size() == 2 &&
            prove(trie, key_with_nibble(63, 1)).size() == 3,
        "proof redundantly includes an embedded leaf");
  for (const auto& key : {Hash{}, key_with_nibble(63, 1)})
    check(verify_proof(trie.kind, trie.root_hash(), key, prove(trie, key))
              .has_value(),
          "threshold proof failed");
  validate_trie(trie);

  const auto value = storage_value(1);
  const Trie nested = build_trie(
      TrieKind::storage, {{{}, value}, {key_with_nibble(63, 1), value},
                          {key_with_nibble(59, 1), value}});
  const auto& outer_branch = nested.root->child;
  const auto& inline_extension = outer_branch->children[0];
  check(inline_extension->kind == NodeKind::extension &&
            inline_extension->rlp.size() < 32 &&
            inline_extension->child->kind == NodeKind::branch &&
            inline_extension->child->rlp.size() < 32,
        "nested inline extension/branch fixture changed");
  check(verify_proof(nested.kind, nested.root_hash(), {}, prove(nested, {})) ==
            value,
        "nested inline subtree proof failed");
  validate_trie(nested);
}

void adversarial_depth_and_maximum_nodes() {
  const Bytes value = encode_account(Account{});
  std::vector<Entry> entries{{{}, value}};
  for (std::size_t depth = 0; depth < 64; ++depth)
    entries.push_back({key_with_nibble(depth, 1), value});
  const Trie deep = build_trie(TrieKind::account, entries);
  auto node = deep.root;
  for (std::size_t depth = 0; depth < 64; ++depth) {
    check(node->kind == NodeKind::branch, "adversarial chain lost a branch");
    node = node->children[0];
  }
  check(node->kind == NodeKind::leaf && node->path.empty(),
        "depth-64 leaf must have an empty suffix");
  const auto proof = prove(deep, {});
  check(proof.size() == 65, "adversarial proof should visit 65 stored nodes");
  check(verify_proof(deep.kind, deep.root_hash(), {}, proof) == value,
        "65-node proof failed");
  validate_trie(deep);

  entries.clear();
  for (std::uint8_t nibble = 0; nibble < 16; ++nibble)
    entries.push_back({key_with_nibble(0, nibble), value});
  const Trie wide = build_trie(TrieKind::account, entries);
  check(wide.root->rlp.size() == 532, "maximum branch must occupy 532 bytes");
  validate_trie(wide);

  Account maximum;
  maximum.nonce = UINT64_MAX;
  maximum.balance.fill(0xff);
  const auto max_account = encode_account(maximum);
  const Trie max_leaf = build_trie(TrieKind::account, {{{}, max_account}});
  check(max_account.size() == 110 && max_leaf.root->rlp.size() == 148,
        "maximum account or account leaf bound changed");
  const Trie max_storage = build_trie(TrieKind::storage, {{{}, storage_value(32)}});
  check(max_storage.root->rlp.size() == 70, "maximum storage leaf bound changed");
}

void malformed_nodes() {
  const auto value = storage_value(1);
  const auto terminal = leaf({}, value);
  const auto sibling = leaf({}, storage_value(2));
  const auto valid_branch = branch({{0, terminal}, {1, sibling}});
  check(decode_node(valid_branch, TrieKind::storage, 63).kind == NodeKind::branch,
        "canonical inline branch rejected");
  rejects([&] { decode_node(branch({{0, terminal}}), TrieKind::storage, 63); },
          "single-child branch accepted");
  rejects([&] { decode_node(valid_branch, TrieKind::storage, 64); },
          "branch at depth 64 accepted");
  rejects([&] { decode_node(terminal, TrieKind::storage, 63); },
          "short secure-key leaf accepted");
  rejects([&] { decode_node(terminal, TrieKind::storage, 65); },
          "depth beyond 64 accepted");
  rejects([&] { decode_node(rlp_bytes({}), TrieKind::storage, 0); },
          "string accepted as trie node");

  const auto zero_extension = rlp_list({rlp_bytes({0}), valid_branch});
  rejects([&] { decode_node(zero_extension, TrieKind::storage, 63); },
          "zero-length extension accepted");
  const auto extension_to_leaf =
      rlp_list({rlp_bytes(compact_encode({0}, false)), terminal});
  rejects([&] { decode_node(extension_to_leaf, TrieKind::storage, 63); },
          "extension consuming the full key accepted");
  const auto longer_leaf = leaf({0}, value);
  const auto noncanonical_extension =
      rlp_list({rlp_bytes(compact_encode({0}, false)), longer_leaf});
  rejects([&] { decode_node(noncanonical_extension, TrieKind::storage, 62); },
          "extension pointing to an inline leaf accepted");

  const auto large_leaf = leaf({}, storage_value(28));
  rejects([&] {
    decode_node(branch({{0, terminal}, {1, large_leaf}}), TrieKind::storage, 63);
  }, "32-byte embedded child accepted");
  const Hash short_hash = keccak256(terminal);
  const Bytes hashed_short = branch(
      {{0, rlp_bytes(Bytes(short_hash.begin(), short_hash.end()))}, {1, sibling}});
  const Hash branch_hash = keccak256(hashed_short);
  const Bytes root = rlp_list(
      {rlp_bytes(compact_encode(Nibbles(63, 0), false)),
       rlp_bytes(Bytes(branch_hash.begin(), branch_hash.end()))});
  rejects([&] {
    verify_proof(TrieKind::storage, keccak256(root), {},
                 {root, hashed_short, terminal});
  }, "hashed short child accepted");

  const Bytes hashed_leaf = leaf(Nibbles(63, 0), value);
  const Hash leaf_hash = keccak256(hashed_leaf);
  const Bytes extension = rlp_list(
      {rlp_bytes(compact_encode({0}, false)),
       rlp_bytes(Bytes(leaf_hash.begin(), leaf_hash.end()))});
  rejects([&] {
    verify_proof(TrieKind::storage, keccak256(extension), {},
                 {extension, hashed_leaf});
  }, "extension pointing to a hashed leaf accepted");
  rejects([&] {
    decode_node(branch({{0, terminal}, {1, rlp_bytes({1})}}),
                TrieKind::storage, 63);
  }, "invalid child reference length accepted");
  rejects([&] {
    decode_node(branch({{0, terminal}, {1, sibling}, {16, rlp_bytes({1})}}),
                TrieKind::storage, 63);
  }, "nonempty secure-trie branch value accepted");
  rejects([&] { decode_node(Bytes(533, 0), TrieKind::storage, 0); },
          "oversized trie node accepted");
}

}  // namespace

void run_trie_tests() {
  empty_and_singleton();
  proof_failures_and_absence();
  embedding_threshold_and_nested_subtrees();
  adversarial_depth_and_maximum_nodes();
  malformed_nodes();
}
