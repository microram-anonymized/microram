// Canonical Ethereum secure-trie reference: node graph, builder, updater,
// validator, lookup and proofs.

#pragma once

#include "codec.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <vector>

namespace ethereum_mpt {

// All routines in this reference module are variable-time. They operate on
// public data and must not be used inside the private traversal.
enum class TrieKind : std::uint8_t { account = 0, storage = 1 };
enum class NodeKind : std::uint8_t { branch = 0, extension = 1, leaf = 2 };

struct Node;
using NodePtr = std::shared_ptr<const Node>;

struct Node {
  NodeKind kind = NodeKind::leaf;
  Nibbles path;
  std::array<NodePtr, 16> children{};
  NodePtr child;
  Bytes value;
  Bytes rlp;
  Hash hash{};
};

struct Entry {
  Hash key;
  Bytes value;
};

struct Trie {
  TrieKind kind = TrieKind::account;
  NodePtr root;

  Hash root_hash() const;
};

// Entries use already-hashed 256-bit secure-trie keys and role-specific encoded
// values. Duplicate keys, zero storage values and invalid encodings are errors.
Trie build_trie(TrieKind kind, const std::vector<Entry>& entries);

struct TrieMutation {
  Hash key{};
  std::optional<Bytes> value;  // nullopt erases the key, including absent keys.
};

struct TrieUpdateStats {
  // Distinct existing nodes inspected by traversal or path normalization.
  std::size_t visited_nodes = 0;
  // Newly encoded and hashed nodes, including any intermediate structural nodes.
  std::size_t created_nodes = 0;
};

// These variable-time operations require a canonical, immutable object graph
// from build_trie/update_trie, or one checked by validate_trie and left unchanged.
// They deliberately do not revalidate the complete graph on each call.
std::optional<Bytes> lookup_trie(const Trie& trie, const Hash& key);

// Applies one batch to the union of its paths, retaining untouched subtrees.
// Duplicate keys and invalid values/roles reject the whole batch. The original
// graph is never modified; a no-op retains root identity. Stats are replaced
// only on success and are left unchanged if any validation/allocation fails.
Trie update_trie(const Trie& trie, const std::vector<TrieMutation>& mutations,
                 TrieUpdateStats* stats = nullptr);

// Validates the complete public object graph, including every child reference,
// cached hash and decoded field, rather than only one proof path.
void validate_trie(const Trie& trie);

struct ChildReference {
  Bytes embedded;
  std::optional<Hash> hash;

  bool empty() const { return embedded.empty() && !hash; }
};

struct DecodedNode {
  NodeKind kind = NodeKind::leaf;
  Nibbles path;
  std::array<ChildReference, 16> children{};
  ChildReference child;
  Bytes value;
};

// Enforces canonical node syntax, depth and role constraints, and recursively
// validates embedded subtrees. A hashed extension target must additionally be
// checked to be a branch when its bytes become available to the caller.
DecodedNode decode_node(const Bytes& encoded, TrieKind kind,
                        std::size_t incoming_depth);

// Ordered minimal proof: the root, then only hashed descendants on the path.
// Embedded descendants are already contained in their parent's encoding.
using Proof = std::vector<Bytes>;
Proof prove(const Trie& trie, const Hash& key);

// Returns nullopt only for authenticated absence. Malformed, missing, tampered
// or superfluous proof nodes throw std::invalid_argument.
std::optional<Bytes> verify_proof(TrieKind kind, const Hash& root,
                                const Hash& key, const Proof& proof);

}  // namespace ethereum_mpt
