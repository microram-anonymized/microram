// Reference canonical MPT (variable-time, public data only): construction from
// sorted secure keys, immutable batch updates sharing untouched nodes, full
// graph validation, proof generation and proof verification.

#include "trie.hpp"

#include <algorithm>
#include <iterator>
#include <stdexcept>
#include <unordered_set>
#include <utility>

namespace ethereum_mpt {
namespace {

constexpr std::size_t kKeyNibbles = 64;
constexpr std::size_t kMaxNodeBytes = 532;

void require(bool condition, const char* message) {
  if (!condition) throw std::invalid_argument(message);
}

void validate_kind(TrieKind kind) {
  require(kind == TrieKind::account || kind == TrieKind::storage,
          "invalid trie role");
}

void validate_value(TrieKind kind, const Bytes& value) {
  if (kind == TrieKind::account) {
    (void)decode_account(value);
  } else {
    const Word decoded = decode_storage(value);
    require(std::any_of(decoded.begin(), decoded.end(),
                        [](std::uint8_t byte) { return byte != 0; }),
            "zero storage must be absent from the trie");
  }
}

Bytes encode_reference(const NodePtr& node) {
  if (!node) return rlp_bytes({});
  if (node->rlp.size() < 32) return node->rlp;
  return rlp_bytes(Bytes(node->hash.begin(), node->hash.end()));
}

NodePtr finish_node(std::shared_ptr<Node> node, TrieUpdateStats* stats = nullptr) {
  std::vector<Bytes> items;
  if (node->kind == NodeKind::branch) {
    items.reserve(17);
    for (const auto& child : node->children)
      items.push_back(encode_reference(child));
    items.push_back(rlp_bytes({}));
  } else {
    items.push_back(rlp_bytes(
        compact_encode(node->path, node->kind == NodeKind::leaf)));
    items.push_back(node->kind == NodeKind::leaf
                        ? rlp_bytes(node->value)
                        : encode_reference(node->child));
  }
  node->rlp = rlp_list(items);
  require(node->rlp.size() <= kMaxNodeBytes, "node exceeds secure-trie bound");
  node->hash = keccak256(node->rlp);
  if (stats) ++stats->created_nodes;
  return node;
}

struct PreparedEntry {
  Nibbles path;
  const Bytes* value;
};

using EntryIterator = std::vector<PreparedEntry>::const_iterator;

NodePtr build_subtrie(EntryIterator begin, EntryIterator end,
                      std::size_t depth, TrieUpdateStats* stats = nullptr) {
  if (begin == end) return {};
  auto node = std::make_shared<Node>();
  if (std::next(begin) == end) {
    node->kind = NodeKind::leaf;
    node->path.assign(begin->path.begin() + depth, begin->path.end());
    node->value = *begin->value;
    return finish_node(std::move(node), stats);
  }

  const auto& first = begin->path;
  const auto& last = std::prev(end)->path;
  std::size_t common_end = depth;
  while (common_end < kKeyNibbles && first[common_end] == last[common_end])
    ++common_end;
  require(common_end < kKeyNibbles, "duplicate trie key");
  if (common_end != depth) {
    node->kind = NodeKind::extension;
    node->path.assign(first.begin() + depth, first.begin() + common_end);
    node->child = build_subtrie(begin, end, common_end, stats);
    return finish_node(std::move(node), stats);
  }

  node->kind = NodeKind::branch;
  for (auto group_begin = begin; group_begin != end;) {
    const std::uint8_t index = group_begin->path[depth];
    auto group_end = std::next(group_begin);
    while (group_end != end && group_end->path[depth] == index) ++group_end;
    node->children[index] = build_subtrie(group_begin, group_end, depth + 1, stats);
    group_begin = group_end;
  }
  return finish_node(std::move(node), stats);
}

bool path_matches(const Nibbles& key, std::size_t depth,
                  const Nibbles& path) {
  return depth <= key.size() && path.size() <= key.size() - depth &&
         std::equal(path.begin(), path.end(), key.begin() + depth);
}

struct PreparedMutation {
  Nibbles path;
  const std::optional<Bytes>* value;
};
using MutationIterator = std::vector<PreparedMutation>::const_iterator;

// A short-node slice is a virtual subtree after some of its path has been
// consumed. Deferring its encoding avoids constructing throwaway nodes while
// splitting a prefix, and preserves pointer identity for absent-key erasures.
struct NodeView {
  NodePtr node;
  std::size_t skip = 0;
  bool original = true;
};

bool same_view(const NodeView& lhs, const NodeView& rhs) {
  return lhs.node == rhs.node && lhs.skip == rhs.skip;
}

struct UpdateContext {
  TrieUpdateStats stats;
  std::unordered_set<const Node*> visited;

  void inspect(const NodeView& view) {
    if (view.node && view.original && visited.insert(view.node.get()).second)
      ++stats.visited_nodes;
  }

  NodeView finish(std::shared_ptr<Node> node) {
    NodePtr result = finish_node(std::move(node), &stats);
    return {std::move(result), 0, false};
  }
};

NodeView suffix(const NodeView& view, std::size_t consumed) {
  const std::size_t skip = view.skip + consumed;
  if (view.node->kind == NodeKind::extension && skip == view.node->path.size())
    return {view.node->child, 0, view.original};
  return {view.node, skip, view.original};
}

NodeView prepend(const Nibbles& prefix, const NodeView& view,
                 UpdateContext& context) {
  if (!view.node || (prefix.empty() && view.skip == 0)) return view;
  context.inspect(view);
  auto node = std::make_shared<Node>();
  node->path = prefix;
  if (view.node->kind == NodeKind::branch) {
    node->kind = NodeKind::extension;
    node->child = view.node;
  } else {
    node->kind = view.node->kind;
    node->path.insert(node->path.end(), view.node->path.begin() + view.skip,
                      view.node->path.end());
    node->child = view.node->child;
    node->value = view.node->value;
  }
  return context.finish(std::move(node));
}

NodeView assemble(const std::array<NodeView, 16>& children, Nibbles prefix,
                  UpdateContext& context) {
  std::size_t count = 0, sole_index = 0;
  for (std::size_t i = 0; i < children.size(); ++i) {
    if (children[i].node) {
      ++count;
      sole_index = i;
    }
  }
  if (count == 0) return {};
  if (count == 1) {
    prefix.push_back(static_cast<std::uint8_t>(sole_index));
    return prepend(prefix, children[sole_index], context);
  }
  auto branch = std::make_shared<Node>();
  branch->kind = NodeKind::branch;
  for (std::size_t i = 0; i < children.size(); ++i)
    branch->children[i] = prepend({}, children[i], context).node;
  return prepend(prefix, context.finish(std::move(branch)), context);
}

NodeView update_subtrie(const NodeView& existing, std::size_t depth,
                       MutationIterator begin, MutationIterator end,
                       UpdateContext& context) {
  if (begin == end) return existing;
  if (!existing.node) {
    // Only insertions contribute structure in an empty subtree. Keeping this
    // sorted subset lets the ordinary builder create each new node once.
    std::vector<PreparedEntry> entries;
    for (auto it = begin; it != end; ++it)
      if (*it->value) entries.push_back({it->path, &**it->value});
    return {build_subtrie(entries.begin(), entries.end(), depth, &context.stats),
            0, false};
  }

  context.inspect(existing);
  const Node& old = *existing.node;
  std::size_t split = depth;
  Nibbles prefix;
  std::array<NodeView, 16> children{};
  if (old.kind == NodeKind::branch) {
    for (std::size_t i = 0; i < children.size(); ++i)
      children[i] = {old.children[i], 0, existing.original};
  } else {
    const std::size_t remaining = old.path.size() - existing.skip;
    std::size_t common = 0;
    while (common < remaining &&
           old.path[existing.skip + common] == begin->path[depth + common] &&
           old.path[existing.skip + common] == std::prev(end)->path[depth + common])
      ++common;
    if (common == remaining) {
      if (old.kind == NodeKind::leaf) {
        if (!*begin->value) return {};
        if (**begin->value == old.value) return existing;
        auto leaf = std::make_shared<Node>();
        leaf->path.assign(old.path.begin() + existing.skip, old.path.end());
        leaf->value = **begin->value;
        return context.finish(std::move(leaf));
      }
      const NodeView child{old.child, 0, existing.original};
      const NodeView updated = update_subtrie(child, depth + remaining,
                                              begin, end, context);
      if (same_view(child, updated)) return existing;
      return prepend(Nibbles(old.path.begin() + existing.skip, old.path.end()),
                     updated, context);
    }
    split += common;
    prefix.assign(old.path.begin() + existing.skip,
                   old.path.begin() + existing.skip + common);
    children[old.path[existing.skip + common]] = suffix(existing, common + 1);
  }

  bool changed = false;
  for (auto group = begin; group != end;) {
    const std::uint8_t index = group->path[split];
    auto group_end = std::next(group);
    while (group_end != end && group_end->path[split] == index) ++group_end;
    const NodeView updated = update_subtrie(children[index], split + 1,
                                           group, group_end, context);
    changed = changed || !same_view(updated, children[index]);
    children[index] = updated;
    group = group_end;
  }
  if (!changed) return existing;
  return assemble(children, std::move(prefix), context);
}

ChildReference decode_reference(const RlpItem& item, TrieKind kind,
                                std::size_t depth, bool allow_empty,
                                bool require_branch) {
  ChildReference reference;
  if (item.is_list) {
    require(item.encoded.size() < 32, "oversized embedded trie child");
    const DecodedNode child = decode_node(item.encoded, kind, depth);
    require(!require_branch || child.kind == NodeKind::branch,
            "extension must point to a branch");
    require(!child.child.hash, "embedded node contains a hashed child");
    for (const auto& nested : child.children)
      require(!nested.hash, "embedded node contains a hashed child");
    reference.embedded = item.encoded;
  } else if (item.payload.empty()) {
    require(allow_empty, "extension has an empty child");
  } else {
    require(item.payload.size() == 32, "invalid trie child reference");
    Hash hash{};
    std::copy(item.payload.begin(), item.payload.end(), hash.begin());
    reference.hash = hash;
  }
  return reference;
}

void validate_subtrie(const NodePtr& node, TrieKind kind, std::size_t depth) {
  require(static_cast<bool>(node), "missing trie node");
  const DecodedNode decoded = decode_node(node->rlp, kind, depth);
  require(node->hash == keccak256(node->rlp), "cached trie hash mismatch");
  require(node->kind == decoded.kind && node->path == decoded.path &&
              node->value == decoded.value,
          "trie fields disagree with canonical bytes");
  auto validate_child = [&](const NodePtr& child,
                            const ChildReference& reference,
                            std::size_t child_depth) {
    if (reference.empty()) {
      require(!child, "unexpected trie child");
      return;
    }
    require(static_cast<bool>(child), "missing referenced trie child");
    if (reference.hash) {
      require(child->rlp.size() >= 32, "short trie child must be embedded");
      require(child->hash == *reference.hash, "trie child hash mismatch");
    } else {
      require(child->rlp == reference.embedded,
              "embedded trie child bytes mismatch");
    }
    validate_subtrie(child, kind, child_depth);
  };
  if (decoded.kind == NodeKind::branch) {
    require(!node->child, "unexpected extension child on a branch");
    for (std::size_t i = 0; i < 16; ++i)
      validate_child(node->children[i], decoded.children[i], depth + 1);
  } else {
    for (const auto& child : node->children)
      require(!child, "unexpected branch child on a short node");
    if (decoded.kind == NodeKind::extension) {
      validate_child(node->child, decoded.child, depth + decoded.path.size());
      require(node->child->kind == NodeKind::branch,
              "extension must point to a branch");
    } else {
      require(!node->child, "unexpected extension child on a leaf");
    }
  }
}

}  // namespace

Hash Trie::root_hash() const { return root ? root->hash : empty_trie_root(); }

Trie build_trie(TrieKind kind, const std::vector<Entry>& entries) {
  validate_kind(kind);
  std::vector<PreparedEntry> sorted;
  sorted.reserve(entries.size());
  for (const auto& entry : entries) {
    validate_value(kind, entry.value);
    sorted.push_back({nibbles(entry.key), &entry.value});
  }
  std::sort(sorted.begin(), sorted.end(),
            [](const PreparedEntry& lhs, const PreparedEntry& rhs) {
              return lhs.path < rhs.path;
            });
  for (std::size_t i = 1; i < sorted.size(); ++i)
    require(sorted[i - 1].path != sorted[i].path, "duplicate trie key");
  return {kind, build_subtrie(sorted.begin(), sorted.end(), 0)};
}

std::optional<Bytes> lookup_trie(const Trie& trie, const Hash& key) {
  validate_kind(trie.kind);
  const Nibbles path = nibbles(key);
  NodePtr node = trie.root;
  std::size_t depth = 0;
  while (node) {
    if (node->kind == NodeKind::branch) {
      node = node->children[path[depth++]];
    } else {
      if (!path_matches(path, depth, node->path)) return std::nullopt;
      if (node->kind == NodeKind::leaf) return node->value;
      depth += node->path.size();
      node = node->child;
    }
  }
  return std::nullopt;
}

Trie update_trie(const Trie& trie, const std::vector<TrieMutation>& mutations,
                 TrieUpdateStats* stats) {
  validate_kind(trie.kind);
  std::vector<PreparedMutation> sorted;
  sorted.reserve(mutations.size());
  for (const auto& mutation : mutations) {
    if (mutation.value) validate_value(trie.kind, *mutation.value);
    sorted.push_back({nibbles(mutation.key), &mutation.value});
  }
  std::sort(sorted.begin(), sorted.end(),
            [](const PreparedMutation& lhs, const PreparedMutation& rhs) {
              return lhs.path < rhs.path;
            });
  for (std::size_t i = 1; i < sorted.size(); ++i)
    require(sorted[i - 1].path != sorted[i].path, "duplicate trie mutation key");
  UpdateContext context;
  const NodeView root = update_subtrie({trie.root}, 0, sorted.begin(), sorted.end(),
                                      context);
  if (stats) *stats = context.stats;
  return {trie.kind, root.node};
}

void validate_trie(const Trie& trie) {
  validate_kind(trie.kind);
  if (trie.root) validate_subtrie(trie.root, trie.kind, 0);
}

DecodedNode decode_node(const Bytes& encoded, TrieKind kind,
                        std::size_t incoming_depth) {
  validate_kind(kind);
  require(incoming_depth <= kKeyNibbles, "trie depth exceeds key length");
  require(encoded.size() <= kMaxNodeBytes, "node exceeds secure-trie bound");
  const RlpItem outer = rlp_decode(encoded);
  require(outer.is_list, "trie node must be an RLP list");
  const auto items = rlp_items(outer);
  DecodedNode node;
  if (items.size() == 17) {
    require(incoming_depth < kKeyNibbles, "branch exceeds secure-key length");
    require(!items[16].is_list && items[16].payload.empty(),
            "secure-trie branch value must be empty");
    node.kind = NodeKind::branch;
    std::size_t child_count = 0;
    for (std::size_t i = 0; i < 16; ++i) {
      node.children[i] = decode_reference(items[i], kind, incoming_depth + 1,
                                          true, false);
      child_count += !node.children[i].empty();
    }
    require(child_count >= 2, "canonical branch needs at least two children");
  } else {
    require(items.size() == 2, "trie node must have two or seventeen items");
    require(!items[0].is_list, "compact path must be an RLP string");
    const CompactPath compact = compact_decode(items[0].payload);
    node.path = compact.path;
    require(node.path.size() <= kKeyNibbles - incoming_depth,
            "compact path exceeds secure-key length");
    if (compact.leaf) {
      node.kind = NodeKind::leaf;
      require(node.path.size() == kKeyNibbles - incoming_depth,
              "leaf does not terminate at secure-key length");
      require(!items[1].is_list, "leaf value must be an RLP string");
      node.value = items[1].payload;
      validate_value(kind, node.value);
    } else {
      node.kind = NodeKind::extension;
      require(!node.path.empty(), "zero-length trie extension");
      require(node.path.size() < kKeyNibbles - incoming_depth,
              "extension has no remaining branch nibble");
      node.child = decode_reference(items[1], kind,
                                    incoming_depth + node.path.size(), false,
                                    true);
    }
  }
  return node;
}

Proof prove(const Trie& trie, const Hash& key) {
  validate_kind(trie.kind);
  Proof proof;
  const Nibbles path = nibbles(key);
  auto node = trie.root;
  std::size_t depth = 0;
  if (node) proof.push_back(node->rlp);
  while (node) {
    if (node->kind == NodeKind::leaf) break;
    if (node->kind == NodeKind::branch) {
      require(depth < kKeyNibbles, "branch exceeds secure-key length");
      node = node->children[path[depth++]];
    } else {
      if (!path_matches(path, depth, node->path)) break;
      depth += node->path.size();
      node = node->child;
    }
    if (node && node->rlp.size() >= 32) proof.push_back(node->rlp);
  }
  return proof;
}

std::optional<Bytes> verify_proof(TrieKind kind, const Hash& root,
                                const Hash& key, const Proof& proof) {
  validate_kind(kind);
  if (root == empty_trie_root()) {
    require(proof.empty(), "empty trie has a nonempty proof");
    return std::nullopt;
  }
  require(!proof.empty(), "missing trie root proof node");
  require(proof.size() <= kKeyNibbles + 1, "proof exceeds secure-trie bound");
  require(keccak256(proof.front()) == root, "proof root hash mismatch");

  const Nibbles path = nibbles(key);
  std::size_t depth = 0;
  std::size_t used = 1;
  Bytes encoded = proof.front();
  bool expect_branch = false;
  auto finish = [&](std::optional<Bytes> value) {
    require(used == proof.size(), "superfluous trie proof node");
    return value;
  };

  for (std::size_t visited = 0; visited <= kKeyNibbles; ++visited) {
    const DecodedNode node = decode_node(encoded, kind, depth);
    require(!expect_branch || node.kind == NodeKind::branch,
            "extension must point to a branch");
    ChildReference next;
    if (node.kind == NodeKind::leaf)
      return finish(path_matches(path, depth, node.path)
                        ? std::optional<Bytes>(node.value)
                        : std::nullopt);
    if (node.kind == NodeKind::extension) {
      if (!path_matches(path, depth, node.path)) return finish(std::nullopt);
      depth += node.path.size();
      next = node.child;
      expect_branch = true;
    } else {
      next = node.children[path[depth++]];
      if (next.empty()) return finish(std::nullopt);
      expect_branch = false;
    }
    if (next.hash) {
      require(used < proof.size(), "missing hashed child proof node");
      encoded = proof[used++];
      require(encoded.size() >= 32, "short trie child must be embedded");
      require(keccak256(encoded) == *next.hash, "proof child hash mismatch");
    } else {
      encoded = next.embedded;
    }
  }
  throw std::invalid_argument("proof traversal exceeds secure-trie bound");
}

}  // namespace ethereum_mpt
