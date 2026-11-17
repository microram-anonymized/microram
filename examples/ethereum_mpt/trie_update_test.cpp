// Tests update_trie against full rebuilds: no-ops and rejection, structural
// splits/merges, shared paths, maximum depth and randomized batches.

#include "trie.hpp"

#include <algorithm>
#include <map>
#include <numeric>
#include <random>
#include <stdexcept>

namespace {
using namespace ethereum_mpt;
using Values = std::map<Hash, Bytes>;

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

Hash key_at(std::size_t depth, std::uint8_t nibble) {
  Hash key{};
  key[depth / 2] = static_cast<std::uint8_t>(nibble << (depth % 2 ? 0 : 4));
  return key;
}

Bytes value_for(TrieKind kind, std::uint64_t seed) {
  Word word{};
  word[31] = static_cast<std::uint8_t>(1 + seed % 255);
  word[30] = static_cast<std::uint8_t>(seed >> 8);
  if (kind == TrieKind::storage) return encode_storage(word);
  Account account;
  account.nonce = seed;
  account.balance = word;
  return encode_account(account);
}

Bytes wide_storage(std::size_t bytes) {
  Word word{};
  std::fill(word.end() - bytes, word.end(), 1);
  return encode_storage(word);
}

std::vector<Entry> entries_for(const Values& values) {
  std::vector<Entry> entries;
  for (const auto& item : values) entries.push_back({item.first, item.second});
  return entries;
}

void apply_mutations(Values& values, const std::vector<TrieMutation>& mutations) {
  for (const auto& mutation : mutations) {
    if (mutation.value)
      values[mutation.key] = *mutation.value;
    else
      values.erase(mutation.key);
  }
}

void equivalent(const Trie& trie, const Values& values,
                const std::vector<Hash>& queries) {
  const Trie rebuilt = build_trie(trie.kind, entries_for(values));
  check(trie.root_hash() == rebuilt.root_hash(), "updated root differs from rebuild");
  check(!trie.root || trie.root->rlp == rebuilt.root->rlp,
        "updated root bytes differ from rebuild");
  validate_trie(trie);
  for (const auto& key : queries) {
    const auto found = values.find(key);
    const std::optional<Bytes> expected = found == values.end()
        ? std::nullopt : std::optional<Bytes>(found->second);
    check(lookup_trie(trie, key) == expected, "updated direct lookup mismatch");
    const Proof proof = prove(trie, key);
    check(proof == prove(rebuilt, key), "updated proof differs from rebuild");
    check(verify_proof(trie.kind, trie.root_hash(), key, proof) == expected,
          "updated membership/absence proof mismatch");
  }
}

void empty_noop_and_rejection() {
  const Hash key{}, absent = key_at(0, 1);
  const Bytes value = value_for(TrieKind::storage, 1);
  const Trie empty = build_trie(TrieKind::storage, {});
  TrieUpdateStats stats{99, 99};
  check(!update_trie(empty, {}, &stats).root && stats.visited_nodes == 0 &&
            stats.created_nodes == 0,
        "empty mutation batch did work");
  const Trie single = update_trie(empty, {{key, value}}, &stats);
  check(single.root->kind == NodeKind::leaf && single.root->path.size() == 64 &&
            stats.visited_nodes == 0 && stats.created_nodes == 1,
        "empty insertion did not create one full-key leaf");
  check(update_trie(single, {{key, value}, {absent, std::nullopt}}, &stats).root ==
            single.root && stats.created_nodes == 0 && stats.visited_nodes == 1,
        "equal replacement and absent erase lost root identity");
  check(update_trie(single, {}, &stats).root == single.root &&
            stats.visited_nodes == 0 && stats.created_nodes == 0,
        "empty batch visited existing graph");
  check(!update_trie(single, {{key, std::nullopt}}, &stats).root &&
            stats.visited_nodes == 1 && stats.created_nodes == 0,
        "last-key erase did not return empty trie");
  const Hash near = key_at(63, 1);
  const Trie mixed = update_trie(empty, {{absent, std::nullopt}, {key, value},
                                        {near, value}}, &stats);
  equivalent(mixed, {{key, value}, {near, value}}, {key, near, absent});
  check(stats.visited_nodes == 0 && stats.created_nodes == 4,
        "empty mixed batch counted erased keys as trie structure");

  const Hash original_hash = single.root_hash();
  const Bytes original_rlp = single.root->rlp;
  const auto rejected_batch = [&](const std::vector<TrieMutation>& mutations) {
    stats = {123, 456};
    rejects([&] { (void)update_trie(single, mutations, &stats); },
            "invalid mutation batch accepted");
    check(stats.visited_nodes == 123 && stats.created_nodes == 456,
          "rejected mutation changed output statistics");
    check(single.root_hash() == original_hash && single.root->rlp == original_rlp &&
              lookup_trie(single, key) == value,
          "rejected batch changed parent trie");
  };
  rejected_batch({{key, value}, {key, value}});
  rejected_batch({{key, std::nullopt}, {key, value}});
  rejected_batch({{absent, value}, {key, Bytes{0x80}}});
  rejected_batch({{key, Bytes{0x81, 0x01}}});
  const Trie account = build_trie(TrieKind::account, {});
  rejects([&] { update_trie(account, {{key, value}}); },
          "account updater accepted a storage encoding");
  const Trie invalid{static_cast<TrieKind>(99), nullptr};
  stats = {123, 456};
  rejects([&] { update_trie(invalid, {}, &stats); }, "invalid updater role accepted");
  check(stats.visited_nodes == 123 && stats.created_nodes == 456,
        "invalid role changed output statistics");
  rejects([&] { lookup_trie(invalid, key); }, "invalid lookup role accepted");
}

void structural_updates() {
  const Hash a{}, b = key_at(63, 1), c = key_at(62, 1),
             d = key_at(0, 1), e = key_at(31, 1), f = key_at(0, 2);
  const std::vector<Hash> keys{a, b, c, d, e, f};
  for (const TrieKind kind : {TrieKind::storage, TrieKind::account}) {
    const Bytes value = value_for(kind, 7);
    Values values{{a, value}, {b, value}, {d, value}};
    Trie trie = build_trie(kind, entries_for(values));
    const Trie parent = trie;
    const auto unaffected = trie.root->children[1];
    auto mutate = [&](const std::vector<TrieMutation>& mutations) {
      const Hash old_root = trie.root_hash();
      const Trie old = trie;
      trie = update_trie(trie, mutations);
      apply_mutations(values, mutations);
      equivalent(trie, values, keys);
      check(old.root_hash() == old_root, "structural update changed parent hash");
      validate_trie(old);
    };
    mutate({{a, std::nullopt}, {b, std::nullopt}, {c, value}, {e, value}});
    check(trie.root->children[1] == unaffected,
          "prefix splits copied an unrelated subtree");
    equivalent(parent, {{a, value}, {b, value}, {d, value}}, keys);
    mutate({{c, std::nullopt}}); // Collapse below the existing extension.
    mutate({{d, std::nullopt}}); // Merge the root branch into a full-key leaf.
    check(trie.root->kind == NodeKind::leaf && trie.root->path.size() == 64,
          "branch collapse did not merge the full path");
    mutate({{e, std::nullopt}, {a, value}, {b, value}, {f, value}});
    mutate({{a, std::nullopt}, {b, std::nullopt}, {f, std::nullopt}});
    check(!trie.root, "batch deletion retained an empty graph");
  }
}

void shared_paths_and_thresholds() {
  const Hash a{}, b = key_at(63, 1), c = key_at(63, 2), d = key_at(0, 1);
  const Bytes value = wide_storage(27), changed = wide_storage(28);
  const Trie parent = build_trie(TrieKind::storage,
      {{a, value}, {b, value}, {c, value}, {d, value}});
  const auto original_branch = parent.root->children[0]->child;
  check(original_branch->children[0]->path.empty() &&
            original_branch->children[0]->rlp.size() == 31,
        "zero-nibble leaf threshold setup changed");
  TrieUpdateStats batch_stats;
  const Trie updated = update_trie(parent, {{a, changed}, {b, changed}}, &batch_stats);
  check(batch_stats.visited_nodes == 5 && batch_stats.created_nodes == 5,
        "batch did not visit/encode the shared ancestors once");
  check(updated.root->children[1] == parent.root->children[1] &&
            updated.root->children[0]->child->children[2] ==
                original_branch->children[2],
        "batch copied untouched sibling nodes");
  const auto changed_branch = updated.root->children[0]->child;
  check(changed_branch->children[0]->rlp.size() == 32,
        "updated storage leaf missed 31-to-32-byte transition");
  const auto decoded = decode_node(changed_branch->rlp, TrieKind::storage, 63);
  check(decoded.children[0].hash && decoded.children[1].hash &&
            !decoded.children[2].hash,
        "updated branch child reference threshold mismatch");
  TrieUpdateStats first_stats, second_stats;
  const Trie first = update_trie(parent, {{a, changed}}, &first_stats);
  const Trie second = update_trie(first, {{b, changed}}, &second_stats);
  check(second.root_hash() == updated.root_hash() &&
            batch_stats.created_nodes < first_stats.created_nodes + second_stats.created_nodes &&
            batch_stats.visited_nodes < first_stats.visited_nodes + second_stats.visited_nodes,
        "batch shared no work versus repeated single-key mutations");
  equivalent(updated, {{a, changed}, {b, changed}, {c, value}, {d, value}}, {a, b, c, d});
  const Trie restored = update_trie(updated, {{a, value}, {b, value}});
  check(restored.root_hash() == parent.root_hash() &&
            restored.root->children[0]->child->children[0]->rlp.size() == 31,
        "32-to-31-byte child transition failed");

  const Trie extension = build_trie(TrieKind::storage, {{a, value}, {b, value}});
  const Trie noop = update_trie(extension, {{key_at(20, 3), std::nullopt},
                                           {key_at(0, 4), std::nullopt}}, &batch_stats);
  check(noop.root == extension.root && batch_stats.created_nodes == 0,
        "absent erasures split an extension");
  const Trie switched = update_trie(extension, {{a, std::nullopt}, {b, std::nullopt},
                                                {d, value}});
  equivalent(switched, {{d, value}}, {a, b, c, d});
}

void maximum_depth_updates() {
  // Every nibble branches on the all-zero path, ending in a zero-length leaf.
  // Exercise updates and full collapse/re-expansion at the 65-node limit.
  std::vector<Hash> keys(1);
  for (std::size_t depth = 0; depth < 64; ++depth)
    keys.push_back(key_at(depth, 1));
  for (const TrieKind kind : {TrieKind::storage, TrieKind::account}) {
    const Bytes value = value_for(kind, 7), changed = value_for(kind, 8);
    Values values;
    for (const auto& key : keys) values[key] = value;
    const Trie parent = build_trie(kind, entries_for(values));
    TrieUpdateStats stats;
    const Trie updated = update_trie(parent, {{{}, changed}}, &stats);
    values[{}] = changed;
    equivalent(updated, values, keys);
    check(stats.visited_nodes == 65 && stats.created_nodes == 65,
          "maximum-depth replacement did not copy exactly one complete path");
    auto original_node = parent.root, updated_node = updated.root;
    for (std::size_t depth = 0; depth < 64; ++depth) {
      check(updated_node->children[1] == original_node->children[1],
            "maximum-depth replacement copied a sibling");
      original_node = original_node->children[0];
      updated_node = updated_node->children[0];
    }
    check(lookup_trie(parent, {}) == value,
          "maximum-depth replacement modified its parent");

    std::vector<TrieMutation> deletions, insertions;
    for (std::size_t i = 1; i < keys.size(); ++i) {
      deletions.push_back({keys[i], std::nullopt});
      insertions.push_back({keys[i], value});
    }
    const Trie collapsed = update_trie(updated, deletions);
    check(collapsed.root->kind == NodeKind::leaf && collapsed.root->path.size() == 64,
          "maximum-depth deletion failed to collapse all branches");
    equivalent(collapsed, {{{}, changed}}, keys);
    const Trie expanded = update_trie(collapsed, insertions);
    equivalent(expanded, values, keys);
    check(expanded.root_hash() == updated.root_hash(),
          "maximum-depth re-expansion failed to restore the canonical root");
  }
}

void randomized_batches() {
  std::mt19937_64 random(0x747269655f626174ULL);
  std::vector<Hash> keys(72);
  for (std::size_t i = 0; i < keys.size(); ++i) {
    for (auto& byte : keys[i]) byte = static_cast<std::uint8_t>(random());
    if (i % 3 == 0) std::fill(keys[i].begin(), keys[i].begin() + 24, 0);
    if (i % 3 == 1) std::fill(keys[i].begin(), keys[i].begin() + 31, 0);
    keys[i][31] = static_cast<std::uint8_t>(i);
  }
  for (const TrieKind kind : {TrieKind::storage, TrieKind::account}) {
    Trie trie = build_trie(kind, {});
    Values values;
    std::vector<std::size_t> order(keys.size());
    std::iota(order.begin(), order.end(), 0);
    for (std::size_t round = 0; round < 80; ++round) {
      std::shuffle(order.begin(), order.end(), random);
      std::vector<TrieMutation> mutations;
      for (std::size_t i = 0, count = 1 + random() % 12; i < count; ++i) {
        const Hash& key = keys[order[i]];
        const auto found = values.find(key);
        if (random() % 3 == 0)
          mutations.push_back({key, std::nullopt});
        else if (found != values.end() && random() % 3 == 0)
          mutations.push_back({key, found->second});
        else
          mutations.push_back({key, value_for(kind, random())});
      }
      const Trie parent = trie;
      const Values previous = values;
      TrieUpdateStats stats;
      trie = update_trie(parent, mutations, &stats);
      apply_mutations(values, mutations);
      equivalent(trie, values, keys);
      // Retained roots stay queryable after arbitrary subsequent mutations.
      equivalent(parent, previous, {keys[order.front()], keys[order.back()]});
      if (values == previous)
        check(trie.root == parent.root && stats.created_nodes == 0,
              "random no-op did not preserve graph identity");
      const Trie reversed = update_trie(parent,
          std::vector<TrieMutation>(mutations.rbegin(), mutations.rend()));
      check(reversed.root_hash() == trie.root_hash(), "batch depends on input order");
    }
  }
}
}  // namespace

void test_trie_updates() {
  empty_noop_and_rejection();
  structural_updates();
  shared_paths_and_thresholds();
  maximum_depth_updates();
  randomized_batches();
}
