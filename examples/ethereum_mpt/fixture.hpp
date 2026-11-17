// Deterministic public demo/test fixture: 48 accounts, with odd accounts
// sharing one eight-slot storage trie, plus address/word helpers.

#pragma once

#include "packing.hpp"

namespace ethereum_mpt {

inline Word word_from_u64(uint64_t value) {
  Word out{};
  for (size_t i = 0; i < 8; ++i) {
    out[31 - i] = static_cast<uint8_t>(value);
    value >>= 8;
  }
  return out;
}

inline Address fixture_address(uint8_t id) {
  Address address{};
  address.back() = id;
  return address;
}

// Public deterministic state for the snapshot demo. The separate update demo
// uses mock_chain/version and the independently generated block fixtures.
inline Snapshot make_fixture() {
  std::vector<Entry> storage_entries;
  for (uint64_t i = 1; i <= 8; ++i) {
    const auto slot = word_from_u64(i);
    storage_entries.push_back(
        {keccak256(slot.data(), slot.size()), encode_storage(word_from_u64(i * 128))});
  }
  const auto storage = build_trie(TrieKind::storage, storage_entries);
  std::vector<Entry> accounts;
  for (uint8_t i = 1; i <= 48; ++i) {
    const auto address = fixture_address(i);
    Account account;
    account.nonce = i;
    account.balance = word_from_u64(uint64_t{i} * 1000);
    if (i % 2) account.storage_root = storage.root_hash();
    accounts.push_back({keccak256(address.data(), address.size()), encode_account(account)});
  }
  return {build_trie(TrieKind::account, accounts), {{storage.root_hash(), storage}}};
}

}  // namespace ethereum_mpt
