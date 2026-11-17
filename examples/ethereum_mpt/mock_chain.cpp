// Public final-state block deltas: validation, application to public state,
// incremental canonical construction (CanonicalState), identity fingerprints
// and the fixture parser. Variable-time code over public data only.

#include "mock_chain.hpp"

#include <algorithm>
#include <array>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

namespace ethereum_mpt {
namespace {

[[noreturn]] void invalid(const std::string& message) {
  throw std::invalid_argument("mock chain: " + message);
}

bool zero(const Word& value) {
  return std::all_of(value.begin(), value.end(),
                     [](std::uint8_t byte) { return byte == 0; });
}

void validate_delta(const MockBlockDelta& delta) {
  std::set<Address> addresses;
  for (const auto& account : delta.account_upserts) {
    if (!addresses.insert(account.address).second)
      invalid("duplicate upsert address");
    std::set<Word> slots;
    for (const auto& change : account.storage_changes)
      if (!slots.insert(change.slot).second) invalid("duplicate storage slot");
  }
  for (const auto& address : delta.account_deletions)
    if (!addresses.insert(address).second)
      invalid("duplicate or overlapping deletion address");
}

template <std::size_t Size>
void append(Bytes& output, const std::array<std::uint8_t, Size>& bytes) {
  output.insert(output.end(), bytes.begin(), bytes.end());
}

void append_u64(Bytes& output, std::uint64_t value) {
  for (std::size_t i = 0; i < 8; ++i)
    output.push_back(static_cast<std::uint8_t>(value >> (8 * (7 - i))));
}

template <std::size_t Size>
std::array<std::uint8_t, Size> read_hex(const std::string& text) {
  if (text.size() != 2 * Size ||
      !std::all_of(text.begin(), text.end(), [](char c) {
        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
      }))
    invalid("expected fixed-width lowercase hexadecimal");
  const auto bytes = from_hex(text);
  std::array<std::uint8_t, Size> result{};
  std::copy(bytes.begin(), bytes.end(), result.begin());
  return result;
}

std::uint64_t read_u64(const std::string& text) {
  if (text.empty() || (text.size() > 1 && text.front() == '0'))
    invalid("noncanonical unsigned decimal integer");
  std::uint64_t result = 0;
  for (const char c : text) {
    if (c < '0' || c > '9') invalid("invalid unsigned decimal integer");
    const auto digit = static_cast<unsigned>(c - '0');
    if (result > (std::numeric_limits<std::uint64_t>::max() - digit) / 10)
      invalid("unsigned decimal integer overflow");
    result = result * 10 + digit;
  }
  return result;
}

void fields(const std::vector<std::string>& row, std::size_t count) {
  if (row.size() != count) invalid("incorrect fixture field count");
}

}  // namespace

Snapshot snapshot_from_state(const PublicState& state) {
  Snapshot snapshot;
  std::vector<Entry> accounts;
  accounts.reserve(state.size());
  for (const auto& [address, source] : state) {
    std::vector<Entry> storage_entries;
    storage_entries.reserve(source.storage.size());
    for (const auto& [slot, value] : source.storage) {
      if (zero(value)) invalid("public state contains zero storage");
      storage_entries.push_back(
          {keccak256(slot.data(), slot.size()), encode_storage(value)});
    }
    auto storage = build_trie(TrieKind::storage, storage_entries);
    Account account;
    account.nonce = source.nonce;
    account.balance = source.balance;
    account.code_hash = source.code_hash;
    account.storage_root = storage.root_hash();
    if (storage.root)
      snapshot.storage_tries.emplace(account.storage_root, std::move(storage));
    accounts.push_back(
        {keccak256(address.data(), address.size()), encode_account(account)});
  }
  snapshot.accounts = build_trie(TrieKind::account, accounts);
  return snapshot;
}

PublicState apply_delta(const PublicState& parent, const MockBlockDelta& delta) {
  validate_delta(delta);
  PublicState result = parent;
  for (const auto& address : delta.account_deletions) result.erase(address);
  for (const auto& update : delta.account_upserts) {
    auto& account = result[update.address];
    account.nonce = update.nonce;
    account.balance = update.balance;
    account.code_hash = update.code_hash;
    if (update.reset_storage) account.storage.clear();
    for (const auto& change : update.storage_changes) {
      if (zero(change.value)) account.storage.erase(change.slot);
      else account.storage[change.slot] = change.value;
    }
  }
  if (snapshot_from_state(result).accounts.root_hash() != delta.expected_state_root)
    invalid("state root differs from expected block root");
  return result;
}

CanonicalState::CanonicalState(PublicState initial)
    : state_(std::move(initial)), snapshot_(snapshot_from_state(state_)) {
  for (const auto& [address, account] : state_) {
    if (account.storage.empty()) continue;
    const auto key = keccak256(address.data(), address.size());
    const auto encoded = lookup_trie(snapshot_.accounts, key);
    if (!encoded) throw std::logic_error("canonical state: missing account");
    ++storage_references_[decode_account(*encoded).storage_root];
  }
}

CanonicalState CanonicalState::apply(const MockBlockDelta& delta,
                                     CanonicalUpdateStats* stats) const {
  validate_delta(delta);
  // Copy the public maps while retaining all immutable trie node pointers.
  // No constructor or full snapshot reconstruction runs on this staging path.
  CanonicalState result(*this);
  CanonicalUpdateStats measured;
  std::vector<TrieMutation> accounts;
  accounts.reserve(delta.account_deletions.size() + delta.account_upserts.size());
  std::set<Hash> released_roots;
  const auto previous_storage_root = [&](const Address& address, const Hash& key) {
    const auto found = state_.find(address);
    if (found == state_.end() || found->second.storage.empty())
      return empty_trie_root();
    const auto encoded = lookup_trie(snapshot_.accounts, key);
    if (!encoded) throw std::logic_error("canonical state: missing account");
    return decode_account(*encoded).storage_root;
  };
  const auto release = [&](const Hash& root) {
    if (root == empty_trie_root()) return;
    auto& references = result.storage_references_.at(root);
    if (references == 0)
      throw std::logic_error("canonical state: storage reference underflow");
    --references;
    released_roots.insert(root);
  };
  for (const auto& address : delta.account_deletions) {
    const auto key = keccak256(address.data(), address.size());
    release(previous_storage_root(address, key));
    result.state_.erase(address);
    accounts.push_back({key, std::nullopt});
  }
  for (const auto& update : delta.account_upserts) {
    const auto key = keccak256(update.address.data(), update.address.size());
    const auto old_root = previous_storage_root(update.address, key);
    Trie storage{TrieKind::storage, nullptr};
    if (!update.reset_storage && old_root != empty_trie_root())
      storage = snapshot_.storage_tries.at(old_root);
    auto& account = result.state_[update.address];
    account.nonce = update.nonce;
    account.balance = update.balance;
    account.code_hash = update.code_hash;
    if (update.reset_storage) account.storage.clear();
    std::vector<TrieMutation> mutations;
    mutations.reserve(update.storage_changes.size());
    for (const auto& change : update.storage_changes) {
      const auto slot_key = keccak256(change.slot.data(), change.slot.size());
      if (zero(change.value)) {
        account.storage.erase(change.slot);
        mutations.push_back({slot_key, std::nullopt});
      } else {
        account.storage[change.slot] = change.value;
        mutations.push_back({slot_key, encode_storage(change.value)});
      }
    }
    if (!mutations.empty() || (update.reset_storage && old_root != empty_trie_root())) {
      TrieUpdateStats storage_stats;
      storage = update_trie(storage, mutations, &storage_stats);
      measured.storage.visited_nodes += storage_stats.visited_nodes;
      measured.storage.created_nodes += storage_stats.created_nodes;
      ++measured.storage_tries_updated;
    }
    const auto new_root = storage.root_hash();
    if (new_root != old_root) {
      release(old_root);
      if (storage.root) ++result.storage_references_[new_root];
    }
    // Keep the existing node graph when distinct accounts converge on a root.
    // Old roots stay available until the complete batch is accounted for.
    if (storage.root) result.snapshot_.storage_tries.emplace(new_root, storage);
    Account encoded;
    encoded.nonce = account.nonce;
    encoded.balance = account.balance;
    encoded.code_hash = account.code_hash;
    encoded.storage_root = new_root;
    accounts.push_back({key, encode_account(encoded)});
  }
  result.snapshot_.accounts = update_trie(snapshot_.accounts, accounts, &measured.accounts);
  if (result.snapshot_.accounts.root_hash() != delta.expected_state_root)
    invalid("state root differs from expected block root");
  for (const auto& root : released_roots) {
    if (result.storage_references_.at(root) != 0) continue;
    result.storage_references_.erase(root);
    result.snapshot_.storage_tries.erase(root);
  }
  if (stats) *stats = measured;
  return result;
}

Hash delta_fingerprint(const MockBlockDelta& delta) {
  validate_delta(delta);
  // Fixed-size fields plus u64 counts make the identity encoding unambiguous.
  // This is an example protocol digest, not an Ethereum block-header hash.
  const std::string domain = "ethereum_mpt_mock_delta_v1";
  Bytes encoded(domain.begin(), domain.end());
  append(encoded, delta.block_id);
  append(encoded, delta.parent_id);
  append_u64(encoded, delta.number);
  append(encoded, delta.expected_state_root);
  std::vector<const AccountUpsert*> accounts;
  for (const auto& account : delta.account_upserts) accounts.push_back(&account);
  std::sort(accounts.begin(), accounts.end(), [](const auto* lhs, const auto* rhs) {
    return lhs->address < rhs->address;
  });
  append_u64(encoded, accounts.size());
  for (const auto* account : accounts) {
    append(encoded, account->address);
    append_u64(encoded, account->nonce);
    append(encoded, account->balance);
    append(encoded, account->code_hash);
    encoded.push_back(account->reset_storage ? 1 : 0);
    std::vector<const StorageChange*> changes;
    for (const auto& change : account->storage_changes) changes.push_back(&change);
    std::sort(changes.begin(), changes.end(), [](const auto* lhs, const auto* rhs) {
      return lhs->slot < rhs->slot;
    });
    append_u64(encoded, changes.size());
    for (const auto* change : changes) {
      append(encoded, change->slot);
      append(encoded, change->value);
    }
  }
  auto deletions = delta.account_deletions;
  std::sort(deletions.begin(), deletions.end());
  append_u64(encoded, deletions.size());
  for (const auto& address : deletions) append(encoded, address);
  return keccak256(encoded);
}

std::vector<MockBlockDelta> load_mock_blocks(std::istream& input) {
  std::vector<MockBlockDelta> blocks;
  MockBlockDelta block;
  AccountUpsert account;
  bool header = false, in_block = false, in_account = false;
  std::size_t line_number = 0;
  std::string line;
  while (std::getline(input, line)) {
    ++line_number;
    std::istringstream stream(line);
    std::vector<std::string> row;
    std::string token;
    while (stream >> token) row.push_back(token);
    if (row.empty() || row.front().front() == '#') continue;
    try {
      const auto& command = row.front();
      if (!header) {
        fields(row, 1);
        if (command != "mock_blocks_v1") invalid("missing fixture format header");
        header = true;
      } else if (command == "block") {
        fields(row, 5);
        if (in_block) invalid("nested block");
        block = {};
        block.block_id = read_hex<32>(row[1]);
        block.parent_id = read_hex<32>(row[2]);
        block.number = read_u64(row[3]);
        block.expected_state_root = read_hex<32>(row[4]);
        in_block = true;
      } else if (command == "upsert") {
        fields(row, 6);
        if (!in_block || in_account) invalid("upsert outside block or nested");
        account = {};
        account.address = read_hex<20>(row[1]);
        account.nonce = read_u64(row[2]);
        account.balance = read_hex<32>(row[3]);
        account.code_hash = read_hex<32>(row[4]);
        if (row[5] != "0" && row[5] != "1") invalid("invalid reset_storage flag");
        account.reset_storage = row[5] == "1";
        in_account = true;
      } else if (command == "storage") {
        fields(row, 3);
        if (!in_account) invalid("storage outside upsert");
        account.storage_changes.push_back({read_hex<32>(row[1]), read_hex<32>(row[2])});
      } else if (command == "endupsert") {
        fields(row, 1);
        if (!in_account) invalid("endupsert without upsert");
        block.account_upserts.push_back(std::move(account));
        in_account = false;
      } else if (command == "delete") {
        fields(row, 2);
        if (!in_block || in_account) invalid("delete outside block or inside upsert");
        block.account_deletions.push_back(read_hex<20>(row[1]));
      } else if (command == "endblock") {
        fields(row, 1);
        if (!in_block || in_account) invalid("endblock outside block or inside upsert");
        validate_delta(block);
        blocks.push_back(std::move(block));
        in_block = false;
      } else {
        invalid("unknown fixture command");
      }
    } catch (const std::invalid_argument& error) {
      throw std::invalid_argument("mock block fixture line " +
                                  std::to_string(line_number) + ": " + error.what());
    }
  }
  if (input.bad() || (!input.eof() && input.fail())) invalid("fixture read failure");
  if (!header || in_block || in_account || blocks.empty()) invalid("incomplete fixture");
  return blocks;
}

}  // namespace ethereum_mpt
