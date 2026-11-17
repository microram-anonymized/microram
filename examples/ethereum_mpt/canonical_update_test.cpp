// Tests CanonicalState: path-copying canonical updates must match full rebuilds
// and the independent py-trie block fixtures, share unchanged nodes, and leave
// the parent state untouched when a delta is rejected.

#include "fixture.hpp"
#include "mock_chain.hpp"

#include <algorithm>
#include <fstream>
#include <random>
#include <sstream>
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

Hash address_key(const Address& address) {
  return keccak256(address.data(), address.size());
}

Hash slot_key(const Word& slot) {
  return keccak256(slot.data(), slot.size());
}

Hash storage_root(const CanonicalState& state, std::uint8_t id) {
  const auto value = lookup_trie(state.snapshot().accounts, address_key(fixture_address(id)));
  check(bool(value), "canonical account missing from trie");
  return decode_account(*value).storage_root;
}

void compare_states(const PublicState& actual, const PublicState& expected) {
  check(actual.size() == expected.size(), "canonical public account count differs");
  for (const auto& [address, wanted] : expected) {
    const auto& found = actual.at(address);
    check(found.nonce == wanted.nonce && found.balance == wanted.balance &&
              found.code_hash == wanted.code_hash && found.storage == wanted.storage,
          "canonical public account differs from baseline");
  }
}

void compare_snapshot(const CanonicalState& actual, const PublicState& expected) {
  compare_states(actual.state(), expected);
  const auto baseline = snapshot_from_state(expected);
  const auto& snapshot = actual.snapshot();
  check(snapshot.accounts.root_hash() == baseline.accounts.root_hash(),
        "incremental account root differs from full rebuild");
  check(snapshot.storage_tries.size() == baseline.storage_tries.size(),
        "incremental storage root set differs from full rebuild");
  validate_trie(snapshot.accounts);
  for (const auto& [root, trie] : snapshot.storage_tries) {
    check(baseline.storage_tries.count(root) == 1,
          "incremental snapshot retains an unused storage root");
    validate_trie(trie);
  }
  for (const auto& [address, account] : expected) {
    const auto key = address_key(address);
    check(prove(snapshot.accounts, key) == prove(baseline.accounts, key),
          "incremental account proof differs from full rebuild");
    const auto root = decode_account(*lookup_trie(snapshot.accounts, key)).storage_root;
    if (account.storage.empty()) {
      check(root == empty_trie_root(), "empty incremental storage has nonempty root");
      continue;
    }
    const auto& storage = snapshot.storage_tries.at(root);
    const auto& rebuilt = baseline.storage_tries.at(root);
    for (const auto& [slot, value] : account.storage) {
      const auto path = slot_key(slot);
      check(lookup_trie(storage, path) == std::optional<Bytes>(encode_storage(value)) &&
                prove(storage, path) == prove(rebuilt, path),
            "incremental storage value or proof differs from full rebuild");
    }
    const auto absent = slot_key(word_from_u64(99999));
    check(prove(storage, absent) == prove(rebuilt, absent),
          "incremental storage absence proof differs from full rebuild");
  }
  const auto absent = address_key(fixture_address(255));
  check(prove(snapshot.accounts, absent) == prove(baseline.accounts, absent),
        "incremental account absence proof differs from full rebuild");
}

AccountUpsert full_upsert(std::uint8_t id, const PublicAccountState& account) {
  AccountUpsert update;
  update.address = fixture_address(id);
  update.nonce = account.nonce;
  update.balance = account.balance;
  update.code_hash = account.code_hash;
  update.reset_storage = true;
  for (const auto& [slot, value] : account.storage)
    update.storage_changes.push_back({slot, value});
  return update;
}

CanonicalState apply_expected(const CanonicalState& parent, MockBlockDelta delta,
                              const PublicState& expected,
                              CanonicalUpdateStats* stats = nullptr) {
  delta.expected_state_root = snapshot_from_state(expected).accounts.root_hash();
  compare_states(apply_delta(parent.state(), delta), expected);
  auto result = parent.apply(delta, stats);
  compare_snapshot(result, expected);
  return result;
}

void independent_blocks() {
  std::ifstream input(ETHEREUM_MPT_BLOCK_FIXTURES);
  check(bool(input), "cannot read independent block roots for canonical updates");
  const auto blocks = load_mock_blocks(input);
  std::map<Hash, CanonicalState> retained;
  for (const auto& block : blocks) {
    const auto parent = block.number == 0 ? CanonicalState{} : retained.at(block.parent_id);
    const auto parent_root = parent.snapshot().accounts.root;
    const auto expected = apply_delta(parent.state(), block);
    auto result = parent.apply(block);
    check(result.snapshot().accounts.root_hash() == block.expected_state_root,
          "incremental block root differs from py-trie fixture");
    compare_snapshot(result, expected);
    check(parent.snapshot().accounts.root == parent_root,
          "canonical apply changed immutable parent pointer");
    retained.emplace(block.block_id, std::move(result));
  }
  for (const auto& block : blocks) {
    const auto& state = retained.at(block.block_id);
    check(state.snapshot().accounts.root_hash() == block.expected_state_root,
          "descendant canonical update changed a retained root");
    compare_snapshot(state, state.state());
  }
}

void independent_proofs() {
  // These public values are those used by fixtures/generate.py. Build them one
  // account at a time, then compare against independent py-trie proof bytes.
  CanonicalState state;
  Trie single;
  PublicState expected;
  Word maximum;
  maximum.fill(0xff);
  const std::vector<Word> values = {word_from_u64(1), word_from_u64(127),
                                  word_from_u64(128), word_from_u64(255),
                                  word_from_u64(256), maximum};
  const std::string bytecode = "fixture bytecode";
  for (std::uint8_t id = 1; id <= 4; ++id) {
    auto& account = expected[fixture_address(id)];
    account.nonce = id;
    account.balance = id == 4 ? maximum : word_from_u64(id * 1000);
    if (id == 3) account.code_hash = keccak256(Bytes(bytecode.begin(), bytecode.end()));
    if (id % 2)
      for (std::size_t slot = 0; slot < values.size(); ++slot)
        account.storage[word_from_u64(slot)] = values[slot];
    MockBlockDelta delta;
    delta.account_upserts.push_back(full_upsert(id, account));
    state = apply_expected(state, delta, expected);
    if (id == 1) single = state.snapshot().accounts;
  }
  std::ifstream input(ETHEREUM_MPT_FIXTURES);
  check(bool(input), "cannot read independent canonical update proof fixtures");
  std::string line, name;
  const Trie* target = nullptr;
  Hash key{};
  Proof proof;
  std::size_t queries = 0;
  while (std::getline(input, line)) {
    if (line.empty() || line.front() == '#') continue;
    std::istringstream row(line);
    std::string command, a, b;
    row >> command >> a >> b;
    if (command == "case") {
      name = a;
      target = name == "secure_accounts" ? &state.snapshot().accounts :
               name == "single_account" ? &single :
               name == "secure_storage" ? &state.snapshot().storage_tries.begin()->second :
               nullptr;
    } else if (target && command == "root") {
      check(hex(target->root_hash()) == a, "canonical update root differs from oracle");
    } else if (target && command == "query") {
      const auto bytes = from_hex(a);
      check(bytes.size() == key.size(), "invalid oracle proof key width");
      std::copy(bytes.begin(), bytes.end(), key.begin());
      proof.clear();
    } else if (target && command == "node") {
      proof.push_back(from_hex(a));
    } else if (target && command == "endquery") {
      check(prove(*target, key) == proof,
            "incremental canonical proof differs byte-for-byte from py-trie");
      ++queries;
    }
  }
  check(queries == 14 && !input.bad(), "incomplete independent canonical proof checks");
}

void shared_roots_and_noops() {
  PublicState initial;
  initial[fixture_address(1)].storage[word_from_u64(1)] = word_from_u64(11);
  initial[fixture_address(2)] = initial.at(fixture_address(1));
  initial[fixture_address(3)].storage[word_from_u64(2)] = word_from_u64(22);
  const CanonicalState parent(initial);
  const auto r = storage_root(parent, 1), s = storage_root(parent, 3);
  const auto r_node = parent.snapshot().storage_tries.at(r).root;
  const auto s_node = parent.snapshot().storage_tries.at(s).root;
  check(parent.snapshot().storage_tries.size() == 2,
        "constructor did not deduplicate shared storage roots");

  PublicState expected = initial;
  expected.erase(fixture_address(1));
  MockBlockDelta delta;
  delta.account_deletions = {fixture_address(1)};
  auto reduced = apply_expected(parent, delta, expected);
  check(reduced.snapshot().storage_tries.at(r).root == r_node,
        "deleting one shared root owner discarded the remaining owner's nodes");

  expected.at(fixture_address(2)).storage = expected.at(fixture_address(3)).storage;
  delta = {};
  delta.account_upserts.push_back(full_upsert(2, expected.at(fixture_address(2))));
  auto converged = apply_expected(reduced, delta, expected);
  check(converged.snapshot().storage_tries.size() == 1 &&
            converged.snapshot().storage_tries.at(s).root == s_node,
        "converged storage failed to reuse target nodes or release old root");

  // Delete the last owner of R before another account adopts R in one batch.
  expected = reduced.state();
  expected.erase(fixture_address(2));
  expected.at(fixture_address(3)).storage = initial.at(fixture_address(1)).storage;
  delta = {};
  delta.account_deletions = {fixture_address(2)};
  delta.account_upserts.push_back(full_upsert(3, expected.at(fixture_address(3))));
  auto resurrected = apply_expected(reduced, delta, expected);
  check(resurrected.snapshot().storage_tries.size() == 1 &&
            resurrected.snapshot().storage_tries.at(r).root == r_node,
        "storage root released too early for same-batch convergence");

  expected = reduced.state();
  std::swap(expected.at(fixture_address(2)).storage, expected.at(fixture_address(3)).storage);
  delta = {};
  delta.account_upserts = {full_upsert(2, expected.at(fixture_address(2))),
                           full_upsert(3, expected.at(fixture_address(3)))};
  auto swapped = apply_expected(reduced, delta, expected);
  check(swapped.snapshot().storage_tries.at(r).root == r_node &&
            swapped.snapshot().storage_tries.at(s).root == s_node,
        "same-batch storage root swap failed to preserve existing nodes");

  CanonicalUpdateStats stats;
  delta = {};
  auto no_op = full_upsert(1, initial.at(fixture_address(1)));
  no_op.reset_storage = false;
  no_op.storage_changes.push_back({word_from_u64(99), {}});
  delta.account_upserts.push_back(no_op);
  delta.account_deletions.push_back(fixture_address(100));
  auto unchanged = apply_expected(parent, delta, initial, &stats);
  check(unchanged.snapshot().accounts.root == parent.snapshot().accounts.root &&
            unchanged.snapshot().storage_tries.at(r).root == r_node &&
            stats.accounts.created_nodes == 0 && stats.storage.created_nodes == 0 &&
            stats.storage_tries_updated == 1,
        "explicit no-op delta rebuilt canonical nodes or miscounted storage work");

  delta = {};
  delta.account_upserts.push_back(full_upsert(1, initial.at(fixture_address(1))));
  unchanged = apply_expected(parent, delta, initial);
  check(unchanged.snapshot().accounts.root == parent.snapshot().accounts.root &&
            unchanged.snapshot().storage_tries.at(r).root == r_node,
        "reset to identical storage discarded previously canonical nodes");

  expected = initial;
  expected.at(fixture_address(1)).storage.clear();
  expected.erase(fixture_address(2));
  expected.erase(fixture_address(3));
  delta = {};
  delta.account_upserts.push_back(full_upsert(1, expected.at(fixture_address(1))));
  delta.account_deletions = {fixture_address(2), fixture_address(3)};
  check(apply_expected(parent, delta, expected).snapshot().storage_tries.empty(),
        "clearing/deleting final storage owners retained unused roots");
}

void rejection_is_immutable() {
  PublicState initial;
  initial[fixture_address(1)].storage[word_from_u64(1)] = word_from_u64(11);
  const CanonicalState parent(initial);
  const auto root = parent.snapshot().accounts.root;
  const auto storage = parent.snapshot().storage_tries.begin()->second.root;
  for (unsigned failure = 0; failure < 5; ++failure) {
    MockBlockDelta delta;
    auto changed = initial.at(fixture_address(1));
    ++changed.nonce;
    delta.account_upserts.push_back(full_upsert(1, changed));
    delta.expected_state_root = parent.snapshot().accounts.root_hash();
    if (failure == 1) delta.account_upserts.push_back(delta.account_upserts.front());
    if (failure == 2) delta.account_deletions = {fixture_address(1)};
    if (failure == 3) delta.account_deletions = {fixture_address(99), fixture_address(99)};
    if (failure == 4)
      delta.account_upserts.front().storage_changes.push_back(
          delta.account_upserts.front().storage_changes.front());
    CanonicalUpdateStats stats{{101, 102}, {103, 104}, 105};
    rejects([&] { parent.apply(delta, &stats); }, "invalid canonical delta accepted");
    check(stats.accounts.visited_nodes == 101 && stats.accounts.created_nodes == 102 &&
              stats.storage.visited_nodes == 103 && stats.storage.created_nodes == 104 &&
              stats.storage_tries_updated == 105,
          "rejected canonical delta changed caller counters");
    check(parent.snapshot().accounts.root == root &&
              parent.snapshot().storage_tries.begin()->second.root == storage,
          "rejected canonical delta changed parent nodes");
    compare_snapshot(parent, initial);
  }
  initial.at(fixture_address(1)).storage[word_from_u64(99)] = {};
  rejects([&] { CanonicalState invalid(initial); }, "zero initial storage accepted");
}

void randomized_updates() {
  std::mt19937_64 random(0xc4110ca1);
  std::vector<CanonicalState> retained(1);
  for (unsigned round = 0; round < 100; ++round) {
    const auto& parent = retained[round % 5 == 0 ? random() % retained.size() :
                                                retained.size() - 1];
    PublicState expected = parent.state();
    MockBlockDelta delta;
    std::vector<std::uint8_t> ids;
    for (std::uint8_t id = 1; id <= 20; ++id) ids.push_back(id);
    std::shuffle(ids.begin(), ids.end(), random);
    const auto count = 1 + random() % 5;
    for (std::size_t i = 0; i < count; ++i) {
      const auto address = fixture_address(ids[i]);
      if (random() % 4 == 0) {
        delta.account_deletions.push_back(address);
        expected.erase(address);
        continue;
      }
      auto& account = expected[address];
      account.nonce = random() % 10000;
      account.balance = word_from_u64(random());
      AccountUpsert update;
      update.address = address;
      update.nonce = account.nonce;
      update.balance = account.balance;
      update.reset_storage = random() % 4 == 0;
      if (update.reset_storage) account.storage.clear();
      for (std::uint64_t slot = 0; slot < 8; ++slot) {
        if (random() % 3 != 0) continue;
        const auto value = random() % 3 == 0 ? 0 : random() % 1000 + 1;
        update.storage_changes.push_back({word_from_u64(slot), word_from_u64(value)});
        if (value) account.storage[word_from_u64(slot)] = word_from_u64(value);
        else account.storage.erase(word_from_u64(slot));
      }
      delta.account_upserts.push_back(std::move(update));
    }
    retained.push_back(apply_expected(parent, delta, expected));
  }
  for (const auto& ancestor : retained) compare_snapshot(ancestor, ancestor.state());
}
}  // namespace

void test_canonical_updates() {
  independent_blocks();
  independent_proofs();
  shared_roots_and_noops();
  rejection_is_immutable();
  randomized_updates();
}
