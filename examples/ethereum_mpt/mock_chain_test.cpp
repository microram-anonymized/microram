// Tests mock block deltas against the independent py-trie fixture roots and
// proofs, fingerprint/validation rules and the strict fixture parser.

#include "fixture.hpp"
#include "mock_chain.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <limits>
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

void verify_state_proofs(const PublicState& state, const Snapshot& snapshot) {
  validate_trie(snapshot.accounts);
  for (std::uint8_t id = 1; id <= 4; ++id) {
    const auto address = fixture_address(id);
    const auto key = keccak256(address.data(), address.size());
    const auto value = verify_proof(TrieKind::account, snapshot.accounts.root_hash(),
                                    key, prove(snapshot.accounts, key));
    const auto expected = state.find(address);
    check(value.has_value() == (expected != state.end()),
          "mock account proof membership disagrees with public state");
    if (!value) continue;
    const auto account = decode_account(*value);
    check(account.nonce == expected->second.nonce &&
              account.balance == expected->second.balance &&
              account.code_hash == expected->second.code_hash,
          "mock account proof fields disagree with public state");
    if (expected->second.storage.empty()) {
      check(account.storage_root == empty_trie_root(), "mock empty storage root");
      continue;
    }
    const auto& storage = snapshot.storage_tries.at(account.storage_root);
    validate_trie(storage);
    for (const unsigned slot_id : {1, 2, 3, 4, 7, 9, 99}) {
      const auto slot = word_from_u64(slot_id);
      const auto path = keccak256(slot.data(), slot.size());
      const auto found = verify_proof(TrieKind::storage, account.storage_root,
                                      path, prove(storage, path));
      const auto wanted = expected->second.storage.find(slot);
      check(found.has_value() == (wanted != expected->second.storage.end()),
            "mock storage proof membership disagrees with public state");
      if (found)
        check(decode_storage(*found) == wanted->second,
              "mock storage proof value disagrees with public state");
    }
  }
}

std::vector<MockBlockDelta> golden_blocks() {
  std::ifstream input(ETHEREUM_MPT_BLOCK_FIXTURES);
  check(bool(input), "cannot read independent mock block fixtures");
  auto blocks = load_mock_blocks(input);
  check(blocks.size() == 8, "unexpected independent mock block fixture count");
  std::map<Hash, PublicState> states;
  std::map<Hash, Snapshot> snapshots;
  for (const auto& block : blocks) {
    const PublicState parent = block.number == 0 ? PublicState{} : states.at(block.parent_id);
    const auto before = snapshot_from_state(parent).accounts.root_hash();
    auto state = apply_delta(parent, block);
    check(snapshot_from_state(parent).accounts.root_hash() == before,
          "mock delta mutated its parent state");
    auto snapshot = snapshot_from_state(state);
    check(snapshot.accounts.root_hash() == block.expected_state_root,
          "mock root differs from independent py-trie root");
    verify_state_proofs(state, snapshot);
    for (const auto profile : {TierProfile{}, TierProfile{0, 0}, TierProfile{3, 2}}) {
      const auto packed = pack_snapshot(snapshot, profile);
      validate_packed_snapshot(packed);
      check(packed.state_root == block.expected_state_root,
            "mock packing changed independently checked root");
    }
    states.emplace(block.block_id, std::move(state));
    snapshots.emplace(block.block_id, std::move(snapshot));
  }
  const auto& genesis = states.at(blocks[0].block_id);
  check(genesis.size() == 3 && snapshots.at(blocks[0].block_id).storage_tries.size() == 1,
        "genesis should deduplicate identical account storage roots");
  const auto& replaced = states.at(blocks[1].block_id);
  const auto& changed = replaced.at(fixture_address(1));
  check(changed.nonce == 2 && changed.balance == word_from_u64(9999) &&
            changed.code_hash != genesis.at(fixture_address(1)).code_hash &&
            changed.storage.at(word_from_u64(1)) == word_from_u64(512) &&
            changed.storage.count(word_from_u64(2)) == 0 &&
            changed.storage.at(word_from_u64(3)) == word_from_u64(1),
        "account replacement/storage patch semantics changed");
  Word maximum;
  maximum.fill(0xff);
  check(replaced.at(fixture_address(3)).nonce == std::numeric_limits<std::uint64_t>::max() &&
            replaced.at(fixture_address(3)).balance == maximum,
        "maximum nonce/balance fields were truncated");
  check(states.at(blocks[2].block_id).size() == 1 &&
            snapshots.at(blocks[2].block_id).accounts.root->kind == NodeKind::leaf,
        "account deletion did not collapse the trie to a singleton");
  const auto& recreated = states.at(blocks[3].block_id).at(fixture_address(1));
  check(recreated.storage.size() == 1 &&
            recreated.storage.at(word_from_u64(9)) == word_from_u64(7) &&
            recreated.code_hash == empty_code_hash(),
        "recreated account inherited deleted storage or code");
  const auto& reset = states.at(blocks[4].block_id).at(fixture_address(2));
  check(reset.storage.size() == 1 && reset.storage.count(word_from_u64(7)) == 1,
        "reset_storage did not clear previously live slots");
  check(blocks[5].parent_id == blocks[1].block_id &&
            blocks[6].parent_id == blocks[5].block_id &&
            states.at(blocks[6].block_id).count(fixture_address(2)) == 0 &&
            snapshots.at(blocks[6].block_id).storage_tries.size() == 1,
        "fork did not rebuild from its own parent or deduplicate storage");
  check(states.at(blocks[7].block_id).empty() &&
            blocks[7].expected_state_root == empty_trie_root(),
        "deleting all accounts did not restore the empty root");
  // Revisit every immutable ancestor after both branches have been applied.
  for (const auto& block : blocks) {
    const auto& state = states.at(block.block_id);
    const auto& snapshot = snapshots.at(block.block_id);
    check(snapshot_from_state(state).accounts.root_hash() == block.expected_state_root,
          "retained public state changed after a descendant update");
    verify_state_proofs(state, snapshot);
  }
  std::cout << "Independent py-trie mock blocks: " << blocks.size()
            << " state roots and both fork branches matched\n";
  return blocks;
}

void fingerprints_and_validation(const std::vector<MockBlockDelta>& blocks) {
  auto reordered = blocks.front();
  std::reverse(reordered.account_upserts.begin(), reordered.account_upserts.end());
  for (auto& account : reordered.account_upserts)
    std::reverse(account.storage_changes.begin(), account.storage_changes.end());
  const auto fingerprint = delta_fingerprint(blocks.front());
  check(delta_fingerprint(reordered) == fingerprint,
        "delta fingerprint depends on public mutation order");
  auto deletions = blocks[2];
  std::reverse(deletions.account_deletions.begin(), deletions.account_deletions.end());
  check(delta_fingerprint(deletions) == delta_fingerprint(blocks[2]),
        "delta fingerprint depends on deletion order");
  for (unsigned field = 0; field != 12; ++field) {
    auto changed = blocks.front();
    auto& account = changed.account_upserts.front();
    switch (field) {
      case 0: changed.block_id[0] ^= 1; break;
      case 1: changed.parent_id[0] ^= 1; break;
      case 2: ++changed.number; break;
      case 3: changed.expected_state_root[0] ^= 1; break;
      case 4: account.address[0] ^= 1; break;
      case 5: ++account.nonce; break;
      case 6: account.balance[0] ^= 1; break;
      case 7: account.code_hash[0] ^= 1; break;
      case 8: account.reset_storage = !account.reset_storage; break;
      case 9: account.storage_changes.front().slot[0] ^= 1; break;
      case 10: account.storage_changes.front().value[0] ^= 1; break;
      case 11: changed.account_deletions.push_back(fixture_address(99)); break;
    }
    check(delta_fingerprint(changed) != fingerprint, "delta fingerprint omits a field");
  }
  for (unsigned failure = 0; failure != 4; ++failure) {
    auto invalid = blocks.front();
    switch (failure) {
      case 0: invalid.account_upserts.push_back(invalid.account_upserts.front()); break;
      case 1:
        invalid.account_deletions = {fixture_address(99), fixture_address(99)};
        break;
      case 2:
        invalid.account_deletions.push_back(invalid.account_upserts.front().address);
        break;
      case 3:
        auto& changes = invalid.account_upserts.front().storage_changes;
        changes.push_back(changes.front());
        break;
    }
    rejects([&] { apply_delta({}, invalid); }, "ambiguous delta accepted");
    rejects([&] { delta_fingerprint(invalid); }, "ambiguous delta fingerprint accepted");
  }
  auto wrong_root = blocks.front();
  wrong_root.expected_state_root[0] ^= 1;
  rejects([&] { apply_delta({}, wrong_root); }, "incorrect expected root accepted");
}

void empty_and_creation_semantics() {
  check(snapshot_from_state({}).accounts.root_hash() == empty_trie_root(),
        "empty public state has wrong root");
  MockBlockDelta no_op;
  no_op.expected_state_root = empty_trie_root();
  no_op.account_deletions = {fixture_address(77)};
  check(apply_delta({}, no_op).empty(), "deleting an absent account changed state");
  PublicState wanted;
  auto& account = wanted[fixture_address(1)];
  account.nonce = 7;
  account.balance = word_from_u64(9);
  account.storage[word_from_u64(0)] = word_from_u64(5);
  MockBlockDelta create;
  create.expected_state_root = snapshot_from_state(wanted).accounts.root_hash();
  AccountUpsert update;
  update.address = fixture_address(1);
  update.nonce = account.nonce;
  update.balance = account.balance;
  update.storage_changes = {{word_from_u64(0), word_from_u64(5)},
                            {word_from_u64(99), {}}};
  create.account_upserts.push_back(update);
  const auto state = apply_delta({}, create);
  check(state.at(update.address).storage == account.storage,
        "new account without reset or deletion of an absent slot failed");
  auto invalid_state = wanted;
  invalid_state.at(update.address).storage[word_from_u64(99)] = {};
  rejects([&] { snapshot_from_state(invalid_state); }, "zero public storage accepted");
  // A no-op mutation is still part of duplicate-delivery content identity.
  auto extra_no_op = create;
  extra_no_op.account_upserts.front().storage_changes.push_back({word_from_u64(100), {}});
  check(delta_fingerprint(create) != delta_fingerprint(extra_no_op),
        "explicit no-op mutation omitted from delta identity");
}

void strict_fixture_parser() {
  const auto hash = std::string(64, '0');
  const auto address = std::string(40, '0');
  const auto block = "block " + hash + " " + hash + " 0 " + hex(empty_trie_root()) + "\n";
  const auto upsert = "upsert " + address + " 0 " + hash + " " + hash + " 0\n";
  const auto slot = "storage " + hash + " " + hash + "\n";
  const auto header = std::string("mock_blocks_v1\n");
  const auto valid = header + block + "endblock\n";
  {
    std::istringstream input("  # comment\n\n" + valid);
    const auto blocks = load_mock_blocks(input);
    check(blocks.size() == 1 && apply_delta({}, blocks.front()).empty(),
          "empty block fixture did not parse/apply");
  }
  const std::vector<std::string> bad = {
      "", header, block + "endblock\n", valid + "extra\n", valid + "endblock\n",
      header + block, header + block + "endblock extra\n",
      header + block + block, header + block + "endupsert\n",
      header + block + slot + "endblock\n",
      header + upsert + "endupsert\n", header + block + upsert + "endblock\n",
      header + block + upsert + upsert, header + block + "delete " + address + " extra\n",
      header + block + upsert + "delete " + address + "\n",
      header + block + upsert + slot + slot + "endupsert\nendblock\n",
      header + block + upsert + "endupsert\n" + upsert + "endupsert\nendblock\n",
      header + block + "delete " + address + "\ndelete " + address + "\nendblock\n",
      header + block + upsert + "endupsert\ndelete " + address + "\nendblock\n",
      header + "block " + hash + " " + hash + " 18446744073709551616 " + hash + "\nendblock\n",
      header + "block " + hash + " " + hash + " -1 " + hash + "\nendblock\n",
      header + "block " + hash + " " + hash + " +1 " + hash + "\nendblock\n",
      header + "block " + hash + " " + hash + " 01 " + hash + "\nendblock\n",
      header + "block 0x" + hash + " " + hash + " 0 " + hash + "\nendblock\n",
      header + "block " + std::string(64, 'A') + " " + hash + " 0 " + hash + "\nendblock\n",
      header + block + "upsert " + address + " 0 " + hash + " " + hash + " 2\n",
      header + block + "upsert " + address + " 18446744073709551616 " + hash + " " + hash + " 0\n",
      header + block + "delete 00\nendblock\n",
  };
  for (const auto& source : bad)
    rejects([&] { std::istringstream input(source); load_mock_blocks(input); },
            "malformed mock fixture accepted");
  std::istringstream broken(valid);
  broken.setstate(std::ios::badbit);
  rejects([&] { load_mock_blocks(broken); }, "fixture I/O error accepted");
}

}  // namespace

void run_mock_chain_tests() {
  const auto blocks = golden_blocks();
  fingerprints_and_validation(blocks);
  empty_and_creation_semantics();
  strict_fixture_parser();
}
