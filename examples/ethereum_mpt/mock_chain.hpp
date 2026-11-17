// Public chain-update model: final-state block deltas, the canonical state they
// produce, block identity fingerprints and the mock fixture loader.

#pragma once

#include "packing.hpp"

#include <cstdint>
#include <istream>
#include <map>
#include <vector>

namespace ethereum_mpt {

// Public final-state changes, not transactions or an Ethereum execution engine.
struct StorageChange {
  Word slot{};
  Word value{};  // Zero removes the slot.
};

struct AccountUpsert {
  Address address{};
  std::uint64_t nonce = 0;
  Word balance{};
  Hash code_hash = empty_code_hash();
  bool reset_storage = false;
  std::vector<StorageChange> storage_changes;
};

struct MockBlockDelta {
  Hash block_id{};
  Hash parent_id{};
  std::uint64_t number = 0;
  Hash expected_state_root{};
  std::vector<AccountUpsert> account_upserts;
  std::vector<Address> account_deletions;
};

struct PublicAccountState {
  std::uint64_t nonce = 0;
  Word balance{};
  Hash code_hash = empty_code_hash();
  std::map<Word, Word> storage;  // Only nonzero values are canonical.
};

using PublicState = std::map<Address, PublicAccountState>;

// Rebuild the complete canonical snapshot, deduplicating equal storage roots.
// Directly supplied public states containing zero storage values are rejected.
Snapshot snapshot_from_state(const PublicState& state);

// Complete account fields replace their old values. Storage is patched unless
// reset_storage is true; a previously absent address always starts empty.
// Duplicate addresses/slots, overlapping upserts/deletes, and root mismatches
// throw std::invalid_argument without modifying the input. Parent identity,
// block numbering and duplicate delivery belong to the public version manager.
PublicState apply_delta(const PublicState& parent, const MockBlockDelta& delta);

struct CanonicalUpdateStats {
  // update_trie work only; excludes public map copies and account-root lookups.
  TrieUpdateStats accounts;
  TrieUpdateStats storage;
  // Upserts which process storage changes or reset previously nonempty storage.
  // Explicit no-op storage changes are included.
  std::size_t storage_tries_updated = 0;
};

// Immutable public state with persistent canonical trie nodes. Construction
// builds the initial snapshot once; apply hashes/encodes only changed paths.
// PublicState and the std::map metadata are still copied in full on each apply.
class CanonicalState {
 public:
  explicit CanonicalState(PublicState initial = {});

  const PublicState& state() const { return state_; }
  const Snapshot& snapshot() const { return snapshot_; }

  // The same delta validation and expected-root contract as apply_delta.
  // On failure the parent and optional output counters remain unchanged.
  CanonicalState apply(const MockBlockDelta& delta,
                       CanonicalUpdateStats* stats = nullptr) const;

 private:
  PublicState state_;
  Snapshot snapshot_;
  // Number of live accounts referencing each nonempty storage trie.
  std::map<Hash, std::size_t> storage_references_;
};

// Canonical, order-independent identity of all delta fields. Invalid duplicate
// mutations are rejected. Explicit no-op changes remain part of the identity.
Hash delta_fingerprint(const MockBlockDelta& delta);

// Strict mock_blocks_v1 fixture format (full-line comments and blanks allowed):
//   mock_blocks_v1
//   block <id32> <parent32> <decimal_number> <expected_root32>
//   upsert <address20> <decimal_nonce> <balance32> <code_hash32> <0_or_1>
//   storage <slot32> <value32>
//   endupsert
//   delete <address20>
//   endblock
// Hex fields are fixed-width lowercase without 0x; unknown/trailing fields and
// unclosed sections are errors. Blocks may follow any branch; roots are checked
// when the caller supplies the corresponding parent state to apply_delta.
std::vector<MockBlockDelta> load_mock_blocks(std::istream& input);

}  // namespace ethereum_mpt
