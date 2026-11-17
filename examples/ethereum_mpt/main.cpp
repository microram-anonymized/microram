// ethereum_mpt_example: packs the fixture snapshot into real ORAM maps and runs
// one framed Q=19, K=2 proof batch, verifying every result on the client side.

#include "client.hpp"
#include "fixture.hpp"
#include "page_map.hpp"

#include <iomanip>
#include <iostream>

using namespace ethereum_mpt;

int main() {
  try {
    const auto snapshot = make_fixture();
    const auto packed = pack_snapshot(snapshot);
    validate_packed_snapshot(packed);
    std::cout << "MPT fixed-round batch correctness demo (no encrypted transport)\n"
              << "state_root=0x" << hex(packed.state_root) << '\n';

    // Verify the storage root through the authenticated account value first.
    const auto address = fixture_address(1);
    const auto account_key = keccak256(address.data(), address.size());
    const auto account_proof = prove(snapshot.accounts, account_key);
    const auto account_value = verify_proof(TrieKind::account, packed.state_root,
                                           account_key, account_proof);
    if (!account_value) throw std::runtime_error("fixture account missing");
    const auto account = decode_account(*account_value);
    const auto& storage = snapshot.storage_tries.at(account.storage_root);
    for (uint64_t slot_id : {1u, 99u}) {
      const auto slot = word_from_u64(slot_id);
      const auto key = keccak256(slot.data(), slot.size());
      const auto proof = prove(storage, key);
      const auto value = verify_proof(TrieKind::storage, account.storage_root, key, proof);
      if ((slot_id == 1 && (!value || decode_storage(*value) != word_from_u64(128))) ||
          (slot_id == 99 && value))
        throw std::runtime_error("storage reference proof mismatch");
      std::cout << "storage_slot=" << slot_id << " present=" << bool(value)
                << " proof_nodes=" << proof.size() << '\n';
    }
    const auto absent = fixture_address(99);
    const auto absent_key = keccak256(absent.data(), absent.size());
    if (verify_proof(TrieKind::account, packed.state_root, absent_key,
                     prove(snapshot.accounts, absent_key)))
      throw std::runtime_error("absent account unexpectedly present");

    TieredPageMaps maps(packed, 128);
    for (size_t tier = 0; tier < packed.pages.size(); ++tier) {
      const auto& pages = packed.pages[tier];
      if (pages.empty()) continue;
      const auto& map = *maps.map(static_cast<Tier>(tier));
      // All loaded pages, plus duplicate real/dummy IDs and one absent ID.
      std::vector<uint64_t> ids;
      for (size_t id = 0; id < pages.size(); ++id) ids.push_back(id);
      ids.insert(ids.end(), {0, 0, pages.size() - 1, pages.size() - 1, pages.size()});
      std::vector<Page> outputs(ids.size());
      std::vector<uint8_t> found(ids.size());
      const auto before = map.access_count();
      maps.read_pages_batch(static_cast<Tier>(tier), ids.size(), ids.data(),
                            outputs.data(), found.data());
      if (map.access_count() - before != ids.size())
        throw std::runtime_error("batch lane accounting mismatch");
      for (size_t i = 0; i < ids.size(); ++i) {
        const bool present = ids[i] < pages.size();
        if (found[i] != present || outputs[i] != (present ? pages[ids[i]] : Page{}))
          throw std::runtime_error("ORAM page round-trip mismatch");
      }
      const auto& s = packed.stats[tier];
      std::cout << tier_name(static_cast<Tier>(tier))
                << " S=" << s.canonical_bytes << " N=" << s.records
                << " E=" << s.ordinary_links << " A=" << s.account_leaves
                << " R=" << s.record_bytes << " P=" << s.real_pages
                << " runs=" << s.packing_runs << " utilization=" << std::fixed
                << std::setprecision(3) << s.utilization()
                << " page_value_bytes=" << s.page_value_bytes()
                << " tree_capacity=" << map.capacity()
                << " oram_arena_bytes=" << map.arena_bytes() << '\n';
    }
    // These plaintext fixture requests/results are disclosed after processing.
    // 19 account / 38 storage lanes also exercise batches beyond 16 lanes.
    const BatchProfile profile{19, 2};
    std::vector<ClientRequest> client_requests;
    for (size_t i = 0; i < profile.requests; ++i) {
      const auto id = static_cast<uint8_t>(i % 4 == 3 ? 99 : i % 4 + 1);
      client_requests.push_back({fixture_address(id),
                                 {word_from_u64(1), word_from_u64(99)}});
    }
    // A zero block ID denotes this synthetic snapshot, not an Ethereum block.
    // Expected roots/requests are known locally, never learned from a response.
    const ClientContext context{word_from_u64(1), {}, packed.state_root,
                                packed.profile, profile};
    const auto request_frame = encode_request_frame(context, client_requests);
    const auto received_requests = decode_request_frame(context, request_frame);
    const auto requests = make_path_requests(context, received_requests);
    const auto calls_before = maps.calls();
    const auto accesses_before = maps.accesses();
    const auto results = BatchTraversal(packed.state_root, packed.account_root,
                                        packed.profile, profile).run(maps, requests);
    const auto response_frame = encode_response_frame(context, received_requests, results);
    const auto verified = verify_response_frame(context, client_requests, response_frame);
    for (size_t q = 0; q < requests.size(); ++q) {
      const auto& answer = results.accounts[q];
      const auto proof = decode_proof(answer.proof);
      if (answer.error || proof != prove(snapshot.accounts, requests[q].account_key))
        throw std::runtime_error("batched account proof mismatch");
      const auto value = verify_proof(TrieKind::account, packed.state_root,
                                     requests[q].account_key, proof);
      if (bool(answer.present) != bool(value))
        throw std::runtime_error("batched account presence mismatch");
      if (verified[q].error || bool(verified[q].account) != bool(value))
        throw std::runtime_error("client account verification mismatch");
      const auto root = value ? decode_account(*value).storage_root : empty_trie_root();
      if (value) {
        const auto account_fields = decode_account(*value);
        if (answer.nonce != account_fields.nonce || answer.balance != account_fields.balance ||
            answer.storage_root != root || answer.code_hash != account_fields.code_hash)
          throw std::runtime_error("batched account fields mismatch");
      }
      for (size_t s = 0; s < profile.storage_slots; ++s) {
        const auto& storage_answer = results.storage[q * profile.storage_slots + s];
        if (storage_answer.error) throw std::runtime_error("batched storage error");
        const auto storage_proof = decode_proof(storage_answer.proof);
        const auto stored = verify_proof(TrieKind::storage, root,
                                         requests[q].storage_keys[s], storage_proof);
        if (bool(storage_answer.present) != bool(stored) ||
            storage_answer.storage_value != (stored ? decode_storage(*stored) : Word{}))
          throw std::runtime_error("batched storage value mismatch");
        if (verified[q].storage[s].error ||
            verified[q].storage[s].present != bool(stored) ||
            verified[q].storage[s].value != storage_answer.storage_value)
          throw std::runtime_error("client storage verification mismatch");
        const auto expected = root == empty_trie_root() ? Proof{} :
            prove(snapshot.storage_tries.at(root), requests[q].storage_keys[s]);
        if (storage_proof != expected) throw std::runtime_error("batched storage proof mismatch");
      }
    }
    uint64_t calls = 0, accesses = 0;
    for (size_t t = 0; t < 3; ++t) {
      calls += maps.calls()[t] - calls_before[t];
      accesses += maps.accesses()[t] - accesses_before[t];
    }
    if (calls != 130 || accesses != 65 * profile.requests * (1 + profile.storage_slots))
      throw std::runtime_error("fixed traversal schedule mismatch");
    std::cout << "batch Q=" << profile.requests << " K=" << profile.storage_slots
              << " calls=" << calls << " page_accesses=" << accesses
              << " node_hash_permutations=" << 4 * accesses
              << " proof_slot_bytes=" << sizeof(FixedProof) * profile.requests *
                                         (1 + profile.storage_slots)
              << " request_frame_bytes=" << request_frame.size()
              << " response_frame_bytes=" << response_frame.size() << '\n';
    // Exercise the public account-only profile against the same real maps.
    const ClientContext singleton_context{word_from_u64(2), {}, packed.state_root,
                                          packed.profile, BatchProfile{1, 0}};
    const std::vector<ClientRequest> singleton_requests{{address, {}}};
    const auto singleton_request_frame = encode_request_frame(singleton_context,
                                                             singleton_requests);
    const auto singleton_received = decode_request_frame(singleton_context,
                                                         singleton_request_frame);
    const auto singleton_calls_before = maps.calls();
    const auto singleton = BatchTraversal(packed.state_root, packed.account_root,
        packed.profile, singleton_context.batch).run(maps,
            make_path_requests(singleton_context, singleton_received));
    const auto singleton_response_frame = encode_response_frame(singleton_context,
                                                                singleton_received, singleton);
    const auto singleton_verified = verify_response_frame(singleton_context,
        singleton_requests, singleton_response_frame);
    uint64_t singleton_calls = 0;
    for (size_t t = 0; t < 3; ++t)
      singleton_calls += maps.calls()[t] - singleton_calls_before[t];
    if (singleton_calls != 65 || !singleton.storage.empty() ||
        singleton.accounts[0].error || !singleton.accounts[0].present ||
        singleton_verified[0].error || !singleton_verified[0].account ||
        decode_proof(singleton.accounts[0].proof) != account_proof)
      throw std::runtime_error("account-only ORAM batch mismatch");
    std::cout << "batch Q=1 K=0 calls=" << singleton_calls << " page_accesses=65"
              << " request_frame_bytes=" << singleton_request_frame.size()
              << " response_frame_bytes=" << singleton_response_frame.size() << '\n'
              << "Account/storage membership, absence and fixed-size client frames verified.\n";
  } catch (const std::exception& error) {
    std::cerr << "ethereum_mpt_example: " << error.what() << '\n';
    return 1;
  }
}
