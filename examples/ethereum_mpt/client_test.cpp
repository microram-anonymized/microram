// Tests client framing: fixed frame sizes for every Q/K shape, context and
// request binding, admission limits, rejection of malformed or tampered frames,
// error-versus-absence semantics and EIP-1186 JSON conversion.

#include "client.hpp"
#include "fixture.hpp"

#include <algorithm>
#include <array>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("client test: ") + message);
}

template <class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::invalid_argument&) {
        return;
    }
    throw std::runtime_error(std::string("client test accepted: ") + message);
}

// Public fixture backend: the test deliberately knows the snapshot and page IDs.
class FixtureReader final : public PageReader {
public:
    explicit FixtureReader(const PackedSnapshot& image, bool fail = false)
        : image_(image), fail_(fail) {}

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        const auto& pages = image_.pages[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            const bool exists = !fail_ && ids[i] < pages.size();
            found[i] = static_cast<std::uint8_t>(exists);
            output[i] = exists ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }

private:
    const PackedSnapshot& image_;
    bool fail_;
};

ClientContext context_for(const PackedSnapshot& image, std::size_t requests,
                          std::size_t slots) {
    ClientContext context;
    context.request_id = word_from_u64(0x10203);
    context.block_id = word_from_u64(0x40506);
    context.state_root = image.state_root;
    context.tiers = image.profile;
    context.batch = {requests, slots};
    return context;
}

BatchResult traverse(const PackedSnapshot& image, const ClientContext& context,
                     const std::vector<ClientRequest>& requests, bool fail = false) {
    FixtureReader reader(image, fail);
    BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                             context.batch);
    return traversal.run(reader, make_path_requests(context, requests));
}

std::size_t account_offset(const ClientContext& context, std::size_t q) {
    return client_header_bytes + q * (client_account_bytes +
                                     context.batch.storage_slots * client_storage_bytes);
}

std::size_t storage_offset(const ClientContext& context, std::size_t q, std::size_t s) {
    return account_offset(context, q) + client_account_bytes + s * client_storage_bytes;
}

void compare_requests(const std::vector<ClientRequest>& actual,
                      const std::vector<ClientRequest>& expected) {
    require(actual.size() == expected.size(), "request count round trip");
    for (std::size_t q = 0; q < actual.size(); ++q)
        require(actual[q].address == expected[q].address &&
                actual[q].storage_slots == expected[q].storage_slots,
                "ordered addresses and duplicate slots round trip");
}

void compare_reference(const Snapshot& source, const std::vector<ClientRequest>& requests,
                       const std::vector<VerifiedAccount>& actual) {
    require(actual.size() == requests.size(), "verified account count");
    const auto empty_storage = build_trie(TrieKind::storage, {});
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto& request = requests[q];
        const auto& account = actual[q];
        const auto key = keccak256(request.address.data(), request.address.size());
        const auto proof = prove(source.accounts, key);
        const auto value = verify_proof(TrieKind::account, source.accounts.root_hash(), key, proof);
        require(account.address == request.address && !account.error && account.proof == proof &&
                account.account.has_value() == value.has_value(),
                "verified account and absence agree with scalar proof");
        Account fields;
        if (value) {
            fields = decode_account(*value);
            require(account.account->nonce == fields.nonce &&
                    account.account->balance == fields.balance &&
                    account.account->storage_root == fields.storage_root &&
                    account.account->code_hash == fields.code_hash,
                    "verified convenience fields are authenticated");
        }
        const auto& storage = fields.storage_root == empty_trie_root()
            ? empty_storage : source.storage_tries.at(fields.storage_root);
        require(account.storage.size() == request.storage_slots.size(),
                "verified storage count retains duplicate lanes");
        for (std::size_t s = 0; s < request.storage_slots.size(); ++s) {
            const auto& slot = request.storage_slots[s];
            const auto storage_key = keccak256(slot.data(), slot.size());
            const auto storage_proof = prove(storage, storage_key);
            const auto stored = verify_proof(TrieKind::storage, storage.root_hash(),
                                            storage_key, storage_proof);
            const auto& result = account.storage[s];
            require(result.slot == slot && !result.error && result.proof == storage_proof &&
                    result.present == stored.has_value() &&
                    result.value == (stored ? decode_storage(*stored) : Word{}),
                    "verified storage inclusion and absence agree with scalar proof");
        }
    }
}

void test_roundtrip_shapes() {
    const auto source = make_fixture();
    const auto image = pack_snapshot(source, {3, 2});
    const auto context = context_for(image, 19, 2);
    const std::array<std::uint8_t, 5> addresses{{1, 2, 90, 1, 48}};
    std::vector<ClientRequest> requests;
    for (std::size_t q = 0; q < context.batch.requests; ++q)
        requests.push_back({fixture_address(addresses[q % addresses.size()]),
                           {word_from_u64(1), word_from_u64(q % 4 == 3 ? 1 : 9)}});

    const auto sizes = client_frame_sizes(context);
    require(sizes.request_bytes == 128 + 19 * (20 + 2 * 32) &&
            sizes.response_bytes == 128 + 19 * (34980 + 2 * 34920),
            "explicit wire dimensions are independent of ABI padding");
    const auto request_frame = encode_request_frame(context, requests);
    require(request_frame.size() == sizes.request_bytes, "fixed request width");
    compare_requests(decode_request_frame(context, request_frame), requests);
    const auto paths = make_path_requests(context, requests);
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto expected = make_path_request(requests[q].address, requests[q].storage_slots);
        require(paths[q].account_key == expected.account_key &&
                paths[q].storage_keys == expected.storage_keys, "secure trie key hashing");
    }

    const auto result = traverse(image, context, requests);
    const auto frame = encode_response_frame(context, requests, result);
    require(frame.size() == sizes.response_bytes, "fixed response width");
    compare_reference(source, requests, verify_response_frame(context, requests, frame));

    auto absent_requests = requests;
    for (auto& request : absent_requests) request.address = fixture_address(90);
    require(encode_request_frame(context, absent_requests).size() == request_frame.size(),
            "request width does not disclose account membership");
    const auto absent_result = traverse(image, context, absent_requests);
    const auto absent_frame = encode_response_frame(context, absent_requests, absent_result);
    require(absent_frame.size() == frame.size(), "absence keeps every fixed proof slot");
    compare_reference(source, absent_requests,
                      verify_response_frame(context, absent_requests, absent_frame));

    for (const auto slots : {std::size_t{0}, std::size_t{2}}) {
        const Snapshot empty{build_trie(TrieKind::account, {}), {}};
        for (const auto* snapshot : {&source, &empty}) {
            const auto packed = pack_snapshot(*snapshot, {0, 0});
            const auto shape = context_for(packed, 3, slots);
            std::vector<ClientRequest> queries;
            for (const auto address : {1, 2, 90})
                queries.push_back({fixture_address(static_cast<std::uint8_t>(address)),
                                   std::vector<Word>(slots, word_from_u64(1))});
            const auto encoded_requests = encode_request_frame(shape, queries);
            compare_requests(decode_request_frame(shape, encoded_requests), queries);
            const auto answers = traverse(packed, shape, queries);
            const auto response = encode_response_frame(shape, queries, answers);
            require(response.size() == client_frame_sizes(shape).response_bytes,
                    "K=0 and empty-root responses retain their public widths");
            compare_reference(*snapshot, queries, verify_response_frame(shape, queries, response));
        }
    }
}

void test_context_binding_and_admission() {
    const auto image = pack_snapshot(make_fixture(), {3, 2});
    const auto context = context_for(image, 1, 2);
    const std::vector<ClientRequest> requests{{fixture_address(1),
                                              {word_from_u64(1), word_from_u64(9)}}};
    const auto result = traverse(image, context, requests);
    const auto request = encode_request_frame(context, requests);
    const auto response = encode_response_frame(context, requests, result);
    // Every public field is bound to the caller's expected context. In particular,
    // the state root in a response cannot replace the trusted block-header root.
    for (const auto offset : {0, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 23,
                              24, 31, 32, 63, 64, 95, 96, 127}) {
        auto bad_request = request;
        bad_request[static_cast<std::size_t>(offset)] ^= 1;
        reject([&] { decode_request_frame(context, bad_request); }, "changed request context");
        auto bad_response = response;
        bad_response[static_cast<std::size_t>(offset)] ^= 1;
        reject([&] { verify_response_frame(context, requests, bad_response); },
               "changed response context");
    }
    for (const auto size : {std::size_t{0}, std::size_t{127}, request.size() - 1,
                            request.size() + 1}) {
        auto malformed = request;
        malformed.resize(size);
        reject([&] { decode_request_frame(context, malformed); }, "request truncation or suffix");
    }
    for (const auto size : {std::size_t{0}, std::size_t{127}, response.size() - 1,
                            response.size() + 1}) {
        auto malformed = response;
        malformed.resize(size);
        reject([&] { verify_response_frame(context, requests, malformed); },
               "response truncation or suffix");
    }
    for (const auto offset : {account_offset(context, 0), storage_offset(context, 0, 0),
                              storage_offset(context, 0, 1)}) {
        auto malformed = response;
        malformed[offset] ^= 1;
        reject([&] { verify_response_frame(context, requests, malformed); },
               "response does not echo original address or ordered slot");
    }
    auto wrong_queries = requests;
    std::swap(wrong_queries[0].storage_slots[0], wrong_queries[0].storage_slots[1]);
    reject([&] { verify_response_frame(context, wrong_queries, response); },
           "request slot reordering");

    reject([&] { encode_request_frame(context, {}); }, "missing request lane");
    reject([&] { make_path_requests(context, {}); }, "missing path lane");
    wrong_queries[0].storage_slots.pop_back();
    reject([&] { encode_request_frame(context, wrong_queries); }, "missing request slot");
    reject([&] { make_path_requests(context, wrong_queries); }, "missing path slot");
    reject([&] { encode_response_frame(context, wrong_queries, result); }, "wrong response query shape");
    auto wrong_result = result;
    wrong_result.accounts.clear();
    reject([&] { encode_response_frame(context, requests, wrong_result); }, "missing result account");
    wrong_result = result;
    wrong_result.storage.pop_back();
    reject([&] { encode_response_frame(context, requests, wrong_result); }, "missing result slot");

    auto exact = context;
    exact.max_frame_bytes = response.size();
    exact.batch.max_proof_bytes = 3 * sizeof(FixedProof);
    require(client_frame_sizes(exact).response_bytes == response.size(),
            "exact public admission bounds are allowed");
    const auto maximum = std::numeric_limits<std::size_t>::max();
    std::vector<ClientContext> invalid;
    auto bad = exact;
    --bad.max_frame_bytes;
    invalid.push_back(bad);
    bad = exact;
    --bad.batch.max_proof_bytes;
    invalid.push_back(bad);
    bad = context;
    bad.batch.requests = 0;
    invalid.push_back(bad);
    for (const auto shape : {BatchProfile{maximum, 0, maximum},
                            BatchProfile{maximum / 20, 0, maximum},
                            BatchProfile{2, maximum, maximum},
                            BatchProfile{maximum / 2 + 1, 2, maximum}}) {
        bad = context;
        bad.batch = shape;
        bad.max_frame_bytes = maximum;
        invalid.push_back(bad);
    }
    for (const auto tiers : {TierProfile{66, 0}, TierProfile{0, 66}}) {
        bad = context;
        bad.tiers = tiers;
        invalid.push_back(bad);
    }
    for (const auto& invalid_context : invalid) {
        reject([&] { client_frame_sizes(invalid_context); }, "invalid public buffer arithmetic");
        reject([&] { decode_request_frame(invalid_context, {}); },
               "invalid sizes fail before frame-directed allocation");
        reject([&] { verify_response_frame(invalid_context, requests, {}); },
               "invalid sizes fail before response allocation");
    }
}

void test_authentication_and_error_semantics() {
    const auto image = pack_snapshot(make_fixture(), {3, 2});
    const auto context = context_for(image, 3, 2);
    const std::vector<ClientRequest> requests{
        {fixture_address(1), {word_from_u64(1), word_from_u64(9)}},
        {fixture_address(2), {word_from_u64(1), word_from_u64(9)}},
        {fixture_address(90), {word_from_u64(1), word_from_u64(9)}}};
    const auto result = traverse(image, context, requests);
    const auto frame = encode_response_frame(context, requests, result);
    const auto account = account_offset(context, 0);
    const auto storage = storage_offset(context, 0, 0);
    const auto absent_account = account_offset(context, 2);
    const auto absent_storage = storage_offset(context, 0, 1);
    for (const auto offset : {account + 20, account + 28, account + 36,
                             account + 44, account + 76, account + 108,
                             storage + 32, storage + 40, storage + 48,
                             absent_account + 28, absent_account + 36,
                             absent_account + 44, absent_account + 76,
                             absent_account + 108, absent_storage + 40,
                             absent_storage + 48}) {
        auto malformed = frame;
        malformed[offset] ^= 1;
        reject([&] { verify_response_frame(context, requests, malformed); },
               "noncanonical status masks or contradictory convenience fields");
    }
    // Clearing a valid all-ones mask is canonical but contradicts its proof.
    for (const auto offset : {account + 28, storage + 40}) {
        auto malformed = frame;
        std::fill_n(malformed.begin() + offset, 8, 0);
        reject([&] { verify_response_frame(context, requests, malformed); },
               "presence cannot override authenticated inclusion");
    }
    for (const auto proof_offset : {account + 140, storage + 80}) {
        for (const auto relative : {std::size_t{0}, std::size_t{1}, std::size_t{2},
                                    std::size_t{3}, std::size_t{4},
                                    sizeof(FixedProof) - 1}) {
            auto malformed = frame;
            malformed[proof_offset + relative] ^= 1;
            reject([&] { verify_response_frame(context, requests, malformed); },
                   "proof payload, header and inactive padding are authenticated or rejected");
        }
        std::size_t padding_offset = 0;
        for (std::size_t depth = 0; depth < proof_rounds; ++depth) {
            const auto offset = proof_offset + depth * proof_slot_bytes;
            const auto length = frame[offset] + (static_cast<std::size_t>(frame[offset + 1]) << 8);
            if (length > 0 && length < 532) {
                padding_offset = offset + 4 + length;
                break;
            }
        }
        require(padding_offset != 0, "fixture contains included proof padding");
        auto malformed = frame;
        malformed[padding_offset] = 1;
        reject([&] { verify_response_frame(context, requests, malformed); },
               "included proof slots have zero tails");
        malformed = frame;
        malformed[proof_offset] = 0xff;
        malformed[proof_offset + 1] = 0xff;
        reject([&] { verify_response_frame(context, requests, malformed); },
               "proof length cannot exceed its fixed slot");
        malformed = frame;
        std::copy_n(frame.begin() + proof_offset, proof_slot_bytes,
                    malformed.begin() + proof_offset + (proof_rounds - 1) * proof_slot_bytes);
        reject([&] { verify_response_frame(context, requests, malformed); },
               "canonical but superfluous proof nodes are rejected");
    }

    for (const auto destination : {storage_offset(context, 1, 0),
                                    storage_offset(context, 2, 0)}) {
        auto transplanted = frame;
        std::copy_n(frame.begin() + storage, client_storage_bytes,
                    transplanted.begin() + destination);
        reject([&] { verify_response_frame(context, requests, transplanted); },
               "storage proof cannot be transplanted to a different account root");
    }
    auto transplanted = frame;
    std::copy_n(frame.begin() + account + 20, client_account_bytes - 20,
                transplanted.begin() + account_offset(context, 1) + 20);
    reject([&] { verify_response_frame(context, requests, transplanted); },
           "account proof cannot be transplanted to a different requested address");

    const auto failures = traverse(image, context, requests, true);
    const auto failed_frame = encode_response_frame(context, requests, failures);
    require(failed_frame.size() == frame.size(), "service failure retains constant frame width");
    const auto failed = verify_response_frame(context, requests, failed_frame);
    for (const auto& item : failed) {
        require(item.error && !item.account && item.proof.empty(),
                "failed account is distinguishable from proven absence");
        require(std::all_of(item.storage.begin(), item.storage.end(), [](const auto& slot) {
                    return slot.error && !slot.present && slot.value == Word{} && slot.proof.empty();
                }), "account errors propagate to every requested storage lane");
        reject([&] { to_eip1186_json(item); }, "failed query cannot produce success JSON");
    }
    auto mixed = result;
    mixed.accounts[0] = failures.accounts[0];
    mixed.storage[0] = failures.storage[0];
    mixed.storage[1] = failures.storage[1];
    const auto mixed_verified = verify_response_frame(context, requests,
        encode_response_frame(context, requests, mixed));
    require(mixed_verified[0].error && !mixed_verified[1].error &&
            mixed_verified[1].account && mixed_verified[1].account->nonce == 2 &&
            !mixed_verified[2].error && !mixed_verified[2].account,
            "failed, included and proven-absent accounts retain independent status");
    require(!to_eip1186_json(mixed_verified[1]).empty() &&
            !to_eip1186_json(mixed_verified[2]).empty(),
            "successful neighbors can export JSON despite another account's failure");
    for (const auto offset : {account + 28, account + 36, account + 44,
                             account + 76, account + 108, account + 140 + 4,
                             storage + 40, storage + 48, storage + 80 + 4}) {
        auto malformed = failed_frame;
        malformed[offset] = 1;
        reject([&] { verify_response_frame(context, requests, malformed); },
               "error results must be canonical zero values and empty proofs");
    }
    auto missing_propagation = failed_frame;
    std::fill_n(missing_propagation.begin() + storage + 32, 8, 0);
    reject([&] { verify_response_frame(context, requests, missing_propagation); },
           "account failure cannot be represented as successful storage absence");

    auto storage_failure = result;
    storage_failure.storage[0] = {};
    storage_failure.storage[0].error = std::numeric_limits<std::uint64_t>::max();
    const auto partially_failed = verify_response_frame(context, requests,
        encode_response_frame(context, requests, storage_failure));
    require(!partially_failed[0].error && partially_failed[0].account &&
            partially_failed[0].storage[0].error && !partially_failed[0].storage[1].error,
            "storage-only errors preserve the verified account and neighboring slots");
    reject([&] { to_eip1186_json(partially_failed[0]); }, "storage error cannot produce success JSON");

    // Encoding is fixed copying, including malformed private masks. Validation
    // belongs to the disclosed client stage and must not gate service framing.
    auto raw = result;
    raw.accounts[0].error = 1;
    raw.storage[0].present = 7;
    const auto raw_frame = encode_response_frame(context, requests, raw);
    require(raw_frame.size() == frame.size() && raw_frame[account + 20] == 1 &&
            raw_frame[storage + 40] == 7, "encoder copies masks without inspecting private results");
    reject([&] { verify_response_frame(context, requests, raw_frame); }, "client rejects raw malformed masks");
}

std::string compact_json(std::string text) {
    text.erase(std::remove_if(text.begin(), text.end(), [](unsigned char character) {
        return character == ' ' || character == '\t' || character == '\r' || character == '\n';
    }), text.end());
    return text;
}

void contains(const std::string& text, const std::string& fragment, const char* message) {
    require(text.find(fragment) != std::string::npos, message);
}

void test_json() {
    const auto image = pack_snapshot(make_fixture());
    const auto context = context_for(image, 3, 2);
    const std::vector<ClientRequest> requests{
        {fixture_address(1), {word_from_u64(1), word_from_u64(9)}},
        {fixture_address(2), {word_from_u64(1), word_from_u64(1)}},
        {fixture_address(90), {word_from_u64(1), word_from_u64(9)}}};
    const auto result = traverse(image, context, requests);
    const auto verified = verify_response_frame(context, requests,
        encode_response_frame(context, requests, result));
    const auto present = compact_json(to_eip1186_json(verified[0]));
    contains(present, "\"address\":\"0x0000000000000000000000000000000000000001\"", "JSON address");
    contains(present, "\"balance\":\"0x3e8\"", "JSON balance quantity");
    contains(present, "\"nonce\":\"0x1\"", "JSON nonce quantity");
    contains(present, "\"codeHash\":\"0x" + hex(empty_code_hash()) + "\"", "JSON code hash");
    contains(present, "\"storageHash\":\"0x" + hex(verified[0].account->storage_root) + "\"",
             "JSON committed storage root");
    contains(present, "\"key\":\"0x1\"", "JSON storage key quantity");
    contains(present, "\"value\":\"0x80\"", "JSON storage inclusion quantity");
    contains(present, "\"value\":\"0x0\"", "JSON storage absence quantity");
    contains(present, "\"accountProof\":[\"0x" + hex(verified[0].proof.front()) + "\"",
             "JSON account proof contains canonical RLP");
    for (const auto& node : verified[0].storage[0].proof)
        contains(present, "\"0x" + hex(node) + "\"", "JSON storage proof contains canonical RLP");
    const auto empty_storage = compact_json(to_eip1186_json(verified[1]));
    contains(empty_storage, "\"proof\":[]", "empty storage root emits empty proof");
    const auto absent = compact_json(to_eip1186_json(verified[2]));
    contains(absent, "\"balance\":\"0x0\"", "absent account JSON zero balance");
    contains(absent, "\"nonce\":\"0x0\"", "absent account JSON zero nonce");
    contains(absent, "\"codeHash\":\"0x" + hex(empty_code_hash()) + "\"",
             "absent account normalizes internal zero code hash");
    contains(absent, "\"storageHash\":\"0x" + hex(empty_trie_root()) + "\"",
             "absent account JSON empty storage root");

    const Snapshot empty{build_trie(TrieKind::account, {}), {}};
    const auto packed = pack_snapshot(empty);
    const auto no_slots = context_for(packed, 1, 0);
    const std::vector<ClientRequest> queries{{fixture_address(90), {}}};
    const auto empty_result = traverse(packed, no_slots, queries);
    const auto empty_verified = verify_response_frame(no_slots, queries,
        encode_response_frame(no_slots, queries, empty_result));
    const auto no_proof = compact_json(to_eip1186_json(empty_verified.front()));
    contains(no_proof, "\"accountProof\":[]", "empty state root emits no account nodes");
    contains(no_proof, "\"storageProof\":[]", "K=0 emits an empty storage array");
}

void test_full_width_scalars() {
    Address address{};
    Word slot{}, value{};
    for (std::size_t i = 0; i < address.size(); ++i)
        address[i] = static_cast<std::uint8_t>(i * 7 + 3);
    for (std::size_t i = 0; i < slot.size(); ++i) {
        slot[i] = static_cast<std::uint8_t>(i * 5 + 1);
        value[i] = static_cast<std::uint8_t>(255 - i * 3);
    }
    const auto storage = build_trie(TrieKind::storage,
        {{keccak256(slot.data(), slot.size()), encode_storage(value)}});
    Account account;
    account.nonce = 0xfedcba9876543210ULL;
    account.balance = value;
    account.balance[0] = 1;
    account.storage_root = storage.root_hash();
    account.code_hash = keccak256(Bytes{1, 2, 3});
    const Snapshot source{build_trie(TrieKind::account,
        {{keccak256(address.data(), address.size()), encode_account(account)}}),
        {{storage.root_hash(), storage}}};
    const auto image = pack_snapshot(source, {65, 65});
    const auto context = context_for(image, 1, 1);
    const std::vector<ClientRequest> requests{{address, {slot}}};
    compare_requests(decode_request_frame(context, encode_request_frame(context, requests)), requests);
    const auto result = traverse(image, context, requests);
    const auto frame = encode_response_frame(context, requests, result);
    const std::array<std::uint8_t, 8> nonce_le{{0x10, 0x32, 0x54, 0x76, 0x98, 0xba, 0xdc, 0xfe}};
    require(std::equal(nonce_le.begin(), nonce_le.end(), frame.begin() + client_header_bytes + 36),
            "full-width nonce is explicitly little endian");
    const auto verified = verify_response_frame(context, requests, frame);
    compare_reference(source, requests, verified);
    const auto json = compact_json(to_eip1186_json(verified.front()));
    contains(json, "\"nonce\":\"0xfedcba9876543210\"", "JSON preserves unsigned 64-bit nonce");
    contains(json, "\"balance\":\"0x" + hex(account.balance).substr(1) + "\"",
             "JSON removes only leading zero nibbles of a 256-bit balance");
    contains(json, "\"key\":\"0x" + hex(slot).substr(1) + "\"",
             "JSON preserves a 256-bit storage key");
    contains(json, "\"value\":\"0x" + hex(value) + "\"",
             "JSON preserves a 256-bit storage value");
}

}  // namespace

int main() {
    try {
        test_roundtrip_shapes();
        test_context_binding_and_admission();
        test_authentication_and_error_semantics();
        test_json();
        test_full_width_scalars();
        std::cout << "ethereum MPT client tests passed\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
