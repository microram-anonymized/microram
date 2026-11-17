// Tests BatchTraversal: exact per-round map/lane schedules across tier cutoffs,
// admission, duplicates, maximum depth and node width, corrupt metadata and
// missing pages, all compared with the reference proofs.

#include "fixture.hpp"
#include "traversal.hpp"

#include <algorithm>
#include <array>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("traversal test: ") + message);
}

template <class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::invalid_argument&) {
        return;
    }
    throw std::runtime_error(std::string("traversal test accepted: ") + message);
}

Hash key_with_nibble(std::size_t depth, std::uint8_t nibble) {
    Hash key{};
    key[depth / 2] = static_cast<std::uint8_t>(nibble << (depth % 2 == 0 ? 4 : 0));
    return key;
}

Hash address_key(std::uint8_t id) {
    const auto address = fixture_address(id);
    return keccak256(address.data(), address.size());
}

Hash slot_key(std::uint64_t id) {
    const auto slot = word_from_u64(id);
    return keccak256(slot.data(), slot.size());
}

struct Call {
    Tier tier;
    std::vector<std::uint64_t> ids;
};

// This is intentionally a public, instrumented fixture backend. Production
// traversal uses the ORAM adapter; reference checks may inspect these page IDs.
class FixtureReader final : public PageReader {
public:
    explicit FixtureReader(const PackedSnapshot& image) : image_(image) {}

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        calls.push_back({tier, {ids, ids + count}});
        const auto& pages = image_.pages[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            const bool exists = ids[i] < pages.size() &&
                !(drop_page && tier == dropped_tier && ids[i] == dropped_id);
            found[i] = static_cast<std::uint8_t>(exists);
            output[i] = exists ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }

    std::size_t max_lanes() const override { return lanes; }

    std::vector<Call> calls;
    std::size_t lanes = std::numeric_limits<std::size_t>::max();
    bool drop_page = false;
    Tier dropped_tier = Tier::bulk;
    std::uint64_t dropped_id = 0;

private:
    const PackedSnapshot& image_;
};

void check_schedule(const FixtureReader& reader, TierProfile tiers,
                    std::size_t requests, std::size_t slots) {
    require(reader.calls.size() == (slots == 0 ? 65 : 130), "fixed phase call count");
    for (std::size_t depth = 0; depth < 65; ++depth) {
        require(reader.calls[depth].tier == tier_for(TrieKind::account, depth, tiers),
                "account tier sequence depends only on public depth");
        require(reader.calls[depth].ids.size() == requests, "fixed account lane count");
        if (slots != 0) {
            require(reader.calls[65 + depth].tier == tier_for(TrieKind::storage, depth, tiers),
                    "storage tier sequence depends only on public depth");
            require(reader.calls[65 + depth].ids.size() == requests * slots,
                    "fixed storage lane count");
        }
    }
}

Proof checked_proof(const FixedProof& fixed) {
    for (const auto& slot : fixed.slots) {
        const std::size_t size = slot[0] + (static_cast<std::size_t>(slot[1]) << 8);
        require(size <= 532 && slot[2] <= 1 && slot[3] == 0, "fixed proof slot header");
        require((size != 0) == (slot[2] != 0), "fixed proof inactive length");
        require(std::all_of(slot.begin() + 4 + size, slot.end(),
                            [](std::uint8_t value) { return value == 0; }),
                "fixed proof payload tail must be zero");
    }
    return decode_proof(fixed);
}

void check_reference(const Snapshot& source, const std::vector<PathRequest>& requests,
                     std::size_t slots, const BatchResult& result) {
    require(result.accounts.size() == requests.size() &&
            result.storage.size() == requests.size() * slots, "fixed result dimensions");
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto& account = result.accounts[q];
        const auto expected = prove(source.accounts, requests[q].account_key);
        const auto actual = checked_proof(account.proof);
        require(account.error == 0 && actual == expected, "account proof equals scalar proof");
        const auto value = verify_proof(TrieKind::account, source.accounts.root_hash(),
                                        requests[q].account_key, actual);
        require((account.present != 0) == value.has_value(), "account presence equals reference");
        Account decoded;
        if (value) {
            decoded = decode_account(*value);
            require(account.nonce == decoded.nonce && account.balance == decoded.balance &&
                    account.storage_root == decoded.storage_root &&
                    account.code_hash == decoded.code_hash, "account field extraction");
        }
        const Trie empty_storage = build_trie(TrieKind::storage, {});
        const Trie& storage = decoded.storage_root == empty_trie_root()
            ? empty_storage : source.storage_tries.at(decoded.storage_root);
        for (std::size_t s = 0; s < slots; ++s) {
            const auto& item = result.storage[q * slots + s];
            const auto proof = checked_proof(item.proof);
            require(item.error == 0 && proof == prove(storage, requests[q].storage_keys[s]),
                    "storage proof equals scalar proof");
            const auto scalar = verify_proof(TrieKind::storage, storage.root_hash(),
                                             requests[q].storage_keys[s], proof);
            require((item.present != 0) == scalar.has_value(), "storage presence equals reference");
            require(item.storage_value == (scalar ? decode_storage(*scalar) : Word{}),
                    "storage field extraction and absent zero");
        }
    }
}

BatchResult run_checked(const Snapshot& source, const PackedSnapshot& image,
                        const std::vector<PathRequest>& requests, std::size_t slots,
                        FixtureReader& reader) {
    BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                             BatchProfile{requests.size(), slots});
    auto result = traversal.run(reader, requests);
    check_schedule(reader, image.profile, requests.size(), slots);
    check_reference(source, requests, slots, result);
    return result;
}

void test_empty_and_fixed_batch_shapes() {
    Snapshot source{build_trie(TrieKind::account, {}), {}};
    for (const auto tiers : {TierProfile{0, 0}, TierProfile{3, 2}, TierProfile{65, 65}}) {
        const auto image = pack_snapshot(source, tiers);
        for (const auto slots : {std::size_t{0}, std::size_t{3}}) {
            std::vector<PathRequest> requests(2);
            for (auto& request : requests) request.storage_keys.resize(slots);
            FixtureReader reader(image);
            run_checked(source, image, requests, slots, reader);
            for (const auto& call : reader.calls)
                require(std::all_of(call.ids.begin(), call.ids.end(),
                                    [](std::uint64_t id) { return id == 0; }),
                        "empty trie retains every dummy lane");
        }
    }
}

void test_public_admission_and_request_hashes() {
    const Hash root = empty_trie_root();
    const auto maximum = std::numeric_limits<std::size_t>::max();
    for (const auto profile : {BatchProfile{0, 0}, BatchProfile{1, maximum},
                              BatchProfile{maximum, 1},
                              BatchProfile{1, 0, sizeof(FixedProof) - 1}})
        reject([&] { BatchTraversal traversal(root, {}, {}, profile); },
               "zero, overflowing, or over-budget public batch profile");
    for (const auto tiers : {TierProfile{66, 0}, TierProfile{0, 66}})
        reject([&] { BatchTraversal traversal(root, {}, tiers, {}); },
               "public tier cutoff beyond depth 64");

    const auto image = pack_snapshot({build_trie(TrieKind::account, {}), {}});
    FixtureReader reader(image);
    BatchTraversal traversal(root, {}, image.profile, BatchProfile{1, 2});
    reject([&] { traversal.run(reader, {}); }, "request count mismatches public profile");
    reject([&] { traversal.run(reader, {{Hash{}, {Hash{}}}}); },
           "storage slot count mismatches public profile");
    // A reader needs max(Q, Q*K) lanes: Q*K here, Q without storage.
    reader.lanes = 1;
    reject([&] { traversal.run(reader, {{Hash{}, {Hash{}, Hash{}}}}); },
           "storage phase wider than the reader's lanes");
    BatchTraversal accounts_only(root, {}, image.profile, BatchProfile{2, 0});
    reject([&] { accounts_only.run(reader, {{Hash{}, {}}, {Hash{}, {}}}); },
           "account phase wider than the reader's lanes");
    require(reader.calls.empty(), "public admission fails before touching maps");
    reader.lanes = 2;
    traversal.run(reader, {{Hash{}, {Hash{}, Hash{}}}});
    accounts_only.run(reader, {{Hash{}, {}}, {Hash{}, {}}});
    require(reader.calls.size() == 130 + 65, "a reader of exactly max(Q, Q*K) lanes runs");

    Address address{};
    Word slot{};
    for (std::size_t i = 0; i < address.size(); ++i)
        address[i] = static_cast<std::uint8_t>(17 * i + 1);
    for (std::size_t i = 0; i < slot.size(); ++i)
        slot[i] = static_cast<std::uint8_t>(13 * i + 2);
    const auto request = make_path_request(address, {slot, Word{}, slot});
    require(request.account_key == keccak256(address.data(), address.size()) &&
            request.storage_keys == std::vector<Hash>{
                keccak256(slot.data(), slot.size()), keccak256(Word{}.data(), 32),
                keccak256(slot.data(), slot.size())},
            "private path hashing agrees with reference and retains duplicate slots");
}

void test_fixture_batches_and_duplicates() {
    const auto source = make_fixture();
    const auto image = pack_snapshot(source, TierProfile{3, 2});
    std::vector<PathRequest> requests;
    // Nineteen account lanes and thirty-eight storage lanes exceed a SIMD
    // chunk, include an uneven tail, and retain repeated pages and keys.
    const std::array<std::uint8_t, 5> addresses{{1, 2, 3, 90, 1}};
    for (std::size_t i = 0; i < 19; ++i)
        requests.push_back({address_key(addresses[i % addresses.size()]),
                            {slot_key(1 + i % 8), slot_key(9)}});
    FixtureReader reader(image);
    run_checked(source, image, requests, 2, reader);
    require(reader.calls[0].ids.size() == 19 &&
            std::all_of(reader.calls[0].ids.begin(), reader.calls[0].ids.end(),
                        [&](std::uint64_t id) { return id == image.account_root.page_id; }),
            "duplicate root requests remain independent lanes");

    FixtureReader singleton_reader(image);
    run_checked(source, image, {{address_key(1), {}}}, 0, singleton_reader);
    FixtureReader dummy_storage_reader(image);
    run_checked(source, image,
                {{address_key(2), {slot_key(1), slot_key(2)}},
                 {address_key(90), {slot_key(1), slot_key(2)}}}, 2, dummy_storage_reader);
    for (std::size_t depth = 0; depth < 65; ++depth)
        for (const auto id : dummy_storage_reader.calls[65 + depth].ids)
            require(id == 0, "absent accounts and empty storage run an all-dummy storage phase");
}

void test_maximum_depth() {
    Word maximum{};
    maximum.fill(0xff);
    std::vector<Entry> storage_entries{{{}, encode_storage(maximum)}};
    for (std::size_t depth = 0; depth < 64; ++depth)
        storage_entries.push_back({key_with_nibble(depth, 1), encode_storage(maximum)});
    const auto storage = build_trie(TrieKind::storage, storage_entries);
    Account account;
    account.nonce = std::numeric_limits<std::uint64_t>::max();
    account.balance = maximum;
    account.code_hash.fill(0xa5);
    account.storage_root = storage.root_hash();
    std::vector<Entry> accounts{{{}, encode_account(account)}};
    for (std::size_t depth = 0; depth < 64; ++depth)
        accounts.push_back({key_with_nibble(depth, 1), encode_account(account)});
    const Snapshot source{build_trie(TrieKind::account, accounts),
                          {{storage.root_hash(), storage}}};
    const auto image = pack_snapshot(source, TierProfile{3, 2});
    FixtureReader reader(image);
    const auto result = run_checked(source, image,
        {{Hash{}, {Hash{}, key_with_nibble(63, 2)}},
         {key_with_nibble(0, 2), {Hash{}, Hash{}}}}, 2, reader);
    require(decode_proof(result.accounts[0].proof).size() == 65 &&
            decode_proof(result.storage[0].proof).size() == 65,
            "account and storage proofs include a depth-64 empty-suffix leaf");
    for (std::size_t depth = 0; depth < 65; ++depth) {
        require(reader.calls[depth].ids[0] != 0 && reader.calls[65 + depth].ids[0] != 0,
                "deep path remains live through the last public round");
        if (depth != 0)
            require(reader.calls[depth].ids[1] == 0,
                    "early missing branch child retains dummy account lanes");
    }
}

void test_maximum_node_width() {
    Account account;
    account.nonce = std::numeric_limits<std::uint64_t>::max();
    account.balance.fill(0xff);
    std::vector<Entry> entries;
    for (std::uint8_t nibble = 0; nibble < 16; ++nibble)
        entries.push_back({key_with_nibble(0, nibble), encode_account(account)});
    const Snapshot wide{build_trie(TrieKind::account, entries), {}};
    require(wide.accounts.root->rlp.size() == 532, "maximum branch width fixture");
    const auto image = pack_snapshot(wide);
    FixtureReader reader(image);
    const auto result = run_checked(wide, image,
        {{Hash{}, {}}, {key_with_nibble(0, 15), {}}, {key_with_nibble(63, 1), {}}},
        0, reader);
    require(decode_proof(result.accounts[0].proof).front().size() == 532,
            "full-width canonical node survives the fixed proof slot");

    const Snapshot singleton{build_trie(TrieKind::account,
        {{Hash{}, encode_account(account)}}), {}};
    require(singleton.accounts.root->rlp.size() == 148, "maximum account leaf fixture");
    const auto one_image = pack_snapshot(singleton);
    FixtureReader one_reader(one_image);
    run_checked(singleton, one_image, {{Hash{}, {}}}, 0, one_reader);
}

void test_extension_waits_and_inline_nodes() {
    for (const std::size_t split : {std::size_t{2}, std::size_t{5}}) {
        const Snapshot source{build_trie(TrieKind::account,
            {{Hash{}, encode_account(Account{})},
             {key_with_nibble(split, 1), encode_account(Account{})}}), {}};
        const auto image = pack_snapshot(source, TierProfile{3, 0});
        FixtureReader reader(image);
        const auto result = run_checked(source, image,
            {{Hash{}, {}}, {key_with_nibble(0, 1), {}},
             {key_with_nibble(63, 1), {}}}, 0, reader);
        for (std::size_t depth = 1; depth < split; ++depth)
            require(reader.calls[depth].ids[0] == 0 &&
                    result.accounts[0].proof.slots[depth][2] == 0,
                    "extension waits across skipped public depths");
        require(reader.calls[split].ids[0] != 0,
                "extension retains its pending locator across dummy rounds");
    }

    Word below_threshold{}, at_threshold{};
    std::fill(below_threshold.end() - 27, below_threshold.end(), 1);
    std::fill(at_threshold.end() - 28, at_threshold.end(), 1);
    const auto threshold = build_trie(TrieKind::storage,
        {{Hash{}, encode_storage(below_threshold)},
         {key_with_nibble(63, 1), encode_storage(at_threshold)}});
    const auto nested = build_trie(TrieKind::storage,
        {{Hash{}, encode_storage(word_from_u64(1))},
         {key_with_nibble(63, 1), encode_storage(word_from_u64(1))},
         {key_with_nibble(59, 1), encode_storage(word_from_u64(1))}});
    Account first, second;
    first.storage_root = threshold.root_hash();
    second.storage_root = nested.root_hash();
    const Snapshot source{build_trie(TrieKind::account,
        {{Hash{}, encode_account(first)},
         {key_with_nibble(0, 1), encode_account(second)}}),
        {{threshold.root_hash(), threshold}, {nested.root_hash(), nested}}};
    const auto image = pack_snapshot(source, TierProfile{3, 2});
    FixtureReader reader(image);
    const auto result = run_checked(source, image,
        {{Hash{}, {Hash{}, key_with_nibble(63, 1)}},
         {key_with_nibble(0, 1), {Hash{}, key_with_nibble(63, 2)}},
         {Hash{}, {key_with_nibble(62, 1), key_with_nibble(63, 2)}}}, 2, reader);
    require(decode_proof(result.storage[0].proof).size() == 2 &&
            decode_proof(result.storage[1].proof).size() == 3,
            "31-byte embedded leaf versus 32-byte hash-referenced leaf");
    require(reader.calls[129].ids[0] == 0 && reader.calls[129].ids[1] != 0,
            "embedded leaves consume scheduled dummy reads");
    require(nested.root->child->children[0]->rlp.size() < 32 &&
            nested.root->child->children[0]->child->rlp.size() < 32,
            "fixture contains nested embedded extension and branch");
    for (std::size_t depth = 60; depth < 65; ++depth)
        require(reader.calls[65 + depth].ids[2] == 0,
                "pending nested inline nodes persist across skipped dummy depths");
}

void test_failures_keep_the_schedule() {
    const Snapshot source{build_trie(TrieKind::account,
        {{Hash{}, encode_account(Account{})}}), {}};
    const auto original = pack_snapshot(source);
    const std::vector<PathRequest> requests{{Hash{}, {Hash{}, Hash{}}}};
    const auto check_failure = [&](const PackedSnapshot& image, FixtureReader& reader) {
        BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                                 BatchProfile{1, 2});
        const auto result = traversal.run(reader, requests);
        check_schedule(reader, image.profile, 1, 2);
        require(result.accounts[0].error != 0 && result.accounts[0].present == 0,
                "malformed or missing account page is an error, never presence");
        require(checked_proof(result.accounts[0].proof).empty() &&
                result.accounts[0].nonce == 0 && result.accounts[0].balance == Word{},
                "failed account clears partial proofs and values");
        for (const auto& storage : result.storage)
            require(storage.error != 0 && storage.present == 0,
                    "account error propagates through padded storage lanes");
    };
    const std::array<std::pair<std::size_t, std::uint8_t>, 9> corruptions{{
        {0, 0xff}, {1, 0xff}, {2, 0xff}, {3, 0xff}, {4, 17},
        {5, 65}, {6, 1}, {7, 1}, {8, 0x80}}};
    for (const auto& mutation : corruptions) {
        auto image = original;
        image.pages[0][image.account_root.page_id][image.account_root.offset + mutation.first] =
            mutation.second;
        FixtureReader reader(image);
        check_failure(image, reader);
    }
    for (const auto locator : {
             Locator{original.account_root.page_id, static_cast<std::uint16_t>(page_bytes - 1), 732},
             Locator{original.account_root.page_id, std::numeric_limits<std::uint16_t>::max(), 8},
             Locator{std::numeric_limits<std::uint64_t>::max(), 0, 8},
             Locator{0, 1, 8}, Locator{}}) {
        auto image = original;
        image.account_root = locator;
        FixtureReader reader(image);
        check_failure(image, reader);
    }
    auto image = original;
    image.state_root.front() ^= 1;
    FixtureReader hash_reader(image);
    check_failure(image, hash_reader);

    FixtureReader missing_reader(original);
    missing_reader.drop_page = true;
    missing_reader.dropped_tier = Tier::account_top;
    missing_reader.dropped_id = original.account_root.page_id;
    check_failure(original, missing_reader);

    FixtureReader missing_dummy(original);
    missing_dummy.drop_page = true;
    missing_dummy.dropped_tier = Tier::bulk;
    missing_dummy.dropped_id = 0;
    check_failure(original, missing_dummy);
}

void test_storage_failures_preserve_account_proof() {
    const auto storage = build_trie(TrieKind::storage,
        {{Hash{}, encode_storage(word_from_u64(128))}});
    Account account;
    account.storage_root = storage.root_hash();
    const Snapshot source{build_trie(TrieKind::account,
        {{Hash{}, encode_account(account)}}), {{storage.root_hash(), storage}}};
    const auto original = pack_snapshot(source, TierProfile{3, 2});
    const auto record = read_packed_record(original, Tier::account_top, original.account_root);
    const auto storage_root = record.links.at(0);
    const auto check_storage_failure = [&](const PackedSnapshot& image, FixtureReader& reader) {
        BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                                 BatchProfile{1, 2});
        const auto result = traversal.run(reader,
            {{Hash{}, {Hash{}, key_with_nibble(63, 1)}}});
        check_schedule(reader, image.profile, 1, 2);
        require(result.accounts[0].error == 0 && result.accounts[0].present != 0 &&
                checked_proof(result.accounts[0].proof) == prove(source.accounts, Hash{}),
                "storage failure preserves authenticated account proof");
        for (const auto& item : result.storage)
            require(item.error != 0 && item.present == 0 && item.storage_value == Word{} &&
                    checked_proof(item.proof).empty(),
                    "storage corruption is error for both matching and absent paths");
    };
    auto image = original;
    image.pages[1][storage_root.page_id][storage_root.offset + 5] = 1;
    FixtureReader metadata_reader(image);
    check_storage_failure(image, metadata_reader);
    FixtureReader missing_reader(original);
    missing_reader.drop_page = true;
    missing_reader.dropped_tier = Tier::storage_top;
    missing_reader.dropped_id = storage_root.page_id;
    check_storage_failure(original, missing_reader);
}

void test_mixed_failed_present_absent_lanes() {
    Account first, second;
    first.nonce = 7;
    second.nonce = 8;
    const Snapshot source{build_trie(TrieKind::account,
        {{Hash{}, encode_account(first)},
         {key_with_nibble(0, 1), encode_account(second)}}), {}};
    auto image = pack_snapshot(source, TierProfile{1, 0});
    const auto root = read_packed_record(image, Tier::account_top, image.account_root);
    require(root.links.size() == 2, "mixed-failure fixture has two external children");
    const auto first_leaf = root.links[0];
    image.pages[2][first_leaf.page_id][first_leaf.offset + 6] = 1;
    const std::vector<PathRequest> requests{
        {Hash{}, {Hash{}}}, {key_with_nibble(0, 1), {Hash{}}},
        {key_with_nibble(0, 2), {Hash{}}}};
    FixtureReader reader(image);
    BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                             BatchProfile{3, 1});
    const auto result = traversal.run(reader, requests);
    check_schedule(reader, image.profile, 3, 1);
    require(result.accounts[0].error != 0 && result.accounts[0].present == 0 &&
            result.storage[0].error != 0, "failed lane retains and propagates error");
    require(result.accounts[1].error == 0 && result.accounts[1].present != 0 &&
            result.accounts[1].nonce == second.nonce && result.storage[1].error == 0,
            "successful neighbor sharing a page remains valid");
    require(result.accounts[2].error == 0 && result.accounts[2].present == 0 &&
            result.storage[2].error == 0, "absence remains distinct from failure");
    require(checked_proof(result.accounts[1].proof) ==
            prove(source.accounts, requests[1].account_key), "successful neighbor proof");
}

void test_client_proof_padding() {
    FixedProof empty;
    require(decode_proof(empty).empty(), "zero-filled proof decodes to empty");
    for (const auto index : {std::size_t{0}, std::size_t{2}, std::size_t{3},
                             std::size_t{4}, std::size_t{535}}) {
        FixedProof malformed;
        malformed.slots[17][index] = 1;
        reject([&] { decode_proof(malformed); }, "malformed inactive proof slot");
    }
    FixedProof oversized;
    oversized.slots[0][0] = 0xff;
    oversized.slots[0][1] = 0xff;
    oversized.slots[0][2] = 1;
    reject([&] { decode_proof(oversized); }, "oversized fixed proof slot");
}

}  // namespace

void run_traversal_tests() {
    test_empty_and_fixed_batch_shapes();
    test_public_admission_and_request_hashes();
    test_fixture_batches_and_duplicates();
    test_maximum_depth();
    test_maximum_node_width();
    test_extension_waits_and_inline_nodes();
    test_failures_keep_the_schedule();
    test_storage_failures_preserve_account_proof();
    test_mixed_failed_present_absent_lanes();
    test_client_proof_padding();
}
