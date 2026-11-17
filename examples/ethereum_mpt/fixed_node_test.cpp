// Differential tests of the fixed-work node parser against the reference trie
// decoder, over a node corpus, malformed inputs and packed records.

#include "fixed_node.hpp"
#include "fixture.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>
#include <string>

namespace ethereum_mpt {
namespace {

void expect(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("fixed node test: ") + message);
}

fixed::NodeBytes padded(const Bytes& encoded) {
    fixed::NodeBytes result{};
    std::copy(encoded.begin(), encoded.end(), result.begin());
    return result;
}

void compare_child(const fixed::Child& actual, const ChildReference& expected,
                   std::size_t link_index) {
    if (expected.hash) {
        expect(actual.type == 2 && actual.hash == *expected.hash, "hashed child");
        expect(actual.link_index == link_index, "hashed-child locator ordinal");
    } else if (!expected.embedded.empty()) {
        expect(actual.type == 1 && actual.length == expected.embedded.size(), "inline child");
        expect(std::equal(expected.embedded.begin(), expected.embedded.end(),
                          actual.embedded.begin()), "inline child bytes");
    } else {
        expect(actual.type == 0, "empty child");
    }
}

void compare_node(const Bytes& encoded, TrieKind role, std::size_t depth) {
    const auto expected = decode_node(encoded, role, depth);
    const auto actual = fixed::parse_node(padded(encoded), encoded.size(), role, depth);
    expect(actual.valid == ~fixed::Mask{0}, "valid canonical node rejected");
    expect(actual.kind == static_cast<std::uint64_t>(expected.kind), "node kind");
    expect(actual.path_length == expected.path.size(), "compact path length");
    expect(std::equal(expected.path.begin(), expected.path.end(), actual.path.begin()),
           "compact path nibbles");
    std::size_t hashes = 0;
    if (expected.kind == NodeKind::branch) {
        for (std::size_t i = 0; i < expected.children.size(); ++i) {
            compare_child(actual.children[i], expected.children[i], hashes);
            hashes += expected.children[i].hash.has_value();
        }
    } else if (expected.kind == NodeKind::extension) {
        compare_child(actual.child, expected.child, 0);
        hashes = expected.child.hash.has_value();
    } else if (role == TrieKind::account) {
        const auto value = decode_account(expected.value);
        expect(actual.nonce == value.nonce && actual.balance == value.balance &&
               actual.storage_root == value.storage_root && actual.code_hash == value.code_hash,
               "account scalar/hash fields");
    } else {
        expect(actual.storage_value == decode_storage(expected.value), "storage scalar value");
    }
    expect(actual.hashed_children == hashes, "hashed child count");
}

void compare_tree(const NodePtr& node, TrieKind role, std::size_t depth) {
    if (!node) return;
    compare_node(node->rlp, role, depth);
    if (node->kind == NodeKind::branch) {
        for (const auto& child : node->children) compare_tree(child, role, depth + 1);
    } else if (node->kind == NodeKind::extension) {
        compare_tree(node->child, role, depth + node->path.size());
    }
}

void reject_node(const Bytes& bytes, TrieKind role, std::size_t depth) {
    expect(fixed::parse_node(padded(bytes), bytes.size(), role, depth).valid == 0,
           "malformed node accepted");
}

Bytes leaf(const Nibbles& path, const Bytes& value) {
    return rlp_list({rlp_bytes(compact_encode(path, true)), rlp_bytes(value)});
}

void corpus() {
    const auto fixture = make_fixture();
    compare_tree(fixture.accounts.root, TrieKind::account, 0);
    for (const auto& [hash, trie] : fixture.storage_tries)
        compare_tree(trie.root, TrieKind::storage, 0);

    Account account;
    account.nonce = std::numeric_limits<std::uint64_t>::max();
    account.balance.fill(255);
    const auto maximum = leaf(Nibbles(64, 15), encode_account(account));
    expect(maximum.size() == 148, "maximum account leaf fixture");
    compare_node(maximum, TrieKind::account, 0);
    for (std::size_t scalar_size = 0; scalar_size <= 32; ++scalar_size) {
        Word value{};
        for (std::size_t i = 32 - scalar_size; i < 32; ++i)
            value[i] = static_cast<std::uint8_t>(i + 1);
        account.balance = value;
        account.nonce = scalar_size;
        compare_node(leaf({}, encode_account(account)), TrieKind::account, 64);
        if (scalar_size != 0) {
            for (std::size_t depth : {std::size_t{0}, std::size_t{1}, std::size_t{63}, std::size_t{64}})
                compare_node(leaf(Nibbles(64 - depth, 7), encode_storage(value)),
                             TrieKind::storage, depth);
        }
    }
    // The 31/32-byte threshold and both 55/56-byte RLP list payloads.
    for (const std::size_t size : {27, 28}) {
        Word value{};
        std::fill(value.end() - size, value.end(), 0x80);
        const auto encoded = leaf({}, encode_storage(value));
        expect(encoded.size() == size + 4, "inline threshold fixture");
        compare_node(encoded, TrieKind::storage, 64);
    }
    for (const std::size_t size : {19, 20}) {
        Word value{};
        std::fill(value.end() - size, value.end(), 0x80);
        const auto encoded = leaf(Nibbles(64, 1), encode_storage(value));
        expect(encoded[0] == (size == 19 ? 0xf7 : 0xf8), "55/56-byte prefix fixture");
        compare_node(encoded, TrieKind::storage, 0);
    }
    std::vector<Bytes> items(17, rlp_bytes(Bytes(32, 0x55)));
    items[16] = rlp_bytes({});
    const auto branch = rlp_list(items);
    expect(branch.size() == 532, "maximum branch fixture");
    compare_node(branch, TrieKind::account, 0);
    compare_node(branch, TrieKind::storage, 63);
    reject_node(branch, TrieKind::storage, 64);
    const auto wrong_role = static_cast<TrieKind>(2);
    reject_node(branch, wrong_role, 0);
    reject_node(branch, TrieKind::storage, 65);

    // Two last-nibble siblings exercise an inline branch and empty suffix leaves.
    Hash left{}, right{};
    right.back() = 1;
    Word one{};
    one.back() = 1;
    compare_tree(build_trie(TrieKind::storage,
        {{left, encode_storage(one)}, {right, encode_storage(one)}}).root,
        TrieKind::storage, 0);
}

void malformed() {
    const auto scalar = Bytes{1};
    for (const Bytes& bytes : {Bytes{}, Bytes{0x80}, Bytes{0xc0}, Bytes{0xc1, 0x80},
                              Bytes{0xf8, 0}, Bytes{0xf9, 0, 56},
                              Bytes{0xff, 255, 255, 255, 255, 255, 255, 255, 255},
                              Bytes{0xc2, 0x81, 0}, Bytes{0xc3, 0x20, 0x81, 1}})
        reject_node(bytes, TrieKind::storage, 64);
    reject_node(leaf({}, Bytes{0x80}), TrieKind::storage, 64);  // Zero storage.
    reject_node(leaf({}, Bytes{0}), TrieKind::storage, 64);     // Leading zero.
    reject_node(leaf({}, Bytes{0x82, 0, 1}), TrieKind::storage, 64);
    reject_node(leaf({}, rlp_list({Bytes{1}})), TrieKind::storage, 64);
    reject_node(leaf({}, scalar), TrieKind::storage, 63);
    reject_node(leaf(Nibbles(1, 1), scalar), TrieKind::storage, 64);
    reject_node(rlp_list({Bytes{0x40}, Bytes{1}}), TrieKind::storage, 64);
    reject_node(rlp_list({Bytes{0x21}, Bytes{1}}), TrieKind::storage, 64);
    reject_node(rlp_list({Bytes{0}, rlp_bytes(Bytes(32, 1))}), TrieKind::storage, 0);
    reject_node(rlp_list({Bytes{0x11}, rlp_bytes({})}), TrieKind::storage, 0);
    reject_node(rlp_list({Bytes{0x11}, rlp_bytes(Bytes(32, 1))}), TrieKind::storage, 63);
    auto fields = std::vector<Bytes>{Bytes{0}, Bytes{0x80}, rlp_bytes(Bytes(32)), rlp_bytes(Bytes(32))};
    reject_node(leaf({}, rlp_list(fields)), TrieKind::account, 64);
    fields[0] = rlp_bytes(Bytes(9, 1));
    reject_node(leaf({}, rlp_list(fields)), TrieKind::account, 64);
    fields[0] = Bytes{0x80};
    fields[1] = rlp_bytes(Bytes(33, 1));
    reject_node(leaf({}, rlp_list(fields)), TrieKind::account, 64);
    fields[1] = Bytes{0x80};
    fields[2] = rlp_bytes(Bytes(31, 1));
    reject_node(leaf({}, rlp_list(fields)), TrieKind::account, 64);
    std::vector<Bytes> branch(17, Bytes{0x80});
    branch[0] = rlp_bytes(Bytes(32, 1));
    reject_node(rlp_list(branch), TrieKind::storage, 0);  // Unary branch.
    branch[1] = Bytes{1};
    reject_node(rlp_list(branch), TrieKind::storage, 0);  // Child is not a hash.
    branch[1] = rlp_bytes(Bytes(32, 2));
    branch.push_back(Bytes{0x80});
    reject_node(rlp_list(branch), TrieKind::storage, 0);  // Eighteenth item.
    fixed::NodeBytes zero{};
    expect(fixed::parse_node(zero, 533, TrieKind::storage, 0).valid == 0,
           "oversized node length");
    expect(fixed::parse_node(zero, ~std::uint64_t{0}, TrieKind::storage, 0).valid == 0,
           "overflowing node length");
}

void differential_syntax() {
    Account account;
    account.balance.fill(255);
    account.nonce = ~std::uint64_t{0};
    Word value{};
    value.fill(255);
    std::vector<Bytes> children(17, rlp_bytes(Bytes(32, 0x55)));
    children.back() = Bytes{0x80};
    const std::array<Bytes, 3> seeds{{leaf(Nibbles(64, 1), encode_account(account)),
                                    leaf(Nibbles(64, 1), encode_storage(value)),
                                    rlp_list(children)}};
    std::uint64_t random = 0x351c87f390ab12ULL;
    for (std::size_t seed = 0; seed < seeds.size(); ++seed) {
        const auto role = seed == 0 ? TrieKind::account : TrieKind::storage;
        for (std::size_t iteration = 0; iteration < 128; ++iteration) {
            auto candidate = seeds[seed];
            random = random * 6364136223846793005ULL + 1442695040888963407ULL;
            candidate[(random >> 8) % candidate.size()] ^= static_cast<std::uint8_t>(random >> 32);
            bool expected = true;
            try {
                (void)decode_node(candidate, role, 0);
            } catch (const std::invalid_argument&) {
                expected = false;
            }
            const auto actual = fixed::parse_node(padded(candidate), candidate.size(), role, 0);
            expect((actual.valid != 0) == expected, "mutated syntax differs from reference");
        }
    }
}

void records() {
    const auto packed = pack_snapshot(make_fixture());
    std::size_t tested = 0;
    for (const auto& pages : packed.pages) {
        for (std::size_t page = 1; page < pages.size(); ++page) {
            for (std::size_t offset = 0; offset + 8 <= page_bytes;) {
                const auto length = std::size_t{pages[page][offset]} |
                                    (std::size_t{pages[page][offset + 1]} << 8);
                if (length == 0) break;
                const auto role = static_cast<TrieKind>(pages[page][offset + 3]);
                const auto links = pages[page][offset + 4];
                const auto depth = pages[page][offset + 5];
                const auto total = 8 + length + 12 * links;
                fixed::RecordBytes bytes{};
                std::copy_n(pages[page].begin() + offset, total, bytes.begin());
                const auto result = fixed::decode_record(bytes, total, role, depth);
                expect(result.valid == ~fixed::Mask{0}, "canonical packed record rejected");
                expect(result.length == length && result.link_count == links,
                       "record header fields");
                const auto node = fixed::parse_node(result.node, length, role, depth);
                expect(node.valid != 0 && node.kind == result.kind, "record node binding");
                const auto expected_links = node.hashed_children +
                    (role == TrieKind::account && node.kind == static_cast<std::uint64_t>(NodeKind::leaf));
                expect(expected_links == links, "record link count binding");
                expect(std::equal(bytes.begin() + 8, bytes.begin() + 8 + length,
                                  result.node.begin()), "record canonical RLP preservation");
                for (std::size_t i = length; i < result.node.size(); ++i)
                    expect(result.node[i] == 0, "record node padding");
                for (std::size_t i = 0; i < links; ++i) {
                    const auto begin = 8 + length + i * 12;
                    std::uint64_t expected_page = 0;
                    for (std::size_t j = 0; j < 8; ++j)
                        expected_page |= std::uint64_t{bytes[begin + j]} << (8 * j);
                    expect(result.links[i].page_id == expected_page, "record locator page");
                }
                expect(fixed::decode_record(bytes, total - 1, role, depth).valid == 0,
                       "truncated record accepted");
                bytes[6] = 1;
                expect(fixed::decode_record(bytes, total, role, depth).valid == 0,
                       "reserved record byte accepted");
                offset += total;
                ++tested;
            }
        }
    }
    expect(tested != 0, "packed record corpus empty");

    fixed::RecordBytes bytes{};
    bytes[0] = 1;
    bytes[4] = 1;
    expect(fixed::decode_record(bytes, 21, TrieKind::account, 0).valid != 0,
           "empty storage-root locator rejected");
    bytes[17] = 1;
    expect(fixed::decode_record(bytes, 21, TrieKind::account, 0).valid == 0,
           "partially zero sentinel accepted");
    bytes[9] = 1;
    bytes[17] = static_cast<std::uint8_t>(page_bytes - 1);
    bytes[18] = static_cast<std::uint8_t>((page_bytes - 1) >> 8);
    bytes[19] = 8;
    expect(fixed::decode_record(bytes, 21, TrieKind::account, 0).valid == 0,
           "cross-page locator accepted");
    bytes[17] = 0;
    bytes[18] = 0;
    expect(fixed::decode_record(bytes, 21, TrieKind::account, 0).valid != 0,
           "valid minimal locator rejected");
    expect(fixed::decode_record(bytes, ~std::uint64_t{0}, TrieKind::account, 0).valid == 0,
           "overflowing record length accepted");
}

}  // namespace
}  // namespace ethereum_mpt

void run_fixed_node_tests() {
    ethereum_mpt::corpus();
    ethereum_mpt::malformed();
    ethereum_mpt::differential_syntax();
    ethereum_mpt::records();
}
