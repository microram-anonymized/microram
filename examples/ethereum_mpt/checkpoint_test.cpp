// Tests the checkpoint codec and file API: exact byte layout, strict rejection
// of malformed or corrupted input, admission limits, atomic replacement and
// restore of retained history into fresh maps.

#include "checkpoint.hpp"
#include "fixture.hpp"

#include <algorithm>
#include <array>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <sys/stat.h>
#include <vector>

namespace {
using namespace ethereum_mpt;
namespace fs = std::filesystem;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("checkpoint test: ") + message);
}

template<class Exception = std::exception, class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const Exception&) {
        return;
    }
    throw std::runtime_error(std::string("checkpoint test accepted: ") + message);
}

// Deliberately spell out all persisted fields: byte equality alone could hide
// matching omissions in the serializer and deserializer.
void check_equal(const PublicCheckpoint& actual, const PublicCheckpoint& expected) {
    require(actual.block.block_id == expected.block.block_id &&
            actual.block.parent_id == expected.block.parent_id &&
            actual.block.state_root == expected.block.state_root &&
            actual.block.number == expected.block.number &&
            actual.fingerprint == expected.fingerprint,
            "checkpoint preserves complete block metadata and identity");
    require(actual.state.size() == expected.state.size(), "checkpoint preserves account count");
    auto received = actual.state.begin();
    for (const auto& [address, account] : expected.state) {
        require(received->first == address && received->second.nonce == account.nonce &&
                received->second.balance == account.balance &&
                received->second.code_hash == account.code_hash &&
                received->second.storage == account.storage,
                "checkpoint preserves account fields and storage keys/values");
        ++received;
    }
}

void check_equal(const PublicHistoryCheckpoint& actual, const PublicHistoryCheckpoint& expected) {
    require(actual.served_head == expected.served_head &&
            actual.versions.size() == expected.versions.size(),
            "history preserves served head and retained count");
    for (std::size_t i = 0; i < actual.versions.size(); ++i)
        check_equal(actual.versions[i], expected.versions[i]);
}

struct Fixture {
    std::vector<MockBlockDelta> blocks;
    std::vector<PublicCheckpoint> checkpoints;
};

Fixture fixtures() {
    std::ifstream input(ETHEREUM_MPT_BLOCK_FIXTURES);
    require(bool(input), "independent mock fixture opens");
    Fixture result;
    result.blocks = load_mock_blocks(input);
    require(result.blocks.size() == 8, "independent fixture contains eight roots");
    std::map<Hash, PublicState> states;
    for (const auto& block : result.blocks) {
        const auto parent = block.number == 0 ? PublicState{} : states.at(block.parent_id);
        PublicCheckpoint checkpoint;
        checkpoint.block = {block.block_id, block.parent_id, block.expected_state_root, block.number};
        checkpoint.fingerprint = delta_fingerprint(block);
        checkpoint.state = apply_delta(parent, block);
        states.emplace(block.block_id, checkpoint.state);
        result.checkpoints.push_back(std::move(checkpoint));
    }
    return result;
}

constexpr std::size_t header_bytes = 176;
constexpr std::size_t account_bytes = 100;
constexpr std::size_t slot_bytes = 64;
constexpr std::size_t checksum_bytes = 32;

void put_integer(Bytes& bytes, std::size_t offset, std::uint64_t value, std::size_t width = 8) {
    require(offset + width <= bytes.size(), "test integer fits fixture");
    for (std::size_t i = 0; i < width; ++i) {
        bytes[offset + width - 1 - i] = static_cast<std::uint8_t>(value);
        value >>= 8;
    }
}

void repair_checksum(Bytes& bytes) {
    require(bytes.size() >= checksum_bytes, "test checksum fits fixture");
    const auto hash = keccak256(bytes.data(), bytes.size() - checksum_bytes);
    std::copy(hash.begin(), hash.end(), bytes.end() - checksum_bytes);
}

void test_roundtrips_and_format(const Fixture& fixture) {
    for (const auto& checkpoint : fixture.checkpoints) {
        const auto encoded = encode_public_checkpoint(checkpoint);
        const auto decoded = decode_public_checkpoint(encoded);
        check_equal(decoded, checkpoint);
        require(encode_public_checkpoint(decoded) == encoded,
                "decode/re-encode preserves canonical bytes");
        require(snapshot_from_state(decoded.state).accounts.root_hash() == checkpoint.block.state_root,
                "checkpoint roundtrip agrees with independent py-trie state root");
    }

    const auto& empty = fixture.checkpoints.back();
    require(empty.state.empty(), "empty checkpoint fixture has no accounts");
    // Build the empty version-1 wire image independently of the encoder. These
    // offsets form a compatibility contract for checkpoints surviving a restart.
    Bytes expected(header_bytes + checksum_bytes, 0);
    const std::array<std::uint8_t, 8> magic{'E', 'M', 'P', 'T', 'C', 'P', 'T', 0};
    std::copy(magic.begin(), magic.end(), expected.begin());
    put_integer(expected, 8, 1, 4);
    put_integer(expected, 16, expected.size());
    std::copy(empty.block.block_id.begin(), empty.block.block_id.end(), expected.begin() + 24);
    std::copy(empty.block.parent_id.begin(), empty.block.parent_id.end(), expected.begin() + 56);
    std::copy(empty.block.state_root.begin(), empty.block.state_root.end(), expected.begin() + 88);
    put_integer(expected, 120, empty.block.number);
    std::copy(empty.fingerprint.begin(), empty.fingerprint.end(), expected.begin() + 128);
    repair_checksum(expected);
    require(encode_public_checkpoint(empty) == expected, "empty version-1 wire image is stable");
    check_equal(decode_public_checkpoint(expected), empty);

    auto edge = fixture.checkpoints[1];
    edge.block.number = std::numeric_limits<std::uint64_t>::max();
    edge.fingerprint.fill(0xa5);
    auto& first = edge.state.begin()->second;
    first.storage.emplace(Word{}, word_from_u64(1));
    Word maximum;
    maximum.fill(0xff);
    first.storage.emplace(maximum, maximum);
    edge.block.state_root = snapshot_from_state(edge.state).accounts.root_hash();
    const auto encoded = encode_public_checkpoint(edge);
    check_equal(decode_public_checkpoint(encoded), edge);
    require(edge.state.at(fixture_address(3)).nonce == std::numeric_limits<std::uint64_t>::max() &&
            edge.state.at(fixture_address(3)).balance == maximum,
            "roundtrip exercises full-width nonce, balance, slot and storage values");
    PublicState reordered;
    for (auto it = edge.state.rbegin(); it != edge.state.rend(); ++it) {
        auto account = it->second;
        account.storage.clear();
        for (auto slot = it->second.storage.rbegin(); slot != it->second.storage.rend(); ++slot)
            account.storage.emplace(*slot);
        reordered.emplace(it->first, std::move(account));
    }
    edge.state = std::move(reordered);
    require(encode_public_checkpoint(edge) == encoded,
            "canonical checkpoint does not depend on state insertion order");
}

void test_malformed_inputs(const Fixture& fixture) {
    const auto valid = encode_public_checkpoint(fixture.checkpoints.front());
    require(valid.size() == header_bytes + 3 * account_bytes + 4 * slot_bytes + checksum_bytes,
            "malformation fixture layout has expected account and slot counts");
    for (std::size_t size = 0; size < valid.size(); ++size) {
        const Bytes truncated(valid.begin(), valid.begin() + size);
        reject([&] { decode_public_checkpoint(truncated); }, "truncated checkpoint");
    }
    for (std::size_t position = 0; position < valid.size(); ++position) {
        auto corrupted = valid;
        corrupted[position] ^= 1;
        reject([&] { decode_public_checkpoint(corrupted); }, "single-byte corruption");
    }
    auto trailing = valid;
    trailing.push_back(0);
    reject([&] { decode_public_checkpoint(trailing); }, "trailing byte");
    trailing.insert(trailing.end(), valid.begin(), valid.end());
    reject([&] { decode_public_checkpoint(trailing); }, "concatenated checkpoints");

    const auto malformed = [&](auto change, const char* message) {
        auto bytes = valid;
        change(bytes);
        repair_checksum(bytes);
        reject<std::invalid_argument>([&] { decode_public_checkpoint(bytes); }, message);
    };
    malformed([](Bytes& b) { b[0] ^= 1; }, "magic with valid checksum");
    for (std::uint64_t version : {0ULL, 2ULL, 0xffffffffULL})
        malformed([&](Bytes& b) { put_integer(b, 8, version, 4); }, "unsupported format version");
    malformed([](Bytes& b) { put_integer(b, 12, 1, 4); }, "nonzero reserved header");
    malformed([](Bytes& b) { put_integer(b, 16, b.size() - 1); }, "short declared file size");
    malformed([](Bytes& b) { put_integer(b, 16, b.size() + 1); }, "long declared file size");
    malformed([](Bytes& b) { put_integer(b, 16, std::numeric_limits<std::uint64_t>::max()); },
              "overflowing declared file size");
    malformed([](Bytes& b) { std::fill(b.begin() + 24, b.begin() + 56, 0); }, "zero block identity");
    malformed([](Bytes& b) { b[88] ^= 1; }, "state root inconsistent with payload");
    malformed([](Bytes& b) { b[header_bytes + 27] ^= 1; }, "account nonce inconsistent with root");
    for (const std::uint64_t count : {0ULL, 2ULL, 4ULL, 0xffffffffffffffffULL})
        malformed([&](Bytes& b) { put_integer(b, 160, count); }, "invalid account count");
    for (const std::uint64_t count : {0ULL, 3ULL, 5ULL, 0xffffffffffffffffULL})
        malformed([&](Bytes& b) { put_integer(b, 168, count); }, "invalid total storage count");
    for (const std::uint64_t count : {0ULL, 1ULL, 3ULL, 0xffffffffffffffffULL})
        malformed([&](Bytes& b) { put_integer(b, header_bytes + 92, count); },
                  "invalid per-account storage count");

    constexpr auto second_account = header_bytes + account_bytes + 2 * slot_bytes;
    malformed([](Bytes& b) {
        std::copy_n(b.begin() + header_bytes, 20, b.begin() + second_account);
    }, "duplicate account address");
    malformed([](Bytes& b) {
        std::swap_ranges(b.begin() + header_bytes, b.begin() + header_bytes + 20,
                         b.begin() + second_account);
    }, "descending account addresses");
    constexpr auto first_slot = header_bytes + account_bytes;
    constexpr auto second_slot = first_slot + slot_bytes;
    malformed([](Bytes& b) {
        std::copy_n(b.begin() + first_slot, 32, b.begin() + second_slot);
    }, "duplicate storage slot");
    malformed([](Bytes& b) {
        std::swap_ranges(b.begin() + first_slot, b.begin() + first_slot + 32,
                         b.begin() + second_slot);
    }, "descending storage slots");
    malformed([](Bytes& b) {
        std::fill_n(b.begin() + first_slot + 32, 32, 0);
    }, "noncanonical zero storage value");
    malformed([](Bytes& b) {
        b.insert(b.end() - checksum_bytes, 1, 0);
        put_integer(b, 16, b.size());
    }, "extra payload despite corrected size and checksum");

    auto invalid = fixture.checkpoints.front();
    invalid.block.state_root.front() ^= 1;
    reject([&] { encode_public_checkpoint(invalid); }, "encoding inconsistent state root");
    invalid = fixture.checkpoints.front();
    invalid.block.block_id = {};
    reject([&] { encode_public_checkpoint(invalid); }, "encoding zero block identity");
    invalid = fixture.checkpoints.front();
    invalid.state.begin()->second.storage.begin()->second = {};
    reject([&] { encode_public_checkpoint(invalid); }, "encoding zero storage");
}

void test_limits(const Fixture& fixture) {
    const auto& checkpoint = fixture.checkpoints.front();
    const auto bytes = encode_public_checkpoint(checkpoint);
    const CheckpointLimits exact{bytes.size(), 3, 4};
    require(encode_public_checkpoint(checkpoint, exact) == bytes, "encoding accepts exact limits");
    check_equal(decode_public_checkpoint(bytes, exact), checkpoint);
    for (const auto limit : {CheckpointLimits{bytes.size() - 1, 3, 4},
                             CheckpointLimits{bytes.size(), 2, 4},
                             CheckpointLimits{bytes.size(), 3, 3}}) {
        reject([&] { encode_public_checkpoint(checkpoint, limit); }, "encoder resource bound");
        reject([&] { decode_public_checkpoint(bytes, limit); }, "decoder resource bound");
    }
    // The storage bound is cumulative: each account independently has only two.
    const auto empty = encode_public_checkpoint(fixture.checkpoints.back(),
                                               CheckpointLimits{208, 0, 0});
    check_equal(decode_public_checkpoint(empty, CheckpointLimits{208, 0, 0}),
                fixture.checkpoints.back());
    reject([&] { decode_public_checkpoint(empty, CheckpointLimits{207, 0, 0}); },
           "file bound smaller than empty checkpoint");
    reject([&] { encode_public_checkpoint(checkpoint, CheckpointLimits{0, 0, 0}); },
           "zero resource bounds for nonempty state");
    const auto maximum = std::numeric_limits<std::size_t>::max();
    check_equal(decode_public_checkpoint(bytes, CheckpointLimits{maximum, maximum, maximum}),
                checkpoint);
    for (const std::size_t offset : {160, 168}) {
        auto overflowing = bytes;
        put_integer(overflowing, offset, std::numeric_limits<std::uint64_t>::max());
        repair_checksum(overflowing);
        reject<std::invalid_argument>([&] {
            decode_public_checkpoint(overflowing, CheckpointLimits{maximum, maximum, maximum});
        }, "record size overflow even with unrestricted caller limits");
    }
}

void test_history_roundtrips_and_format(const Fixture& fixture) {
    // The fixture contains both forks. Choosing every head also exercises a
    // served ancestor while retaining newer and alternate branch versions.
    for (const auto& version : fixture.checkpoints) {
        const PublicHistoryCheckpoint checkpoint{version.block.block_id, fixture.checkpoints};
        const auto bytes = encode_public_history_checkpoint(checkpoint);
        const auto decoded = decode_public_history_checkpoint(bytes);
        check_equal(decoded, checkpoint);
        require(encode_public_history_checkpoint(decoded) == bytes,
                "history decode/re-encode preserves deterministic bytes and retention order");
        reject([&] { decode_public_checkpoint(bytes); }, "single API cannot discard retained history");
        const auto promoted = decode_public_history_checkpoint(encode_public_checkpoint(version));
        check_equal(promoted, PublicHistoryCheckpoint{version.block.block_id, {version}});
    }

    const auto& empty = fixture.checkpoints.back();
    const PublicHistoryCheckpoint single{empty.block.block_id, {empty}};
    // Independently specify the empty v2 image, including the single outer
    // checksum and version metadata offset, to lock down restart compatibility.
    Bytes expected(80 + 152 + checksum_bytes, 0);
    const std::array<std::uint8_t, 8> magic{'E', 'M', 'P', 'T', 'C', 'P', 'T', 0};
    std::copy(magic.begin(), magic.end(), expected.begin());
    put_integer(expected, 8, 2, 4);
    put_integer(expected, 16, expected.size());
    std::copy(empty.block.block_id.begin(), empty.block.block_id.end(), expected.begin() + 24);
    put_integer(expected, 56, 1);
    std::copy(empty.block.block_id.begin(), empty.block.block_id.end(), expected.begin() + 80);
    std::copy(empty.block.parent_id.begin(), empty.block.parent_id.end(), expected.begin() + 112);
    std::copy(empty.block.state_root.begin(), empty.block.state_root.end(), expected.begin() + 144);
    put_integer(expected, 176, empty.block.number);
    std::copy(empty.fingerprint.begin(), empty.fingerprint.end(), expected.begin() + 184);
    repair_checksum(expected);
    require(encode_public_history_checkpoint(single) == expected, "empty version-2 wire image is stable");
    check_equal(decode_public_history_checkpoint(expected), single);
    reject([&] { decode_public_checkpoint(expected); }, "single API rejects even one-version v2");

    const PublicHistoryCheckpoint pruned{fixture.checkpoints[6].block.block_id,
                                         {fixture.checkpoints[3], fixture.checkpoints[5],
                                          fixture.checkpoints[6]}};
    check_equal(decode_public_history_checkpoint(encode_public_history_checkpoint(pruned)), pruned);
    auto anchor = single;
    anchor.versions[0].block.number = std::numeric_limits<std::uint64_t>::max();
    anchor.versions[0].block.parent_id = {};
    check_equal(decode_public_history_checkpoint(encode_public_history_checkpoint(anchor)), anchor);
    check_equal(decode_public_history_checkpoint(encode_public_checkpoint(anchor.versions[0])), anchor);
}

void test_history_malformed_inputs(const Fixture& fixture) {
    auto self_parent = fixture.checkpoints.front();
    self_parent.block.parent_id = self_parent.block.block_id;
    const auto legacy = encode_public_checkpoint(self_parent);
    check_equal(decode_public_checkpoint(legacy), self_parent);
    reject<std::invalid_argument>([&] { decode_public_history_checkpoint(legacy); },
                                  "legacy promotion rejects a retained self-parent");

    const PublicHistoryCheckpoint checkpoint{fixture.checkpoints[0].block.block_id,
                                             {fixture.checkpoints[0], fixture.checkpoints[1]}};
    const auto valid = encode_public_history_checkpoint(checkpoint);
    constexpr std::size_t first = 80;
    constexpr std::size_t second = first + 152 + 3 * account_bytes + 4 * slot_bytes;
    for (std::size_t size = 0; size < valid.size(); ++size)
        reject([&] { decode_public_history_checkpoint(Bytes(valid.begin(), valid.begin() + size)); },
               "truncated history");
    for (std::size_t offset = 0; offset < valid.size(); ++offset) {
        auto bytes = valid;
        bytes[offset] ^= 1;
        reject([&] { decode_public_history_checkpoint(bytes); }, "single-byte history corruption");
    }
    const auto malformed = [&](auto change, const char* message) {
        auto bytes = valid;
        change(bytes);
        repair_checksum(bytes);
        reject<std::invalid_argument>([&] { decode_public_history_checkpoint(bytes); }, message);
    };
    malformed([](Bytes& b) { b[0] ^= 1; }, "history magic");
    malformed([](Bytes& b) { put_integer(b, 8, 3, 4); }, "unknown history version");
    malformed([](Bytes& b) { put_integer(b, 12, 1, 4); }, "history reserved field");
    malformed([](Bytes& b) { put_integer(b, 16, b.size() + 1); }, "history length mismatch");
    malformed([](Bytes& b) { std::fill_n(b.begin() + 24, 32, 0); }, "zero served head");
    malformed([](Bytes& b) { b[24] ^= 1; }, "served head missing from history");
    malformed([](Bytes& b) { std::fill_n(b.begin() + second, 32, 0); }, "zero version ID");
    malformed([](Bytes& b) { std::copy_n(b.begin() + first, 32, b.begin() + second); },
              "duplicate retained identity");
    malformed([](Bytes& b) { std::copy_n(b.begin() + second, 32, b.begin() + first + 32); },
              "parent follows child");
    malformed([](Bytes& b) { std::copy_n(b.begin() + first, 32, b.begin() + first + 32); },
              "self-parent version");
    malformed([](Bytes& b) { put_integer(b, second + 96, 3); }, "parent number discontinuity");
    malformed([](Bytes& b) {
        put_integer(b, first + 96, std::numeric_limits<std::uint64_t>::max());
        put_integer(b, second + 96, 0);
    }, "parent number increment overflows");
    malformed([](Bytes& b) { b[second + 64] ^= 1; }, "non-head state root mismatch");
    malformed([](Bytes& b) { b[first + 152 + 27] ^= 1; }, "history state root mismatch");
    for (const auto offset : {std::size_t{56}, std::size_t{64}, std::size_t{72}}) {
        malformed([&](Bytes& b) { put_integer(b, offset, 0); }, "zero history count");
        malformed([&](Bytes& b) { put_integer(b, offset, std::numeric_limits<std::uint64_t>::max()); },
                  "overflowing history count");
    }
    malformed([](Bytes& b) { put_integer(b, first + 136, 7); }, "version account exceeds total");
    malformed([](Bytes& b) { put_integer(b, first + 144, 9); }, "version storage exceeds total");
    malformed([](Bytes& b) { put_integer(b, first + 152 + 92, 5); }, "account exceeds version storage");
    malformed([](Bytes& b) { put_integer(b, second + 144, 3); }, "version totals underfill history");
    malformed([](Bytes& b) {
        std::copy_n(b.begin() + first + 152, 20, b.begin() + first + 152 + account_bytes + 2 * slot_bytes);
    }, "duplicate address within history version");
    malformed([](Bytes& b) {
        std::fill_n(b.begin() + first + 152 + account_bytes + 32, 32, 0);
    }, "zero storage within history version");
    malformed([](Bytes& b) {
        b.insert(b.end() - checksum_bytes, 1, 0);
        put_integer(b, 16, b.size());
    }, "history trailing payload");
    malformed([](Bytes& b) {
        std::rotate(b.begin() + first, b.begin() + second, b.end() - checksum_bytes);
    }, "reordered retained parent and child records");

    auto invalid = checkpoint;
    invalid.versions.clear();
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding empty window");
    invalid = checkpoint;
    invalid.served_head = {};
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding absent head");
    invalid = checkpoint;
    invalid.versions[1] = invalid.versions[0];
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding duplicate IDs");
    invalid = checkpoint;
    std::swap(invalid.versions[0], invalid.versions[1]);
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding reordered history");
    invalid = checkpoint;
    ++invalid.versions[1].block.number;
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding wrong parent number");
    invalid = checkpoint;
    invalid.versions[1].block.state_root[0] ^= 1;
    reject([&] { encode_public_history_checkpoint(invalid); }, "encoding non-head invalid root");
}

void test_history_limits(const Fixture& fixture) {
    const PublicHistoryCheckpoint checkpoint{fixture.checkpoints[0].block.block_id,
                                             {fixture.checkpoints[0], fixture.checkpoints[1]}};
    const auto bytes = encode_public_history_checkpoint(checkpoint);
    const CheckpointLimits exact{bytes.size(), 6, 8, 2};
    require(encode_public_history_checkpoint(checkpoint, exact) == bytes, "history exact limits encode");
    check_equal(decode_public_history_checkpoint(bytes, exact), checkpoint);
    for (const auto limits : {CheckpointLimits{bytes.size() - 1, 6, 8, 2},
                              CheckpointLimits{bytes.size(), 5, 8, 2},
                              CheckpointLimits{bytes.size(), 6, 7, 2},
                              CheckpointLimits{bytes.size(), 6, 8, 1},
                              CheckpointLimits{bytes.size(), 6, 8, 0}}) {
        reject([&] { encode_public_history_checkpoint(checkpoint, limits); }, "history encoding bounds");
        reject([&] { decode_public_history_checkpoint(bytes, limits); }, "history decoding bounds");
    }
    const auto maximum = std::numeric_limits<std::size_t>::max();
    const CheckpointLimits unlimited{maximum, maximum, maximum, maximum};
    check_equal(decode_public_history_checkpoint(bytes, unlimited), checkpoint);
    for (const auto offset : {std::size_t{56}, std::size_t{64}, std::size_t{72}}) {
        auto overflowing = bytes;
        put_integer(overflowing, offset, std::numeric_limits<std::uint64_t>::max());
        repair_checksum(overflowing);
        reject<std::invalid_argument>([&] { decode_public_history_checkpoint(overflowing, unlimited); },
                                      "history size arithmetic overflows");
    }
    const auto legacy = encode_public_checkpoint(fixture.checkpoints[0]);
    reject([&] { decode_public_history_checkpoint(legacy, CheckpointLimits{legacy.size(), 3, 4, 0}); },
           "version limit also applies to v1 promotion");
}

class TemporaryDirectory {
public:
    TemporaryDirectory() {
        auto pattern = (fs::temp_directory_path() / "ethereum-mpt-checkpoint-test-XXXXXX").string();
        std::vector<char> buffer(pattern.begin(), pattern.end());
        buffer.push_back('\0');
        const auto created = ::mkdtemp(buffer.data());
        if (!created) throw std::runtime_error("cannot create checkpoint test directory");
        path = created;
    }
    ~TemporaryDirectory() {
        std::error_code ignored;
        fs::remove_all(path, ignored);
    }
    std::size_t entries() const {
        return static_cast<std::size_t>(std::distance(fs::directory_iterator(path),
                                                     fs::directory_iterator{}));
    }
    fs::path path;
};

Bytes read_file(const fs::path& path) {
    std::ifstream input(path, std::ios::binary);
    require(bool(input), "raw checkpoint file opens");
    return Bytes(std::istreambuf_iterator<char>(input), std::istreambuf_iterator<char>());
}

void write_file(const fs::path& path, const Bytes& bytes) {
    std::ofstream output(path, std::ios::binary | std::ios::trunc);
    output.write(reinterpret_cast<const char*>(bytes.data()),
                 static_cast<std::streamsize>(bytes.size()));
    require(bool(output), "raw checkpoint file writes");
}

void test_filesystem(const Fixture& fixture) {
    TemporaryDirectory directory;
    const auto file = directory.path / "public-state.bin";
    save_public_checkpoint(file.string(), fixture.checkpoints[0]);
    require(directory.entries() == 1, "successful save leaves no temporary file");
    require(read_file(file) == encode_public_checkpoint(fixture.checkpoints[0]),
            "filesystem save writes canonical checkpoint bytes");
    check_equal(load_public_checkpoint(file.string()), fixture.checkpoints[0]);
    const auto previous = read_file(file);
    std::ifstream previous_reader(file, std::ios::binary);
    require(bool(previous_reader), "reader pins previous checkpoint file");
    save_public_checkpoint(file.string(), fixture.checkpoints[1]);
    const auto saved = read_file(file);
    const Bytes previous_after_replace{std::istreambuf_iterator<char>(previous_reader),
                                      std::istreambuf_iterator<char>()};
    require(previous_after_replace == previous,
            "atomic replacement preserves complete prior bytes for an existing reader");
    check_equal(load_public_checkpoint(file.string()), fixture.checkpoints[1]);
    require(directory.entries() == 1, "atomic replacement leaves no temporary file");

    auto invalid = fixture.checkpoints[2];
    invalid.block.state_root.front() ^= 1;
    reject([&] { save_public_checkpoint(file.string(), invalid); }, "invalid replacement state");
    reject([&] { save_public_checkpoint(file.string(), fixture.checkpoints[2],
                                        CheckpointLimits{1, 1, 1}); }, "replacement exceeds resource limits");
    require(read_file(file) == saved && directory.entries() == 1,
            "failed replacement validation preserves prior file and cleans temporary files");

    const auto target_directory = directory.path / "invalid-target";
    fs::create_directory(target_directory);
    reject([&] { save_public_checkpoint(target_directory.string(), fixture.checkpoints[2]); },
           "save over a directory");
    require(fs::is_directory(target_directory) && directory.entries() == 2,
            "failed installation preserves target and removes temporary file");
    reject([&] { load_public_checkpoint(target_directory.string()); }, "load directory");
    reject([&] { load_public_checkpoint((directory.path / "missing").string()); }, "load missing file");
    reject([&] { save_public_checkpoint((directory.path / "missing" / "checkpoint").string(),
                                        fixture.checkpoints[0]); }, "save under missing parent");
    reject([&] { save_public_checkpoint("", fixture.checkpoints[0]); }, "save empty path");
    reject([&] { load_public_checkpoint(""); }, "load empty path");
    const auto nul_path = file.string() + std::string(1, '\0') + "ignored";
    reject([&] { save_public_checkpoint(nul_path, fixture.checkpoints[0]); }, "save embedded-NUL path");
    reject([&] { load_public_checkpoint(nul_path); }, "load embedded-NUL path");
    reject([&] { load_public_checkpoint(file.string(), CheckpointLimits{saved.size() - 1, 3, 4}); },
           "filesystem loader file bound");
    reject([&] { load_public_checkpoint(file.string(), CheckpointLimits{saved.size(), 2, 4}); },
           "filesystem loader account bound");
    reject([&] { load_public_checkpoint(file.string(), CheckpointLimits{saved.size(), 3, 3}); },
           "filesystem loader cumulative slot bound");
    auto corrupt = saved;
    corrupt[88] ^= 1;
    write_file(file, corrupt);
    reject([&] { load_public_checkpoint(file.string()); }, "filesystem loader rejects corrupt bytes");
    write_file(file, {});
    reject([&] { load_public_checkpoint(file.string()); }, "filesystem loader rejects empty file");
    require(directory.entries() == 2, "all filesystem error paths leave no temporary files");

    // A sparse oversized file must be rejected from its stat size before the
    // loader allocates or reads its advertised contents.
    const auto oversized = directory.path / "oversized";
    write_file(oversized, {});
    fs::resize_file(oversized, CheckpointLimits{}.max_file_bytes + 1);
    reject([&] { load_public_checkpoint(oversized.string()); }, "oversized sparse checkpoint");
    const auto fifo = directory.path / "fifo";
    require(::mkfifo(fifo.c_str(), 0600) == 0, "nonregular test input is created");
    reject([&] { load_public_checkpoint(fifo.string()); }, "nonregular checkpoint input");
    require(directory.entries() == 4, "nonregular and oversized loads leave no temporary files");
}

void test_history_filesystem(const Fixture& fixture) {
    TemporaryDirectory directory;
    const auto file = directory.path / "public-history.bin";
    const auto& legacy = fixture.checkpoints[1];
    save_public_checkpoint(file.string(), legacy);
    check_equal(load_public_history_checkpoint(file.string()),
                PublicHistoryCheckpoint{legacy.block.block_id, {legacy}});
    const auto previous = read_file(file);
    std::ifstream previous_reader(file, std::ios::binary);
    const PublicHistoryCheckpoint checkpoint{fixture.checkpoints[5].block.block_id, fixture.checkpoints};
    save_public_history_checkpoint(file.string(), checkpoint);
    const Bytes previous_after_replace{std::istreambuf_iterator<char>(previous_reader),
                                      std::istreambuf_iterator<char>()};
    require(previous_after_replace == previous, "history replacement preserves pinned v1 reader");
    const auto saved = read_file(file);
    require(saved == encode_public_history_checkpoint(checkpoint), "history file bytes are canonical");
    check_equal(load_public_history_checkpoint(file.string()), checkpoint);
    reject([&] { load_public_checkpoint(file.string()); }, "legacy loader rejects history file");

    auto invalid = checkpoint;
    invalid.versions.back().block.state_root[0] ^= 1;
    reject([&] { save_public_history_checkpoint(file.string(), invalid); }, "invalid history replacement");
    auto limit = CheckpointLimits{};
    limit.max_versions = checkpoint.versions.size() - 1;
    reject([&] { save_public_history_checkpoint(file.string(), checkpoint, limit); },
           "history save version limit");
    reject([&] { load_public_history_checkpoint(file.string(), limit); }, "history load version limit");
    limit = {};
    limit.max_file_bytes = saved.size() - 1;
    reject([&] { load_public_history_checkpoint(file.string(), limit); }, "history load byte limit");
    require(read_file(file) == saved && directory.entries() == 1,
            "failed history replacement preserves old bytes and leaves no temporary files");

    const auto target_directory = directory.path / "invalid-target";
    fs::create_directory(target_directory);
    reject([&] { save_public_history_checkpoint(target_directory.string(), checkpoint); },
           "history rename over directory fails");
    require(fs::is_directory(target_directory) && directory.entries() == 2,
            "failed history rename removes temporary file");
    reject([&] { load_public_history_checkpoint(target_directory.string()); }, "history directory input");
    auto corrupt = saved;
    corrupt[24] ^= 1;
    write_file(file, corrupt);
    reject([&] { load_public_history_checkpoint(file.string()); }, "history file corruption");
    require(directory.entries() == 2, "history error paths leave no temporary files");
}

struct StoreControl {
    std::size_t loads = 0, live_stores = 0, reads = 0;
    std::vector<std::size_t> read_stores;
};

// This public instrumented store checks reconstruction and version lifecycle;
// real ORAM checkpoint restarts are exercised by the update demo integration.
class ImageStore final : public PageStore {
public:
    ImageStore(const PackedGeneration& image, std::array<std::size_t, 3> capacities,
               std::shared_ptr<StoreControl> control)
        : pages_(image.pages), capacities_(capacities), control_(std::move(control)),
          serial_(++control_->loads) {
        ++control_->live_stores;
    }
    ~ImageStore() override { --control_->live_stores; }
    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        ++control_->reads;
        control_->read_stores.push_back(serial_);
        const auto& pages = pages_[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            found[i] = static_cast<std::uint8_t>(ids[i] < pages.size());
            output[i] = found[i] ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }
    void write_pages_batch(Tier tier, std::uint64_t first, const std::vector<Page>& pages) override {
        const auto index = static_cast<std::size_t>(tier);
        auto& destination = pages_[index];
        require(first == destination.size() && first <= capacities_[index] &&
                pages.size() <= capacities_[index] - first,
                "restarted append remains within fresh map capacity");
        destination.insert(destination.end(), pages.begin(), pages.end());
    }
    void finish_pending_work() override {}
    std::array<std::size_t, 3> capacities() const override { return capacities_; }
private:
    std::array<std::vector<Page>, 3> pages_;
    std::array<std::size_t, 3> capacities_;
    std::shared_ptr<StoreControl> control_;
    std::size_t serial_;
};

std::unique_ptr<VersionService> start_service(const PublicCheckpoint& checkpoint, bool incremental,
                                             const std::shared_ptr<StoreControl>& control) {
    const ReplacementOptions options{TierProfile{3, 2}, 4, 8};
    IncrementalLoader loader = [control](const PackedGeneration& image, std::size_t lanes,
                                         const std::array<std::size_t, 3>& capacities) {
        require(lanes == 8, "checkpoint restart retains lane profile");
        return LoadedGeneration{std::make_unique<ImageStore>(image, capacities, control), 4096};
    };
    if (incremental) {
        IncrementalOptions append;
        append.service = options;
        append.page_headroom = {32, 32, 32};
        append.compact_after_updates = 0;
        return std::make_unique<IncrementalService>(checkpoint, append, loader);
    }
    GenerationLoader replacement = [loader](const PackedGeneration& image, std::size_t lanes) {
        std::array<std::size_t, 3> capacities{};
        for (std::size_t tier = 0; tier < capacities.size(); ++tier)
            capacities[tier] = image.pages[tier].size();
        return loader(image, lanes, capacities);
    };
    return std::make_unique<ReplacementService>(checkpoint, options, replacement);
}

void check_proofs(VersionService& service, const PublicCheckpoint& expected) {
    const auto snapshot = snapshot_from_state(expected.state);
    std::vector<PathRequest> paths;
    for (const std::uint8_t id : {1, 2, 3, 99})
        paths.push_back(make_path_request(fixture_address(id), {word_from_u64(1), word_from_u64(99)}));
    const auto result = service.run(expected.block.block_id, BatchProfile{4, 2}, paths);
    require(result.manifest.state_root == expected.block.state_root &&
            result.manifest.block_id == expected.block.block_id,
            "restarted proofs use checkpoint block and independent state root");
    require(result.proofs.accounts.size() == 4 && result.proofs.storage.size() == 8,
            "restarted proof result has fixed batch shape");
    const auto empty_storage = build_trie(TrieKind::storage, {});
    for (std::size_t i = 0; i < paths.size(); ++i) {
        const auto& account = result.proofs.accounts[i];
        const auto proof = decode_proof(account.proof);
        require(account.error == 0 && proof == prove(snapshot.accounts, paths[i].account_key),
                "restarted account proof matches canonical reference");
        const auto encoded = verify_proof(TrieKind::account, expected.block.state_root,
                                          paths[i].account_key, proof);
        require((account.present != 0) == encoded.has_value(), "restarted account membership verifies");
        const auto fields = encoded ? decode_account(*encoded) : Account{};
        if (encoded)
            require(account.nonce == fields.nonce && account.balance == fields.balance &&
                    account.code_hash == fields.code_hash && account.storage_root == fields.storage_root,
                    "restarted account fields authenticate");
        const auto& storage = fields.storage_root == empty_trie_root()
            ? empty_storage : snapshot.storage_tries.at(fields.storage_root);
        for (std::size_t slot = 0; slot < 2; ++slot) {
            const auto& item = result.proofs.storage[i * 2 + slot];
            const auto storage_proof = decode_proof(item.proof);
            require(item.error == 0 && storage_proof == prove(storage, paths[i].storage_keys[slot]),
                    "restarted storage proof matches canonical reference");
            const auto value = verify_proof(TrieKind::storage, fields.storage_root,
                                             paths[i].storage_keys[slot], storage_proof);
            require((item.present != 0) == value.has_value() &&
                    item.storage_value == (value ? decode_storage(*value) : Word{}),
                    "restarted storage proof authenticates selected account version");
        }
    }
}

void test_durable_restart(const Fixture& fixture, bool incremental) {
    TemporaryDirectory directory;
    const auto file = (directory.path / "restart.bin").string();
    const auto control = std::make_shared<StoreControl>();
    {
        auto original = start_service(fixture.checkpoints[0], incremental, control);
        require(original->prepare(fixture.blocks[1]), "next block prepares before checkpoint");
        save_public_checkpoint(file, original->checkpoint());
        check_equal(load_public_checkpoint(file), fixture.checkpoints[0]);
        require(original->pending_head()->block_id == fixture.blocks[1].block_id,
                "checkpoint during pending update preserves publication state");
        require(original->publish(), "prepared block publishes after checkpoint");
        save_public_checkpoint(file, original->checkpoint());
        check_equal(load_public_checkpoint(file), fixture.checkpoints[1]);
    }
    require(control->live_stores == 0, "checkpoint does not keep old page maps alive");
    const auto previous_loads = control->loads;
    auto restored = start_service(load_public_checkpoint(file), incremental, control);
    require(control->loads == previous_loads + 1 && control->live_stores == 1 &&
            restored->retained_blocks() == std::vector<Hash>{fixture.blocks[1].block_id},
            "durable restart loads fresh maps and retains only checkpoint head");
    control->read_stores.clear();
    check_proofs(*restored, fixture.checkpoints[1]);
    require(control->read_stores.size() == 130 &&
            std::all_of(control->read_stores.begin(), control->read_stores.end(),
                        [&](std::size_t serial) { return serial == previous_loads + 1; }),
            "all fixed account/storage rounds read only the fresh maps");
    require(!restored->prepare(fixture.blocks[1]), "durable checkpoint preserves duplicate identity");
    const auto reads = control->reads;
    reject([&] { restored->manifest(fixture.blocks[0].block_id); }, "restart unavailable ancestor");
    reject([&] { restored->prepare_reorg(fixture.blocks[0].block_id); }, "restart unavailable reorg");
    require(control->reads == reads, "unavailable history rejection does not access maps");
    require(restored->prepare(fixture.blocks[2]) && restored->publish(),
            "durable restart continues with next public block");
    check_proofs(*restored, fixture.checkpoints[2]);
    check_proofs(*restored, fixture.checkpoints[1]);
    save_public_checkpoint(file, restored->checkpoint());
    check_equal(load_public_checkpoint(file), fixture.checkpoints[2]);
    require(directory.entries() == 1, "repeated durable service checkpoints leave no temporary files");
}

void write_cli_fixtures(const Fixture& fixture, const fs::path& directory) {
    fs::create_directories(directory);
    save_public_history_checkpoint((directory / "disconnected.checkpoint").string(),
        PublicHistoryCheckpoint{fixture.checkpoints[4].block.block_id,
                                {fixture.checkpoints[1], fixture.checkpoints[4]}});
    save_public_history_checkpoint((directory / "nonlast.checkpoint").string(),
        PublicHistoryCheckpoint{fixture.checkpoints[0].block.block_id, fixture.checkpoints});
    PublicHistoryCheckpoint untrusted{fixture.checkpoints[1].block.block_id,
                                      {fixture.checkpoints[0], fixture.checkpoints[1]}};
    untrusted.versions[0].fingerprint[0] ^= 1;
    save_public_history_checkpoint((directory / "untrusted.checkpoint").string(), untrusted);
}

}  // namespace

int main(int argc, char** argv) {
    try {
        const auto fixture = fixtures();
        if (argc == 3 && std::string(argv[1]) == "--write-cli-fixtures") {
            write_cli_fixtures(fixture, argv[2]);
            return 0;
        }
        if (argc != 1)
            throw std::invalid_argument("usage: ethereum_mpt_checkpoint_test [--write-cli-fixtures DIRECTORY]");
        test_roundtrips_and_format(fixture);
        test_malformed_inputs(fixture);
        test_limits(fixture);
        test_filesystem(fixture);
        test_history_roundtrips_and_format(fixture);
        test_history_malformed_inputs(fixture);
        test_history_limits(fixture);
        test_history_filesystem(fixture);
        test_durable_restart(fixture, false);
        test_durable_restart(fixture, true);
        std::cout << "ethereum_mpt_checkpoint_test passed\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_checkpoint_test: " << error.what() << '\n';
        return 1;
    }
}
