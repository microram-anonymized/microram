// Fixed-work node and record parsing used by the private traversal.

#pragma once

#include "fixed.hpp"
#include "packing.hpp"

namespace ethereum_mpt::fixed {

struct Child {
    std::uint64_t type = 0;  // 0: empty, 1: embedded list, 2: hash.
    std::uint64_t length = 0;
    std::array<std::uint8_t, 31> embedded{};
    Hash hash{};
    std::uint64_t link_index = 0;
};

struct ParsedNode {
    Mask valid = 0;
    std::uint64_t kind = 0;
    std::uint64_t path_length = 0;
    std::uint64_t hashed_children = 0;
    std::array<std::uint8_t, 64> path{};
    std::array<Child, 16> children{};
    Child child{};
    std::uint64_t nonce = 0;
    Word balance{};
    Hash storage_root{}, code_hash{};
    Word storage_value{};
};

// Role and incoming depth are public schedule parameters; bytes and length are
// private. This opens exactly 17 outer item slots. Embedded descendants are
// opened in subsequent depth rounds, after full public snapshot validation.
ParsedNode parse_node(const NodeBytes& bytes, std::uint64_t length,
                      TrieKind role, std::size_t depth);

struct DecodedRecord {
    Mask valid = 0;
    NodeBytes node{};
    std::uint64_t length = 0;
    std::uint64_t kind = 0;
    std::uint64_t link_count = 0;
    std::array<Locator, 16> links{};
};

// The caller separately checks the source locator's page extent, then compares
// kind/link_count with parse_node and authenticates its canonical node bytes.
DecodedRecord decode_record(const RecordBytes& bytes,
                            std::uint64_t record_length,
                            TrieKind role, std::size_t depth);

}  // namespace ethereum_mpt::fixed
