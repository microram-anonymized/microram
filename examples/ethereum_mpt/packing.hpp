// Packed representation of public MPT snapshots: records (canonical RLP plus
// physical child locators), fixed-width pages per tier, and immutable images
// holding one or more retained roots.

#pragma once

#include "trie.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <vector>

namespace ethereum_mpt {

// These routines process public snapshots. They are not private query helpers.
// One build-wide packed-page width, not a per-node allocation.
// The largest record is 732 bytes including metadata (DESIGN.md, "Public packed
// snapshot"), so 768 is the smallest supported width.
#ifndef ETHEREUM_MPT_PAGE_BYTES
#define ETHEREUM_MPT_PAGE_BYTES 1024
#endif
inline constexpr std::size_t page_bytes = ETHEREUM_MPT_PAGE_BYTES;
static_assert(page_bytes == 768 || page_bytes == 1024 || page_bytes == 2048,
              "ETHEREUM_MPT_PAGE_BYTES must be 768, 1024, or 2048");
using Page = std::array<std::uint8_t, page_bytes>;

enum class Tier : std::uint8_t { account_top = 0, storage_top = 1, bulk = 2 };

struct TierProfile {
    std::uint8_t account_top_depth = 3;
    std::uint8_t storage_top_depth = 0;
};

struct Locator {
    std::uint64_t page_id = 0;
    std::uint16_t offset = 0;
    std::uint16_t record_bytes = 0;

    bool empty() const;
};

bool operator==(const Locator& lhs, const Locator& rhs);
bool operator!=(const Locator& lhs, const Locator& rhs);

struct Snapshot {
    Trie accounts;
    std::map<Hash, Trie> storage_tries;
};

struct PackingStats {
    std::size_t canonical_bytes = 0;  // S
    std::size_t records = 0;          // N
    std::size_t ordinary_links = 0;   // E
    std::size_t account_leaves = 0;   // A, including empty storage roots
    std::size_t record_bytes = 0;     // R
    std::size_t real_pages = 0;       // P, excludes dummy pages
    std::size_t packing_runs = 0;
    std::size_t dummy_pages = 0;

    double utilization() const;
    std::size_t page_value_bytes() const;
};

struct PackedSnapshot {
    TierProfile profile;
    Hash state_root{};
    Locator account_root;
    // Index with static_cast<std::size_t>(Tier). Disabled top tiers are empty;
    // every configured tier has an all-zero page at index zero.
    std::array<std::vector<Page>, 3> pages;
    std::array<PackingStats, 3> stats;

    PackingStats total_stats() const;
};

struct PackedRoot {
    Hash state_root{};
    Locator account_root;
};

// One immutable image contains the union of all retained roots. Roots preserve
// input order (including duplicates); record identities are deduplicated across
// the whole generation by trie role, incoming nibble depth, and canonical hash.
struct PackedGeneration {
    TierProfile profile;
    std::vector<PackedRoot> roots;
    std::array<std::vector<Page>, 3> pages;
    std::array<PackingStats, 3> stats;
    // First real page ID of each nonempty sealed run, per tier. Appending
    // never fills an earlier run's tail; this records its packing overhead.
    std::array<std::vector<std::uint64_t>, 3> packing_run_starts;

    PackingStats total_stats() const;
};

struct PackedRecord {
    NodeKind kind;
    TrieKind trie_kind;
    std::uint8_t nibble_depth;
    Bytes canonical_rlp;
    std::vector<Locator> links;
};

Tier tier_for(TrieKind kind, std::size_t depth, TierProfile profile);
const char* tier_name(Tier tier);

// Metadata is explicitly little endian; canonical Ethereum RLP is unchanged.
PackedRecord read_packed_record(const PackedSnapshot& snapshot, Tier tier,
                                const Locator& locator);
PackedRecord read_packed_record(const PackedGeneration& generation, Tier tier,
                                const Locator& locator);
PackedSnapshot pack_snapshot(const Snapshot& snapshot, TierProfile profile = {});
PackedGeneration pack_generation(const std::vector<Snapshot>& snapshots,
                                 TierProfile profile = {});
// Reuse the validated, confirmed-loaded base's (role, depth, hash) locators.
// Return its immutable pages and roots followed by fresh sealed pages and the
// supplied roots, including duplicates. The base is unchanged on failure.
PackedGeneration append_generation(const PackedGeneration& base,
                                   const std::vector<Snapshot>& snapshots);
// Validates the entire reachable image and all physical extents and tails.
// Throws std::invalid_argument on malformed canonical data or metadata.
void validate_packed_snapshot(const PackedSnapshot& snapshot);
void validate_packed_generation(const PackedGeneration& generation);

}  // namespace ethereum_mpt
