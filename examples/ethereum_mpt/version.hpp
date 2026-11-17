// Published-version coordination: VersionService pins a manifest for each proof
// batch; ReplacementService loads fresh generations, IncrementalService appends
// stable pages to the current one. All decisions use public data only.

#pragma once

#include "mock_chain.hpp"
#include "page_store.hpp"
#include "traversal.hpp"

#include <functional>
#include <memory>
#include <optional>
#include <vector>

namespace ethereum_mpt {

struct BlockHeader {
    Hash block_id{}, parent_id{}, state_root{};
    std::uint64_t number = 0;
};

struct BlockManifest : BlockHeader {
    std::uint64_t generation = 0;
    Locator account_root;
    TierProfile tiers;
};

// Public restart material only. Restoring always constructs fresh ORAM maps.
struct PublicCheckpoint {
    BlockHeader block;
    Hash fingerprint{};
    PublicState state;
};

// Published queryable versions in oldest-to-newest retention order. This is
// publication order, not a sort by block height or ID; a reorg may select any
// retained head. Pending state and discarded/pruned identity tombstones are
// excluded. Restore reconstructs the complete retained closure in fresh maps.
struct PublicHistoryCheckpoint {
    Hash served_head{};
    std::vector<PublicCheckpoint> versions;
};
// Checks retained identities, head membership, parent ordering/heights and all
// reconstructed state roots. Missing parents are permitted after pruning;
// incomplete anchor metadata is accepted as in a single public checkpoint.
void validate_public_history_checkpoint(const PublicHistoryCheckpoint& checkpoint);
PublicCheckpoint genesis_checkpoint(const MockBlockDelta& genesis);

struct LoadedGeneration {
    std::unique_ptr<PageReader> reader;
    std::size_t arena_bytes = 0;
};
using GenerationLoader = std::function<LoadedGeneration(const PackedGeneration&,
                                                        std::size_t max_lanes)>;

struct ReplacementOptions {
    TierProfile tiers;
    std::size_t retained_blocks = 4;
    std::size_t max_lanes = 64;
};

struct IncrementalOptions {
    ReplacementOptions service;
    // Public spare page IDs per enabled tier, in addition to the freshly packed
    // retained closure and its dummy. Disabled tiers always have capacity zero.
    std::array<std::size_t, 3> page_headroom{16, 16, 16};
    // Rebuild before the next block after this many append publications. Zero
    // disables periodic compaction; capacity exhaustion still forces a rebuild.
    std::size_t compact_after_updates = 16;
    // Public per-tier percentages, 1..100 inclusive; zero disables the policy.
    // Evaluate the proposed append and post-update retention window. Fullness
    // includes dummy pages and only triggers for a tier receiving new pages.
    // Dead bytes are unreachable record bytes / all record bytes, excluding
    // page slack and dummy bytes. Either threshold stages a fresh generation.
    std::size_t compact_at_fullness_percent = 0;
    std::size_t compact_at_dead_bytes_percent = 0;
};

using IncrementalLoader = std::function<LoadedGeneration(
    const PackedGeneration&, std::size_t max_lanes,
    const std::array<std::size_t, 3>& capacities)>;

struct UpdateStats {
    std::size_t incremental_publications = 0, replacement_publications = 0;
    std::size_t compactions = 0, failed_uploads = 0;
    // Pages in fully completed append publications, excluding fresh loading
    // and every reserved/uncertain page from a failed upload closure.
    std::array<std::size_t, 3> uploaded_pages{};
};

struct GenerationMemory {
    std::size_t current_arena_bytes = 0, staged_arena_bytes = 0;
    std::size_t peak_arena_bytes = 0;
    std::size_t current_page_bytes = 0, staged_page_bytes = 0;
    std::size_t peak_page_bytes = 0;
};

// Public published-image occupancy, one entry per Tier. Reachability uses all
// retained roots, counts shared records once, and never reads the ORAM backend.
// allocated_pages includes dummies, but excludes pending uploads and uncertain
// reservations after backend failure (those remain in GenerationMemory).
struct GenerationOccupancy {
    std::array<std::size_t, 3> allocated_pages{}, page_capacities{};
    std::array<std::size_t, 3> live_record_bytes{}, dead_record_bytes{};
};

// Logical payload retained by the public builder at the observation boundary,
// separate from GenerationMemory's loaded backend. This is not allocated bytes
// or RSS: exclude container/allocator overhead, unused capacity, decoded node
// fields, other metadata, and temporary construction buffers.
struct PublicBuilderMemory {
    // Distinct Version objects across current and pending generations.
    std::size_t retained_versions = 0;
    // Address + nonce + balance + code hash (92 bytes), plus 64 per storage slot.
    std::size_t public_state_bytes = 0;
    // RLP vector sizes for distinct live Node objects, including embedded nodes
    // also encoded in their parent. Equal bytes in separate objects count twice.
    std::size_t canonical_trie_rlp_bytes = 0;
    // Page vector sizes in each distinct current/pending public packed image.
    // Append preparation copies the image even though its ORAM backend is shared.
    std::size_t packed_image_bytes = 0;
    std::size_t staged_upload_bytes = 0;
    // Known block ID/fingerprint pairs (64 bytes) and published IDs (32 bytes),
    // including tombstones for discarded, failed, or pruned versions.
    std::size_t identity_bytes = 0;

    std::size_t payload_bytes() const {
        return public_state_bytes + canonical_trie_rlp_bytes + packed_image_bytes +
               staged_upload_bytes + identity_bytes;
    }
};

struct VersionedBatch {
    BlockManifest manifest;
    BatchResult proofs;
};

// Example-local serialized coordinator following explicitly supplied latest
// heads. All admission, preparation and publication calls run on one caller.
// Preparation may be invoked at a public read boundary; publication is refused
// until the entire admitted account + storage batch has completed. This is not
// a concurrent server or a consensus/fork-choice implementation.
class VersionService {
 public:
    virtual ~VersionService();
    VersionService(const VersionService&) = delete;
    VersionService& operator=(const VersionService&) = delete;

    // True stages an update; false is identical delivery. Incremental updates
    // prepare public sealed pages here and upload only inside publish(). Fresh
    // replacements are fully loaded here. Preparation never mutates live maps.
    bool prepare(const MockBlockDelta& block);
    void prepare_reorg(const Hash& retained_head);
    void prepare_compaction();
    // False when no update is ready or a complete proof batch is still active.
    bool publish();
    void discard_pending();

    VersionedBatch run(const Hash& block_id, BatchProfile profile,
                       const std::vector<PathRequest>& requests);
    BlockManifest manifest(const Hash& block_id) const;
    BlockManifest served_head() const;
    BlockHeader observed_head() const;
    std::optional<BlockManifest> pending_head() const;
    std::optional<Hash> pending_common_ancestor() const;
    std::vector<Hash> retained_blocks() const;
    PublicCheckpoint checkpoint() const;
    PublicHistoryCheckpoint history_checkpoint() const;
    GenerationMemory memory() const;
    GenerationOccupancy occupancy() const;
    PublicBuilderMemory public_builder_memory() const;
    // Current published image, including historical records until compaction.
    std::array<PackingStats, 3> packing_stats() const;
    UpdateStats update_stats() const;
    bool batch_active() const;
    bool available() const;

 protected:
    VersionService(PublicCheckpoint checkpoint, ReplacementOptions options,
                   GenerationLoader loader);
    VersionService(PublicCheckpoint checkpoint, IncrementalOptions options,
                   IncrementalLoader loader);
    VersionService(PublicHistoryCheckpoint checkpoint, ReplacementOptions options,
                   GenerationLoader loader);
    VersionService(PublicHistoryCheckpoint checkpoint, IncrementalOptions options,
                   IncrementalLoader loader);

 private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

class ReplacementService final : public VersionService {
 public:
    ReplacementService(PublicCheckpoint checkpoint, ReplacementOptions options,
                       GenerationLoader loader);
    ReplacementService(PublicHistoryCheckpoint checkpoint, ReplacementOptions options,
                       GenerationLoader loader);
};

class IncrementalService final : public VersionService {
 public:
    IncrementalService(PublicCheckpoint checkpoint, IncrementalOptions options,
                       IncrementalLoader loader);
    IncrementalService(PublicHistoryCheckpoint checkpoint, IncrementalOptions options,
                       IncrementalLoader loader);
};

}  // namespace ethereum_mpt
