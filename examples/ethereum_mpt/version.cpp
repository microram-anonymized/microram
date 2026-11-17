// Version services: public preparation of new heads, full-batch-boundary
// publication, retention, reorgs, append/replacement loading, compaction
// policies, failure recovery and checkpoint export/restore.

#include "version.hpp"

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <tuple>
#include <utility>

namespace ethereum_mpt {
namespace {
BlockHeader header(const MockBlockDelta& block) {
    return {block.block_id, block.parent_id, block.expected_state_root, block.number};
}

struct Version {
    BlockHeader block;
    Hash fingerprint;
    CanonicalState canonical;

    PublicCheckpoint checkpoint() const { return {block, fingerprint, canonical.state()}; }
};
using Versions = std::vector<std::shared_ptr<const Version>>;

struct Backend {
    LoadedGeneration loaded;
    std::array<std::size_t, 3> allocated_pages{}, capacities{};
    bool available = true;

    std::size_t page_value_bytes() const {
        std::size_t total = 0;
        for (const auto count : allocated_pages) total += count * page_bytes;
        return total;
    }
};

struct Generation {
    std::uint64_t id = 0;
    Hash head{};
    Versions versions;
    PackedGeneration packed;
    std::shared_ptr<Backend> backend;
    std::array<std::vector<Page>, 3> uploads;
    std::size_t appended_updates = 0;
    bool append_update = false, compaction = false;

    std::size_t index(const Hash& block) const {
        for (std::size_t i = 0; i < versions.size(); ++i)
            if (versions[i]->block.block_id == block) return i;
        throw std::out_of_range("requested MPT block is unavailable; reload a public checkpoint if needed");
    }

    BlockManifest manifest(const Hash& block) const {
        const auto i = index(block);
        BlockManifest result;
        static_cast<BlockHeader&>(result) = versions[i]->block;
        result.generation = id;
        // Incremental images retain allocated historical roots until compaction,
        // independently of the bounded table of queryable public versions.
        const auto root = std::find_if(packed.roots.begin(), packed.roots.end(),
            [&](const PackedRoot& item) { return item.state_root == result.state_root; });
        if (root == packed.roots.end()) throw std::logic_error("MPT manifest has no packed root");
        result.account_root = root->account_root;
        result.tiers = packed.profile;
        return result;
    }
};

// This walks the immutable public image, not query-dependent backend storage.
// Inline children have no external descendants; their bytes already belong to
// their containing record. Account leaves link to the shared storage closure.
GenerationOccupancy image_occupancy(const PackedGeneration& image, const Versions& versions,
        const std::array<std::size_t, 3>& capacities) {
    GenerationOccupancy result;
    result.page_capacities = capacities;
    std::map<Hash, Locator> roots;
    for (const auto& root : image.roots) roots.emplace(root.state_root, root.account_root);
    std::vector<std::pair<Tier, Locator>> pending;
    for (const auto& version : versions) {
        const auto root = roots.find(version->block.state_root);
        if (root == roots.end()) throw std::logic_error("MPT retained root missing from public image");
        pending.emplace_back(tier_for(TrieKind::account, 0, image.profile), root->second);
    }
    std::set<std::tuple<Tier, std::uint64_t, std::uint16_t>> visited;
    while (!pending.empty()) {
        const auto [tier, locator] = pending.back();
        pending.pop_back();
        if (locator.empty() || !visited.emplace(tier, locator.page_id, locator.offset).second)
            continue;
        const auto record = read_packed_record(image, tier, locator);
        result.live_record_bytes[static_cast<std::size_t>(tier)] += locator.record_bytes;
        if (record.links.empty()) continue;
        auto role = record.trie_kind;
        std::size_t depth = record.nibble_depth + 1;
        if (record.kind == NodeKind::extension) {
            depth = record.nibble_depth +
                decode_node(record.canonical_rlp, role, record.nibble_depth).path.size();
        } else if (record.kind == NodeKind::leaf) {
            role = TrieKind::storage;
            depth = 0;
        }
        const auto target = tier_for(role, depth, image.profile);
        for (const auto& link : record.links) pending.emplace_back(target, link);
    }
    for (std::size_t t = 0; t < 3; ++t) {
        result.allocated_pages[t] = image.pages[t].size();
        if (result.live_record_bytes[t] > image.stats[t].record_bytes)
            throw std::logic_error("MPT live records exceed allocated record bytes");
        result.dead_record_bytes[t] = image.stats[t].record_bytes - result.live_record_bytes[t];
    }
    return result;
}

// ceil(denominator * percent / 100), without overflowing even when the declared
// public capacity approaches size_t's maximum. Options validate percent <= 100.
bool at_percent(std::size_t numerator, std::size_t denominator, std::size_t percent) {
    if (percent == 0 || denominator == 0) return false;
    const auto threshold = (denominator / 100) * percent +
        ((denominator % 100) * percent + 99) / 100;
    return numerator >= threshold;
}

std::optional<Hash> common_ancestor(const Generation& generation, Hash other) {
    std::map<Hash, Hash> parents;
    for (const auto& version : generation.versions)
        parents.emplace(version->block.block_id,
                        version->block.parent_id);
    std::set<Hash> ancestors;
    auto current = generation.head;
    while (parents.count(current) && ancestors.insert(current).second)
        current = parents.at(current);
    std::set<Hash> visited;
    while (parents.count(other) && visited.insert(other).second) {
        if (ancestors.count(other)) return other;
        other = parents.at(other);
    }
    return std::nullopt;
}

// All flags describe public service operations, never private traversal state.
struct FlagGuard {
    explicit FlagGuard(bool& flag) : flag(flag) { flag = true; }
    ~FlagGuard() { flag = false; }
    bool& flag;
};

std::size_t node_rlp_bytes(const NodePtr& node, std::set<const Node*>& visited) {
    if (!node || !visited.insert(node.get()).second) return 0;
    auto bytes = node->rlp.size();
    bytes += node_rlp_bytes(node->child, visited);
    for (const auto& child : node->children) bytes += node_rlp_bytes(child, visited);
    return bytes;
}

PublicHistoryCheckpoint single_history(PublicCheckpoint checkpoint) {
    PublicHistoryCheckpoint history;
    history.served_head = checkpoint.block.block_id;
    history.versions.push_back(std::move(checkpoint));
    return history;
}

void validate_history_metadata(const PublicHistoryCheckpoint& checkpoint) {
    if (checkpoint.versions.empty() || checkpoint.served_head == Hash{})
        throw std::invalid_argument("public history checkpoint requires versions and a served head");
    std::map<Hash, std::size_t> identities;
    for (std::size_t i = 0; i < checkpoint.versions.size(); ++i) {
        const auto& block = checkpoint.versions[i].block;
        if (block.block_id == Hash{} || !identities.emplace(block.block_id, i).second)
            throw std::invalid_argument("public history checkpoint has a zero or duplicate block ID");
    }
    if (!identities.count(checkpoint.served_head))
        throw std::invalid_argument("public history checkpoint served head is not retained");
    for (std::size_t i = 0; i < checkpoint.versions.size(); ++i) {
        const auto& block = checkpoint.versions[i].block;
        const auto parent = identities.find(block.parent_id);
        if (parent == identities.end()) continue;
        if (parent->second >= i)
            throw std::invalid_argument("public history checkpoint parent must precede its child");
        const auto number = checkpoint.versions[parent->second].block.number;
        if (number == std::numeric_limits<std::uint64_t>::max() || block.number != number + 1)
            throw std::invalid_argument("public history checkpoint child number does not follow its parent");
    }
}
}  // namespace

void validate_public_history_checkpoint(const PublicHistoryCheckpoint& checkpoint) {
    validate_history_metadata(checkpoint);
    for (const auto& version : checkpoint.versions)
        if (snapshot_from_state(version.state).accounts.root_hash() != version.block.state_root)
            throw std::invalid_argument("public history checkpoint state root mismatch");
}

PublicCheckpoint genesis_checkpoint(const MockBlockDelta& genesis) {
    if (genesis.block_id == Hash{} || genesis.parent_id != Hash{} || genesis.number != 0)
        throw std::invalid_argument("mock genesis requires a nonzero ID, zero parent and number zero");
    return {header(genesis), delta_fingerprint(genesis), apply_delta({}, genesis)};
}

struct VersionService::Impl {
    ReplacementOptions options;
    GenerationLoader loader;
    IncrementalLoader incremental_loader;
    IncrementalOptions incremental_options;
    std::shared_ptr<Generation> current, pending;
    BlockHeader observed;
    std::optional<Hash> ancestor;
    // Public identity tombstones prevent conflicting reuse after state pruning.
    // They contain no query information and are not full retained snapshots.
    std::map<Hash, Hash> known;
    std::set<Hash> published;
    std::uint64_t next_generation = 1;
    std::size_t peak_arena = 0, peak_pages = 0;
    UpdateStats stats;
    bool active = false, preparing = false;

    bool incremental() const { return bool(incremental_loader); }

    void observe_memory(const std::shared_ptr<Generation>& staged) {
        const auto old_arena = current ? current->backend->loaded.arena_bytes : 0;
        const auto old_pages = current ? current->backend->page_value_bytes() : 0;
        const bool shared = current && staged->backend == current->backend;
        const auto staged_arena = shared ? 0 : staged->backend->loaded.arena_bytes;
        std::size_t staged_pages = 0;
        if (shared) {
            for (const auto& pages : staged->uploads) staged_pages += pages.size() * page_bytes;
        } else {
            staged_pages = staged->backend->page_value_bytes();
        }
        peak_arena = std::max(peak_arena, old_arena + staged_arena);
        peak_pages = std::max(peak_pages, old_pages + staged_pages);
    }

    std::shared_ptr<Generation> build(Versions versions, const Hash& head,
                                      bool compaction = false) {
        if (next_generation == std::numeric_limits<std::uint64_t>::max())
            throw std::overflow_error("MPT generation identifier exhausted");
        auto generation = std::make_shared<Generation>();
        generation->id = next_generation++;
        generation->head = head;
        generation->compaction = compaction;
        generation->versions = std::move(versions);
        std::vector<Snapshot> snapshots;
        snapshots.reserve(generation->versions.size());
        for (const auto& version : generation->versions) snapshots.push_back(version->canonical.snapshot());
        generation->packed = pack_generation(snapshots, options.tiers);
        validate_packed_generation(generation->packed);
        generation->backend = std::make_shared<Backend>();
        auto& backend = *generation->backend;
        for (std::size_t t = 0; t < 3; ++t) {
            const auto count = generation->packed.pages[t].size();
            const auto spare = incremental() && count ? incremental_options.page_headroom[t] : 0;
            if (count > std::numeric_limits<std::size_t>::max() - spare)
                throw std::overflow_error("MPT page capacity exhausted");
            backend.allocated_pages[t] = count;
            backend.capacities[t] = count + spare;
        }
        backend.loaded = incremental()
            ? incremental_loader(generation->packed, options.max_lanes, backend.capacities)
            : loader(generation->packed, options.max_lanes);
        if (!backend.loaded.reader)
            throw std::runtime_error("MPT generation loader returned no reader");
        if (incremental()) {
            auto* store = dynamic_cast<PageStore*>(backend.loaded.reader.get());
            if (!store || store->capacities() != backend.capacities)
                throw std::runtime_error("MPT incremental loader requires a store with requested capacities");
            store->finish_pending_work();
        }
        observe_memory(generation);
        return generation;
    }

    std::shared_ptr<Generation> stage(Versions versions, const Hash& head,
                                      const Snapshot& snapshot) {
        if (!incremental() || !current->backend->available)
            return build(std::move(versions), head);
        const auto interval = incremental_options.compact_after_updates;
        if (interval && current->appended_updates >= interval)
            return build(std::move(versions), head, true);
        auto packed = append_generation(current->packed, {snapshot});
        // Preflight every map before any reservation or shared-map mutation.
        for (std::size_t t = 0; t < 3; ++t)
            if (packed.pages[t].size() > current->backend->capacities[t])
                return build(std::move(versions), head, true);
        for (std::size_t t = 0; t < 3; ++t)
            if (packed.pages[t].size() > current->packed.pages[t].size() &&
                at_percent(packed.pages[t].size(), current->backend->capacities[t],
                           incremental_options.compact_at_fullness_percent))
                return build(std::move(versions), head, true);
        if (incremental_options.compact_at_dead_bytes_percent) {
            const auto occupancy = image_occupancy(packed, versions, current->backend->capacities);
            for (std::size_t t = 0; t < 3; ++t)
                if (at_percent(occupancy.dead_record_bytes[t], packed.stats[t].record_bytes,
                               incremental_options.compact_at_dead_bytes_percent))
                    return build(std::move(versions), head, true);
        }
        auto generation = std::make_shared<Generation>();
        generation->id = current->id;
        generation->head = head;
        generation->versions = std::move(versions);
        generation->backend = current->backend;
        generation->appended_updates = current->appended_updates + 1;
        generation->append_update = true;
        for (std::size_t t = 0; t < 3; ++t)
            generation->uploads[t].assign(
                packed.pages[t].begin() + current->packed.pages[t].size(), packed.pages[t].end());
        generation->packed = std::move(packed);
        observe_memory(generation);
        return generation;
    }

    void initialize(PublicHistoryCheckpoint checkpoint) {
        if ((!loader && !incremental_loader) || options.retained_blocks == 0 ||
            options.max_lanes == 0 || incremental_options.compact_at_fullness_percent > 100 ||
            incremental_options.compact_at_dead_bytes_percent > 100)
            throw std::invalid_argument("invalid MPT version service configuration/checkpoint");
        if (checkpoint.versions.size() > options.retained_blocks)
            throw std::invalid_argument("public history checkpoint exceeds configured retained-block capacity");
        validate_history_metadata(checkpoint);
        Versions versions;
        versions.reserve(checkpoint.versions.size());
        for (std::size_t i = 0; i < checkpoint.versions.size(); ++i) {
            auto& saved = checkpoint.versions[i];
            CanonicalState canonical(std::move(saved.state));
            if (canonical.snapshot().accounts.root_hash() != saved.block.state_root)
                throw std::invalid_argument("public history checkpoint state root mismatch");
            if (saved.block.block_id == checkpoint.served_head) observed = saved.block;
            known.emplace(saved.block.block_id, saved.fingerprint);
            published.insert(saved.block.block_id);
            versions.push_back(std::make_shared<Version>(
                Version{saved.block, saved.fingerprint, std::move(canonical)}));
        }
        current = build(std::move(versions), checkpoint.served_head);
    }

    void require_idle_preparation() const {
        if (preparing || pending)
            throw std::logic_error("MPT replacement already preparing or awaiting publication");
    }
};

VersionService::VersionService(PublicCheckpoint checkpoint,
        ReplacementOptions options, GenerationLoader loader)
    : VersionService(single_history(std::move(checkpoint)), options, std::move(loader)) {}

VersionService::VersionService(PublicCheckpoint checkpoint,
        IncrementalOptions options, IncrementalLoader loader)
    : VersionService(single_history(std::move(checkpoint)), options, std::move(loader)) {}

VersionService::VersionService(PublicHistoryCheckpoint checkpoint,
        ReplacementOptions options, GenerationLoader loader) : impl_(std::make_unique<Impl>()) {
    impl_->options = options;
    impl_->loader = std::move(loader);
    impl_->initialize(std::move(checkpoint));
}

VersionService::VersionService(PublicHistoryCheckpoint checkpoint,
        IncrementalOptions options, IncrementalLoader loader) : impl_(std::make_unique<Impl>()) {
    impl_->options = options.service;
    impl_->incremental_options = options;
    impl_->incremental_loader = std::move(loader);
    impl_->initialize(std::move(checkpoint));
}

VersionService::~VersionService() = default;

ReplacementService::ReplacementService(PublicCheckpoint checkpoint,
        ReplacementOptions options, GenerationLoader loader)
    : VersionService(std::move(checkpoint), options, std::move(loader)) {}

ReplacementService::ReplacementService(PublicHistoryCheckpoint checkpoint,
        ReplacementOptions options, GenerationLoader loader)
    : VersionService(std::move(checkpoint), options, std::move(loader)) {}

IncrementalService::IncrementalService(PublicCheckpoint checkpoint,
        IncrementalOptions options, IncrementalLoader loader)
    : VersionService(std::move(checkpoint), options, std::move(loader)) {}

IncrementalService::IncrementalService(PublicHistoryCheckpoint checkpoint,
        IncrementalOptions options, IncrementalLoader loader)
    : VersionService(std::move(checkpoint), options, std::move(loader)) {}

bool VersionService::prepare(const MockBlockDelta& block) {
    auto& service = *impl_;
    const auto fingerprint = delta_fingerprint(block);
    const auto duplicate = service.known.find(block.block_id);
    if (duplicate != service.known.end()) {
        if (duplicate->second != fingerprint)
            throw std::invalid_argument("conflicting duplicate MPT block ID");
        if (service.published.count(block.block_id)) return false;
    }
    if (service.pending && service.pending->head == block.block_id) {
        const auto& staged = service.pending->versions[service.pending->index(block.block_id)];
        if (staged->fingerprint != fingerprint)
            throw std::invalid_argument("conflicting pending MPT block ID");
        return false;
    }
    service.require_idle_preparation();
    if (block.block_id == Hash{})
        throw std::invalid_argument("zero MPT block ID is reserved for the genesis parent");
    const auto parent = service.current->versions[service.current->index(block.parent_id)];
    if (parent->block.number == std::numeric_limits<std::uint64_t>::max() ||
        block.number != parent->block.number + 1)
        throw std::invalid_argument("MPT block number does not follow its parent");
    const auto ancestor = common_ancestor(*service.current, block.parent_id);
    if (!ancestor)
        throw std::out_of_range("MPT reorg ancestor was pruned; reload a public checkpoint");
    FlagGuard preparing(service.preparing);
    // Keep the replacement service's complete reference rebuild as a baseline.
    // Incremental construction path-copies canonical nodes even when capacity or
    // compaction requires loading a fresh ORAM generation afterward.
    auto canonical = service.incremental() ? parent->canonical.apply(block) :
        CanonicalState(apply_delta(parent->canonical.state(), block));
    auto version = std::make_shared<Version>(Version{
        header(block), fingerprint, std::move(canonical)});
    // Keep validated identities even when loading fails or a staged generation
    // is discarded. Identical unpublished delivery may retry; reuse may not.
    service.known.emplace(block.block_id, fingerprint);
    // This is the validated observed head even if subsequent map loading fails.
    service.observed = header(block);
    auto versions = service.current->versions;
    versions.push_back(version);
    if (versions.size() > service.options.retained_blocks)
        versions.erase(versions.begin(), versions.begin() +
                       (versions.size() - service.options.retained_blocks));
    auto replacement = service.stage(std::move(versions), block.block_id, version->canonical.snapshot());
    service.pending = std::move(replacement);
    service.ancestor = ancestor;
    return true;
}

void VersionService::prepare_reorg(const Hash& retained_head) {
    auto& service = *impl_;
    service.require_idle_preparation();
    const auto i = service.current->index(retained_head);
    const auto ancestor = common_ancestor(*service.current, retained_head);
    if (!ancestor)
        throw std::out_of_range("MPT reorg ancestor was pruned; reload a public checkpoint");
    FlagGuard preparing(service.preparing);
    service.observed = service.current->versions[i]->block;
    if (service.incremental() && service.current->backend->available) {
        auto staged = std::make_shared<Generation>();
        staged->id = service.current->id;
        staged->head = retained_head;
        staged->versions = service.current->versions;
        staged->packed = service.current->packed;
        staged->backend = service.current->backend;
        staged->appended_updates = service.current->appended_updates;
        service.pending = std::move(staged);
    } else {
        service.pending = service.build(service.current->versions, retained_head);
    }
    service.ancestor = ancestor;
}

void VersionService::prepare_compaction() {
    auto& service = *impl_;
    service.require_idle_preparation();
    FlagGuard preparing(service.preparing);
    service.pending = service.build(service.current->versions, service.current->head, true);
    service.ancestor = service.current->head;
}

bool VersionService::publish() {
    auto& service = *impl_;
    if (service.active || service.preparing || !service.pending) return false;
    FlagGuard preparing(service.preparing);
    // A read may have failed after append preparation. Its packed locators are
    // no longer reusable; recover the complete staged closure in fresh maps.
    if (service.pending->backend == service.current->backend &&
        !service.current->backend->available) {
        service.pending = service.build(service.pending->versions, service.pending->head);
    }
    // Allocate any identity bookkeeping before the no-throw publication swap.
    const auto& head = service.pending->versions[service.pending->index(service.pending->head)];
    // Extract a preallocated node: failed uploads must not mark this delivery
    // published and suppress a subsequent retry.
    std::set<Hash> identity;
    identity.insert(head->block.block_id);
    const bool shared = service.pending->backend == service.current->backend;
    if (shared) {
        auto& backend = *service.current->backend;
        auto* store = dynamic_cast<PageStore*>(backend.loaded.reader.get());
        if (!store) throw std::logic_error("MPT append has no writable store");
        const auto starts = backend.allocated_pages;
        bool any_upload = false;
        for (std::size_t t = 0; t < 3; ++t) {
            const auto size = service.pending->uploads[t].size();
            if (starts[t] > backend.capacities[t] || size > backend.capacities[t] - starts[t])
                throw std::logic_error("MPT staged upload exceeds preflight capacity");
            any_upload = any_upload || size != 0;
        }
        // Reserve the complete upload closure, including uncertain pages on
        // failure. No failed backend is ever used as a future deduplication base.
        for (std::size_t t = 0; t < 3; ++t)
            backend.allocated_pages[t] += service.pending->uploads[t].size();
        try {
            for (std::size_t t = 0; t < 3; ++t) {
                const auto& pages = service.pending->uploads[t];
                if (!pages.empty())
                    store->write_pages_batch(static_cast<Tier>(t), starts[t], pages);
            }
            if (any_upload) store->finish_pending_work();
        } catch (...) {
            backend.available = false;
            ++service.stats.failed_uploads;
            service.pending.reset();
            service.ancestor.reset();
            throw;
        }
        for (std::size_t t = 0; t < 3; ++t)
            service.stats.uploaded_pages[t] += service.pending->uploads[t].size();
        if (service.pending->append_update) ++service.stats.incremental_publications;
    } else {
        ++service.stats.replacement_publications;
        if (service.pending->compaction) ++service.stats.compactions;
    }
    service.published.insert(identity.extract(identity.begin()));
    service.current.swap(service.pending);
    service.pending.reset();
    for (auto& pages : service.current->uploads) std::vector<Page>().swap(pages);
    service.ancestor.reset();
    return true;
}

void VersionService::discard_pending() {
    if (impl_->preparing) throw std::logic_error("MPT generation is still preparing");
    impl_->pending.reset();
    impl_->ancestor.reset();
}

VersionedBatch VersionService::run(const Hash& block_id, BatchProfile profile,
        const std::vector<PathRequest>& requests) {
    auto& service = *impl_;
    if (service.active || service.preparing) throw std::logic_error("MPT batches must be serialized");
    if (!service.current->backend->available)
        throw std::runtime_error("MPT generation failed; publish a fresh replacement before reading");
    const auto pinned = service.current;
    const auto manifest = pinned->manifest(block_id);
    if (profile.requests == 0 || profile.requests > service.options.max_lanes ||
        profile.storage_slots > service.options.max_lanes / profile.requests ||
        requests.size() != profile.requests)
        throw std::invalid_argument("MPT batch exceeds public admission bounds");
    for (const auto& request : requests)
        if (request.storage_keys.size() != profile.storage_slots)
            throw std::invalid_argument("MPT request does not match its public storage count");
    BatchTraversal traversal(manifest.state_root, manifest.account_root, manifest.tiers, profile);
    FlagGuard active(service.active);
    try {
        return {manifest, traversal.run(*pinned->backend->loaded.reader, requests)};
    } catch (...) {
        // Conservatively treat an exception after traversal admission as fatal.
        // A failed backend cannot promise to complete the remaining dummy reads.
        pinned->backend->available = false;
        throw;
    }
}

BlockManifest VersionService::manifest(const Hash& block_id) const {
    return impl_->current->manifest(block_id);
}
BlockManifest VersionService::served_head() const { return manifest(impl_->current->head); }
BlockHeader VersionService::observed_head() const { return impl_->observed; }
std::optional<BlockManifest> VersionService::pending_head() const {
    if (!impl_->pending) return std::nullopt;
    return impl_->pending->manifest(impl_->pending->head);
}
std::optional<Hash> VersionService::pending_common_ancestor() const { return impl_->ancestor; }
std::vector<Hash> VersionService::retained_blocks() const {
    std::vector<Hash> result;
    for (const auto& version : impl_->current->versions)
        result.push_back(version->block.block_id);
    return result;
}
PublicCheckpoint VersionService::checkpoint() const {
    return impl_->current->versions[impl_->current->index(impl_->current->head)]->checkpoint();
}
PublicHistoryCheckpoint VersionService::history_checkpoint() const {
    PublicHistoryCheckpoint result;
    result.served_head = impl_->current->head;
    result.versions.reserve(impl_->current->versions.size());
    for (const auto& version : impl_->current->versions)
        result.versions.push_back(version->checkpoint());
    return result;
}
GenerationMemory VersionService::memory() const {
    GenerationMemory result;
    result.current_arena_bytes = impl_->current->backend->loaded.arena_bytes;
    result.current_page_bytes = impl_->current->backend->page_value_bytes();
    if (impl_->pending) {
        if (impl_->pending->backend != impl_->current->backend) {
            result.staged_arena_bytes = impl_->pending->backend->loaded.arena_bytes;
            result.staged_page_bytes = impl_->pending->backend->page_value_bytes();
        } else {
            for (std::size_t t = 0; t < 3; ++t) {
                const auto staged = impl_->pending->packed.pages[t].size();
                const auto reserved = impl_->current->backend->allocated_pages[t];
                // During publish(), reservations already count in current.
                if (staged > reserved) result.staged_page_bytes += (staged - reserved) * page_bytes;
            }
        }
    }
    result.peak_arena_bytes = impl_->peak_arena;
    result.peak_page_bytes = impl_->peak_pages;
    return result;
}
GenerationOccupancy VersionService::occupancy() const {
    return image_occupancy(impl_->current->packed, impl_->current->versions,
                           impl_->current->backend->capacities);
}
PublicBuilderMemory VersionService::public_builder_memory() const {
    PublicBuilderMemory result;
    std::set<const Generation*> generations;
    std::set<const Version*> versions;
    std::set<const Node*> nodes;
    for (const auto& generation : {impl_->current, impl_->pending}) {
        if (!generation || !generations.insert(generation.get()).second) continue;
        for (const auto& pages : generation->packed.pages)
            result.packed_image_bytes += pages.size() * page_bytes;
        for (const auto& pages : generation->uploads)
            result.staged_upload_bytes += pages.size() * page_bytes;
        for (const auto& version : generation->versions) {
            if (!versions.insert(version.get()).second) continue;
            ++result.retained_versions;
            for (const auto& account : version->canonical.state())
                result.public_state_bytes += 20 + 8 + 32 + 32 + account.second.storage.size() * 64;
            result.canonical_trie_rlp_bytes += node_rlp_bytes(version->canonical.snapshot().accounts.root, nodes);
            for (const auto& storage : version->canonical.snapshot().storage_tries)
                result.canonical_trie_rlp_bytes += node_rlp_bytes(storage.second.root, nodes);
        }
    }
    result.identity_bytes = impl_->known.size() * 64 + impl_->published.size() * 32;
    return result;
}
std::array<PackingStats, 3> VersionService::packing_stats() const {
    return impl_->current->packed.stats;
}
UpdateStats VersionService::update_stats() const { return impl_->stats; }
bool VersionService::batch_active() const { return impl_->active; }
bool VersionService::available() const { return impl_->current->backend->available; }

}  // namespace ethereum_mpt
