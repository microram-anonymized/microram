// Tests IncrementalService: stable-page appends pinned across both proof
// phases, retained reorgs, capacity fallback, upload/completion failure
// recovery, retention and compaction policies, and occupancy accounting.

#include "fixture.hpp"
#include "page_store.hpp"
#include "version.hpp"

#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("incremental test: ") + message);
}

template<class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::exception&) {
        return;
    }
    throw std::runtime_error(std::string("incremental test accepted: ") + message);
}

// Deliberately construct expected snapshots without going through apply_delta.
Snapshot reference_snapshot(const PublicState& state) {
    Snapshot snapshot;
    std::vector<Entry> accounts;
    for (const auto& [address, fields] : state) {
        std::vector<Entry> slots;
        for (const auto& [slot, value] : fields.storage)
            slots.push_back({keccak256(slot.data(), slot.size()), encode_storage(value)});
        const auto storage = build_trie(TrieKind::storage, slots);
        Account account;
        account.nonce = fields.nonce;
        account.balance = fields.balance;
        account.code_hash = fields.code_hash;
        account.storage_root = storage.root_hash();
        accounts.push_back({keccak256(address.data(), address.size()), encode_account(account)});
        if (storage.root) snapshot.storage_tries.emplace(storage.root_hash(), storage);
    }
    snapshot.accounts = build_trie(TrieKind::account, accounts);
    return snapshot;
}

struct BlockCase {
    MockBlockDelta delta;
    PublicState state;
};

BlockCase block(std::uint64_t id, const BlockCase* parent, std::uint64_t value) {
    BlockCase result;
    result.delta.block_id = word_from_u64(id + 2000);
    result.delta.parent_id = parent ? parent->delta.block_id : Hash{};
    result.delta.number = parent ? parent->delta.number + 1 : 0;
    for (std::uint8_t account_id : {1, 2}) {
        PublicAccountState fields;
        fields.nonce = value + account_id;
        fields.balance = word_from_u64(value * 1000 + account_id);
        fields.storage.emplace(word_from_u64(1), word_from_u64(value * 128));
        fields.storage.emplace(word_from_u64(2), word_from_u64(value * 256));
        result.state.emplace(fixture_address(account_id), fields);
        AccountUpsert update;
        update.address = fixture_address(account_id);
        update.nonce = fields.nonce;
        update.balance = fields.balance;
        update.code_hash = fields.code_hash;
        update.reset_storage = true;
        for (const auto& [slot, stored] : fields.storage)
            update.storage_changes.push_back({slot, stored});
        result.delta.account_upserts.push_back(std::move(update));
    }
    result.delta.expected_state_root = reference_snapshot(result.state).accounts.root_hash();
    return result;
}

BlockCase unchanged_child(std::uint64_t id, const BlockCase& parent) {
    BlockCase result;
    result.state = parent.state;
    result.delta.block_id = word_from_u64(id + 2000);
    result.delta.parent_id = parent.delta.block_id;
    result.delta.number = parent.delta.number + 1;
    result.delta.expected_state_root = parent.delta.expected_state_root;
    return result;
}

BlockCase account_child(std::uint64_t id, const BlockCase& parent) {
    auto result = unchanged_child(id, parent);
    auto& fields = result.state.at(fixture_address(1));
    fields.balance = word_from_u64(9999);
    result.delta.account_upserts.push_back({fixture_address(1), fields.nonce,
        fields.balance, fields.code_hash, false, {}});
    result.delta.expected_state_root = reference_snapshot(result.state).accounts.root_hash();
    return result;
}

std::vector<PathRequest> requests() {
    return {make_path_request(fixture_address(1), {word_from_u64(1), word_from_u64(99)}),
            make_path_request(fixture_address(2), {word_from_u64(1), word_from_u64(99)})};
}

struct WriteEvent {
    std::size_t store;
    Tier tier;
    std::uint64_t first;
    std::size_t count;
};

struct StoreControl {
    std::size_t loads = 0, live_stores = 0, reads = 0, finishes = 0;
    std::size_t fail_write_call = 0;
    bool fail_finish = false, fail_load = false;
    std::vector<WriteEvent> writes;
    std::vector<PackedGeneration> loaded_images;
    std::vector<std::size_t> read_stores;
    std::function<void(std::size_t)> on_read;
    std::function<void()> on_write;
};

// A public test backend. It enforces append-only writes, checks every declared
// capacity, and can fail after a partial mutation of otherwise shared backing.
class ImageStore final : public PageStore {
public:
    ImageStore(const PackedGeneration& image, std::array<std::size_t, 3> capacities,
               std::shared_ptr<StoreControl> control, std::size_t serial)
        : pages_(image.pages), capacities_(capacities), control_(std::move(control)), serial_(serial) {
        for (std::size_t tier = 0; tier < pages_.size(); ++tier)
            require(pages_[tier].size() <= capacities_[tier], "fresh image fits declared capacity");
        ++control_->live_stores;
    }
    ~ImageStore() override { --control_->live_stores; }

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        ++control_->reads;
        control_->read_stores.push_back(serial_);
        const auto hook = control_->on_read;
        if (hook) hook(control_->reads);
        const auto& pages = pages_[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            found[i] = static_cast<std::uint8_t>(ids[i] < pages.size());
            output[i] = found[i] ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }

    void write_pages_batch(Tier tier, std::uint64_t first, const std::vector<Page>& pages) override {
        if (control_->on_write) control_->on_write();
        const auto index = static_cast<std::size_t>(tier);
        auto& destination = pages_[index];
        require(!pages.empty() && first == destination.size(), "upload appends at sealed page boundary");
        require(first <= capacities_[index] && pages.size() <= capacities_[index] - first,
                "all writes fit their tier's public capacity");
        control_->writes.push_back({serial_, tier, first, pages.size()});
        for (const auto& page : pages) {
            destination.push_back(page);
            if (control_->fail_write_call == control_->writes.size()) {
                control_->fail_write_call = 0;
                throw std::runtime_error("injected partial shared-page upload failure");
            }
        }
    }

    void finish_pending_work() override {
        ++control_->finishes;
        if (control_->fail_finish) {
            control_->fail_finish = false;
            throw std::runtime_error("injected shared-page finish failure");
        }
    }

    std::array<std::size_t, 3> capacities() const override { return capacities_; }

private:
    std::array<std::vector<Page>, 3> pages_;
    std::array<std::size_t, 3> capacities_;
    std::shared_ptr<StoreControl> control_;
    std::size_t serial_;
};

IncrementalLoader loader(const std::shared_ptr<StoreControl>& control) {
    return [control](const PackedGeneration& image, std::size_t max_lanes,
                     const std::array<std::size_t, 3>& capacities) {
        require(max_lanes == 8, "loader receives configured lane capacity");
        auto reader = std::make_unique<ImageStore>(image, capacities, control, ++control->loads);
        if (control->fail_load) {
            control->fail_load = false;
            throw std::runtime_error("injected fresh-map load failure");
        }
        control->loaded_images.push_back(image);
        std::size_t arena_bytes = 4096;
        for (const auto capacity : capacities) arena_bytes += capacity * page_bytes * 3;
        return LoadedGeneration{std::move(reader), arena_bytes};
    };
}

GenerationLoader replacement_loader(const std::shared_ptr<StoreControl>& control) {
    const auto load = loader(control);
    return [load](const PackedGeneration& image, std::size_t max_lanes) {
        std::array<std::size_t, 3> capacities{};
        for (std::size_t tier = 0; tier < capacities.size(); ++tier)
            capacities[tier] = image.pages[tier].size();
        return load(image, max_lanes, capacities);
    };
}

IncrementalOptions options(std::size_t retained = 4) {
    IncrementalOptions result;
    result.service = ReplacementOptions{TierProfile{1, 1}, retained, 8};
    result.page_headroom = {32, 32, 32};
    result.compact_after_updates = 0;
    return result;
}

void accept(VersionService& service, const MockBlockDelta& next) {
    require(service.prepare(next), "new block prepares");
    require(service.publish(), "prepared block publishes at a complete batch boundary");
    require(service.served_head().block_id == next.block_id, "publication selects intended head");
}

bool same_occupancy(const GenerationOccupancy& a, const GenerationOccupancy& b) {
    return a.allocated_pages == b.allocated_pages && a.page_capacities == b.page_capacities &&
           a.live_record_bytes == b.live_record_bytes && a.dead_record_bytes == b.dead_record_bytes;
}

GenerationOccupancy check_occupancy(VersionService& service) {
    std::vector<Snapshot> snapshots;
    for (const auto& version : service.history_checkpoint().versions)
        snapshots.push_back(reference_snapshot(version.state));
    const auto closure = pack_generation(snapshots, service.served_head().tiers);
    const auto actual = service.occupancy();
    const auto allocated = service.packing_stats();
    for (std::size_t t = 0; t < 3; ++t) {
        require(actual.live_record_bytes[t] == closure.stats[t].record_bytes &&
                actual.live_record_bytes[t] + actual.dead_record_bytes[t] == allocated[t].record_bytes,
                "occupancy counts exactly the freshly packed retained closure and historical records");
        require(actual.allocated_pages[t] == allocated[t].real_pages + allocated[t].dummy_pages &&
                actual.allocated_pages[t] <= actual.page_capacities[t],
                "occupancy includes allocated dummy pages within public capacity");
        if (closure.pages[t].empty())
            require(actual.allocated_pages[t] == 0 && actual.page_capacities[t] == 0 &&
                    actual.live_record_bytes[t] == 0 && actual.dead_record_bytes[t] == 0,
                    "disabled tiers have zero occupancy");
    }
    return actual;
}

VersionedBatch check_batch(VersionService& service, const BlockCase& expected) {
    const auto paths = requests();
    auto result = service.run(expected.delta.block_id, BatchProfile{2, 2}, paths);
    const auto snapshot = reference_snapshot(expected.state);
    require(result.manifest.state_root == expected.delta.expected_state_root &&
            result.manifest.block_id == expected.delta.block_id, "batch carries intended root and block");
    require(result.proofs.accounts.size() == 2 && result.proofs.storage.size() == 4,
            "fixed account and storage proof shape");
    const auto empty_storage = build_trie(TrieKind::storage, {});
    for (std::size_t q = 0; q < paths.size(); ++q) {
        const auto& account = result.proofs.accounts[q];
        const auto proof = decode_proof(account.proof);
        require(account.error == 0 && proof == prove(snapshot.accounts, paths[q].account_key),
                "account proof equals independent public reference");
        const auto encoded = verify_proof(TrieKind::account, result.manifest.state_root,
                                          paths[q].account_key, proof);
        require((account.present != 0) == encoded.has_value(), "account proof authenticates membership");
        const auto fields = encoded ? decode_account(*encoded) : Account{};
        if (encoded)
            require(account.nonce == fields.nonce && account.balance == fields.balance &&
                    account.code_hash == fields.code_hash && account.storage_root == fields.storage_root,
                    "decoded account matches authenticated fields");
        const auto& storage = fields.storage_root == empty_trie_root()
            ? empty_storage : snapshot.storage_tries.at(fields.storage_root);
        for (std::size_t slot = 0; slot < 2; ++slot) {
            const auto& item = result.proofs.storage[q * 2 + slot];
            const auto proof = decode_proof(item.proof);
            require(item.error == 0 && proof == prove(storage, paths[q].storage_keys[slot]),
                    "storage proof equals independent public reference");
            const auto encoded = verify_proof(TrieKind::storage, fields.storage_root,
                                              paths[q].storage_keys[slot], proof);
            require((item.present != 0) == encoded.has_value() &&
                    item.storage_value == (encoded ? decode_storage(*encoded) : Word{}),
                    "storage proof authenticates the account's selected version");
        }
    }
    return result;
}

void test_append_pins_both_phases_and_old_locators() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto old_head = block(2, &first, 3);
    const auto fork = block(3, &first, 4);
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    const auto genesis_manifest = service.served_head();
    accept(service, first.delta);
    accept(service, old_head.delta);
    const auto old_manifest = service.served_head();
    const auto writes = control->writes.size();
    control->reads = 0;
    control->read_stores.clear();
    bool injected = false;
    std::size_t expected_page_bytes = 0;
    control->on_write = [&] {
        require(!service.batch_active(), "shared writes wait for full batch boundary");
        const auto memory = service.memory();
        require(memory.current_page_bytes + memory.staged_page_bytes == expected_page_bytes,
                "upload reservations and staged pages are never counted twice");
    };
    control->on_read = [&](std::size_t call) {
        if (call != proof_rounds + 1) return;
        injected = true;
        require(service.batch_active(), "batch remains pinned at first storage read");
        require(service.prepare(fork.delta), "fork prepares between account and storage phases");
        const auto memory = service.memory();
        expected_page_bytes = memory.current_page_bytes + memory.staged_page_bytes;
        require(control->writes.size() == writes && control->loads == 1,
                "public append packing neither uploads nor loads maps during prepare");
        require(service.pending_common_ancestor() == std::optional<Hash>{first.delta.block_id},
                "staged fork identifies retained common ancestor");
        require(!service.publish() && control->writes.size() == writes,
                "publication refuses shared upload while the complete batch is active");
        require(service.served_head().block_id == old_head.delta.block_id &&
                service.served_head().account_root == old_manifest.account_root,
                "preparation preserves pinned head and locator");
        reject([&] { service.manifest(fork.delta.block_id); }, "staged fork manifest");
    };
    check_batch(service, old_head);
    control->on_read = {};
    require(injected && control->reads == 2 * proof_rounds && !service.batch_active(),
            "both fixed phases complete before publication");
    require(std::all_of(control->read_stores.begin(), control->read_stores.end(),
                        [](std::size_t serial) { return serial == 1; }),
            "account and storage phases share original backend");
    require(service.publish() && control->writes.size() > writes && control->finishes >= 3,
            "publication uploads then finishes shared append work");
    require(service.served_head().generation == genesis_manifest.generation &&
            service.manifest(genesis.delta.block_id).account_root == genesis_manifest.account_root &&
            service.manifest(old_head.delta.block_id).account_root == old_manifest.account_root,
            "append keeps generation ID and retained root locators stable");
    const auto stats = service.update_stats();
    require(stats.incremental_publications == 3 && stats.replacement_publications == 0 &&
            stats.failed_uploads == 0 && stats.compactions == 0, "append publication counters");
    std::array<std::size_t, 3> uploaded{};
    for (const auto& event : control->writes) uploaded[static_cast<std::size_t>(event.tier)] += event.count;
    require(stats.uploaded_pages == uploaded, "per-tier counters equal actual successful page uploads");
    check_batch(service, genesis);
    check_batch(service, fork);
}

void test_noop_discard_invalid_root_and_retained_reorg() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto same_root = unchanged_child(2, first);
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    const auto initial_builder = service.public_builder_memory();
    auto invalid = first.delta;
    invalid.expected_state_root.front() ^= 1;
    reject([&] { service.prepare(invalid); }, "incorrect expected root");
    require(control->loads == 1 && control->writes.empty() && !service.pending_head() && service.available(),
            "root validation fails before staging or touching maps");
    require(service.prepare(first.delta), "append can stage before cancellation");
    const auto staged_builder = service.public_builder_memory();
    const auto staged_backend = service.memory();
    require(staged_builder.retained_versions == 2 &&
            staged_builder.public_state_bytes == 2 * initial_builder.public_state_bytes &&
            staged_builder.staged_upload_bytes == staged_backend.staged_page_bytes &&
            staged_builder.staged_upload_bytes > 0 && staged_backend.staged_arena_bytes == 0 &&
            staged_builder.packed_image_bytes == 2 * initial_builder.packed_image_bytes +
                                                   staged_builder.staged_upload_bytes,
            "append shares its backend but retains both full public images and a separate upload copy");
    service.discard_pending();
    const auto discarded_builder = service.public_builder_memory();
    require(discarded_builder.retained_versions == initial_builder.retained_versions &&
            discarded_builder.public_state_bytes == initial_builder.public_state_bytes &&
            discarded_builder.canonical_trie_rlp_bytes == initial_builder.canonical_trie_rlp_bytes &&
            discarded_builder.packed_image_bytes == initial_builder.packed_image_bytes &&
            discarded_builder.staged_upload_bytes == 0,
            "discard releases appended public image, snapshot and upload copy");
    require(control->writes.empty() && control->loads == 1 && !service.pending_head() && !service.publish(),
            "discarding append has no shared-map side effects");
    accept(service, first.delta);
    const auto published_builder = service.public_builder_memory();
    require(published_builder.packed_image_bytes == service.memory().current_page_bytes &&
            published_builder.staged_upload_bytes == 0,
            "successful append releases old packed image and completed upload copy");
    const auto first_manifest = service.served_head();
    const auto writes = control->writes.size();
    accept(service, same_root.delta);
    require(service.public_builder_memory().canonical_trie_rlp_bytes ==
            published_builder.canonical_trie_rlp_bytes,
            "unchanged roots share the canonical graph across distinct retained blocks");
    require(control->writes.size() == writes && control->loads == 1 &&
            service.served_head().account_root == first_manifest.account_root &&
            service.served_head().generation == first_manifest.generation,
            "distinct block with unchanged root reuses all records without writes");
    require(!service.prepare(same_root.delta) && !service.pending_head(), "duplicate append is idempotent");
    const auto retained = service.retained_blocks();
    const auto publications = service.update_stats().incremental_publications;
    service.prepare_reorg(first.delta.block_id);
    require(control->loads == 1 && control->writes.size() == writes && service.publish(),
            "retained ancestor switch reuses current backend without uploads");
    require(service.retained_blocks() == retained && service.served_head().generation == first_manifest.generation &&
            service.update_stats().incremental_publications == publications,
            "ancestor switch preserves retention and new-block publication counter");
    check_batch(service, same_root);
}

void test_incremental_canonical_paths_share_retained_nodes() {
    const auto genesis = block(0, nullptr, 1);
    auto changed = unchanged_child(1, genesis);
    auto& fields = changed.state.at(fixture_address(1));
    fields.balance = word_from_u64(9999);
    changed.delta.account_upserts.push_back({fixture_address(1), fields.nonce,
        fields.balance, fields.code_hash, false, {}});
    changed.delta.expected_state_root = reference_snapshot(changed.state).accounts.root_hash();
    const auto append_control = std::make_shared<StoreControl>();
    const auto replace_control = std::make_shared<StoreControl>();
    IncrementalService append(genesis_checkpoint(genesis.delta), options(), loader(append_control));
    ReplacementService replace(genesis_checkpoint(genesis.delta), options().service,
                               replacement_loader(replace_control));
    const auto initial = append.public_builder_memory().canonical_trie_rlp_bytes;
    accept(append, changed.delta);
    accept(replace, changed.delta);
    require(append.public_builder_memory().canonical_trie_rlp_bytes > initial &&
            append.public_builder_memory().canonical_trie_rlp_bytes <
                replace.public_builder_memory().canonical_trie_rlp_bytes,
            "changed account paths retain shared sibling and storage nodes across versions");
    for (const BlockCase* expected : std::array<const BlockCase*, 2>{&genesis, &changed}) {
        check_batch(append, *expected);
        check_batch(replace, *expected);
    }
}

void test_capacity_fallback_and_failed_fresh_load() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    auto settings = options();
    // Only one tier lacks space: the coordinator must check all tiers before
    // beginning any shared write, even if earlier tiers have ample headroom.
    settings.page_headroom = {32, 0, 32};
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), settings, loader(control));
    const auto old_manifest = service.served_head();
    control->fail_load = true;
    reject([&] { service.prepare(next.delta); }, "capacity fallback fresh-map load failure");
    require(control->loads == 2 && control->live_stores == 1 && control->writes.empty() &&
            service.available() && !service.pending_head() &&
            service.served_head().generation == old_manifest.generation,
            "failed fresh fallback preserves usable original maps without partial uploads");
    control->fail_finish = true;
    reject([&] { service.prepare(next.delta); }, "fresh replacement finish failure");
    require(control->loads == 3 && control->live_stores == 1 && control->writes.empty() &&
            service.available() && !service.pending_head() &&
            service.served_head().generation == old_manifest.generation,
            "fresh loading must finish successfully before staging a replacement");
    check_batch(service, genesis);
    require(service.prepare(next.delta) && control->loads == 4 && control->writes.empty(),
            "capacity retry fully loads replacement before touching served maps");
    require(service.memory().staged_arena_bytes != 0 && control->live_stores == 2,
            "fallback accounts for simultaneously staged and served maps");
    require(service.publish() && control->live_stores == 1 &&
            service.served_head().generation != old_manifest.generation,
            "capacity fallback publishes a fresh generation");
    require(service.update_stats().replacement_publications == 1 &&
            service.update_stats().compactions == 1 && service.update_stats().failed_uploads == 0,
            "failed load is not an upload failure or a successful compaction");
    check_batch(service, next);
}

void test_partial_upload_and_finish_failures_require_fresh_recovery() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    for (const bool fail_finish : {false, true}) {
        const auto control = std::make_shared<StoreControl>();
        IncrementalService service(genesis_checkpoint(genesis.delta), options(), loader(control));
        const auto old_manifest = service.served_head();
        require(service.prepare(next.delta) && control->writes.empty(), "failure case prepares without writes");
        const auto staged_memory = service.memory();
        control->fail_write_call = fail_finish ? 0 : 2;
        control->fail_finish = fail_finish;
        reject([&] { service.publish(); }, "partial upload or finish exception");
        require(control->writes.size() >= 2 &&
                control->writes[0].tier != control->writes[1].tier,
                "injected failure follows actual writes across multiple tiers");
        require(!service.available() && !service.pending_head() && !service.publish() &&
                service.served_head().block_id == genesis.delta.block_id &&
                service.served_head().generation == old_manifest.generation,
                "failed shared mutation clears pending without publishing and invalidates generation");
        require(service.update_stats().failed_uploads == 1 &&
                service.update_stats().incremental_publications == 0 &&
                service.update_stats().uploaded_pages == std::array<std::size_t, 3>{},
                "failed append is counted without recording publication");
        require(service.memory().current_page_bytes == staged_memory.current_page_bytes +
                    staged_memory.staged_page_bytes && service.memory().staged_page_bytes == 0,
                "failed closure reservations remain counted after staging is cleared");
        reject([&] { service.manifest(next.delta.block_id); }, "failed upload manifest");
        const auto reads = control->reads;
        reject([&] { service.run(genesis.delta.block_id, BatchProfile{2, 2}, requests()); },
               "potentially damaged maps cannot serve proofs");
        require(control->reads == reads, "unavailable generation rejects proof before backend access");
        const auto writes = control->writes.size();
        require(service.prepare(next.delta) && control->loads == 2 && control->writes.size() == writes,
                "retry of identical validated block stages fresh maps instead of reusing partial pages");
        require(service.publish() && service.available() && control->live_stores == 1 &&
                service.served_head().generation != old_manifest.generation,
                "fresh recovery retires damaged backend");
        require(service.update_stats().replacement_publications == 1 && service.update_stats().compactions == 0,
                "fresh failure recovery is a replacement, not scheduled compaction");
        check_batch(service, genesis);
        check_batch(service, next);
    }
}

void test_read_failure_after_append_preparation_reloads_before_publication() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    const auto generation = service.served_head().generation;
    control->on_read = [&](std::size_t call) {
        if (call != proof_rounds + 1) return;
        require(service.prepare(next.delta), "next append stages before storage-phase read failure");
        throw std::runtime_error("injected storage-phase read failure");
    };
    reject([&] { service.run(genesis.delta.block_id, BatchProfile{2, 2}, requests()); },
           "reader failure with an already prepared append");
    control->on_read = {};
    require(!service.available() && !service.batch_active() && service.pending_head() &&
            control->writes.empty() && control->loads == 1,
            "read failure invalidates shared backend even when append was previously prepared");
    require(service.publish() && control->loads == 2 && control->writes.empty() &&
            service.available() && service.served_head().generation != generation,
            "pending append rebuilds its complete closure before publishing after read failure");
    require(service.update_stats().incremental_publications == 0 &&
            service.update_stats().replacement_publications == 1,
            "read recovery never counts an upload to the damaged backend");
    check_batch(service, next);
}

void test_retention_compaction_and_periodic_threshold() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto second = block(2, &first, 3);
    const auto third = block(3, &second, 4);
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), options(2), loader(control));
    accept(service, first.delta);
    accept(service, second.delta);
    accept(service, third.delta);
    const auto retained = std::vector<Hash>{second.delta.block_id, third.delta.block_id};
    require(service.retained_blocks() == retained && control->loads == 1,
            "manifest retention prunes while append generation remains cumulative");
    reject([&] { service.manifest(first.delta.block_id); }, "pruned root admission");
    const auto old_manifest = service.served_head();
    const auto old_bytes = service.memory().current_page_bytes;
    const auto old_builder = service.public_builder_memory();
    const auto old_stats = service.packing_stats();
    std::size_t old_stats_bytes = 0;
    for (const auto& stats : old_stats) old_stats_bytes += stats.page_value_bytes();
    require(old_builder.retained_versions == 2 &&
            old_builder.public_state_bytes == 4 * (92 + 2 * 64) &&
            old_builder.packed_image_bytes == old_bytes && old_stats_bytes == old_bytes,
            "retention releases public snapshots while packing statistics include historical pages");
    const auto writes = control->writes.size();
    service.prepare_compaction();
    require(control->loads == 2 && control->writes.size() == writes &&
            service.served_head().generation == old_manifest.generation,
            "explicit compaction loads separate maps without publishing or touching old maps");
    const auto& compacted = control->loaded_images.back();
    const auto staged_builder = service.public_builder_memory();
    require(staged_builder.retained_versions == old_builder.retained_versions &&
            staged_builder.public_state_bytes == old_builder.public_state_bytes &&
            staged_builder.canonical_trie_rlp_bytes == old_builder.canonical_trie_rlp_bytes &&
            staged_builder.staged_upload_bytes == 0 &&
            staged_builder.packed_image_bytes == old_builder.packed_image_bytes +
                                                 compacted.total_stats().page_value_bytes(),
            "compaction shares retained versions while retaining both packed images");
    require(compacted.roots.size() == 2 &&
            compacted.roots[0].state_root == second.delta.expected_state_root &&
            compacted.roots[1].state_root == third.delta.expected_state_root &&
            compacted.total_stats().page_value_bytes() < old_bytes,
            "compaction reclaims pruned roots and sealed-run tail pages");
    check_batch(service, third);
    require(service.publish() && service.retained_blocks() == retained &&
            service.served_head().generation != old_manifest.generation &&
            service.memory().current_page_bytes < old_bytes && service.update_stats().compactions == 1,
            "compaction publishes exact retained roots with smaller public image");
    const auto compacted_builder = service.public_builder_memory();
    require(compacted_builder.public_state_bytes == old_builder.public_state_bytes &&
            compacted_builder.canonical_trie_rlp_bytes == old_builder.canonical_trie_rlp_bytes &&
            compacted_builder.packed_image_bytes == compacted.total_stats().page_value_bytes() &&
            compacted_builder.packed_image_bytes < old_builder.packed_image_bytes &&
            compacted_builder.identity_bytes == old_builder.identity_bytes,
            "compaction reclaims historical packed payload without pruning retained snapshots or identities");
    check_batch(service, second);

    auto settings = options();
    settings.compact_after_updates = 2;
    const auto periodic = std::make_shared<StoreControl>();
    IncrementalService scheduled(genesis_checkpoint(genesis.delta), settings, loader(periodic));
    const auto initial_generation = scheduled.served_head().generation;
    accept(scheduled, first.delta);
    accept(scheduled, second.delta);
    require(periodic->loads == 1 && scheduled.update_stats().incremental_publications == 2,
            "periodic interval permits exactly its configured incremental publications");
    const auto before_writes = periodic->writes.size();
    require(scheduled.prepare(third.delta) && periodic->loads == 2 &&
            periodic->writes.size() == before_writes &&
            scheduled.served_head().generation == initial_generation,
            "next distinct update stages periodic rebuild before further shared uploads");
    require(scheduled.publish() && scheduled.served_head().generation != initial_generation &&
            scheduled.update_stats().compactions == 1 &&
            scheduled.update_stats().replacement_publications == 1,
            "periodic replacement publishes and records compaction");
    const auto fourth = block(4, &third, 5);
    accept(scheduled, fourth.delta);
    require(periodic->loads == 2 && scheduled.update_stats().incremental_publications == 3,
            "periodic replacement resets interval for subsequent appends");
}

void test_occupancy_tracks_records_across_retained_roots() {
    const auto genesis = block(0, nullptr, 1);
    const auto changed = account_child(1, genesis);
    const auto duplicate = unchanged_child(2, changed);
    auto settings = options(2);
    settings.service.tiers = {0, 0};
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), settings, loader(control));
    require(control->loaded_images.front().pages[2].size() == 2,
            "mixed-live/dead fixture initially stores every record on one real bulk page");
    const auto initial = check_occupancy(service);
    require(initial.dead_record_bytes == std::array<std::size_t, 3>{},
            "fresh image contains no unreachable records");
    accept(service, changed.delta);
    const auto retained = check_occupancy(service);
    require(retained.dead_record_bytes == std::array<std::size_t, 3>{},
            "old root records remain live while any retained block references them");
    const auto writes = control->writes.size();
    accept(service, duplicate.delta);
    const auto pruned = check_occupancy(service);
    require(pruned.allocated_pages == retained.allocated_pages &&
            pruned.dead_record_bytes[2] > 0 &&
            pruned.dead_record_bytes[2] < initial.live_record_bytes[2] &&
            control->loads == 1 && control->writes.size() == writes && control->reads == 0,
            "no-op pruning splits original page records into live and dead without backend access");
    // The surviving account and shared storage remain on the original page;
    // the changed account/root die there. Equal retained roots count only once.
    check_batch(service, changed);
    check_batch(service, duplicate);
    service.prepare_compaction();
    require(same_occupancy(service.occupancy(), pruned),
            "staged compaction is excluded from published occupancy");
    require(service.publish(), "occupancy fixture compaction publishes");
    const auto compacted = check_occupancy(service);
    require(compacted.dead_record_bytes == std::array<std::size_t, 3>{} &&
            compacted.live_record_bytes == pruned.live_record_bytes,
            "compaction reclaims dead records while preserving the deduplicated live closure");
}

void test_fullness_threshold_preflight_and_pinning() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    auto settings = options();
    const auto initial_image = pack_generation({reference_snapshot(genesis.state)}, settings.service.tiers);
    const auto proposed = append_generation(initial_image, {reference_snapshot(next.state)});
    settings.compact_at_fullness_percent = 50;
    // Equality at 50% in bulk, including its dummy page, must trigger before
    // writes to any earlier tier. Every tier still fits its hard capacity.
    settings.page_headroom = {64, 64,
        2 * proposed.pages[2].size() - initial_image.pages[2].size()};
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), settings, loader(control));
    const auto original = check_occupancy(service);
    const auto generation = service.served_head().generation;
    control->fail_load = true;
    reject([&] { service.prepare(next.delta); }, "fullness-triggered fresh-map load failure");
    require(control->loads == 2 && control->live_stores == 1 && control->writes.empty() &&
            !service.pending_head() && service.available() &&
            same_occupancy(service.occupancy(), original),
            "failed fullness compaction leaves original served occupancy and maps intact");
    bool staged = false;
    control->on_read = [&](std::size_t call) {
        if (call != proof_rounds + 1) return;
        staged = true;
        require(service.prepare(next.delta) && control->loads == 3 && control->live_stores == 2 &&
                control->writes.empty() && !service.publish() &&
                service.served_head().generation == generation &&
                same_occupancy(service.occupancy(), original),
                "fullness compaction stages fresh maps but keeps both proof phases pinned");
    };
    check_batch(service, genesis);
    control->on_read = {};
    require(staged, "fullness compaction was prepared during the storage phase");
    service.discard_pending();
    require(control->live_stores == 1 && !service.pending_head() &&
            service.update_stats().compactions == 0 && same_occupancy(service.occupancy(), original),
            "discarded fullness compaction releases staged maps without changing published state");
    accept(service, next.delta);
    require(control->loads == 4 && control->writes.empty() &&
            service.served_head().generation != generation && service.update_stats().compactions == 1 &&
            service.update_stats().replacement_publications == 1,
            "fullness threshold publishes a fresh generation without shared writes");
    check_occupancy(service);
    check_batch(service, genesis);
    check_batch(service, next);

    settings = options();
    settings.page_headroom = {0, 0, 0};
    settings.compact_at_fullness_percent = 100;
    const auto noop_control = std::make_shared<StoreControl>();
    IncrementalService noop(genesis_checkpoint(genesis.delta), settings, loader(noop_control));
    accept(noop, unchanged_child(2, genesis).delta);
    require(noop_control->loads == 1 && noop_control->writes.empty(),
            "full tiers without new pages do not force no-op compaction");

    settings.page_headroom = {64, 0, 64};
    const auto unchanged_tier = std::make_shared<StoreControl>();
    IncrementalService partial(genesis_checkpoint(genesis.delta), settings, loader(unchanged_tier));
    const auto changed = account_child(3, genesis);
    accept(partial, changed.delta);
    require(unchanged_tier->loads == 1 && !unchanged_tier->writes.empty(),
            "full unchanged storage tier does not compact account-only appends");
    check_occupancy(partial);
}

void test_dead_byte_thresholds_and_configuration() {
    const auto genesis = block(0, nullptr, 1);
    const auto changed = account_child(1, genesis);
    const auto duplicate = unchanged_child(2, changed);
    auto settings = options(2);
    settings.compact_at_dead_bytes_percent = 1;
    const auto control = std::make_shared<StoreControl>();
    IncrementalService service(genesis_checkpoint(genesis.delta), settings, loader(control));
    accept(service, changed.delta);
    require(control->loads == 1 &&
            check_occupancy(service).dead_record_bytes == std::array<std::size_t, 3>{},
            "dead-byte policy counts all retained roots and ignores page slack and dummy pages");
    const auto writes = control->writes.size();
    const auto before = service.occupancy();
    require(service.prepare(duplicate.delta) && control->loads == 2 &&
            control->writes.size() == writes && same_occupancy(service.occupancy(), before),
            "no-op pruning can stage dead-byte compaction before publishing retention changes");
    require(service.publish() && service.update_stats().compactions == 1 &&
            check_occupancy(service).dead_record_bytes == std::array<std::size_t, 3>{},
            "dead-byte threshold reclaims newly unreachable retained-root records");
    check_batch(service, changed);
    check_batch(service, duplicate);

    settings = options(1);
    settings.compact_at_dead_bytes_percent = 100;
    const auto empty_control = std::make_shared<StoreControl>();
    IncrementalService emptied(genesis_checkpoint(genesis.delta), settings, loader(empty_control));
    accept(emptied, changed.delta);
    require(empty_control->loads == 1 && check_occupancy(emptied).dead_record_bytes[0] > 0,
            "dead fraction below 100 percent leaves partially live records in place");
    auto empty = unchanged_child(3, changed);
    empty.state.clear();
    empty.delta.account_deletions = {fixture_address(1), fixture_address(2)};
    empty.delta.expected_state_root = empty_trie_root();
    const auto old_writes = empty_control->writes.size();
    accept(emptied, empty.delta);
    const auto occupancy = check_occupancy(emptied);
    require(empty_control->loads == 2 && empty_control->writes.size() == old_writes &&
            occupancy.live_record_bytes == std::array<std::size_t, 3>{} &&
            occupancy.dead_record_bytes == std::array<std::size_t, 3>{} &&
            occupancy.allocated_pages == std::array<std::size_t, 3>{1, 1, 1},
            "100-percent dead closure compacts to configured dummy pages only");
    accept(emptied, unchanged_child(4, empty).delta);
    require(empty_control->loads == 2 && empty_control->writes.size() == old_writes,
            "empty record denominator never triggers another dead-byte compaction");
    check_batch(emptied, unchanged_child(4, empty));

    for (const bool fullness : {false, true}) {
        auto invalid = options();
        if (fullness) invalid.compact_at_fullness_percent = 101;
        else invalid.compact_at_dead_bytes_percent = 101;
        const auto rejected = std::make_shared<StoreControl>();
        reject([&] { IncrementalService bad(genesis_checkpoint(genesis.delta), invalid, loader(rejected)); },
               "compaction percentage above 100");
        require(rejected->loads == 0, "invalid compaction thresholds reject before loader invocation");
    }
}

void test_history_restart_rebuilds_retained_closure_and_resumes_appends() {
    const auto genesis = block(0, nullptr, 1);
    const auto ancestor = block(1, &genesis, 2);
    const auto left = block(2, &ancestor, 3);
    const auto left_child = block(3, &left, 4);
    const auto right = block(4, &ancestor, 5);
    const auto next = block(5, &right, 6);
    const auto control = std::make_shared<StoreControl>();
    PublicHistoryCheckpoint saved;
    std::size_t old_bytes = 0;
    {
        IncrementalService original(genesis_checkpoint(genesis.delta), options(), loader(control));
        for (const auto* version : {&ancestor, &left, &left_child, &right}) accept(original, version->delta);
        original.prepare_reorg(left.delta.block_id);
        require(original.publish(), "restart fixture selects an older retained head");
        const auto writes = control->writes.size();
        require(original.prepare(next.delta) && control->writes.size() == writes,
                "restart fixture contains unpublished append pages");
        saved = original.history_checkpoint();
        old_bytes = original.memory().current_page_bytes;
        require(saved.versions.size() == 4 && saved.served_head == left.delta.block_id,
                "incremental checkpoint excludes append pages and pending head");
    }
    require(control->live_stores == 0, "public history owns no previous incremental backend");
    const auto loads = control->loads;
    const auto writes = control->writes.size();
    reject([&] { IncrementalService rejected(saved, options(3), loader(control)); },
           "retained history exceeds incremental service capacity");
    auto malformed = saved;
    malformed.versions.front().block.state_root.front() ^= 1;
    reject([&] { IncrementalService rejected(malformed, options(), loader(control)); },
           "nonhead root mismatch in incremental restart");
    require(control->loads == loads && control->writes.size() == writes,
            "incremental history preflight failures never reach loaders or stores");

    IncrementalService restored(saved, options(), loader(control));
    require(control->loads == loads + 1 && control->live_stores == 1 &&
            control->writes.size() == writes && !restored.pending_head() &&
            restored.served_head().block_id == left.delta.block_id &&
            restored.observed_head().block_id == left.delta.block_id &&
            restored.retained_blocks() == std::vector<Hash>{ancestor.delta.block_id,
                left.delta.block_id, left_child.delta.block_id, right.delta.block_id},
            "incremental restart freshly loads saved publication order and served head");
    const auto& packed = control->loaded_images.back();
    require(packed.roots.size() == 4 && restored.memory().current_page_bytes < old_bytes &&
            restored.public_builder_memory().identity_bytes == 4 * 96,
            "fresh restart drops historical pages and tombstones beyond saved versions");
    for (const auto* version : {&ancestor, &left, &left_child, &right}) {
        check_batch(restored, *version);
        require(!restored.prepare(version->delta), "all restored incremental identities remain published");
    }
    reject([&] { restored.manifest(genesis.delta.block_id); }, "restart does not revive pruned blocks");
    reject([&] { restored.manifest(next.delta.block_id); }, "restart does not publish pending append");
    const auto generation = restored.served_head().generation;
    restored.prepare_reorg(right.delta.block_id);
    require(restored.pending_common_ancestor() == std::optional<Hash>{ancestor.delta.block_id} &&
            restored.publish() && restored.served_head().generation == generation &&
            control->loads == loads + 1 && control->writes.size() == writes,
            "restored retained reorg selects head without fresh maps or writes");
    accept(restored, next.delta);
    require(control->loads == loads + 1 && control->writes.size() > writes &&
            restored.update_stats().incremental_publications == 1 &&
            restored.update_stats().replacement_publications == 0 &&
            restored.retained_blocks() == std::vector<Hash>{left.delta.block_id,
                left_child.delta.block_id, right.delta.block_id, next.delta.block_id},
            "restored store reserves headroom for resumed appends and FIFO retention");
    check_batch(restored, next);
    check_batch(restored, left_child);
}

void test_independent_block_fixtures_match_replacement_proofs() {
    std::ifstream input(ETHEREUM_MPT_BLOCK_FIXTURES);
    require(bool(input), "independent block fixture file opens");
    const auto deltas = load_mock_blocks(input);
    require(deltas.size() == 8, "independent fixture count");
    auto settings = options(deltas.size());
    settings.page_headroom = {64, 64, 64};
    const auto append_control = std::make_shared<StoreControl>();
    const auto replace_control = std::make_shared<StoreControl>();
    IncrementalService append(genesis_checkpoint(deltas.front()), settings, loader(append_control));
    ReplacementService replace(genesis_checkpoint(deltas.front()), settings.service,
                               replacement_loader(replace_control));
    std::map<Hash, PublicState> states;
    for (std::size_t i = 0; i < deltas.size(); ++i) {
        const auto& delta = deltas[i];
        const auto parent = i == 0 ? PublicState{} : states.at(delta.parent_id);
        states.emplace(delta.block_id, apply_delta(parent, delta));
        if (i != 0) {
            accept(append, delta);
            accept(replace, delta);
        }
        require(append.served_head().state_root == delta.expected_state_root,
                "incremental publication matches independent py-trie fixture state root");
    }
    require(append_control->loads == 1 && replace_control->loads == deltas.size(),
            "fixture branches append while replacement baseline reloads each version");
    // Revisit both forks, account deletion/reset/recreation, and the empty root
    // after all publications to catch stale locator or storage-root bindings.
    for (std::size_t index = 0; index < deltas.size(); ++index) {
        const auto& delta = deltas[index];
        const BlockCase expected{delta, states.at(delta.block_id)};
        const auto appended = check_batch(append, expected);
        const auto replaced = check_batch(replace, expected);
        for (std::size_t q = 0; q < appended.proofs.accounts.size(); ++q)
            require(appended.proofs.accounts[q].proof.slots == replaced.proofs.accounts[q].proof.slots,
                    "incremental account proof wire bytes equal replacement baseline");
        for (std::size_t s = 0; s < appended.proofs.storage.size(); ++s)
            require(appended.proofs.storage[s].proof.slots == replaced.proofs.storage[s].proof.slots,
                    "incremental storage proof wire bytes equal replacement baseline");
    }
}
}  // namespace

int main() {
    try {
        test_append_pins_both_phases_and_old_locators();
        test_noop_discard_invalid_root_and_retained_reorg();
        test_incremental_canonical_paths_share_retained_nodes();
        test_capacity_fallback_and_failed_fresh_load();
        test_partial_upload_and_finish_failures_require_fresh_recovery();
        test_read_failure_after_append_preparation_reloads_before_publication();
        test_retention_compaction_and_periodic_threshold();
        test_occupancy_tracks_records_across_retained_roots();
        test_fullness_threshold_preflight_and_pinning();
        test_dead_byte_thresholds_and_configuration();
        test_history_restart_rebuilds_retained_closure_and_resumes_appends();
        test_independent_block_fixtures_match_replacement_proofs();
        std::cout << "ethereum_mpt_incremental_test passed\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_incremental_test: " << error.what() << '\n';
        return 1;
    }
}
