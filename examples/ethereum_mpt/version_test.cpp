// Tests ReplacementService: builder accounting, rejections, batch pinning
// during forks, failed loading, identity/retention rules, pruned ancestors and
// checkpoint restarts.

#include "fixture.hpp"
#include "version.hpp"

#include <algorithm>
#include <exception>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("version test: ") + message);
}

template<class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::exception&) {
        return;
    }
    throw std::runtime_error(std::string("version test accepted: ") + message);
}

// Compute test roots directly from independently specified final states. The
// expected state does not pass through the delta application under test.
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
    result.delta.block_id = word_from_u64(id + 1000);
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
    result.delta.block_id = word_from_u64(id + 1000);
    result.delta.parent_id = parent.delta.block_id;
    result.delta.number = parent.delta.number + 1;
    result.delta.expected_state_root = parent.delta.expected_state_root;
    return result;
}

std::vector<PathRequest> requests() {
    std::vector<PathRequest> result;
    for (std::uint8_t id : {1, 2, 99})
        result.push_back(make_path_request(fixture_address(id),
                                          {word_from_u64(1), word_from_u64(99)}));
    return result;
}

struct ReadEvent {
    std::size_t reader;
    Tier tier;
    std::size_t lanes;
};

struct LoaderControl {
    std::size_t loads = 0, live_readers = 0, partial_load_reads = 0;
    bool fail_next_load = false;
    std::vector<ReadEvent> reads;
    std::function<void(std::size_t)> on_read;
};

// Public instrumented backend, intentionally not an ORAM substitute in the
// example. Copying pages gives every load independent immutable backing data.
class ImageReader final : public PageReader {
public:
    ImageReader(const PackedGeneration& image, std::shared_ptr<LoaderControl> control,
                std::size_t serial)
        : pages_(image.pages), control_(std::move(control)), serial_(serial) {
        ++control_->live_readers;
    }
    ~ImageReader() override { --control_->live_readers; }

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        control_->reads.push_back({serial_, tier, count});
        // Copy the hook because a hook may remove itself or load another image.
        const auto hook = control_->on_read;
        if (hook) hook(control_->reads.size());
        const auto& pages = pages_[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            found[i] = static_cast<std::uint8_t>(ids[i] < pages.size());
            output[i] = found[i] ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }

private:
    std::array<std::vector<Page>, 3> pages_;
    std::shared_ptr<LoaderControl> control_;
    std::size_t serial_;
};

GenerationLoader loader(const std::shared_ptr<LoaderControl>& control) {
    return [control](const PackedGeneration& image, std::size_t max_lanes) {
        require(max_lanes == 8, "loader receives configured lane capacity");
        auto reader = std::make_unique<ImageReader>(image, control, ++control->loads);
        if (control->fail_next_load) {
            control->fail_next_load = false;
            // Failure occurs after creating and touching new backing storage.
            // It must neither damage the served maps nor leak this reader.
            for (std::size_t tier = 0; tier < image.pages.size(); ++tier) {
                if (image.pages[tier].empty()) continue;
                const std::uint64_t dummy = 0;
                Page page{};
                std::uint8_t found = 0;
                reader->read_pages_batch(static_cast<Tier>(tier), 1, &dummy, &page, &found);
                require(found == 1, "partial load can access a configured dummy page");
                ++control->partial_load_reads;
                break;
            }
            throw std::runtime_error("injected partial generation load failure");
        }
        std::size_t arena_bytes = 4096;
        for (const auto& pages : image.pages) arena_bytes += pages.size() * page_bytes * 3;
        return LoadedGeneration{std::move(reader), arena_bytes};
    };
}

ReplacementOptions options(std::size_t retained = 4) {
    return ReplacementOptions{TierProfile{3, 2}, retained, 8};
}

void check_result(const BlockCase& expected, const VersionedBatch& result) {
    const auto snapshot = reference_snapshot(expected.state);
    const auto paths = requests();
    require(result.manifest.block_id == expected.delta.block_id &&
            result.manifest.state_root == snapshot.accounts.root_hash(),
            "batch carries the requested block and state root");
    require(result.proofs.accounts.size() == paths.size() &&
            result.proofs.storage.size() == paths.size() * 2, "fixed proof result shape");
    for (std::size_t q = 0; q < paths.size(); ++q) {
        const auto& account = result.proofs.accounts[q];
        const auto proof = decode_proof(account.proof);
        require(account.error == 0 && proof == prove(snapshot.accounts, paths[q].account_key),
                "retained account proof equals independent reference proof");
        const auto encoded = verify_proof(TrieKind::account, result.manifest.state_root,
                                          paths[q].account_key, proof);
        require((account.present != 0) == encoded.has_value(), "verified account presence");
        Account fields;
        if (encoded) {
            fields = decode_account(*encoded);
            require(account.nonce == fields.nonce && account.balance == fields.balance &&
                    account.code_hash == fields.code_hash &&
                    account.storage_root == fields.storage_root, "verified account fields");
        }
        const auto empty = build_trie(TrieKind::storage, {});
        const auto& storage = fields.storage_root == empty_trie_root()
            ? empty : snapshot.storage_tries.at(fields.storage_root);
        for (std::size_t slot = 0; slot < 2; ++slot) {
            const auto& item = result.proofs.storage[q * 2 + slot];
            const auto storage_proof = decode_proof(item.proof);
            require(item.error == 0 &&
                    storage_proof == prove(storage, paths[q].storage_keys[slot]),
                    "retained storage proof equals independent reference proof");
            const auto value = verify_proof(TrieKind::storage, fields.storage_root,
                                             paths[q].storage_keys[slot], storage_proof);
            require((item.present != 0) == value.has_value() &&
                    item.storage_value == (value ? decode_storage(*value) : Word{}),
                    "storage proof authenticates the same version as its account");
        }
    }
}

VersionedBatch check_batch(ReplacementService& service, const BlockCase& expected) {
    auto result = service.run(expected.delta.block_id, BatchProfile{3, 2}, requests());
    check_result(expected, result);
    return result;
}

void accept(ReplacementService& service, const BlockCase& next) {
    require(service.prepare(next.delta), "distinct block stages a new generation");
    require(service.publish(), "prepared generation publishes at a batch boundary");
    require(service.served_head().block_id == next.delta.block_id, "published head is selected block");
}

void test_public_builder_payload_counts_shared_versions_once() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = unchanged_child(1, genesis);
    const auto second = unchanged_child(2, first);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(2), loader(control));
    const auto initial = service.public_builder_memory();
    require(initial.retained_versions == 1 && initial.public_state_bytes == 2 * (92 + 2 * 64) &&
            initial.canonical_trie_rlp_bytes > 0 &&
            initial.packed_image_bytes == service.memory().current_page_bytes &&
            initial.staged_upload_bytes == 0 && initial.identity_bytes == 96,
            "initial builder counts state fields, slots, canonical nodes, pages and identities");
    require(initial.payload_bytes() == initial.public_state_bytes + initial.canonical_trie_rlp_bytes +
                initial.packed_image_bytes + initial.staged_upload_bytes + initial.identity_bytes,
            "builder payload total includes each reported byte category");
    require(service.prepare(first.delta), "same-root distinct block prepares for accounting");
    const auto staged = service.public_builder_memory();
    require(staged.retained_versions == 2 && staged.public_state_bytes == 2 * initial.public_state_bytes &&
            staged.canonical_trie_rlp_bytes == 2 * initial.canonical_trie_rlp_bytes &&
            staged.packed_image_bytes == 2 * initial.packed_image_bytes &&
            staged.staged_upload_bytes == 0 && staged.identity_bytes == initial.identity_bytes + 64,
            "shared retained version counts once while distinct equal snapshots and packed images both count");
    service.discard_pending();
    const auto discarded = service.public_builder_memory();
    require(discarded.retained_versions == initial.retained_versions &&
            discarded.public_state_bytes == initial.public_state_bytes &&
            discarded.canonical_trie_rlp_bytes == initial.canonical_trie_rlp_bytes &&
            discarded.packed_image_bytes == initial.packed_image_bytes &&
            discarded.identity_bytes == initial.identity_bytes + 64,
            "discard releases staged payload but preserves validated identity tombstones");
    accept(service, first);
    require(service.prepare(second.delta), "next same-root block prepares across retention boundary");
    const auto pruning = service.public_builder_memory();
    require(pruning.retained_versions == 3 && pruning.public_state_bytes == 3 * initial.public_state_bytes &&
            pruning.canonical_trie_rlp_bytes == 3 * initial.canonical_trie_rlp_bytes,
            "pending retention counts the union of old and new versions");
    require(service.publish(), "retention update publishes");
    const auto retained = service.public_builder_memory();
    require(retained.retained_versions == 2 && retained.public_state_bytes == 2 * initial.public_state_bytes &&
            retained.canonical_trie_rlp_bytes == 2 * initial.canonical_trie_rlp_bytes &&
            retained.packed_image_bytes == initial.packed_image_bytes &&
            retained.identity_bytes == 3 * initial.identity_bytes,
            "publication releases pruned snapshots while identity history remains");
    service.prepare_reorg(first.delta.block_id);
    const auto reorg = service.public_builder_memory();
    require(reorg.retained_versions == retained.retained_versions &&
            reorg.public_state_bytes == retained.public_state_bytes &&
            reorg.canonical_trie_rlp_bytes == retained.canonical_trie_rlp_bytes &&
            reorg.packed_image_bytes == 2 * retained.packed_image_bytes,
            "staged ancestor selection shares all versions but retains a separate packed image");
    service.discard_pending();
}

void test_public_rejections_preserve_service() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    require(service.available() && !service.batch_active() && !service.publish(),
            "initial generation is available with no pending publication");
    reject([&] { service.manifest(word_from_u64(999)); }, "unknown manifest");
    reject([&] { service.run(word_from_u64(999), BatchProfile{3, 2}, requests()); },
           "unknown block proof request");
    reject([&] { service.run(genesis.delta.block_id, BatchProfile{3, 2}, {}); },
           "request shape mismatch");
    auto too_wide = requests();
    for (auto& path : too_wide) path.storage_keys.resize(3);
    reject([&] { service.run(genesis.delta.block_id, BatchProfile{3, 3}, too_wide); },
           "storage lanes exceed loaded map capacity");
    require(control->reads.empty() && service.available() && !service.batch_active(),
            "public admission failures do not touch or invalidate maps");

    auto invalid = next.delta;
    invalid.expected_state_root.front() ^= 1;
    reject([&] { service.prepare(invalid); }, "incorrect expected state root");
    invalid = next.delta;
    invalid.parent_id = word_from_u64(999);
    reject([&] { service.prepare(invalid); }, "unknown parent");
    invalid = next.delta;
    ++invalid.number;
    reject([&] { service.prepare(invalid); }, "nonconsecutive block height");
    require(control->loads == 1 && !service.pending_head() &&
            service.served_head().block_id == genesis.delta.block_id,
            "invalid updates fail before loading or changing the served generation");
    check_batch(service, genesis);
}

void test_batch_pins_account_and_storage_during_fork() {
    const auto genesis = block(0, nullptr, 1);
    const auto ancestor = block(1, &genesis, 2);
    const auto old_head = block(2, &ancestor, 3);
    const auto fork_head = block(3, &ancestor, 4);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    accept(service, ancestor);
    accept(service, old_head);
    const auto old_manifest = service.served_head();
    control->reads.clear();
    bool injected = false;
    control->on_read = [&](std::size_t call) {
        if (call != 66) return;
        injected = true;
        require(service.batch_active(), "full batch remains active at first storage read");
        reject([&] { service.run(old_head.delta.block_id, BatchProfile{3, 2}, requests()); },
               "reentrant proof admission");
        require(service.prepare(fork_head.delta), "fork can prepare at public read boundary");
        require(service.pending_head()->block_id == fork_head.delta.block_id &&
                service.pending_common_ancestor() == std::optional<Hash>{ancestor.delta.block_id},
                "fork identifies retained common ancestor");
        require(!service.publish(), "publication is refused between account and storage phases");
        require(service.served_head().generation == old_manifest.generation &&
                service.served_head().block_id == old_head.delta.block_id,
                "pending fork does not change pinned manifest");
        reject([&] { service.manifest(fork_head.delta.block_id); }, "staged root is not published");
    };
    const auto result = check_batch(service, old_head);
    control->on_read = {};
    require(injected && result.manifest.generation == old_manifest.generation &&
            !service.batch_active() && service.available(), "complete batch retains old generation");
    require(control->reads.size() == 130, "version pin preserves both complete fixed phases");
    const auto reader = control->reads.front().reader;
    for (std::size_t round = 0; round < 65; ++round) {
        require(control->reads[round].reader == reader &&
                control->reads[round + 65].reader == reader,
                "account and storage read the identical immutable image");
        require(control->reads[round].lanes == 3 && control->reads[round + 65].lanes == 6 &&
                control->reads[round].tier == tier_for(TrieKind::account, round, options().tiers) &&
                control->reads[round + 65].tier == tier_for(TrieKind::storage, round, options().tiers),
                "public batch schedule survives a prepared fork");
    }
    const auto memory = service.memory();
    require(control->live_readers == 2 && memory.current_arena_bytes != 0 &&
            memory.staged_arena_bytes != 0 &&
            memory.peak_arena_bytes >= memory.current_arena_bytes + memory.staged_arena_bytes &&
            memory.peak_page_bytes >= memory.current_page_bytes + memory.staged_page_bytes,
            "replacement reports simultaneous old and staged memory");
    require(service.publish() && control->live_readers == 1, "boundary publication retires old maps");
    require(service.served_head().generation != old_manifest.generation &&
            service.manifest(old_head.delta.block_id).generation == service.served_head().generation,
            "retained roots share the newly loaded generation");
    check_batch(service, old_head);
    check_batch(service, fork_head);
    check_batch(service, ancestor);
}

void test_failed_load_preserves_served_and_staged_generations() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto staged = block(2, &first, 3);
    const auto failing = block(3, &first, 4);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    accept(service, first);
    require(service.prepare(staged.delta), "successful replacement is staged");
    const auto pending_generation = service.pending_head()->generation;
    const auto old_memory = service.memory();
    const auto staged_loads = control->loads;
    reject([&] { service.prepare(failing.delta); }, "second distinct preparation while publication is pending");
    require(control->loads == staged_loads && control->live_readers == 2 && service.available(),
            "pending replacement admission does not load a third generation");
    require(service.served_head().block_id == first.delta.block_id &&
            service.pending_head()->block_id == staged.delta.block_id &&
            service.pending_head()->generation == pending_generation,
            "rejected preparation preserves previously staged publication");
    require(service.memory().current_arena_bytes == old_memory.current_arena_bytes &&
            service.memory().staged_arena_bytes == old_memory.staged_arena_bytes,
            "rejected preparation leaves live memory accounting intact");
    check_batch(service, first);
    service.discard_pending();
    control->fail_next_load = true;
    reject([&] { service.prepare(failing.delta); }, "partially loaded replacement failure");
    require(control->partial_load_reads == 1 && control->live_readers == 1 && service.available() &&
            !service.pending_head() && service.served_head().block_id == first.delta.block_id,
            "failed fresh reader is released without damaging the current generation");
    require(service.observed_head().block_id == failing.delta.block_id &&
            service.memory().staged_arena_bytes == 0,
            "failed load records validated observed head without publishing its maps");
    reject([&] { service.manifest(failing.delta.block_id); }, "failed update remains unpublished");
    auto conflict = failing.delta;
    conflict.account_upserts.front().reset_storage = false;
    reject([&] { service.prepare(conflict); }, "validated failed block ID cannot change identity");
    check_batch(service, first);
    require(service.prepare(failing.delta), "failed delivery may be retried");
    service.discard_pending();
    require(!service.pending_head() && !service.publish() && control->live_readers == 1,
            "discard releases only staged maps");
    reject([&] { service.prepare(conflict); }, "discarded block ID cannot change identity");
    accept(service, failing);
    check_batch(service, failing);
}

void test_duplicate_identity_fifo_and_ancestor_switch() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto same_root = unchanged_child(2, first);
    const auto third = block(3, &same_root, 3);
    const auto fourth = block(4, &third, 4);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(3), loader(control));
    require(!service.prepare(genesis.delta), "genesis duplicate is idempotent");
    accept(service, first);
    accept(service, same_root);
    require(service.manifest(first.delta.block_id).state_root ==
            service.manifest(same_root.delta.block_id).state_root,
            "distinct blocks may authenticate the same state root");
    auto reordered = first.delta;
    std::reverse(reordered.account_upserts.begin(), reordered.account_upserts.end());
    for (auto& account : reordered.account_upserts)
        std::reverse(account.storage_changes.begin(), account.storage_changes.end());
    const auto loads = control->loads;
    require(!service.prepare(reordered) && control->loads == loads && !service.pending_head(),
            "canonically reordered duplicate does not load or stage a generation");
    auto conflict = first.delta;
    ++conflict.number;
    reject([&] { service.prepare(conflict); }, "same block ID with conflicting header");
    conflict = first.delta;
    conflict.account_upserts.front().reset_storage = false;
    reject([&] { service.prepare(conflict); }, "same ID and root with divergent delta identity");
    conflict = first.delta;
    conflict.expected_state_root.front() ^= 1;
    reject([&] { service.prepare(conflict); }, "same block ID with divergent expected root");
    accept(service, third);
    require(service.retained_blocks() == std::vector<Hash>{first.delta.block_id,
            same_root.delta.block_id, third.delta.block_id}, "retention prunes FIFO by distinct block");
    require(!service.prepare(genesis.delta), "pruned duplicate retains its delivery identity");
    accept(service, fourth);
    const std::vector<Hash> retained{same_root.delta.block_id, third.delta.block_id,
                                     fourth.delta.block_id};
    require(service.retained_blocks() == retained, "duplicates never reorder retention");
    const auto reads = control->reads.size();
    reject([&] { service.manifest(first.delta.block_id); }, "pruned manifest");
    reject([&] { service.run(first.delta.block_id, BatchProfile{3, 2}, requests()); },
           "pruned proof root");
    require(control->reads.size() == reads && service.available(), "pruned admission has no map accesses");
    const auto pruned_child = block(9, &first, 9);
    reject([&] { service.prepare(pruned_child.delta); }, "pruned parent state is unavailable");
    reject([&] { service.prepare_reorg(first.delta.block_id); }, "pruned ancestor switch");
    check_batch(service, same_root);
    check_batch(service, third);
    check_batch(service, fourth);

    const auto generation = service.served_head().generation;
    const auto before_reorg_loads = control->loads;
    service.prepare_reorg(third.delta.block_id);
    require(service.pending_common_ancestor() == std::optional<Hash>{third.delta.block_id} &&
            control->loads == before_reorg_loads + 1,
            "retained ancestor switch constructs fresh maps");
    require(service.publish() && service.served_head().block_id == third.delta.block_id &&
            service.served_head().generation != generation && service.retained_blocks() == retained,
            "ancestor switch publishes fresh generation without reordering retention");
    check_batch(service, fourth);
    check_batch(service, third);
}

void test_fork_with_pruned_common_ancestor_is_rejected() {
    const auto genesis = block(0, nullptr, 1);
    const auto ancestor = block(1, &genesis, 2);
    const auto left = block(2, &ancestor, 3);
    const auto right = block(3, &ancestor, 4);
    const auto left_child = block(4, &left, 5);
    const auto right_child = block(5, &right, 6);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(3), loader(control));
    accept(service, ancestor);
    accept(service, left);
    accept(service, right);
    accept(service, left_child);
    require(service.retained_blocks() == std::vector<Hash>{left.delta.block_id,
            right.delta.block_id, left_child.delta.block_id}, "fork tips survive after common ancestor prunes");
    const auto loads = control->loads;
    reject([&] { service.prepare(right_child.delta); }, "fork common ancestor beyond retention");
    reject([&] { service.prepare_reorg(right.delta.block_id); }, "switch across unavailable common ancestor");
    require(control->loads == loads && !service.pending_head() &&
            service.served_head().block_id == left_child.delta.block_id,
            "unavailable ancestor rejection preserves served head");
    check_batch(service, left_child);
    check_batch(service, right);
}

void test_public_checkpoint_restarts_with_fresh_maps() {
    const auto genesis = block(0, nullptr, 1);
    const auto first = block(1, &genesis, 2);
    const auto second = block(2, &first, 3);
    const auto next = block(3, &second, 4);
    const auto control = std::make_shared<LoaderControl>();
    PublicCheckpoint checkpoint;
    {
        ReplacementService original(genesis_checkpoint(genesis.delta), options(), loader(control));
        accept(original, first);
        accept(original, second);
        checkpoint = original.checkpoint();
        require(checkpoint.block.block_id == second.delta.block_id &&
                checkpoint.block.state_root == second.delta.expected_state_root,
                "checkpoint records published public block metadata");
    }
    require(control->live_readers == 0, "checkpoint keeps no original page reader alive");
    const auto loads = control->loads;
    ReplacementService restarted(checkpoint, options(), loader(control));
    require(control->loads == loads + 1 && control->live_readers == 1 &&
            restarted.retained_blocks() == std::vector<Hash>{second.delta.block_id},
            "restart loads a fresh generation from public state only");
    check_batch(restarted, second);
    require(!restarted.prepare(second.delta), "restart preserves head duplicate identity");
    reject([&] { restarted.manifest(first.delta.block_id); }, "checkpoint does not invent unavailable ancestry");
    accept(restarted, next);
    check_batch(restarted, next);
    auto bad_checkpoint = checkpoint;
    bad_checkpoint.block.state_root.front() ^= 1;
    const auto before_bad = control->loads;
    reject([&] { ReplacementService invalid(bad_checkpoint, options(), loader(control)); },
           "checkpoint with root inconsistent with public state");
    require(control->loads == before_bad, "bad checkpoint is rejected before loading maps");
}

void test_history_checkpoint_retains_forks_head_and_published_state() {
    const auto genesis = block(0, nullptr, 1);
    const auto ancestor = block(9, &genesis, 2);
    const auto left = block(8, &ancestor, 3);
    const auto left_child = block(7, &left, 4);
    const auto right = block(6, &ancestor, 5);
    const auto pending = block(5, &right, 6);
    const auto control = std::make_shared<LoaderControl>();
    PublicHistoryCheckpoint saved;
    const std::vector<Hash> retained{ancestor.delta.block_id, left.delta.block_id,
                                    left_child.delta.block_id, right.delta.block_id};
    {
        ReplacementService original(genesis_checkpoint(genesis.delta), options(), loader(control));
        for (const auto* version : {&ancestor, &left, &left_child, &right}) accept(original, *version);
        original.prepare_reorg(left.delta.block_id);
        require(original.publish(), "history fixture selects a retained nonfinal head");
        require(original.prepare(pending.delta), "history fixture stages an unpublished fork child");
        require(original.observed_head().block_id == pending.delta.block_id,
                "observed head may be newer than the checkpoint's published head");
        saved = original.history_checkpoint();
        require(saved.served_head == left.delta.block_id && saved.versions.size() == retained.size(),
                "history export records published head and excludes staged version");
        for (std::size_t i = 0; i < retained.size(); ++i)
            require(saved.versions[i].block.block_id == retained[i],
                    "history export preserves publication order across heights and IDs");
    }
    require(control->live_readers == 0, "history export owns no old readers");
    const auto loads = control->loads;
    ReplacementService restored(saved, options(), loader(control));
    require(control->loads == loads + 1 && control->live_readers == 1 &&
            restored.retained_blocks() == retained && !restored.pending_head() &&
            restored.served_head().block_id == left.delta.block_id &&
            restored.observed_head().block_id == left.delta.block_id,
            "history restore rebuilds every retained version with the saved head selected");
    require(restored.public_builder_memory().identity_bytes == retained.size() * 96,
            "history restores retained identities without pruned or pending tombstones");
    for (const auto* version : {&ancestor, &left, &left_child, &right}) {
        check_batch(restored, *version);
        require(!restored.prepare(version->delta), "each retained delivery stays idempotent after restart");
    }
    auto conflicting = right.delta;
    ++conflicting.number;
    reject([&] { restored.prepare(conflicting); }, "restored retained identity conflicts");
    reject([&] { restored.manifest(genesis.delta.block_id); }, "history excludes pruned genesis");
    reject([&] { restored.manifest(pending.delta.block_id); }, "history excludes pending block");
    restored.prepare_reorg(right.delta.block_id);
    require(restored.pending_common_ancestor() == std::optional<Hash>{ancestor.delta.block_id} &&
            restored.publish(), "restored fork ancestry supports retained reorgs");
    accept(restored, pending);
    require(restored.retained_blocks() == std::vector<Hash>{left.delta.block_id,
            left_child.delta.block_id, right.delta.block_id, pending.delta.block_id},
            "continuation prunes the saved oldest version without sorting");
    check_batch(restored, pending);
    check_batch(restored, left_child);
}

void test_history_checkpoint_validation_precedes_loading() {
    const auto genesis = block(0, nullptr, 1);
    const auto child = block(1, &genesis, 2);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService source(genesis_checkpoint(genesis.delta), options(), loader(control));
    accept(source, child);
    const auto saved = source.history_checkpoint();
    const auto loads = control->loads;
    const auto invalid = [&](PublicHistoryCheckpoint malformed, const char* message) {
        reject([&] { ReplacementService rejected(std::move(malformed), options(), loader(control)); },
               message);
        require(control->loads == loads, "invalid history fails before any backend load");
    };
    auto malformed = saved;
    malformed.versions.clear();
    invalid(malformed, "empty history");
    malformed = saved;
    malformed.served_head = Hash{};
    invalid(malformed, "zero served head");
    malformed.served_head = word_from_u64(999);
    invalid(malformed, "unknown served head");
    malformed = saved;
    malformed.versions.front().block.block_id = Hash{};
    invalid(malformed, "zero retained identity");
    malformed = saved;
    malformed.versions.push_back(malformed.versions.front());
    invalid(malformed, "duplicate retained identity");
    malformed = saved;
    std::reverse(malformed.versions.begin(), malformed.versions.end());
    invalid(malformed, "child before retained parent");
    malformed = saved;
    malformed.versions.front().block.parent_id = malformed.versions.front().block.block_id;
    invalid(malformed, "self parent");
    malformed = saved;
    ++malformed.versions.back().block.number;
    invalid(malformed, "nonconsecutive retained child height");
    malformed = saved;
    malformed.versions.front().block.number = std::numeric_limits<std::uint64_t>::max();
    malformed.versions.back().block.number = 0;
    invalid(malformed, "wrapped parent height");
    malformed = saved;
    malformed.versions.front().block.state_root.front() ^= 1;
    invalid(malformed, "invalid nonhead state root");
    reject([&] { ReplacementService rejected(saved, options(1), loader(control)); },
           "saved history larger than configured retention capacity");
    require(control->loads == loads, "retention capacity fails before backend load");

    // The single-checkpoint format accepts incomplete anchor metadata. A
    // retained history preserves that policy when the parent is absent.
    auto anchor = saved;
    anchor.versions.erase(anchor.versions.begin());
    anchor.versions.front().block.parent_id = Hash{};
    anchor.versions.front().block.number = std::numeric_limits<std::uint64_t>::max();
    ReplacementService anchored(anchor, options(), loader(control));
    require(anchored.served_head().number == std::numeric_limits<std::uint64_t>::max(),
            "incomplete anchor metadata remains accepted without retained parent");
    check_batch(anchored, child);
}

void test_reader_exception_requires_fresh_generation() {
    const auto genesis = block(0, nullptr, 1);
    const auto next = block(1, &genesis, 2);
    const auto control = std::make_shared<LoaderControl>();
    ReplacementService service(genesis_checkpoint(genesis.delta), options(), loader(control));
    control->on_read = [](std::size_t call) {
        if (call == 66) throw std::runtime_error("injected storage-phase reader failure");
    };
    reject([&] { service.run(genesis.delta.block_id, BatchProfile{3, 2}, requests()); },
           "page reader exception");
    control->on_read = {};
    require(!service.available() && !service.batch_active() && control->reads.size() == 66,
            "reader exception releases batch pin and marks mutable maps unavailable");
    const auto reads = control->reads.size();
    reject([&] { service.run(genesis.delta.block_id, BatchProfile{3, 2}, requests()); },
           "failed mutable maps cannot serve another batch");
    require(control->reads.size() == reads, "unavailable generation fails before map access");
    accept(service, next);
    require(service.available() && control->live_readers == 1,
            "fresh replacement recovers service and retires potentially damaged maps");
    check_batch(service, genesis);
    check_batch(service, next);
}

}  // namespace

int main() {
    try {
        test_public_builder_payload_counts_shared_versions_once();
        test_public_rejections_preserve_service();
        test_batch_pins_account_and_storage_during_fork();
        test_failed_load_preserves_served_and_staged_generations();
        test_duplicate_identity_fifo_and_ancestor_switch();
        test_fork_with_pruned_common_ancestor_is_rejected();
        test_public_checkpoint_restarts_with_fresh_maps();
        test_history_checkpoint_retains_forks_head_and_published_state();
        test_history_checkpoint_validation_precedes_loading();
        test_reader_exception_requires_fresh_generation();
        std::cout << "ethereum_mpt_version_test passed\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_version_test: " << error.what() << '\n';
        return 1;
    }
}
