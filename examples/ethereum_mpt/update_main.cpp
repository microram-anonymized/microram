// ethereum_mpt_updates / ethereum_mpt_incremental: follow the eight mock blocks
// with the replacement or incremental version service, verify proofs against
// every retained root, and optionally save/restore public checkpoints.

#include "client.hpp"
#include "checkpoint.hpp"
#include "fixture.hpp"
#include "page_map.hpp"
#include "version.hpp"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <sys/resource.h>

using namespace ethereum_mpt;

namespace {
void require(bool ok, const char* message) {
    if (!ok) throw std::runtime_error(message);
}

struct Config {
    std::string checkpoint_in, checkpoint_out;
    std::size_t through_index = 7;
};

Config parse(int argc, char** argv) {
    Config config;
    std::set<std::string> seen;
    for (int i = 1; i < argc; ++i) {
        const std::string flag = argv[i];
        if (flag == "--help") {
            std::cout << "Usage: " << argv[0] << " [option value ...]\n"
                "  --checkpoint-in PATH    restore retained fixture roots into fresh maps\n"
                "  --checkpoint-out PATH   atomically save retained roots after verification\n"
                "  --through-index N       last fixture index, inclusive 0..7 (default 7)\n"
                "Legacy single-head checkpoints are accepted with their limited history.\n";
            std::exit(0);
        }
        if (flag != "--checkpoint-in" && flag != "--checkpoint-out" &&
            flag != "--through-index")
            throw std::invalid_argument("unknown option: " + flag);
        if (!seen.insert(flag).second) throw std::invalid_argument("duplicate option: " + flag);
        if (++i == argc) throw std::invalid_argument("missing option value: " + flag);
        const std::string value = argv[i];
        if (value.empty()) throw std::invalid_argument("empty option value: " + flag);
        if (flag == "--checkpoint-in") config.checkpoint_in = value;
        else if (flag == "--checkpoint-out") config.checkpoint_out = value;
        else {
            if (value.size() != 1 || value[0] < '0' || value[0] > '7')
                throw std::invalid_argument("fixture index must be an integer from 0 through 7");
            config.through_index = static_cast<std::size_t>(value[0] - '0');
        }
    }
    return config;
}

// Public instrumentation injects an update exactly between phases. No private
// lane state, page key or result influences the callback or its timing.
class BoundaryReader final : public PageStore {
 public:
    BoundaryReader(const PackedGeneration& image, std::size_t lanes,
                   std::function<void()>& boundary)
        : maps_(image, lanes), boundary_(boundary) {}

    BoundaryReader(const PackedGeneration& image, std::size_t lanes,
                   const std::array<std::size_t, 3>& capacities,
                   std::function<void()>& boundary)
        : maps_(image, lanes, capacities), boundary_(boundary) {}

    void write_pages_batch(Tier tier, std::uint64_t first_page_id,
                           const std::vector<Page>& pages) override {
        maps_.write_pages_batch(tier, first_page_id, pages);
    }
    void finish_pending_work() override { maps_.finish_pending_work(); }
    std::array<std::size_t, 3> capacities() const override { return maps_.capacities(); }

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        if (calls_++ % (2 * proof_rounds) == proof_rounds && boundary_) {
            auto callback = std::move(boundary_);
            boundary_ = {};
            callback();
        }
        maps_.read_pages_batch(tier, count, ids, output, found);
    }
    std::size_t arena_bytes() const { return maps_.arena_bytes(); }

 private:
    TieredPageMaps maps_;
    std::function<void()>& boundary_;
    std::size_t calls_ = 0;
};

void check(const VersionedBatch& result, const Snapshot& snapshot,
           const std::vector<PathRequest>& requests) {
    require(result.manifest.state_root == snapshot.accounts.root_hash(), "wrong pinned state root");
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto& answer = result.proofs.accounts[q];
        const auto proof = decode_proof(answer.proof);
        require(!answer.error && proof == prove(snapshot.accounts, requests[q].account_key),
                "versioned account proof differs from reference");
        const auto value = verify_proof(TrieKind::account, result.manifest.state_root,
                                        requests[q].account_key, proof);
        require(bool(answer.present) == bool(value), "versioned account presence mismatch");
        const auto account = value ? decode_account(*value) : Account{};
        if (value)
            require(answer.nonce == account.nonce && answer.balance == account.balance &&
                    answer.code_hash == account.code_hash && answer.storage_root == account.storage_root,
                    "versioned account fields mismatch");
        const Trie empty{TrieKind::storage, nullptr};
        const auto& storage = account.storage_root == empty_trie_root() ? empty :
                              snapshot.storage_tries.at(account.storage_root);
        // The demo has the public shape Q=2, K=1 throughout.
        const auto& slot = result.proofs.storage[q];
        const auto slot_proof = decode_proof(slot.proof);
        require(!slot.error && slot_proof == prove(storage, requests[q].storage_keys[0]),
                "versioned storage proof differs from reference");
        const auto slot_value = verify_proof(TrieKind::storage, account.storage_root,
                                             requests[q].storage_keys[0], slot_proof);
        require(bool(slot.present) == bool(slot_value) &&
                slot.storage_value == (slot_value ? decode_storage(*slot_value) : Word{}),
                "versioned storage value mismatch");
    }
}
}  // namespace

int main(int argc, char** argv) {
    try {
        const auto config = parse(argc, argv);
        std::ifstream input(ETHEREUM_MPT_BLOCK_FIXTURES);
        require(bool(input), "cannot open mock block fixtures");
        const auto blocks = load_mock_blocks(input);
        require(blocks.size() == 8, "unexpected mock block fixture count");
        std::map<Hash, PublicState> states;
        std::map<Hash, Snapshot> snapshots;
        for (const auto& block : blocks) {
            const auto parent = block.number == 0 ? PublicState{} : states.at(block.parent_id);
            auto state = apply_delta(parent, block);
            snapshots.emplace(block.block_id, snapshot_from_state(state));
            states.emplace(block.block_id, std::move(state));
        }
        CheckpointLimits limits;
        limits.max_versions = blocks.size();
        auto initial = config.checkpoint_in.empty() ?
            PublicHistoryCheckpoint{blocks.front().block_id, {genesis_checkpoint(blocks.front())}} :
            load_public_history_checkpoint(config.checkpoint_in, limits);
        // The checksum detects corruption, not forgery or rollback. This demo's
        // independently generated fixture is the trusted source of block metadata.
        std::map<Hash, Hash> available;
        for (const auto& version : initial.versions) {
            const auto known = std::find_if(blocks.begin(), blocks.end(), [&](const auto& block) {
                return block.block_id == version.block.block_id;
            });
            require(known != blocks.end(), "checkpoint block is not in the trusted fixture");
            require(version.block.parent_id == known->parent_id &&
                    version.block.number == known->number &&
                    version.block.state_root == known->expected_state_root &&
                    version.fingerprint == delta_fingerprint(*known),
                    "checkpoint metadata does not match the trusted fixture");
            available.emplace(version.block.block_id, version.block.parent_id);
        }
        const auto selected = std::find_if(blocks.begin(), blocks.end(), [&](const auto& block) {
            return block.block_id == initial.served_head;
        });
        require(selected != blocks.end(), "checkpoint head is not in the trusted fixture");
        const auto first_index = static_cast<std::size_t>(selected - blocks.begin());
        require(config.through_index >= first_index,
                "last fixture index precedes the checkpoint head");
        // Preflight this fixed fixture schedule before loading maps or saving.
        // A legacy single-head file does not recreate pruned ancestors.
        auto planned_head = initial.served_head;
        for (std::size_t i = first_index + 1; i <= config.through_index; ++i) {
            const auto& block = blocks[i];
            const bool retained = available.count(block.block_id) != 0;
            require(retained || available.count(block.parent_id) != 0,
                    "fixture continuation needs an unavailable ancestor; restore an earlier checkpoint");
            // The service requires a retained common ancestor, including all
            // intermediate parent links. Having just the next parent is not enough.
            std::set<Hash> ancestors;
            auto current = planned_head;
            while (available.count(current) && ancestors.insert(current).second)
                current = available.at(current);
            std::set<Hash> visited;
            current = retained ? block.block_id : block.parent_id;
            bool shared = false;
            while (available.count(current) && visited.insert(current).second) {
                if (ancestors.count(current)) {
                    shared = true;
                    break;
                }
                current = available.at(current);
            }
            require(shared,
                    "fixture continuation needs an unavailable ancestor; restore an earlier checkpoint");
            available.emplace(block.block_id, block.parent_id);
            planned_head = block.block_id;
        }
        std::function<void()> boundary;
#ifdef ETHEREUM_MPT_INCREMENTAL
        const IncrementalLoader loader = [&](const PackedGeneration& packed, std::size_t lanes,
                                              const std::array<std::size_t, 3>& capacities) {
            auto reader = std::make_unique<BoundaryReader>(packed, lanes, capacities, boundary);
            const auto arena = reader->arena_bytes();
            return LoadedGeneration{std::move(reader), arena};
        };
        IncrementalService service(std::move(initial),
            {{{3, 0}, 8, 2}, {8, 8, 8}, 3}, loader);
#else
        const GenerationLoader loader = [&](const PackedGeneration& packed, std::size_t lanes) {
            auto reader = std::make_unique<BoundaryReader>(packed, lanes, boundary);
            const auto arena = reader->arena_bytes();
            return LoadedGeneration{std::move(reader), arena};
        };
        ReplacementService service(std::move(initial), {{3, 0}, 8, 2}, loader);
#endif
        const BatchProfile profile{2, 1};
        const std::vector<ClientRequest> client_requests{
            {fixture_address(1), {word_from_u64(1)}},
            {fixture_address(2), {word_from_u64(1)}}};
        std::uint64_t request_id = 0;
        const auto run_framed = [&](const BlockManifest& selected) {
            // The fixture supplies the client's expected root independently
            // of the response, as a trusted block header would in deployment.
            const auto& snapshot = snapshots.at(selected.block_id);
            const ClientContext expected{word_from_u64(++request_id), selected.block_id,
                snapshot.accounts.root_hash(), selected.tiers, profile};
            const auto request_frame = encode_request_frame(expected, client_requests);
            const ClientContext admission{expected.request_id, selected.block_id,
                selected.state_root, selected.tiers, profile};
            const auto received = decode_request_frame(admission, request_frame);
            const auto paths = make_path_requests(admission, received);
            auto pinned = service.run(selected.block_id, profile, paths);
            check(pinned, snapshot, paths);
            // Always use the completed batch's pinned manifest, including when
            // an update was prepared during the account/storage traversal.
            const ClientContext response_context{expected.request_id,
                pinned.manifest.block_id, pinned.manifest.state_root,
                pinned.manifest.tiers, profile};
            const auto response_frame = encode_response_frame(response_context,
                                                               received, pinned.proofs);
            const auto verified = verify_response_frame(expected, client_requests,
                                                         response_frame);
            for (const auto& account : verified) {
                require(!account.error, "client received an account error");
                for (const auto& slot : account.storage)
                    require(!slot.error, "client received a storage error");
            }
            return pinned;
        };
        const auto sizes = client_frame_sizes(ClientContext{{}, {}, {},
            service.served_head().tiers, profile});
        std::cout << "MPT mock latest-head "
#ifdef ETHEREUM_MPT_INCREMENTAL
                  << "incremental"
#else
                  << "replacement"
#endif
                  << " demo (no encrypted transport)\n"
                  << "batch Q=" << profile.requests << " K=" << profile.storage_slots
                  << " request_frame_bytes=" << sizes.request_bytes
                  << " response_frame_bytes=" << sizes.response_bytes << '\n';
        for (const auto& id : service.retained_blocks())
            run_framed(service.manifest(id));
        const auto save = [&] {
            if (!config.checkpoint_out.empty())
                save_public_history_checkpoint(config.checkpoint_out, service.history_checkpoint(), limits);
        };
        save();
        std::cout << "initial_fixture_index=" << first_index
                  << " restored=" << !config.checkpoint_in.empty()
                  << " retained=" << service.retained_blocks().size() << '\n';
        for (std::size_t i = first_index + 1; i <= config.through_index; ++i) {
            const auto before = service.served_head();
            bool prepared = false;
            boundary = [&] {
                require(service.batch_active(), "update injection requires an admitted batch");
                if (!service.prepare(blocks[i]))
                    service.prepare_reorg(blocks[i].block_id);
                require(!service.publish(), "generation published between account/storage phases");
                require(service.served_head().block_id == before.block_id,
                        "preparation changed the served head");
                prepared = true;
            };
            const auto pinned = run_framed(before);
            require(prepared && pinned.manifest.generation == before.generation &&
                    pinned.manifest.block_id == before.block_id, "batch lost its pinned generation");
            const auto overlap = service.memory();
            const auto ancestor = service.pending_common_ancestor();
            require(service.publish(), "replacement did not publish at batch boundary");
            require(!service.prepare(blocks[i]), "identical block delivery was not idempotent");
            for (const auto& id : service.retained_blocks())
                run_framed(service.manifest(id));
            save();
            const auto head = service.served_head();
            const auto updates = service.update_stats();
            std::cout << "block=" << head.number << " id=0x" << hex(head.block_id)
                      << " root=0x" << hex(head.state_root) << " generation=" << head.generation
                      << " retained=" << service.retained_blocks().size()
                      << " reorg=" << (blocks[i].parent_id != before.block_id)
                      << " common_ancestor=0x" << hex(*ancestor)
                      << " overlap_oram_arena_bytes="
                      << overlap.current_arena_bytes + overlap.staged_arena_bytes
                      << " appended_pages=" << updates.uploaded_pages[0] +
                         updates.uploaded_pages[1] + updates.uploaded_pages[2]
                      << " compactions=" << updates.compactions << '\n';
        }
#ifdef ETHEREUM_MPT_INCREMENTAL
        const auto before_compaction = service.memory().current_page_bytes;
        service.prepare_compaction();
        require(service.publish(), "explicit public compaction did not publish");
        require(service.memory().current_page_bytes <= before_compaction,
                "compaction increased packed page count for the same retained roots");
        for (const auto& id : service.retained_blocks())
            run_framed(service.manifest(id));
        const auto updates = service.update_stats();
        if (config.checkpoint_in.empty() && config.through_index == blocks.size() - 1)
            require(updates.incremental_publications != 0 && updates.compactions >= 2,
                    "full demo must exercise appends and periodic/explicit compaction");
        std::cout << "incremental_publications=" << updates.incremental_publications
                  << " replacement_publications=" << updates.replacement_publications
                  << " compactions=" << updates.compactions
                  << " page_bytes_before_compaction=" << before_compaction
                  << " page_bytes_after_compaction=" << service.memory().current_page_bytes << '\n';
#endif
        const auto memory = service.memory();
        rusage usage{};
        require(getrusage(RUSAGE_SELF, &usage) == 0, "cannot measure process peak RSS");
        // Linux ru_maxrss is KiB and is a whole-process high-water measurement.
        std::cout << "peak_two_generation_oram_arena_bytes=" << memory.peak_arena_bytes
                  << " peak_two_generation_page_value_bytes=" << memory.peak_page_bytes
                  << " process_peak_rss_bytes=" << static_cast<std::uint64_t>(usage.ru_maxrss) * 1024
                  << '\n';
        std::cout << "Verified fixture indices " << first_index << " through "
                  << config.through_index << " and retained client proof frames\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_updates: " << error.what() << '\n';
        return 1;
    }
}
