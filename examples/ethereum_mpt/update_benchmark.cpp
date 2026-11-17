// ethereum_mpt_update_benchmark: serialized read/update schedule on a synthetic
// linear chain; each block prepares an update, serves old-head proof batches,
// then publishes. Emits one JSON row; see README.md, "Read/update benchmark".

#include "client.hpp"
#include "fixture.hpp"
#include "page_map.hpp"
#include "version.hpp"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <string>
#include <sys/resource.h>

using namespace ethereum_mpt;

namespace {
using Clock = std::chrono::steady_clock;
using Counts = std::array<std::uint64_t, 3>;
constexpr std::uint64_t horizon = std::uint64_t{1} << 32;
constexpr std::size_t count_limit = 1000000;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}
std::uint64_t elapsed(Clock::time_point start, Clock::time_point end) {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
}
std::uint64_t sum(const Counts& a) { return a[0] + a[1] + a[2]; }
Counts difference(const Counts& a, const Counts& b) {
    return {a[0] - b[0], a[1] - b[1], a[2] - b[2]};
}
void add(Counts& a, const Counts& b) {
    for (std::size_t t = 0; t < 3; ++t) a[t] += b[t];
}
std::size_t number(const std::string& value) {
    if (value.empty()) throw std::invalid_argument("empty numeric argument");
    std::size_t result = 0;
    for (const auto c : value) {
        if (c < '0' || c > '9' || result > (count_limit - (c - '0')) / 10)
            throw std::invalid_argument("expected an unsigned integer at most 1000000");
        result = result * 10 + (c - '0');
    }
    return result;
}

struct Config {
    std::size_t accounts = 64, storage_entries = 8, blocks = 4;
    std::size_t read_batches_per_block = 2, delta_accounts = 1, storage_changes = 1;
    std::size_t retained_blocks = 2, page_headroom = 16, compact_after_updates = 0;
    std::size_t compact_at_fullness_percent = 0, compact_at_dead_bytes_percent = 0;
    BatchProfile batch{4, 1};
    TierProfile tiers{3, 0};
    PageBackend top_backend = PageBackend::tree;
    bool incremental = true;
};

Config parse(int argc, char** argv) {
    Config c;
    for (int i = 1; i < argc; ++i) {
        const std::string flag = argv[i];
        if (flag == "--help") {
            std::cout << "Usage: ethereum_mpt_update_benchmark [option value ...]\n"
                "  --accounts N --storage-entries N           genesis size (64, 8)\n"
                "  --q N --k N                               batch shape (4, 1)\n"
                "  --blocks N --read-batches-per-block N      updates, pending-head batches (4, 2)\n"
                "  --delta-accounts N --storage-changes N     changes per block/account (1, 1)\n"
                "  --retained-blocks N --page-headroom N      retention, spare pages/tier (2, 16)\n"
                "  --compact-after-updates N                  append interval; 0 disables (0)\n"
                "  --compact-at-fullness-percent N            page occupancy 1..100; 0 disables (0)\n"
                "  --compact-at-dead-bytes-percent N          dead record bytes 1..100; 0 disables (0)\n"
                "  --account-top N --storage-top N            cutoffs 0..4 (3, 0)\n"
                "  --top-backend tree|hierarchical            bulk always tree\n"
                "  --update-mode incremental|replacement     default incremental\n"
                "One JSON result; serialized synthetic updates, one caller, no workers.\n";
            std::exit(0);
        }
        if (++i == argc) throw std::invalid_argument("missing option value: " + flag);
        const std::string value = argv[i];
        if (flag == "--update-mode") {
            if (value != "incremental" && value != "replacement")
                throw std::invalid_argument("update mode must be incremental or replacement");
            c.incremental = value == "incremental";
        } else if (flag == "--top-backend") {
            if (value != "tree" && value != "hierarchical")
                throw std::invalid_argument("top backend must be tree or hierarchical");
            c.top_backend = value == "tree" ? PageBackend::tree : PageBackend::hierarchical;
        } else if (flag == "--accounts") c.accounts = number(value);
        else if (flag == "--storage-entries") c.storage_entries = number(value);
        else if (flag == "--q") c.batch.requests = number(value);
        else if (flag == "--k") c.batch.storage_slots = number(value);
        else if (flag == "--blocks") c.blocks = number(value);
        else if (flag == "--read-batches-per-block") c.read_batches_per_block = number(value);
        else if (flag == "--delta-accounts") c.delta_accounts = number(value);
        else if (flag == "--storage-changes") c.storage_changes = number(value);
        else if (flag == "--retained-blocks") c.retained_blocks = number(value);
        else if (flag == "--page-headroom") c.page_headroom = number(value);
        else if (flag == "--compact-after-updates") c.compact_after_updates = number(value);
        else if (flag == "--compact-at-fullness-percent" || flag == "--compact-at-dead-bytes-percent") {
            const auto percent = number(value);
            if (percent > 100) throw std::invalid_argument("compaction percentage must be 0..100");
            if (flag == "--compact-at-fullness-percent") c.compact_at_fullness_percent = percent;
            else c.compact_at_dead_bytes_percent = percent;
        }
        else if (flag == "--account-top" || flag == "--storage-top") {
            const auto depth = number(value);
            if (depth > 4) throw std::invalid_argument("tier cutoff must be 0..4");
            if (flag == "--account-top") c.tiers.account_top_depth = depth;
            else c.tiers.storage_top_depth = depth;
        } else throw std::invalid_argument("unknown option: " + flag);
    }
    if (!c.accounts || !c.blocks || !c.retained_blocks || c.delta_accounts > c.accounts)
        throw std::invalid_argument("accounts, blocks and retention must be positive; delta accounts <= accounts");
    if (c.read_batches_per_block > count_limit / c.blocks)
        throw std::invalid_argument("at most 1000000 measured batches are supported");
    client_frame_sizes(ClientContext{{}, {}, {}, c.tiers, c.batch});
    BatchTraversal({}, {}, c.tiers, c.batch);
    // Conservative whole-run read bound, including all retained-root probes.
    // Each actual map also checks initial writes and append writes before access.
    const auto probe_bound = std::uint64_t(c.blocks) * std::min(c.retained_blocks, c.blocks + 1);
    const auto batches = c.blocks * c.read_batches_per_block + probe_bound;
    const auto reads = proof_rounds * c.batch.requests * (1 + c.batch.storage_slots);
    if (batches > (horizon - 1) / reads)
        throw std::invalid_argument("workload exceeds conservative 2^32 request horizon");
    return c;
}

Address address(std::uint64_t id) {
    Address result{};
    for (std::size_t i = 0; i < 8; ++i) {
        result[19 - i] = static_cast<std::uint8_t>(id);
        id >>= 8;
    }
    return result;
}

// Oracle state is mutated directly, separately from apply_delta in the service.
// Roots use the local canonical implementation, not an independent chain client.
PublicState genesis(const Config& c) {
    PublicState state;
    for (std::size_t i = 1; i <= c.accounts; ++i) {
        PublicAccountState account;
        account.nonce = i;
        account.balance = word_from_u64(i * 1000);
        if (i % 2)
            for (std::size_t j = 1; j <= c.storage_entries; ++j)
                account.storage.emplace(word_from_u64(j), word_from_u64(j * 128));
        state.emplace(address(i), std::move(account));
    }
    return state;
}

MockBlockDelta next_block(const Config& c, std::size_t height, PublicState& state) {
    MockBlockDelta block;
    block.block_id = word_from_u64(height + 1);
    block.parent_id = word_from_u64(height);
    block.number = height;
    for (std::size_t a = 0; a < c.delta_accounts; ++a) {
        const auto id = 1 + ((height - 1) * c.delta_accounts + a) % c.accounts;
        auto& account = state.at(address(id));
        ++account.nonce;
        account.balance = word_from_u64(height * 1000000 + id);
        AccountUpsert upsert{address(id), account.nonce, account.balance, account.code_hash, false, {}};
        for (std::size_t s = 0; s < c.storage_changes; ++s) {
            const auto slot = word_from_u64(s + 1);
            const auto value = (height + s) % 3 == 0 ? Word{} :
                word_from_u64(height * 1000000 + s + 1);
            upsert.storage_changes.push_back({slot, value});
            if (value == Word{}) account.storage.erase(slot);
            else account.storage[slot] = value;
        }
        block.account_upserts.push_back(std::move(upsert));
    }
    return block;
}

std::vector<ClientRequest> requests(const Config& c, std::size_t height) {
    std::vector<ClientRequest> result;
    const auto first_changed = c.delta_accounts ?
        1 + ((height - 1) * c.delta_accounts) % c.accounts : 1;
    for (std::size_t q = 0; q < c.batch.requests; ++q) {
        // Changed accounts, duplicates and missing accounts; slots mix existing
        // and absent positions. All benchmark query choices are public.
        const auto id = q % 4 == 3 ? c.accounts + 1 :
            1 + (first_changed - 1 + (q % 4 == 2 ? 0 : q)) % c.accounts;
        ClientRequest request{address(id), {}};
        const auto slots = std::max({c.storage_entries, c.storage_changes, std::size_t{1}});
        for (std::size_t s = 0; s < c.batch.storage_slots; ++s)
            request.storage_slots.push_back(word_from_u64(s % 3 == 1 ? slots + 1 : 1 + s % slots));
        result.push_back(std::move(request));
    }
    return result;
}

Counts schedule(const Config& c, bool lanes) {
    Counts result{};
    for (std::size_t depth = 0; depth < proof_rounds; ++depth) {
        result[static_cast<std::size_t>(tier_for(TrieKind::account, depth, c.tiers))] +=
            lanes ? c.batch.requests : 1;
        if (c.batch.storage_slots)
            result[static_cast<std::size_t>(tier_for(TrieKind::storage, depth, c.tiers))] +=
                lanes ? c.batch.requests * c.batch.storage_slots : 1;
    }
    return result;
}

struct Counters {
    Counts read_ns{}, reads{}, calls{}, append_ns{}, appended{}, append_calls{}, fresh_pages{};
    std::uint64_t load_ns = 0, completion_ns = 0;
};

class MeasuredStore final : public PageStore {
 public:
    MeasuredStore(const PackedGeneration& packed, std::size_t lanes,
                  const std::array<std::size_t, 3>& capacities,
                  const Config& config, Counters& counters)
        : maps(packed, lanes, capacities, {config.top_backend, config.top_backend}),
          config_(config), counters_(counters) {}

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        const auto role = round_ < proof_rounds ? TrieKind::account : TrieKind::storage;
        require(tier == tier_for(role, round_ % proof_rounds, config_.tiers) &&
                count == config_.batch.requests * (role == TrieKind::account ? 1 : config_.batch.storage_slots),
                "update benchmark received a non-public read schedule");
        check_horizon(tier, count);
        const auto start = Clock::now();
        maps.read_pages_batch(tier, count, ids, output, found);
        const auto t = static_cast<std::size_t>(tier);
        counters_.read_ns[t] += elapsed(start, Clock::now());
        counters_.reads[t] += count;
        ++counters_.calls[t];
        round_ = (round_ + 1) % (proof_rounds * (config_.batch.storage_slots ? 2 : 1));
    }
    void write_pages_batch(Tier tier, std::uint64_t first, const std::vector<Page>& pages) override {
        check_horizon(tier, pages.size());
        const auto start = Clock::now();
        maps.write_pages_batch(tier, first, pages);
        const auto t = static_cast<std::size_t>(tier);
        counters_.append_ns[t] += elapsed(start, Clock::now());
        counters_.appended[t] += pages.size();
        counters_.append_calls[t] += (pages.size() + 15) / 16;
    }
    void finish_pending_work() override {
        const auto start = Clock::now();
        maps.finish_pending_work();
        counters_.completion_ns += elapsed(start, Clock::now());
    }
    std::array<std::size_t, 3> capacities() const override { return maps.capacities(); }
    TieredPageMaps maps;
 private:
    void check_horizon(Tier tier, std::size_t count) const {
        const auto* map = maps.map(tier);
        require(map && map->access_count() <= horizon && count <= horizon - map->access_count(),
                "update benchmark exceeds per-map request horizon including writes");
    }
    const Config& config_;
    Counters& counters_;
    std::size_t round_ = 0;
};

struct ReadSample { std::uint64_t service = 0, verification = 0; Counts read_ns{}; };

ReadSample read(VersionService& service, const Config& c, Counters& counters,
                const BlockManifest& selected, const Snapshot& snapshot,
                const std::vector<ClientRequest>& queries, std::uint64_t request_id) {
    const ClientContext expected{word_from_u64(request_id), selected.block_id,
        snapshot.accounts.root_hash(), c.tiers, c.batch};
    const auto request_frame = encode_request_frame(expected, queries);
    const auto before = counters;
    const auto start = Clock::now();
    const auto received = decode_request_frame(expected, request_frame);
    const auto paths = make_path_requests(expected, received);
    const auto result = service.run(selected.block_id, c.batch, paths);
    const ClientContext response_context{expected.request_id, result.manifest.block_id,
        result.manifest.state_root, result.manifest.tiers, c.batch};
    const auto frame = encode_response_frame(response_context, received, result.proofs);
    const auto finished = Clock::now();
    require(result.manifest.generation == selected.generation &&
            difference(counters.reads, before.reads) == schedule(c, true) &&
            difference(counters.calls, before.calls) == schedule(c, false),
            "pinned generation or fixed read accounting mismatch");
    const auto decoded = verify_response_frame(expected, queries, frame);
    for (std::size_t q = 0; q < decoded.size(); ++q) {
        const auto& account = decoded[q];
        require(!account.error && account.proof == prove(snapshot.accounts, paths[q].account_key),
                "update benchmark account proof differs from canonical reference");
        const auto root = account.account ? account.account->storage_root : empty_trie_root();
        for (std::size_t s = 0; s < account.storage.size(); ++s) {
            const auto proof = root == empty_trie_root() ? Proof{} :
                prove(snapshot.storage_tries.at(root), paths[q].storage_keys[s]);
            require(!account.storage[s].error && account.storage[s].proof == proof,
                    "update benchmark storage proof differs from canonical reference");
        }
    }
    return {elapsed(start, finished), elapsed(finished, Clock::now()),
        difference(counters.read_ns, before.read_ns)};
}

struct Sample {
    BlockManifest head;
    bool append = false, compaction = false;
    std::uint64_t prepare = 0, publish = 0, fresh_load = 0, completion = 0;
    std::uint64_t wall_lag = 0, verification = 0, read_total = 0;
    Counts read_ns{}, append_ns{}, appended{}, append_calls{}, fresh_pages{};
    GenerationOccupancy occupancy;
    std::vector<std::uint64_t> reads;
    std::size_t retained = 0, overlap_arena = 0, arena = 0, page_values = 0, slack = 0;
    std::size_t builder_staged = 0, builder_published = 0;
};

template<class T>
void array_json(const std::array<T, 3>& a) {
    std::cout << '[' << a[0] << ',' << a[1] << ',' << a[2] << ']';
}
void times_json(const std::vector<std::uint64_t>& values) {
    std::cout << '[';
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << values[i];
    }
    std::cout << ']';
}
void percentile_json(std::vector<std::uint64_t> values, unsigned percent) {
    if (values.empty()) { std::cout << "null"; return; }
    std::sort(values.begin(), values.end());
    std::cout << values[(values.size() * percent + 99) / 100 - 1];
}

void run(const Config& c) {
    auto oracle_start = Clock::now();
    auto state = genesis(c);
    auto initial_snapshot = snapshot_from_state(state);
    PublicCheckpoint checkpoint{{word_from_u64(1), {}, initial_snapshot.accounts.root_hash(), 0}, {}, state};
    std::map<Hash, Snapshot> snapshots;
    snapshots.emplace(checkpoint.block.block_id, std::move(initial_snapshot));
    std::uint64_t oracle_ns = elapsed(oracle_start, Clock::now());
    Counters counters;
    MeasuredStore* newest_store = nullptr;
    const IncrementalLoader loader = [&](const PackedGeneration& packed, std::size_t lanes,
                                       const std::array<std::size_t, 3>& capacities) {
        for (const auto& pages : packed.pages)
            require(pages.size() < horizon, "initial loading exceeds request horizon");
        const auto start = Clock::now();
        auto store = std::make_unique<MeasuredStore>(packed, lanes, capacities, c, counters);
        counters.load_ns += elapsed(start, Clock::now());
        for (std::size_t t = 0; t < 3; ++t) counters.fresh_pages[t] += packed.pages[t].size();
        const auto arena = store->maps.arena_bytes();
        newest_store = store.get();
        return LoadedGeneration{std::move(store), arena};
    };
    const ReplacementOptions options{c.tiers, c.retained_blocks,
        std::max(c.batch.requests, c.batch.requests * c.batch.storage_slots)};
    const auto setup_start = Clock::now();
    std::unique_ptr<VersionService> service;
    if (c.incremental)
        service = std::make_unique<IncrementalService>(std::move(checkpoint),
            IncrementalOptions{options, {c.page_headroom, c.page_headroom, c.page_headroom},
                               c.compact_after_updates, c.compact_at_fullness_percent,
                               c.compact_at_dead_bytes_percent}, loader);
    else
        service = std::make_unique<ReplacementService>(std::move(checkpoint), options,
            [&](const PackedGeneration& packed, std::size_t lanes) {
                return loader(packed, lanes, {packed.pages[0].size(), packed.pages[1].size(), packed.pages[2].size()});
            });
    const auto setup_ns = elapsed(setup_start, Clock::now());
    const auto initial = counters;
    std::vector<Sample> samples;
    samples.reserve(c.blocks);
    std::uint64_t request_id = 0, validation_batches = 0;
    std::size_t peak_builder = service->public_builder_memory().payload_bytes();
    for (std::size_t height = 1; height <= c.blocks; ++height) {
        oracle_start = Clock::now();
        auto block = next_block(c, height, state);
        auto snapshot = snapshot_from_state(state);
        block.expected_state_root = snapshot.accounts.root_hash();
        snapshots.emplace(block.block_id, std::move(snapshot));
        const auto queries = requests(c, height);
        oracle_ns += elapsed(oracle_start, Clock::now());
        const auto previous = service->served_head();
        const auto before = counters;
        const auto stats_before = service->update_stats();
        Sample sample;
        const auto arrived = Clock::now();
        require(service->prepare(block), "synthetic block unexpectedly duplicated");
        const auto prepared = Clock::now();
        sample.prepare = elapsed(arrived, prepared);
        require(service->observed_head().block_id == block.block_id &&
                service->served_head().block_id == previous.block_id &&
                service->pending_head()->state_root == block.expected_state_root,
                "preparation changed served head or lost the observed root");
        const auto overlap = service->memory();
        sample.overlap_arena = overlap.current_arena_bytes + overlap.staged_arena_bytes;
        sample.builder_staged = service->public_builder_memory().payload_bytes();
        for (std::size_t r = 0; r < c.read_batches_per_block; ++r) {
            const auto measured = read(*service, c, counters, previous,
                snapshots.at(previous.block_id), queries, ++request_id);
            sample.reads.push_back(measured.service);
            sample.read_total += measured.service;
            sample.verification += measured.verification;
            add(sample.read_ns, measured.read_ns);
        }
        const auto publish_start = Clock::now();
        require(service->publish(), "update did not publish at complete batch boundary");
        const auto published = Clock::now();
        sample.publish = elapsed(publish_start, published);
        sample.wall_lag = elapsed(arrived, published);
        sample.head = service->served_head();
        require(sample.head.block_id == block.block_id && sample.head.state_root == block.expected_state_root &&
                service->observed_head().block_id == sample.head.block_id && !service->pending_head(),
                "published block/root binding mismatch");
        const auto stats = service->update_stats();
        sample.append = stats.incremental_publications != stats_before.incremental_publications;
        sample.compaction = stats.compactions != stats_before.compactions;
        sample.fresh_load = counters.load_ns - before.load_ns;
        sample.completion = counters.completion_ns - before.completion_ns;
        sample.append_ns = difference(counters.append_ns, before.append_ns);
        sample.appended = difference(counters.appended, before.appended);
        sample.append_calls = difference(counters.append_calls, before.append_calls);
        sample.fresh_pages = difference(counters.fresh_pages, before.fresh_pages);
        require(sample.prepare + sample.publish >= sample.fresh_load + sample.completion + sum(sample.append_ns),
                "update timing partition is invalid");
        const auto memory = service->memory();
        // Public reachability sampling is reporting overhead, after the timed
        // publication and arrival-to-publication wall interval have both ended.
        sample.occupancy = service->occupancy();
        sample.arena = memory.current_arena_bytes;
        sample.page_values = memory.current_page_bytes;
        for (const auto& tier : service->packing_stats())
            sample.slack += tier.real_pages * page_bytes - tier.record_bytes;
        sample.builder_published = service->public_builder_memory().payload_bytes();
        peak_builder = std::max({peak_builder, sample.builder_staged, sample.builder_published});
        const auto retained = service->retained_blocks();
        sample.retained = retained.size();
        // Mandatory new/retained-root probes are verification overhead, excluded
        // from measured workload throughput, lag, and compaction duty cycle.
        for (const auto& id : retained) {
            read(*service, c, counters, service->manifest(id), snapshots.at(id), queries, ++request_id);
            ++validation_batches;
        }
        for (auto it = snapshots.begin(); it != snapshots.end();) {
            if (std::find(retained.begin(), retained.end(), it->first) == retained.end()) it = snapshots.erase(it);
            else ++it;
        }
        samples.push_back(std::move(sample));
    }
    const auto drain_start = Clock::now();
    newest_store->finish_pending_work();
    const auto drain_ns = elapsed(drain_start, Clock::now());
    const auto stats = service->update_stats();
    require(stats.uploaded_pages == counters.appended && stats.failed_uploads == 0,
            "completed upload accounting mismatch");
    std::uint64_t read_total = 0, pause_total = 0, compaction_total = 0;
    std::vector<std::uint64_t> read_times;
    for (const auto& sample : samples) {
        read_total += sample.read_total;
        pause_total += sample.prepare + sample.publish;
        if (sample.compaction) compaction_total += sample.prepare + sample.publish;
        read_times.insert(read_times.end(), sample.reads.begin(), sample.reads.end());
    }
    const auto scheduled = read_total + pause_total;
    require(scheduled != 0, "invalid benchmark clock");
    rusage usage{};
    require(getrusage(RUSAGE_SELF, &usage) == 0, "cannot measure process peak RSS");
    const auto memory = service->memory();
    const auto builder = service->public_builder_memory();
    const auto frames = client_frame_sizes(ClientContext{{}, {}, {}, c.tiers, c.batch});
    std::cout << std::setprecision(12)
        << "{\"schema\":\"ethereum_mpt_update_benchmark_v1\",\"update_mode\":\""
        << (c.incremental ? "incremental" : "replacement")
        << "\",\"canonical_builder\":\"" << (c.incremental ? "path_copy" : "full_rebuild")
        << "\",\"page_bytes\":" << page_bytes
        << ",\"accounts\":" << c.accounts << ",\"storage_entries\":" << c.storage_entries
        << ",\"q\":" << c.batch.requests << ",\"k\":" << c.batch.storage_slots
        << ",\"blocks\":" << c.blocks << ",\"read_batches_per_block\":" << c.read_batches_per_block
        << ",\"delta_accounts\":" << c.delta_accounts << ",\"storage_changes\":" << c.storage_changes
        << ",\"retained_blocks\":" << c.retained_blocks << ",\"page_headroom\":" << c.page_headroom
        << ",\"compact_after_updates\":" << c.compact_after_updates
        << ",\"compact_at_fullness_percent\":" << c.compact_at_fullness_percent
        << ",\"compact_at_dead_bytes_percent\":" << c.compact_at_dead_bytes_percent
        << ",\"account_top\":" << unsigned(c.tiers.account_top_depth)
        << ",\"storage_top\":" << unsigned(c.tiers.storage_top_depth)
        << ",\"top_backend\":\"" << page_backend_name(c.top_backend)
        << "\",\"bulk_backend\":\"tree\",\"caller_threads\":1,\"worker_threads\":0"
        << ",\"request_horizon_per_map\":" << horizon
        << ",\"queue_fill_latency_ns\":null,\"physical_oram_traffic_bytes\":null"
        << ",\"measured_batches\":" << read_times.size() << ",\"validation_batches\":" << validation_batches
        << ",\"verified_batches\":" << request_id << ",\"initial_service_setup_ns\":" << setup_ns
        << ",\"oracle_build_ns\":" << oracle_ns << ",\"initial_load_ns\":" << initial.load_ns
        << ",\"final_drain_ns\":" << drain_ns << ",\"total_read_service_ns\":" << read_total
        << ",\"total_update_pause_ns\":" << pause_total << ",\"total_scheduled_service_ns\":" << scheduled
        << ",\"total_compaction_pause_ns\":" << compaction_total
        << ",\"compaction_duty_cycle\":" << double(compaction_total) / scheduled
        << ",\"requests_per_scheduled_service_second\":" << 1e9 * c.batch.requests * read_times.size() / scheduled
        << ",\"read_service_p50_ns\":";
    percentile_json(read_times, 50);
    std::cout << ",\"read_service_p95_ns\":"; percentile_json(read_times, 95);
    std::cout << ",\"read_service_p99_ns\":"; percentile_json(read_times, 99);
    std::cout << ",\"round_calls_per_batch\":"; array_json(schedule(c, false));
    std::cout << ",\"page_reads_per_batch\":"; array_json(schedule(c, true));
    std::cout << ",\"initial_loaded_pages\":"; array_json(initial.fresh_pages);
    std::cout << ",\"fresh_loaded_pages\":"; array_json(difference(counters.fresh_pages, initial.fresh_pages));
    std::cout << ",\"appended_pages\":"; array_json(counters.appended);
    std::cout << ",\"logical_update_write_bytes\":" <<
        (sum(counters.appended) + sum(difference(counters.fresh_pages, initial.fresh_pages))) * page_bytes
        << ",\"request_frame_bytes\":" << frames.request_bytes
        << ",\"response_frame_bytes\":" << frames.response_bytes
        << ",\"incremental_publications\":" << stats.incremental_publications
        << ",\"replacement_publications\":" << stats.replacement_publications
        << ",\"compactions\":" << stats.compactions
        << ",\"final_state_root\":\"0x" << hex(service->served_head().state_root) << '"'
        << ",\"peak_oram_arena_bytes\":" << memory.peak_arena_bytes
        << ",\"peak_page_value_bytes\":" << memory.peak_page_bytes
        << ",\"sampled_peak_builder_payload_bytes\":" << peak_builder
        << ",\"process_peak_rss_bytes\":" << std::uint64_t(usage.ru_maxrss) * 1024
        << ",\"builder_payload\":{\"retained_versions\":" << builder.retained_versions
        << ",\"public_state_bytes\":" << builder.public_state_bytes
        << ",\"canonical_trie_rlp_bytes\":" << builder.canonical_trie_rlp_bytes
        << ",\"packed_image_bytes\":" << builder.packed_image_bytes
        << ",\"staged_upload_bytes\":" << builder.staged_upload_bytes
        << ",\"identity_bytes\":" << builder.identity_bytes
        << ",\"payload_bytes\":" << builder.payload_bytes() << "},\"tiers\":[";
    const auto packing = service->packing_stats();
    const auto& occupancy = samples.back().occupancy;
    for (std::size_t t = 0; t < 3; ++t) {
        if (t) std::cout << ',';
        const auto& p = packing[t];
        const auto* map = newest_store->maps.map(static_cast<Tier>(t));
        std::cout << "{\"name\":\"" << tier_name(static_cast<Tier>(t))
            << "\",\"backend\":\"" << (map ? map->backend_name() : "disabled")
            << "\",\"S\":" << p.canonical_bytes << ",\"N\":" << p.records
            << ",\"E\":" << p.ordinary_links << ",\"A\":" << p.account_leaves
            << ",\"R\":" << p.record_bytes << ",\"P\":" << p.real_pages
            << ",\"packing_runs\":" << p.packing_runs
            << ",\"allocated_pages\":" << occupancy.allocated_pages[t]
            << ",\"live_record_bytes\":" << occupancy.live_record_bytes[t]
            << ",\"dead_record_bytes\":" << occupancy.dead_record_bytes[t]
            << ",\"requested_capacity\":" << newest_store->capacities()[t]
            << ",\"allocated_capacity\":" << (map ? map->capacity() : 0)
            << ",\"arena_bytes\":" << (map ? map->arena_bytes() : 0) << '}';
    }
    std::cout << "],\"samples\":[";
    for (std::size_t i = 0; i < samples.size(); ++i) {
        if (i) std::cout << ',';
        const auto& s = samples[i];
        std::cout << "{\"block_number\":" << s.head.number << ",\"block_id\":\"0x" << hex(s.head.block_id)
            << "\",\"state_root\":\"0x" << hex(s.head.state_root) << "\",\"generation\":" << s.head.generation
            << ",\"publication\":\"" << (s.append ? "append" : "replacement")
            << "\",\"compaction\":" << (s.compaction ? "true" : "false")
            << ",\"prepare_ns\":" << s.prepare << ",\"publish_ns\":" << s.publish
            << ",\"update_pause_ns\":" << s.prepare + s.publish
            << ",\"fresh_load_ns\":" << s.fresh_load << ",\"completion_ns\":" << s.completion
            << ",\"append_write_ns\":"; array_json(s.append_ns);
        std::cout << ",\"read_service_ns\":"; times_json(s.reads);
        std::cout << ",\"read_service_total_ns\":" << s.read_total << ",\"page_read_ns\":"; array_json(s.read_ns);
        std::cout << ",\"scheduled_service_lag_ns\":" << s.prepare + s.publish + s.read_total
            << ",\"arrival_to_publish_wall_ns\":" << s.wall_lag
            << ",\"verification_while_pending_ns\":" << s.verification
            << ",\"pending_block_lag\":1,\"published_block_lag\":0"
            << ",\"fresh_loaded_pages\":"; array_json(s.fresh_pages);
        std::cout << ",\"appended_pages\":"; array_json(s.appended);
        std::cout << ",\"append_oram_calls\":"; array_json(s.append_calls);
        std::cout << ",\"allocated_pages\":"; array_json(s.occupancy.allocated_pages);
        std::cout << ",\"page_capacities\":"; array_json(s.occupancy.page_capacities);
        std::cout << ",\"live_record_bytes\":"; array_json(s.occupancy.live_record_bytes);
        std::cout << ",\"dead_record_bytes\":"; array_json(s.occupancy.dead_record_bytes);
        std::cout << ",\"retained_blocks\":" << s.retained << ",\"validation_batches\":" << s.retained
            << ",\"overlap_oram_arena_bytes\":" << s.overlap_arena
            << ",\"oram_arena_bytes\":" << s.arena << ",\"packed_page_value_bytes\":" << s.page_values
            << ",\"packing_slack_bytes\":" << s.slack
            << ",\"builder_payload_bytes_staged\":" << s.builder_staged
            << ",\"builder_payload_bytes_published\":" << s.builder_published << '}';
    }
    std::cout << "]}\n";
    // The row is the only output; a failed write must not exit 0.
    std::cout.flush();
    if (!std::cout) throw std::runtime_error("cannot write the benchmark result");
}
}  // namespace

int main(int argc, char** argv) {
    try { run(parse(argc, argv)); }
    catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_update_benchmark: " << error.what() << '\n';
        return 1;
    }
}
