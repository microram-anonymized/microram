// ethereum_mpt_benchmark: serves disclosed synthetic Ethereum account/storage
// proof batches through real ORAM maps and emits one JSON row with service
// latency samples, per-tier call/read counts, packing and memory accounting.
// Every response is verified by the client outside the timed service interval.
// See README.md, "Read benchmark".

#include "client.hpp"
#include "fixture.hpp"
#include "page_map.hpp"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <sys/resource.h>

using namespace ethereum_mpt;

namespace {
using Clock = std::chrono::steady_clock;
using Counts = std::array<std::uint64_t, 3>;
constexpr std::uint64_t request_horizon = std::uint64_t{1} << 32;

std::uint64_t elapsed(Clock::time_point start, Clock::time_point end) {
    return std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();
}

void require(bool ok, const char* message) {
    if (!ok) throw std::runtime_error(message);
}

struct Config {
    std::size_t accounts = 256, storage_entries = 64;
    BatchProfile batch{8, 1};
    TierProfile tiers{3, 0};
    PageBackend top_backend = PageBackend::tree;
    bool scalar = false;
    std::size_t warmup = 1, samples = 5;
};

std::size_t number(const std::string& value) {
    if (value.empty()) throw std::invalid_argument("empty numeric argument");
    std::size_t result = 0;
    for (const auto c : value) {
        if (c < '0' || c > '9' ||
            result > (std::numeric_limits<std::size_t>::max() - (c - '0')) / 10)
            throw std::invalid_argument("expected an unsigned decimal integer");
        result = result * 10 + (c - '0');
    }
    return result;
}

Config parse(int argc, char** argv) {
    Config config;
    for (int i = 1; i < argc; ++i) {
        const std::string flag = argv[i];
        if (flag == "--help") {
            std::cout << "Usage: ethereum_mpt_benchmark [option value ...]\n"
                "  --accounts N          synthetic accounts (default 256)\n"
                "  --storage-entries N   entries in one shared storage trie (64)\n"
                "  --q N --k N           requests and storage slots per request (8, 1)\n"
                "  --account-top N --storage-top N   public cutoffs, 0..4 (3, 0)\n"
                "  --top-backend tree|hierarchical   bulk always tree (tree)\n"
                "  --mode batch|scalar   scalar splits each round into one-lane calls\n"
                "  --warmup N --samples N           complete batches (1, 5)\n"
                "One JSON result; fixed one-caller budget, no workers or arrival queue.\n";
            std::exit(0);
        }
        if (++i == argc) throw std::invalid_argument("missing option value: " + flag);
        const std::string value = argv[i];
        if (flag == "--mode") {
            if (value != "scalar" && value != "batch")
                throw std::invalid_argument("mode must be scalar or batch");
            config.scalar = value == "scalar";
        } else if (flag == "--top-backend") {
            if (value != "tree" && value != "hierarchical")
                throw std::invalid_argument("top backend must be tree or hierarchical");
            config.top_backend = value == "tree" ? PageBackend::tree : PageBackend::hierarchical;
        } else if (flag == "--accounts") config.accounts = number(value);
        else if (flag == "--storage-entries") config.storage_entries = number(value);
        else if (flag == "--q") config.batch.requests = number(value);
        else if (flag == "--k") config.batch.storage_slots = number(value);
        else if (flag == "--warmup") config.warmup = number(value);
        else if (flag == "--samples") config.samples = number(value);
        else if (flag == "--account-top" || flag == "--storage-top") {
            const auto depth = number(value);
            if (depth > 4) throw std::invalid_argument("benchmark tier cutoff must be 0..4");
            if (flag == "--account-top") config.tiers.account_top_depth = depth;
            else config.tiers.storage_top_depth = depth;
        } else throw std::invalid_argument("unknown option: " + flag);
    }
    // Public admission bounds keep generation, samples and arithmetic bounded.
    if (config.accounts > 1000000 || config.storage_entries > 1000000 ||
        config.samples == 0 || config.samples > 1000000 || config.warmup > 1000000)
        throw std::invalid_argument("dataset and iteration counts must be at most 1000000; samples > 0");
    // Validate frame and traversal arithmetic before building public tries/maps.
    client_frame_sizes(ClientContext{{}, {}, {}, config.tiers, config.batch});
    BatchTraversal({}, {}, config.tiers, config.batch);
    return config;
}

Address address_from_id(std::uint64_t id) {
    Address address{};
    for (std::size_t i = 0; i < 8; ++i) {
        address[19 - i] = static_cast<std::uint8_t>(id);
        id >>= 8;
    }
    return address;
}

// Public, deterministic synthetic state. Odd accounts share one storage trie;
// even accounts have empty storage. This is not an Ethereum state distribution.
Snapshot make_snapshot(const Config& config) {
    std::vector<Entry> slots, accounts;
    for (std::size_t i = 1; i <= config.storage_entries; ++i) {
        const auto slot = word_from_u64(i);
        slots.push_back({keccak256(slot.data(), slot.size()),
                         encode_storage(word_from_u64(i * 128))});
    }
    auto storage = build_trie(TrieKind::storage, slots);
    for (std::size_t i = 1; i <= config.accounts; ++i) {
        const auto address = address_from_id(i);
        Account account;
        account.nonce = i;
        account.balance = word_from_u64(i * 1000);
        if (i % 2) account.storage_root = storage.root_hash();
        accounts.push_back({keccak256(address.data(), address.size()), encode_account(account)});
    }
    Snapshot snapshot{build_trie(TrieKind::account, accounts), {}};
    if (config.accounts != 0 && config.storage_entries != 0)
        snapshot.storage_tries.emplace(storage.root_hash(), std::move(storage));
    return snapshot;
}

std::vector<ClientRequest> make_requests(const Config& config) {
    std::vector<ClientRequest> requests;
    for (std::size_t q = 0; q < config.batch.requests; ++q) {
        // Eight-lane pattern includes duplicates, absent accounts and empty
        // storage. All choices are disclosed synthetic benchmark inputs.
        const auto pattern = q % 8;
        const auto id = pattern == 3 || config.accounts == 0 ? config.accounts + 1 :
            (pattern == 4 ? 1 : 1 + pattern % config.accounts);
        ClientRequest request{address_from_id(id), {}};
        for (std::size_t s = 0; s < config.batch.storage_slots; ++s) {
            const auto slot = s % 3 == 1 || config.storage_entries == 0 ?
                config.storage_entries + 1 : 1 + (s % 3) % config.storage_entries;
            request.storage_slots.push_back(word_from_u64(slot));
        }
        requests.push_back(std::move(request));
    }
    return requests;
}

Counts round_counts(const Config& config) {
    Counts rounds{};
    for (std::size_t d = 0; d < proof_rounds; ++d) {
        ++rounds[static_cast<std::size_t>(tier_for(TrieKind::account, d, config.tiers))];
        if (config.batch.storage_slots)
            ++rounds[static_cast<std::size_t>(tier_for(TrieKind::storage, d, config.tiers))];
    }
    return rounds;
}

Counts access_counts(const Config& config) {
    Counts reads{};
    for (std::size_t d = 0; d < proof_rounds; ++d) {
        reads[static_cast<std::size_t>(tier_for(TrieKind::account, d, config.tiers))] +=
            config.batch.requests;
        if (config.batch.storage_slots)
            reads[static_cast<std::size_t>(tier_for(TrieKind::storage, d, config.tiers))] +=
                config.batch.requests * config.batch.storage_slots;
    }
    return reads;
}

// Benchmark-only scalar baseline. Every round's complete independent input is
// prepared by BatchTraversal before this wrapper splits it. No IDs or results
// affect the split, timing boundaries, counters, or public lane schedule.
class MeasuredReader final : public PageReader {
 public:
    MeasuredReader(TieredPageMaps& maps, const Config& config) : maps_(maps), config_(config) {}
    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        const auto role = round_ < proof_rounds ? TrieKind::account : TrieKind::storage;
        require(round_ < proof_rounds * (config_.batch.storage_slots ? 2 : 1) &&
            tier == tier_for(role, round_ % proof_rounds, config_.tiers) &&
            count == config_.batch.requests * (role == TrieKind::account ? 1 :
                                               config_.batch.storage_slots),
            "benchmark received a non-public traversal schedule");
        const auto start = Clock::now();
        if (config_.scalar) {
            for (std::size_t i = 0; i < count; ++i)
                maps_.read_pages_batch(tier, 1, ids + i, output + i, found + i);
        } else maps_.read_pages_batch(tier, count, ids, output, found);
        const auto end = Clock::now();
        read_ns[static_cast<std::size_t>(tier)] += elapsed(start, end);
        ++round_;
    }
    std::size_t max_lanes() const override { return maps_.max_lanes(); }
    Counts read_ns{};
    std::size_t rounds() const { return round_; }
 private:
    TieredPageMaps& maps_;
    const Config& config_;
    std::size_t round_ = 0;
};

struct Sample {
    std::uint64_t service = 0, request = 0, traversal = 0, response = 0;
    Counts read_ns{};
};

std::uint64_t sum(const Counts& values) { return values[0] + values[1] + values[2]; }

void verify(const Snapshot& snapshot, const ClientContext& context,
            const std::vector<ClientRequest>& requests, const Bytes& frame,
            const std::vector<PathRequest>& paths) {
    const auto decoded = verify_response_frame(context, requests, frame);
    for (std::size_t q = 0; q < decoded.size(); ++q) {
        const auto& answer = decoded[q];
        require(!answer.error && answer.proof == prove(snapshot.accounts, paths[q].account_key),
                "benchmark account proof differs from canonical reference");
        const auto root = answer.account ? answer.account->storage_root : empty_trie_root();
        for (std::size_t s = 0; s < answer.storage.size(); ++s) {
            const auto expected = root == empty_trie_root() ? Proof{} :
                prove(snapshot.storage_tries.at(root), paths[q].storage_keys[s]);
            require(!answer.storage[s].error && answer.storage[s].proof == expected,
                    "benchmark storage proof differs from canonical reference");
        }
    }
}

void array_json(const Counts& values) {
    std::cout << '[' << values[0] << ',' << values[1] << ',' << values[2] << ']';
}

std::uint64_t percentile(std::vector<std::uint64_t> values, unsigned percent) {
    std::sort(values.begin(), values.end());
    // Nearest rank, with p99 of small runs intentionally equal to their maximum.
    return values[(values.size() * percent + 99) / 100 - 1];
}

void run(const Config& config) {
    const auto build_start = Clock::now();
    const auto snapshot = make_snapshot(config);
    const auto packed = pack_snapshot(snapshot, config.tiers);
    const auto build_end = Clock::now();
    const auto reads = access_counts(config);
    const auto rounds = round_counts(config);
    const auto calls = config.scalar ? reads : rounds;
    const auto iterations = config.warmup + config.samples;
    for (std::size_t t = 0; t < 3; ++t) {
        if (packed.pages[t].size() > request_horizon ||
            reads[t] > (request_horizon - packed.pages[t].size()) / iterations)
            throw std::invalid_argument("benchmark exceeds per-map 2^32 request horizon including loading");
    }
    const auto load_start = Clock::now();
    TieredPageMaps maps(packed,
        std::max(config.batch.requests, config.batch.requests * config.batch.storage_slots),
        TieredPageMapOptions{config.top_backend, config.top_backend});
    const auto load_end = Clock::now();
    const auto requests = make_requests(config);
    const ClientContext context{word_from_u64(1), {}, packed.state_root, config.tiers, config.batch};
    const auto request_frame = encode_request_frame(context, requests);
    const auto frame_sizes = client_frame_sizes(context);
    std::vector<Sample> samples;
    samples.reserve(config.samples);
    for (std::size_t i = 0; i < iterations; ++i) {
        MeasuredReader reader(maps, config);
        const auto before_calls = maps.calls(), before_reads = maps.accesses();
        const auto start = Clock::now();
        const auto received = decode_request_frame(context, request_frame);
        const auto paths = make_path_requests(context, received);
        const auto decoded = Clock::now();
        const auto result = BatchTraversal(packed.state_root, packed.account_root,
            config.tiers, config.batch).run(reader, paths);
        const auto traversed = Clock::now();
        const auto response = encode_response_frame(context, received, result);
        const auto finished = Clock::now();
        require(reader.rounds() == sum(rounds), "benchmark round count mismatch");
        for (std::size_t t = 0; t < 3; ++t)
            require(maps.calls()[t] - before_calls[t] == calls[t] &&
                    maps.accesses()[t] - before_reads[t] == reads[t],
                    "benchmark page accounting mismatch");
        require(response.size() == frame_sizes.response_bytes, "benchmark response width changed");
        // Reference dictionaries and variable-time client work stay outside all
        // service timings. Even warmups must return valid, complete proofs.
        verify(snapshot, context, requests, response, paths);
        if (i >= config.warmup)
            samples.push_back({elapsed(start, finished), elapsed(start, decoded),
                elapsed(decoded, traversed), elapsed(traversed, finished), reader.read_ns});
    }
    // Flush deferred tail work and detect any pending backend failure before
    // emitting success. Report this boundary separately from batch latency.
    const auto drain_start = Clock::now();
    maps.finish_pending_work();
    const auto drain_ns = elapsed(drain_start, Clock::now());
    std::uint64_t total_service = 0, total_request = 0, total_traversal = 0, total_response = 0;
    Counts total_reads{};
    std::vector<std::uint64_t> service_times;
    for (const auto& sample : samples) {
        total_service += sample.service;
        total_request += sample.request;
        total_traversal += sample.traversal;
        total_response += sample.response;
        service_times.push_back(sample.service);
        for (std::size_t t = 0; t < 3; ++t) total_reads[t] += sample.read_ns[t];
    }
    require(total_service != 0 && total_traversal >= sum(total_reads), "invalid benchmark clock readings");
    rusage usage{};
    require(getrusage(RUSAGE_SELF, &usage) == 0, "cannot read process high-water RSS");
    const auto stats = packed.total_stats();
    std::cout << std::setprecision(12)
        << "{\"schema\":\"ethereum_mpt_read_benchmark_v1\",\"mode\":\""
        << (config.scalar ? "scalar" : "batch") << "\",\"page_bytes\":" << page_bytes
        << ",\"accounts\":" << config.accounts << ",\"storage_entries\":" << config.storage_entries
        << ",\"q\":" << config.batch.requests << ",\"k\":" << config.batch.storage_slots
        << ",\"account_top\":" << unsigned(config.tiers.account_top_depth)
        << ",\"storage_top\":" << unsigned(config.tiers.storage_top_depth)
        << ",\"top_backend\":\"" << page_backend_name(config.top_backend)
        << "\",\"bulk_backend\":\"tree\",\"caller_threads\":1,\"worker_threads\":0"
        << ",\"request_horizon_per_map\":" << request_horizon
        << ",\"state_root\":\"0x" << hex(packed.state_root) << "\",\"warmup_batches\":" << config.warmup
        << ",\"measured_batches\":" << config.samples << ",\"verified_batches\":" << iterations
        << ",\"queue_fill_latency_ns\":null,\"physical_oram_traffic_bytes\":null"
        << ",\"build_pack_ns\":" << elapsed(build_start, build_end)
        << ",\"initial_load_ns\":" << elapsed(load_start, load_end)
        << ",\"final_drain_ns\":" << drain_ns
        << ",\"batch_service_p50_ns\":" << percentile(service_times, 50)
        << ",\"batch_service_p95_ns\":" << percentile(service_times, 95)
        << ",\"batch_service_p99_ns\":" << percentile(service_times, 99)
        << ",\"requests_per_service_second\":" <<
            (1e9 * double(config.batch.requests) * config.samples / total_service)
        << ",\"total_batch_service_ns\":" << total_service
        << ",\"total_request_decode_hash_ns\":" << total_request
        << ",\"total_traversal_ns\":" << total_traversal
        << ",\"total_page_read_ns\":";
    array_json(total_reads);
    std::cout << ",\"total_local_traversal_ns\":" << total_traversal - sum(total_reads)
        << ",\"total_response_encode_ns\":" << total_response
        << ",\"round_calls_per_batch\":";
    array_json(rounds);
    std::cout << ",\"oram_calls_per_batch\":";
    array_json(calls);
    std::cout << ",\"page_reads_per_batch\":";
    array_json(reads);
    std::cout << ",\"logical_page_read_bytes_per_batch\":" << sum(reads) * page_bytes
        << ",\"node_hash_permutations_per_batch\":" << sum(reads) * 4
        << ",\"request_frame_bytes\":" << frame_sizes.request_bytes
        << ",\"response_frame_bytes\":" << frame_sizes.response_bytes
        << ",\"proof_slot_bytes\":" << sizeof(FixedProof) * config.batch.requests *
                                          (1 + config.batch.storage_slots)
        << ",\"oram_arena_bytes\":" << maps.arena_bytes()
        << ",\"packed_page_value_bytes\":" << stats.page_value_bytes()
        << ",\"packing_slack_bytes\":" << stats.real_pages * page_bytes - stats.record_bytes
        << ",\"oram_arena_to_page_value_ratio\":" <<
            double(maps.arena_bytes()) / stats.page_value_bytes()
        << ",\"process_peak_rss_bytes\":" << std::uint64_t(usage.ru_maxrss) * 1024
        << ",\"tiers\":[";
    for (std::size_t t = 0; t < 3; ++t) {
        if (t) std::cout << ',';
        const auto* map = maps.map(static_cast<Tier>(t));
        const auto& s = packed.stats[t];
        std::cout << "{\"name\":\"" << tier_name(static_cast<Tier>(t)) << "\",\"backend\":\""
            << (map ? map->backend_name() : "disabled") << "\",\"S\":" << s.canonical_bytes
            << ",\"N\":" << s.records << ",\"E\":" << s.ordinary_links << ",\"A\":" << s.account_leaves
            << ",\"R\":" << s.record_bytes << ",\"P\":" << s.real_pages
            << ",\"packing_runs\":" << s.packing_runs << ",\"utilization\":" << s.utilization()
            << ",\"requested_capacity\":" << packed.pages[t].size()
            << ",\"allocated_capacity\":" << (map ? map->capacity() : 0)
            << ",\"arena_bytes\":" << (map ? map->arena_bytes() : 0) << '}';
    }
    std::cout << "],\"samples\":[";
    for (std::size_t i = 0; i < samples.size(); ++i) {
        if (i) std::cout << ',';
        const auto& s = samples[i];
        std::cout << "{\"batch_service_ns\":" << s.service
            << ",\"request_decode_hash_ns\":" << s.request << ",\"traversal_ns\":" << s.traversal
            << ",\"page_read_ns\":";
        array_json(s.read_ns);
        std::cout << ",\"local_traversal_ns\":" << s.traversal - sum(s.read_ns)
            << ",\"response_encode_ns\":" << s.response << '}';
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
        std::cerr << "ethereum_mpt_benchmark: " << error.what() << '\n';
        return 1;
    }
}
