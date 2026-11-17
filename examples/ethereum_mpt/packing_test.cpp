// Tests packing: empty and tiered configurations, record preservation and
// deduplication, corruption detection, retained-root generations and
// stable-page incremental appends.

#include "packing.hpp"

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("packing test: ") + message);
}

template <class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const std::invalid_argument&) {
        return;
    }
    throw std::runtime_error(std::string("packing test accepted: ") + message);
}

std::size_t tier_index(Tier tier) { return static_cast<std::size_t>(tier); }

Hash key(std::uint8_t first, std::uint8_t last) {
    Hash result{};
    result.front() = first;
    result.back() = last;
    return result;
}

struct PhysicalRecord {
    Tier tier;
    Locator locator;
    PackedRecord record;
};

template <class Image>
std::vector<PhysicalRecord> records(const Image& packed) {
    std::vector<PhysicalRecord> result;
    for (std::size_t tier = 0; tier < 3; ++tier) {
        for (std::size_t page = 1; page < packed.pages[tier].size(); ++page) {
            std::size_t offset = 0;
            const auto& bytes = packed.pages[tier][page];
            while (offset + 8 <= page_bytes) {
                const std::size_t rlp = bytes[offset] +
                    (static_cast<std::size_t>(bytes[offset + 1]) << 8);
                if (rlp == 0) break;
                const auto length = static_cast<std::uint16_t>(8 + rlp + 12 * bytes[offset + 4]);
                const Locator locator{page, static_cast<std::uint16_t>(offset), length};
                const auto selected = static_cast<Tier>(tier);
                result.push_back({selected, locator, read_packed_record(packed, selected, locator)});
                offset += length;
            }
        }
    }
    return result;
}

Snapshot shared_snapshot() {
    Word small{};
    small.back() = 1;
    Word large{};
    large.fill(0xff);
    const auto nested_inline = build_trie(TrieKind::storage,
        {{key(0, 0), encode_storage(small)}, {key(0, 1), encode_storage(small)}});
    const auto external = build_trie(TrieKind::storage,
        {{key(0, 0), encode_storage(large)}, {key(0, 1), encode_storage(large)}});
    Account first;
    first.storage_root = nested_inline.root_hash();
    Account second;
    second.storage_root = external.root_hash();
    Account empty;
    Snapshot result;
    result.accounts = build_trie(TrieKind::account,
        {{key(0, 0), encode_account(first)}, {key(0, 1), encode_account(first)},
         {key(0x80, 0), encode_account(second)}, {key(0xf0, 0), encode_account(empty)}});
    result.storage_tries.emplace(nested_inline.root_hash(), nested_inline);
    result.storage_tries.emplace(external.root_hash(), external);
    return result;
}

Snapshot changed_snapshot(const Snapshot& source, std::uint8_t value) {
    Snapshot changed = source;
    Word storage_value{};
    storage_value.back() = value;
    const auto storage = build_trie(TrieKind::storage,
        {{key(0, 0), encode_storage(storage_value)}});
    changed.storage_tries.emplace(storage.root_hash(), storage);
    std::vector<Entry> entries;
    for (const auto& account_key : {key(0, 0), key(0, 1), key(0x80, 0), key(0xf0, 0)}) {
        auto account_value = *verify_proof(TrieKind::account, source.accounts.root_hash(),
                                           account_key, prove(source.accounts, account_key));
        if (account_key == key(0, 0)) {
            auto account = decode_account(account_value);
            account.nonce = value;
            account.storage_root = storage.root_hash();
            account_value = encode_account(account);
        }
        entries.push_back({account_key, std::move(account_value)});
    }
    changed.accounts = build_trie(TrieKind::account, entries);
    return changed;
}

void require_same_stats(const PackingStats& first, const PackingStats& second) {
    require(std::tie(first.canonical_bytes, first.records, first.ordinary_links,
                     first.account_leaves, first.record_bytes, first.real_pages,
                     first.packing_runs, first.dummy_pages) ==
            std::tie(second.canonical_bytes, second.records, second.ordinary_links,
                     second.account_leaves, second.record_bytes, second.real_pages,
                     second.packing_runs, second.dummy_pages),
            "unchanged image preserves every packing statistic");
}

void test_empty_and_configuration() {
    Snapshot empty;
    empty.accounts = build_trie(TrieKind::account, {});
    const auto packed = pack_snapshot(empty);
    require(packed.state_root == empty_trie_root() && packed.account_root.empty(),
            "empty snapshot root and locator");
    require(packed.pages[0].size() == 1 && packed.pages[1].empty() &&
            packed.pages[2].size() == 1, "only configured dummy pages exist");
    require(packed.total_stats().records == 0 && packed.total_stats().dummy_pages == 2 &&
            packed.total_stats().page_value_bytes() == 2 * page_bytes, "empty snapshot accounting");
    auto bad = packed;
    bad.pages[0][0][0] = 1;
    reject([&] { validate_packed_snapshot(bad); }, "nonzero dummy page");
    bad = packed;
    bad.account_root.offset = 1;
    reject([&] { validate_packed_snapshot(bad); }, "noncanonical empty root locator");
    bad = packed;
    bad.pages[1].emplace_back(Page{});
    reject([&] { validate_packed_snapshot(bad); }, "disabled tier image");
    reject([&] { pack_snapshot(empty, TierProfile{66, 0}); }, "invalid account cutoff");
    reject([&] { pack_snapshot(empty, TierProfile{0, 255}); }, "invalid storage cutoff");
    const auto bulk_only = pack_snapshot(empty, TierProfile{0, 0});
    require(bulk_only.pages[0].empty() && bulk_only.pages[1].empty() &&
            bulk_only.pages[2].size() == 1, "bulk-only empty configuration");
}

void test_preservation_deduplication_and_tiers() {
    const auto source = shared_snapshot();
    const auto packed = pack_snapshot(source, TierProfile{3, 2});
    const auto repeated = pack_snapshot(source, TierProfile{3, 2});
    require(packed.pages == repeated.pages && packed.account_root == repeated.account_root,
            "packing must be deterministic");
    require(packed.state_root == source.accounts.root_hash(), "packing preserves state root");
    using Identity = std::tuple<TrieKind, std::size_t, Hash>;
    std::map<Identity, Bytes> expected;
    std::set<Identity> seen;
    std::function<void(const NodePtr&, TrieKind, std::size_t, bool)> walk;
    walk = [&](const NodePtr& node, TrieKind role, std::size_t depth, bool external) {
        const Identity identity{role, depth, node->hash};
        if (external) expected[identity] = node->rlp;
        if (!seen.insert(identity).second) return;
        if (node->kind == NodeKind::branch) {
            for (const auto& child : node->children)
                if (child) walk(child, role, depth + 1, child->rlp.size() >= 32);
        } else if (node->kind == NodeKind::extension) {
            walk(node->child, role, depth + node->path.size(), node->child->rlp.size() >= 32);
        } else if (role == TrieKind::account) {
            const auto root = decode_account(node->value).storage_root;
            if (root != empty_trie_root())
                walk(source.storage_tries.at(root).root, TrieKind::storage, 0, true);
        }
    };
    walk(source.accounts.root, TrieKind::account, 0, true);
    const auto physical = records(packed);
    require(physical.size() == expected.size(), "deduplicated record count");
    bool depth64 = false;
    bool empty_storage = false;
    bool storage_top = false;
    bool storage_bulk = false;
    std::map<Hash, Locator> storage_roots;
    for (const auto& stored : physical) {
        const auto& record = stored.record;
        const Identity identity{record.trie_kind, record.nibble_depth,
                                keccak256(record.canonical_rlp)};
        require(expected.at(identity) == record.canonical_rlp, "canonical RLP byte preservation");
        require(stored.tier == tier_for(record.trie_kind, record.nibble_depth, packed.profile),
                "public depth selects physical tier");
        depth64 = depth64 || record.nibble_depth == 64;
        storage_top = storage_top || stored.tier == Tier::storage_top;
        storage_bulk = storage_bulk || (stored.tier == Tier::bulk &&
                                        record.trie_kind == TrieKind::storage);
        if (record.trie_kind == TrieKind::account && record.kind == NodeKind::leaf) {
            const auto decoded = decode_node(record.canonical_rlp, record.trie_kind,
                                             record.nibble_depth);
            const auto root = decode_account(decoded.value).storage_root;
            require(record.links.size() == 1, "one storage locator per account leaf");
            if (root == empty_trie_root()) {
                require(record.links[0].empty(), "empty storage sentinel");
                empty_storage = true;
            } else {
                const auto previous = storage_roots.emplace(root, record.links[0]);
                require(previous.second || previous.first->second == record.links[0],
                        "shared storage roots reuse the same locator");
            }
        }
    }
    require(depth64 && empty_storage && storage_top && storage_bulk,
            "fixture exercises depth64, empty storage, and cross-tier storage extension");
    const auto totals = packed.total_stats();
    require(totals.record_bytes == totals.canonical_bytes + 8 * totals.records +
            12 * (totals.ordinary_links + totals.account_leaves), "exact annotated byte bill");
    require(totals.real_pages * page_bytes < 2 * totals.record_bytes +
            totals.packing_runs * page_bytes, "next-fit packing bound across tiers");
    require(totals.utilization() > 0 && totals.utilization() <= 1, "packing utilization");

    auto missing = source;
    missing.storage_tries.erase(missing.storage_tries.begin());
    reject([&] { pack_snapshot(missing); }, "missing unqueried storage trie");
    auto wrong_role = source;
    wrong_role.storage_tries.begin()->second.kind = TrieKind::account;
    reject([&] { pack_snapshot(wrong_role); }, "storage trie with incorrect role");
}

void test_corruption() {
    const auto packed = pack_snapshot(shared_snapshot(), TierProfile{3, 2});
    const auto physical = records(packed);
    const auto first = physical.front();
    const auto mutate_first = [&](std::size_t relative, std::uint8_t value) {
        auto bad = packed;
        bad.pages[tier_index(first.tier)][first.locator.page_id]
            [first.locator.offset + relative] = value;
        reject([&] { validate_packed_snapshot(bad); }, "corrupted record header or payload");
    };
    mutate_first(6, 1);              // Reserved metadata.
    mutate_first(5, 65);             // Depth exceeds the fixed-key domain.
    mutate_first(2, 255);            // Invalid kind.
    mutate_first(3, 255);            // Invalid role.
    mutate_first(4, 17);             // Too many links.
    mutate_first(0, 0xff);           // Inconsistent length.
    mutate_first(8, 0x80);           // Wrong canonical node kind / hash.

    auto bad = packed;
    ++bad.account_root.offset;
    reject([&] { validate_packed_snapshot(bad); }, "root points inside a record");
    bad = packed;
    --bad.account_root.record_bytes;
    reject([&] { validate_packed_snapshot(bad); }, "root extent is truncated");
    bad = packed;
    bad.account_root.page_id = std::numeric_limits<std::uint64_t>::max();
    reject([&] { validate_packed_snapshot(bad); }, "root page is missing");
    bad = packed;
    bad.state_root.front() ^= 1;
    reject([&] { validate_packed_snapshot(bad); }, "state root hash mismatch");
    bad = packed;
    ++bad.stats[0].canonical_bytes;
    reject([&] { validate_packed_snapshot(bad); }, "inaccurate packing statistics");

    bool changed_link = false;
    bool changed_tail = false;
    for (const auto& stored : physical) {
        const auto tier = tier_index(stored.tier);
        if (!changed_link && !stored.record.links.empty()) {
            bad = packed;
            const auto offset = stored.locator.offset + 8 + stored.record.canonical_rlp.size();
            bad.pages[tier][stored.locator.page_id][offset + 8] ^= 1;
            reject([&] { validate_packed_snapshot(bad); }, "wrong child/storage locator offset");
            changed_link = true;
        }
        const auto end = static_cast<std::size_t>(stored.locator.offset) + stored.locator.record_bytes;
        const auto& page = packed.pages[tier][stored.locator.page_id];
        if (!changed_tail && end < page_bytes &&
            std::all_of(page.begin() + end, page.end(), [](std::uint8_t b) { return b == 0; })) {
            bad = packed;
            bad.pages[tier][stored.locator.page_id].back() = 1;
            reject([&] { validate_packed_snapshot(bad); }, "nonzero unused page tail");
            changed_tail = true;
        }
    }
    require(changed_link && changed_tail, "corruption fixture contains links and page slack");
    const auto bulk = tier_index(Tier::bulk);
    bad = packed;
    bad.pages[bulk].pop_back();
    // Keep accounting consistent so the remaining checks must detect the missing closure.
    const auto removed_page = packed.pages[bulk].size() - 1;
    for (const auto& stored : physical) {
        if (stored.tier != Tier::bulk || stored.locator.page_id != removed_page) continue;
        auto& stats = bad.stats[bulk];
        stats.canonical_bytes -= stored.record.canonical_rlp.size();
        --stats.records;
        stats.record_bytes -= stored.locator.record_bytes;
        if (stored.record.trie_kind == TrieKind::account && stored.record.kind == NodeKind::leaf)
            --stats.account_leaves;
        else
            stats.ordinary_links -= stored.record.links.size();
    }
    --bad.stats[bulk].real_pages;
    bad.stats[bulk].packing_runs = bad.stats[bulk].real_pages ? 1 : 0;
    reject([&] { validate_packed_snapshot(bad); }, "missing referenced physical page");
    reject([&] { read_packed_record(packed, first.tier,
        Locator{first.locator.page_id, static_cast<std::uint16_t>(page_bytes - 1), 8}); },
           "record extent arithmetic");
}

void test_retained_generations() {
    const auto source = shared_snapshot();
    const TierProfile profile{3, 2};
    const auto original = pack_snapshot(source, profile);
    Snapshot empty;
    const auto shared = pack_generation({empty, source, source, empty}, profile);
    require(shared.roots.size() == 4 && shared.roots[0].state_root == empty_trie_root() &&
            shared.roots[0].account_root.empty() && shared.roots[3].account_root.empty(),
            "generation preserves empty root positions");
    require(shared.roots[1].state_root == original.state_root &&
            shared.roots[1].account_root == original.account_root &&
            shared.roots[2].account_root == original.account_root &&
            shared.pages == original.pages, "shared roots reuse the complete packed image");
    require(shared.total_stats().record_bytes == original.total_stats().record_bytes &&
            shared.total_stats().dummy_pages == 3, "generation counts unique physical bytes");
    const auto no_roots = pack_generation({}, profile);
    require(no_roots.roots.empty() && no_roots.total_stats().records == 0 &&
            no_roots.total_stats().dummy_pages == 3, "rootless generation contains only dummies");
    const auto only_empty = pack_generation({empty, empty}, profile);
    require(only_empty.roots.size() == 2 && only_empty.pages == no_roots.pages,
            "retained empty states require no records");

    auto changed = source;
    Word changed_value{};
    changed_value.back() = 3;
    const auto changed_storage = build_trie(TrieKind::storage,
        {{key(0, 0), encode_storage(changed_value)}});
    changed.storage_tries.emplace(changed_storage.root_hash(), changed_storage);
    std::vector<Entry> changed_entries;
    for (const auto& account_key : {key(0, 0), key(0, 1), key(0x80, 0), key(0xf0, 0)}) {
        auto value = *verify_proof(TrieKind::account, source.accounts.root_hash(),
                                  account_key, prove(source.accounts, account_key));
        if (account_key == key(0, 0)) {
            auto account = decode_account(value);
            account.nonce = 7;
            account.storage_root = changed_storage.root_hash();
            value = encode_account(account);
        }
        changed_entries.push_back({account_key, std::move(value)});
    }
    changed.accounts = build_trie(TrieKind::account, changed_entries);
    const auto latest = pack_snapshot(changed, profile);
    const auto retained = pack_generation({source, changed, empty}, profile);
    require(retained.roots[0].state_root == original.state_root &&
            retained.roots[1].state_root == latest.state_root &&
            retained.roots[0].state_root != retained.roots[1].state_root,
            "generation retains divergent roots with their own locators");
    const auto reversed = pack_generation({empty, changed, source}, profile);
    require(retained.pages == reversed.pages &&
            retained.roots[0].account_root == reversed.roots[2].account_root &&
            retained.roots[1].account_root == reversed.roots[1].account_root,
            "physical packing is independent of retained-root ordering");

    using Identity = std::tuple<TrieKind, std::size_t, Hash>;
    const auto identity = [](const PhysicalRecord& stored) {
        return Identity{stored.record.trie_kind, stored.record.nibble_depth,
                        keccak256(stored.record.canonical_rlp)};
    };
    std::map<Identity, Bytes> expected;
    for (const auto& packed : {original, latest})
        for (const auto& stored : records(packed))
            expected.emplace(identity(stored), stored.record.canonical_rlp);
    const auto physical = records(retained);
    require(physical.size() == expected.size() &&
            physical.size() < original.total_stats().records + latest.total_stats().records &&
            physical.size() > original.total_stats().records,
            "retained roots pack the deduplicated union of their closures");
    for (const auto& stored : physical)
        require(expected.at(identity(stored)) == stored.record.canonical_rlp,
                "generation preserves all retained canonical records");

    auto bad = retained;
    bad.roots[1].account_root = bad.roots[0].account_root;
    reject([&] { validate_packed_generation(bad); }, "second retained root uses wrong locator");
    bad = retained;
    bad.roots[1].state_root.front() ^= 1;
    reject([&] { validate_packed_generation(bad); }, "second retained root hash mismatch");
    bad = retained;
    bad.roots.back().account_root = bad.roots.front().account_root;
    reject([&] { validate_packed_generation(bad); }, "empty retained root uses nonzero locator");
    bad = retained;
    bad.roots.erase(bad.roots.begin());
    reject([&] { validate_packed_generation(bad); }, "unreachable records from removed root");
    bad = retained;
    bad.roots.clear();
    reject([&] { validate_packed_generation(bad); }, "nonempty generation has no manifest roots");
    bad = retained;
    ++bad.stats[0].records;
    reject([&] { validate_packed_generation(bad); }, "generation statistics mismatch");

    // A previously interned root must not conceal an incomplete later source.
    auto incomplete = source;
    incomplete.storage_tries.clear();
    reject([&] { pack_generation({source, incomplete}, profile); },
           "duplicate retained source is missing its storage closure");
    auto wrong_role = source;
    wrong_role.accounts.kind = TrieKind::storage;
    reject([&] { pack_generation({source, wrong_role}, profile); },
           "later retained state has the wrong trie role");
}

void test_incremental_generations() {
    const auto source = shared_snapshot();
    const auto changed = changed_snapshot(source, 3);
    const auto changed_again = changed_snapshot(source, 4);
    const TierProfile profile{3, 2};
    const auto base = pack_generation({source}, profile);
    const auto saved = base;
    const auto unchanged = append_generation(base, {source, Snapshot{}, source});
    require(unchanged.pages == base.pages &&
            unchanged.packing_run_starts == base.packing_run_starts,
            "unchanged and empty roots append no physical pages or packing runs");
    require(unchanged.roots.size() == 4 &&
            unchanged.roots[0].account_root == base.roots[0].account_root &&
            unchanged.roots[1].account_root == base.roots[0].account_root &&
            unchanged.roots[2].state_root == empty_trie_root() &&
            unchanged.roots[2].account_root.empty() &&
            unchanged.roots[3].account_root == base.roots[0].account_root,
            "append preserves old roots and ordered duplicate new roots");
    for (std::size_t i = 0; i < 3; ++i)
        require_same_stats(unchanged.stats[i], base.stats[i]);
    const auto no_change = append_generation(base, {});
    require(no_change.pages == base.pages && no_change.roots.size() == base.roots.size(),
            "empty append preserves the base");

    const auto appended = append_generation(base, {changed, changed});
    const auto again = append_generation(appended, {changed_again, source});
    const auto rebuilt = pack_generation({source, changed, changed_again}, profile);
    const auto batched = append_generation(base, {changed, changed_again, changed});
    const auto reversed = append_generation(base, {changed_again, changed});
    require(batched.total_stats().records == rebuilt.total_stats().records &&
            batched.total_stats().record_bytes == rebuilt.total_stats().record_bytes &&
            batched.pages == reversed.pages &&
            batched.roots[1].account_root == batched.roots[3].account_root &&
            batched.roots[1].account_root == reversed.roots[2].account_root &&
            batched.roots[2].account_root == reversed.roots[1].account_root,
            "distinct new roots share new identities independently of snapshot order");
    require(appended.roots.size() == 3 && again.roots.size() == 5 &&
            appended.roots[1].state_root == changed.accounts.root_hash() &&
            appended.roots[1].account_root == appended.roots[2].account_root &&
            again.roots[3].state_root == changed_again.accounts.root_hash() &&
            again.roots[4].account_root == base.roots[0].account_root,
            "incremental images retain all old roots and deduplicate new snapshot roots");

    using Identity = std::tuple<TrieKind, std::size_t, Hash>;
    const auto identity = [](const PhysicalRecord& stored) {
        return Identity{stored.record.trie_kind, stored.record.nibble_depth,
                        keccak256(stored.record.canonical_rlp)};
    };
    std::map<Identity, PhysicalRecord> expected;
    for (const auto& stored : records(rebuilt)) expected.emplace(identity(stored), stored);
    std::map<Identity, PhysicalRecord> old;
    for (const auto& stored : records(base)) old.emplace(identity(stored), stored);
    const auto physical = records(again);
    require(physical.size() == expected.size(),
            "incremental records equal the deduplicated complete reachable union");
    std::size_t reused = 0;
    std::size_t added = 0;
    for (const auto& stored : physical) {
        const auto id = identity(stored);
        require(expected.at(id).record.canonical_rlp == stored.record.canonical_rlp,
                "incremental canonical bytes retain exact role and depth contexts");
        const auto found = old.find(id);
        if (found != old.end()) {
            require(found->second.tier == stored.tier &&
                    found->second.locator == stored.locator &&
                    found->second.record.links == stored.record.links,
                    "every base identity reuses its exact locator and links");
            ++reused;
        } else {
            require(stored.locator.page_id >= base.pages[tier_index(stored.tier)].size(),
                    "every new identity has a fresh page ID in its tier");
            ++added;
        }
    }
    require(reused == old.size() && added != 0, "append exercises reused and new identities");

    bool seal_prevents_tail_fill = false;
    std::size_t mergeable_tier = 0;
    std::size_t mergeable_run = 0;
    for (std::size_t i = 0; i < 3; ++i) {
        require(std::equal(base.pages[i].begin(), base.pages[i].end(),
                           appended.pages[i].begin()) &&
                std::equal(appended.pages[i].begin(), appended.pages[i].end(),
                           again.pages[i].begin()), "all earlier sealed pages remain byte-identical");
        require(again.packing_run_starts[i].size() == 3 &&
                again.stats[i].packing_runs == 3 &&
                again.packing_run_starts[i][1] == base.pages[i].size() &&
                again.packing_run_starts[i][2] == appended.pages[i].size(),
                "each tier counts and records all three nonempty sealed runs");
        require(again.stats[i].records == rebuilt.stats[i].records &&
                again.stats[i].canonical_bytes == rebuilt.stats[i].canonical_bytes &&
                again.stats[i].record_bytes == rebuilt.stats[i].record_bytes &&
                again.stats[i].ordinary_links == rebuilt.stats[i].ordinary_links &&
                again.stats[i].account_leaves == rebuilt.stats[i].account_leaves &&
                again.stats[i].dummy_pages == base.stats[i].dummy_pages,
                "cumulative counts charge each unique record and each configured dummy once");
        for (std::size_t run = 1; run < again.packing_run_starts[i].size(); ++run) {
            const auto start = again.packing_run_starts[i][run];
            std::size_t previous_used = 0;
            std::size_t first_length = 0;
            for (const auto& stored : physical) {
                if (tier_index(stored.tier) != i) continue;
                if (stored.locator.page_id == start - 1)
                    previous_used = stored.locator.offset + stored.locator.record_bytes;
                if (stored.locator.page_id == start && stored.locator.offset == 0)
                    first_length = stored.locator.record_bytes;
            }
            if (previous_used + first_length <= page_bytes) {
                seal_prevents_tail_fill = true;
                mergeable_tier = i;
                mergeable_run = run;
            }
        }
    }
    require(seal_prevents_tail_fill, "fixture leaves earlier tails that could hold later records");
    const auto stats = again.total_stats();
    require(stats.real_pages * page_bytes < 2 * stats.record_bytes +
            stats.packing_runs * page_bytes, "cumulative next-fit bound includes each sealed tail");
    validate_packed_generation(again);

    auto bad = again;
    --bad.stats[mergeable_tier].packing_runs;
    reject([&] { validate_packed_generation(bad); }, "incorrect cumulative run count");
    bad = again;
    bad.packing_run_starts[mergeable_tier].erase(
        bad.packing_run_starts[mergeable_tier].begin() + mergeable_run);
    --bad.stats[mergeable_tier].packing_runs;
    reject([&] { validate_packed_generation(bad); }, "merging sealed runs violates next-fit");
    bad = again;
    bad.packing_run_starts[0][0] = 0;
    reject([&] { validate_packed_generation(bad); }, "packing run starts at dummy page");
    bad = again;
    bad.packing_run_starts[0][1] = bad.packing_run_starts[0][0];
    reject([&] { validate_packed_generation(bad); }, "duplicate packing run boundary");
    bad = again;
    bad.packing_run_starts[0].back() = bad.pages[0].size();
    reject([&] { validate_packed_generation(bad); }, "packing run starts beyond real pages");
    bad = again;
    bad.roots.erase(bad.roots.begin());
    bad.roots.pop_back();  // Remove the repeated original root as well.
    reject([&] { validate_packed_generation(bad); }, "old unique records need their historical root");

    auto missing = source;
    missing.storage_tries.clear();
    reject([&] { append_generation(base, {changed, missing}); },
           "reused source root still requires a complete independently validated closure");
    auto wrong_role = source;
    wrong_role.accounts.kind = TrieKind::storage;
    reject([&] { append_generation(base, {wrong_role}); }, "reused source has wrong trie role");
    const auto first = records(base).front();
    bad = base;
    ++bad.pages[tier_index(first.tier)][first.locator.page_id][first.locator.offset + 5];
    reject([&] { append_generation(bad, {source}); }, "base identity has the wrong incoming depth");
    bad = base;
    bad.pages[tier_index(first.tier)][first.locator.page_id][first.locator.offset + 3] =
        static_cast<std::uint8_t>(TrieKind::storage);
    reject([&] { append_generation(bad, {source}); }, "base identity has the wrong trie role");
    require(base.pages == saved.pages && base.packing_run_starts == saved.packing_run_starts &&
            base.roots.size() == saved.roots.size() &&
            base.roots.front().account_root == saved.roots.front().account_root &&
            base.roots.front().state_root == saved.roots.front().state_root,
            "successful and rejected appends leave the input base unchanged");
    for (std::size_t i = 0; i < 3; ++i) require_same_stats(base.stats[i], saved.stats[i]);

    const auto empty = pack_generation({}, TierProfile{0, 0});
    const auto from_empty = append_generation(empty, {source});
    const auto fresh = pack_generation({source}, TierProfile{0, 0});
    require(from_empty.pages == fresh.pages && from_empty.pages[0].empty() &&
            from_empty.pages[1].empty() && from_empty.packing_run_starts[0].empty() &&
            from_empty.packing_run_starts[1].empty(), "first append respects disabled tiers");
}

}  // namespace

void run_packing_tests() {
    test_empty_and_configuration();
    test_preservation_deduplication_and_tiers();
    test_corruption();
    test_retained_generations();
    test_incremental_generations();
}
