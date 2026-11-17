// Public packer and packed-image validator: deduplicates records by
// (role, incoming depth, hash), next-fit packs them per tier into fixed-width
// pages, resolves child locators, appends stable-page generations and checks
// complete images.

#include "packing.hpp"

#include <algorithm>
#include <functional>
#include <limits>
#include <set>
#include <stdexcept>
#include <tuple>
#include <utility>

namespace ethereum_mpt {
namespace {

constexpr std::size_t header_bytes = 8;
constexpr std::size_t locator_bytes = 12;
using NodeKey = std::tuple<TrieKind, std::size_t, Hash>;
using RecordAddress = std::tuple<Tier, std::uint64_t, std::uint16_t>;

[[noreturn]] void invalid(const char* reason) {
    throw std::invalid_argument(reason);
}

std::size_t index(Tier tier) {
    const auto value = static_cast<std::size_t>(tier);
    if (value >= 3) invalid("invalid MPT tier");
    return value;
}

void validate_profile(TierProfile profile) {
    if (profile.account_top_depth > 65 || profile.storage_top_depth > 65)
        invalid("MPT tier cutoffs must be in 0..65");
}

bool configured(Tier tier, TierProfile profile) {
    return tier == Tier::bulk ||
           (tier == Tier::account_top && profile.account_top_depth != 0) ||
           (tier == Tier::storage_top && profile.storage_top_depth != 0);
}

std::uint16_t read16(const std::uint8_t* bytes) {
    return static_cast<std::uint16_t>(bytes[0]) |
           static_cast<std::uint16_t>(static_cast<std::uint16_t>(bytes[1]) << 8);
}

std::uint64_t read64(const std::uint8_t* bytes) {
    std::uint64_t result = 0;
    for (std::size_t i = 0; i < 8; ++i)
        result |= static_cast<std::uint64_t>(bytes[i]) << (8 * i);
    return result;
}

void write16(std::uint8_t* bytes, std::uint16_t value) {
    for (std::size_t i = 0; i < 2; ++i)
        bytes[i] = static_cast<std::uint8_t>(value >> (8 * i));
}

void write64(std::uint8_t* bytes, std::uint64_t value) {
    for (std::size_t i = 0; i < 8; ++i)
        bytes[i] = static_cast<std::uint8_t>(value >> (8 * i));
}

void write_locator(std::uint8_t* bytes, const Locator& locator) {
    write64(bytes, locator.page_id);
    write16(bytes + 8, locator.offset);
    write16(bytes + 10, locator.record_bytes);
}

bool all_zero(const Page& page, std::size_t start = 0) {
    return std::all_of(page.begin() + start, page.end(),
                       [](std::uint8_t value) { return value == 0; });
}

std::size_t ordinary_links(const DecodedNode& node) {
    if (node.kind == NodeKind::branch)
        return static_cast<std::size_t>(std::count_if(
            node.children.begin(), node.children.end(),
            [](const ChildReference& child) { return child.hash.has_value(); }));
    return node.kind == NodeKind::extension && node.child.hash ? 1 : 0;
}

void add_stats(PackingStats& out, const PackingStats& value) {
    out.canonical_bytes += value.canonical_bytes;
    out.records += value.records;
    out.ordinary_links += value.ordinary_links;
    out.account_leaves += value.account_leaves;
    out.record_bytes += value.record_bytes;
    out.real_pages += value.real_pages;
    out.packing_runs += value.packing_runs;
    out.dummy_pages += value.dummy_pages;
}

bool same_stats(const PackingStats& lhs, const PackingStats& rhs) {
    return std::tie(lhs.canonical_bytes, lhs.records, lhs.ordinary_links,
                    lhs.account_leaves, lhs.record_bytes, lhs.real_pages,
                    lhs.packing_runs, lhs.dummy_pages) ==
           std::tie(rhs.canonical_bytes, rhs.records, rhs.ordinary_links,
                    rhs.account_leaves, rhs.record_bytes, rhs.real_pages,
                    rhs.packing_runs, rhs.dummy_pages);
}

struct PendingRecord {
    NodePtr node;
    DecodedNode decoded;
    Locator locator;
    Tier tier;
};

// This validates source object pointers as well as canonical bytes. A malformed
// object graph must not be repaired silently by packing its RLP alone.
void check_binding(const ChildReference& reference, const NodePtr& child) {
    if (reference.empty()) {
        if (child) invalid("source child exists behind an empty reference");
    } else {
        if (!child) invalid("source trie is missing a referenced child");
        if (reference.hash) {
            if (child->rlp.size() < 32 || child->hash != *reference.hash)
                invalid("source hashed child does not match canonical reference");
        } else if (child->rlp.size() >= 32 || child->rlp != reference.embedded) {
            invalid("source embedded child does not match canonical bytes");
        }
    }
}

}  // namespace

bool Locator::empty() const {
    return page_id == 0 && offset == 0 && record_bytes == 0;
}

bool operator==(const Locator& lhs, const Locator& rhs) {
    return lhs.page_id == rhs.page_id && lhs.offset == rhs.offset &&
           lhs.record_bytes == rhs.record_bytes;
}

bool operator!=(const Locator& lhs, const Locator& rhs) { return !(lhs == rhs); }

double PackingStats::utilization() const {
    return real_pages == 0 ? 0.0 :
        static_cast<double>(record_bytes) /
        (static_cast<double>(real_pages) * page_bytes);
}

std::size_t PackingStats::page_value_bytes() const {
    return (real_pages + dummy_pages) * page_bytes;
}

PackingStats PackedSnapshot::total_stats() const {
    PackingStats result;
    for (const auto& tier : stats) add_stats(result, tier);
    return result;
}

PackingStats PackedGeneration::total_stats() const {
    PackingStats result;
    for (const auto& tier : stats) add_stats(result, tier);
    return result;
}

Tier tier_for(TrieKind kind, std::size_t depth, TierProfile profile) {
    validate_profile(profile);
    if (depth > 64) invalid("MPT incoming nibble depth exceeds 64");
    if (kind == TrieKind::account)
        return depth < profile.account_top_depth ? Tier::account_top : Tier::bulk;
    if (kind == TrieKind::storage)
        return depth < profile.storage_top_depth ? Tier::storage_top : Tier::bulk;
    invalid("invalid MPT trie role");
}

const char* tier_name(Tier tier) {
    switch (tier) {
        case Tier::account_top: return "account_top";
        case Tier::storage_top: return "storage_top";
        case Tier::bulk: return "bulk";
    }
    invalid("invalid MPT tier");
}

namespace {

template <class Image>
PackedRecord read_record(const Image& snapshot, Tier tier, const Locator& locator) {
    const auto& pages = snapshot.pages[index(tier)];
    if (locator.page_id == 0 || locator.page_id >= pages.size())
        invalid("MPT locator refers to a dummy or missing page");
    const std::size_t offset = locator.offset;
    const std::size_t length = locator.record_bytes;
    if (length < header_bytes || offset + length > page_bytes)
        invalid("MPT record extent is outside its page");
    const auto* bytes = pages[static_cast<std::size_t>(locator.page_id)].data() + offset;
    const std::size_t rlp_bytes = read16(bytes);
    const std::size_t links = bytes[4];
    if (rlp_bytes == 0 || rlp_bytes > 532 ||
        length != header_bytes + rlp_bytes + locator_bytes * links)
        invalid("MPT record length is inconsistent with its header");
    if (bytes[2] > static_cast<std::uint8_t>(NodeKind::leaf) ||
        bytes[3] > static_cast<std::uint8_t>(TrieKind::storage) ||
        links > 16 || bytes[5] > 64 || bytes[6] != 0 || bytes[7] != 0)
        invalid("invalid MPT record header");
    PackedRecord result{static_cast<NodeKind>(bytes[2]),
                        static_cast<TrieKind>(bytes[3]), bytes[5], {}, {}};
    result.canonical_rlp.assign(bytes + header_bytes,
                                bytes + header_bytes + rlp_bytes);
    for (std::size_t i = 0; i < links; ++i) {
        const auto* link = bytes + header_bytes + rlp_bytes + locator_bytes * i;
        Locator decoded{read64(link), read16(link + 8), read16(link + 10)};
        if (decoded.page_id == 0 && !decoded.empty())
            invalid("MPT empty locator must be entirely zero");
        result.links.push_back(decoded);
    }
    return result;
}

}  // namespace

PackedRecord read_packed_record(const PackedSnapshot& snapshot, Tier tier,
                                const Locator& locator) {
    return read_record(snapshot, tier, locator);
}

PackedRecord read_packed_record(const PackedGeneration& generation, Tier tier,
                                const Locator& locator) {
    return read_record(generation, tier, locator);
}

PackedGeneration pack_generation(const std::vector<Snapshot>& snapshots,
                                 TierProfile profile) {
    validate_profile(profile);
    PackedGeneration base;
    base.profile = profile;
    for (std::size_t i = 0; i < 3; ++i) {
        if (configured(static_cast<Tier>(i), profile)) {
            base.pages[i].emplace_back(Page{});
            base.stats[i].dummy_pages = 1;
        }
    }
    return append_generation(base, snapshots);
}

PackedGeneration append_generation(const PackedGeneration& base,
                                   const std::vector<Snapshot>& snapshots) {
    validate_packed_generation(base);
    const auto profile = base.profile;
    std::map<NodeKey, Locator> existing;
    for (std::size_t i = 0; i < 3; ++i) {
        const auto tier = static_cast<Tier>(i);
        for (std::size_t page_id = 1; page_id < base.pages[i].size(); ++page_id) {
            const auto& page = base.pages[i][page_id];
            std::size_t offset = 0;
            while (offset < page_bytes && !all_zero(page, offset)) {
                const auto* header = page.data() + offset;
                const std::size_t length = header_bytes + read16(header) +
                    locator_bytes * header[4];
                const Locator locator{static_cast<std::uint64_t>(page_id),
                                      static_cast<std::uint16_t>(offset),
                                      static_cast<std::uint16_t>(length)};
                const auto record = read_packed_record(base, tier, locator);
                existing.emplace(NodeKey{record.trie_kind, record.nibble_depth,
                                         keccak256(record.canonical_rlp)}, locator);
                offset += length;
            }
        }
    }
    std::map<NodeKey, PendingRecord> records;
    for (const auto& snapshot : snapshots) {
        if (snapshot.accounts.kind != TrieKind::account)
            invalid("snapshot state root must be an account trie");
        validate_trie(snapshot.accounts);
        // Check each source closure independently, even when its records have
        // already been interned by another retained snapshot.
        std::set<Hash> validated_storage;
        std::set<NodeKey> checked;
        std::function<void(const NodePtr&, TrieKind, std::size_t, bool)> collect;
        collect = [&](const NodePtr& node, TrieKind role, std::size_t depth, bool external) {
            if (!node) invalid("missing nonempty MPT node");
            if (depth > 64) invalid("source MPT depth exceeds 64");
            const NodeKey key{role, depth, node->hash};
            const auto decoded = decode_node(node->rlp, role, depth);
            if (keccak256(node->rlp) != node->hash || node->kind != decoded.kind ||
                node->path != decoded.path || node->value != decoded.value)
                invalid("source MPT node fields disagree with canonical bytes");
            if (external && existing.find(key) == existing.end())
                records.emplace(key, PendingRecord{node, decoded, {}, tier_for(role, depth, profile)});
            if (!checked.insert(key).second) return;
            if (decoded.kind == NodeKind::branch) {
                if (node->child) invalid("branch has an unexpected extension child");
                for (std::size_t i = 0; i < 16; ++i) {
                    check_binding(decoded.children[i], node->children[i]);
                    if (node->children[i])
                        collect(node->children[i], role, depth + 1,
                                decoded.children[i].hash.has_value());
                }
            } else {
                if (std::any_of(node->children.begin(), node->children.end(),
                                [](const NodePtr& child) { return static_cast<bool>(child); }))
                    invalid("nonbranch has unexpected branch children");
                if (decoded.kind == NodeKind::extension) {
                    check_binding(decoded.child, node->child);
                    if (!node->child || node->child->kind != NodeKind::branch)
                        invalid("canonical extension must lead to a branch");
                    collect(node->child, role, depth + decoded.path.size(),
                            decoded.child.hash.has_value());
                } else {
                    if (node->child) invalid("leaf has an unexpected child");
                    if (role == TrieKind::account) {
                        if (!external) invalid("account leaf cannot be embedded");
                        const auto storage_root = decode_account(decoded.value).storage_root;
                        if (storage_root != empty_trie_root()) {
                            const auto storage = snapshot.storage_tries.find(storage_root);
                            if (storage == snapshot.storage_tries.end())
                                invalid("snapshot is missing a referenced storage trie");
                            if (storage->second.kind != TrieKind::storage ||
                                !storage->second.root || storage->second.root_hash() != storage_root)
                                invalid("storage trie does not match its snapshot root");
                            if (validated_storage.insert(storage_root).second)
                                validate_trie(storage->second);
                            collect(storage->second.root, TrieKind::storage, 0, true);
                        }
                    }
                }
            }
        };
        if (snapshot.accounts.root)
            collect(snapshot.accounts.root, TrieKind::account, 0, true);
    }

    PackedGeneration packed = base;

    // Pass one: lexicographic (role, incoming depth, hash) order within each
    // tier, followed by next-fit. Fixed-width links make final sizes known now.
    std::array<std::size_t, 3> used{};
    std::array<bool, 3> appended{};
    for (auto& [key, pending] : records) {
        const auto role = std::get<0>(key);
        const std::size_t ordinary = ordinary_links(pending.decoded);
        const std::size_t account = role == TrieKind::account &&
            pending.decoded.kind == NodeKind::leaf ? 1 : 0;
        const std::size_t length = header_bytes + pending.node->rlp.size() +
            locator_bytes * (ordinary + account);
        if (length > page_bytes) invalid("annotated MPT record exceeds one page");
        const auto tier = index(pending.tier);
        auto& pages = packed.pages[tier];
        if (!appended[tier] || used[tier] + length > page_bytes) {
            pages.emplace_back(Page{});
            used[tier] = 0;
            if (!appended[tier]) {
                packed.packing_run_starts[tier].push_back(pages.size() - 1);
                ++packed.stats[tier].packing_runs;
                appended[tier] = true;
            }
        }
        pending.locator = {static_cast<std::uint64_t>(pages.size() - 1),
                           static_cast<std::uint16_t>(used[tier]),
                           static_cast<std::uint16_t>(length)};
        used[tier] += length;
        auto& stats = packed.stats[tier];
        stats.canonical_bytes += pending.node->rlp.size();
        ++stats.records;
        stats.ordinary_links += ordinary;
        stats.account_leaves += account;
        stats.record_bytes += length;
    }
    for (std::size_t i = 0; i < 3; ++i) {
        auto& stats = packed.stats[i];
        stats.real_pages = packed.pages[i].empty() ? 0 : packed.pages[i].size() - 1;
    }

    const auto locate = [&](TrieKind role, std::size_t depth, const Hash& hash) {
        const NodeKey key{role, depth, hash};
        const auto reused = existing.find(key);
        if (reused != existing.end()) return reused->second;
        const auto entry = records.find(key);
        if (entry == records.end()) invalid("missing MPT record while resolving links");
        return entry->second.locator;
    };
    // Pass two: seal pages; canonical RLP is copied verbatim.
    for (const auto& [key, pending] : records) {
        const auto role = std::get<0>(key);
        const auto depth = std::get<1>(key);
        const auto& decoded = pending.decoded;
        std::vector<Locator> links;
        if (decoded.kind == NodeKind::branch) {
            for (const auto& child : decoded.children)
                if (child.hash) links.push_back(locate(role, depth + 1, *child.hash));
        } else if (decoded.kind == NodeKind::extension && decoded.child.hash) {
            links.push_back(locate(role, depth + decoded.path.size(), *decoded.child.hash));
        } else if (decoded.kind == NodeKind::leaf && role == TrieKind::account) {
            const auto root = decode_account(decoded.value).storage_root;
            links.push_back(root == empty_trie_root() ? Locator{} :
                            locate(TrieKind::storage, 0, root));
        }
        auto* bytes = packed.pages[index(pending.tier)][pending.locator.page_id].data() +
            pending.locator.offset;
        write16(bytes, static_cast<std::uint16_t>(pending.node->rlp.size()));
        bytes[2] = static_cast<std::uint8_t>(decoded.kind);
        bytes[3] = static_cast<std::uint8_t>(role);
        bytes[4] = static_cast<std::uint8_t>(links.size());
        bytes[5] = static_cast<std::uint8_t>(depth);
        std::copy(pending.node->rlp.begin(), pending.node->rlp.end(), bytes + header_bytes);
        auto* link_bytes = bytes + header_bytes + pending.node->rlp.size();
        for (const auto& link : links) {
            write_locator(link_bytes, link);
            link_bytes += locator_bytes;
        }
    }
    for (const auto& snapshot : snapshots) {
        const auto hash = snapshot.accounts.root_hash();
        packed.roots.push_back({hash, snapshot.accounts.root ?
            locate(TrieKind::account, 0, hash) : Locator{}});
    }
    validate_packed_generation(packed);
    return packed;
}

PackedSnapshot pack_snapshot(const Snapshot& snapshot, TierProfile profile) {
    auto generation = pack_generation({snapshot}, profile);
    PackedSnapshot packed;
    packed.profile = generation.profile;
    packed.state_root = generation.roots.front().state_root;
    packed.account_root = generation.roots.front().account_root;
    packed.pages = std::move(generation.pages);
    packed.stats = generation.stats;
    return packed;
}

namespace {

template <class Image>
void validate_image(const Image& snapshot, const std::vector<PackedRoot>& roots,
                    const std::array<std::vector<std::uint64_t>, 3>* runs = nullptr) {
    validate_profile(snapshot.profile);
    struct StoredRecord {
        Locator locator;
        PackedRecord record;
        Hash hash;
    };
    std::map<RecordAddress, StoredRecord> inventory;
    std::set<NodeKey> identities;
    for (std::size_t i = 0; i < 3; ++i) {
        const auto tier = static_cast<Tier>(i);
        const auto& pages = snapshot.pages[i];
        PackingStats measured;
        if (!configured(tier, snapshot.profile)) {
            if (!pages.empty()) invalid("disabled MPT tier contains pages");
        } else {
            if (pages.empty() || !all_zero(pages[0]))
                invalid("configured MPT tier needs an all-zero dummy page");
            measured.dummy_pages = 1;
            measured.real_pages = pages.size() - 1;
            measured.packing_runs = measured.real_pages == 0 ? 0 : 1;
        }
        if (runs) {
            const auto& starts = (*runs)[i];
            if (starts.empty() != (measured.real_pages == 0) ||
                (!starts.empty() && starts.front() != 1))
                invalid("MPT sealed packing runs must cover all real pages");
            std::uint64_t previous = 0;
            for (const auto start : starts) {
                if (start <= previous || start >= pages.size())
                    invalid("invalid MPT sealed packing run boundary");
                previous = start;
            }
            measured.packing_runs = starts.size();
        }
        std::size_t previous_used = 0;
        for (std::size_t page_id = 1; page_id < pages.size(); ++page_id) {
            std::size_t offset = 0;
            const bool run_start = page_id == 1 || (runs &&
                std::binary_search((*runs)[i].begin(), (*runs)[i].end(), page_id));
            if (all_zero(pages[page_id])) invalid("real MPT page has no records");
            while (offset < page_bytes && !all_zero(pages[page_id], offset)) {
                if (page_bytes - offset < header_bytes)
                    invalid("MPT page has a nonzero short tail");
                const auto* header = pages[page_id].data() + offset;
                const std::size_t length = header_bytes + read16(header) +
                    locator_bytes * header[4];
                if (length > page_bytes - offset)
                    invalid("MPT physical record crosses its page boundary");
                if (offset == 0 && !run_start && previous_used + length <= page_bytes)
                    invalid("MPT page break violates next-fit within a sealed run");
                const Locator locator{static_cast<std::uint64_t>(page_id),
                                      static_cast<std::uint16_t>(offset),
                                      static_cast<std::uint16_t>(length)};
                auto record = read_packed_record(snapshot, tier, locator);
                if (tier_for(record.trie_kind, record.nibble_depth, snapshot.profile) != tier)
                    invalid("MPT record is in the wrong depth tier");
                const auto decoded = decode_node(record.canonical_rlp, record.trie_kind,
                                                 record.nibble_depth);
                const auto ordinary = ordinary_links(decoded);
                const std::size_t account = record.trie_kind == TrieKind::account &&
                    decoded.kind == NodeKind::leaf ? 1 : 0;
                if (record.kind != decoded.kind || record.links.size() != ordinary + account)
                    invalid("MPT header or link count disagrees with canonical bytes");
                const auto hash = keccak256(record.canonical_rlp);
                if (!identities.emplace(record.trie_kind, record.nibble_depth, hash).second)
                    invalid("duplicate MPT record identity");
                measured.canonical_bytes += record.canonical_rlp.size();
                ++measured.records;
                measured.ordinary_links += ordinary;
                measured.account_leaves += account;
                measured.record_bytes += length;
                inventory.emplace(RecordAddress{tier, page_id, locator.offset},
                                  StoredRecord{locator, std::move(record), hash});
                offset += length;
            }
            previous_used = offset;
        }
        if (!same_stats(snapshot.stats[i], measured))
            invalid("MPT packing statistics disagree with the page image");
    }

    std::set<RecordAddress> visited;
    std::function<NodeKind(const Locator&, TrieKind, std::size_t, const Hash&, bool)> visit;
    std::function<NodeKind(const Bytes&, TrieKind, std::size_t,
                           const std::vector<Locator>*)> walk;
    visit = [&](const Locator& locator, TrieKind role, std::size_t depth,
                const Hash& expected, bool ordinary) {
        if (locator.empty()) invalid("nonempty MPT reference has an empty locator");
        const auto tier = tier_for(role, depth, snapshot.profile);
        const RecordAddress address{tier, locator.page_id, locator.offset};
        const auto found = inventory.find(address);
        if (found == inventory.end() || found->second.locator != locator)
            invalid("MPT link does not point to an exact stored record extent");
        const auto& stored = found->second;
        const auto& record = stored.record;
        if (record.trie_kind != role || record.nibble_depth != depth || stored.hash != expected)
            invalid("MPT link has incorrect role, incoming depth, or canonical hash");
        if (ordinary && record.canonical_rlp.size() < 32)
            invalid("short ordinary child must be embedded");
        if (visited.insert(address).second)
            walk(record.canonical_rlp, role, depth, &record.links);
        return record.kind;
    };
    walk = [&](const Bytes& bytes, TrieKind role, std::size_t depth,
               const std::vector<Locator>* links) {
        const auto node = decode_node(bytes, role, depth);
        std::size_t consumed = 0;
        const auto child_kind = [&](const ChildReference& child, std::size_t child_depth) {
            if (child.hash) {
                if (!links || consumed >= links->size())
                    invalid("embedded MPT subtree has an external reference");
                return visit((*links)[consumed++], role, child_depth, *child.hash, true);
            }
            if (child.embedded.empty() || child.embedded.size() >= 32)
                invalid("invalid embedded MPT child");
            return walk(child.embedded, role, child_depth, nullptr);
        };
        if (node.kind == NodeKind::branch) {
            for (const auto& child : node.children)
                if (!child.empty()) child_kind(child, depth + 1);
        } else if (node.kind == NodeKind::extension) {
            if (child_kind(node.child, depth + node.path.size()) != NodeKind::branch)
                invalid("canonical extension must lead to a branch");
        } else if (role == TrieKind::account) {
            if (!links || links->size() != 1)
                invalid("account leaf must have one external storage-root locator");
            const auto storage = decode_account(node.value).storage_root;
            const auto locator = (*links)[consumed++];
            if (storage == empty_trie_root()) {
                if (!locator.empty()) invalid("empty storage root has a nonzero locator");
            } else {
                visit(locator, TrieKind::storage, 0, storage, false);
            }
        }
        if (links && consumed != links->size())
            invalid("unused auxiliary MPT links");
        return node.kind;
    };
    for (const auto& root : roots) {
        if (root.state_root == empty_trie_root()) {
            if (!root.account_root.empty()) invalid("empty state root has a nonzero locator");
        } else {
            visit(root.account_root, TrieKind::account, 0, root.state_root, false);
        }
    }
    if (visited.size() != inventory.size())
        invalid("packed image contains unreachable records");
}

}  // namespace

void validate_packed_snapshot(const PackedSnapshot& snapshot) {
    validate_image(snapshot, {{snapshot.state_root, snapshot.account_root}});
}

void validate_packed_generation(const PackedGeneration& generation) {
    validate_image(generation, generation.roots, &generation.packing_run_starts);
}

}  // namespace ethereum_mpt
