// BatchTraversal: the private, fixed-schedule account/storage proof traversal.
// Every lane reads one page in each of the 65 public depth rounds (dummy page
// zero when idle), and all transitions use masked selection.

#include "traversal.hpp"
#include "fixed_node.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>

namespace ethereum_mpt {
namespace {
using fixed::Mask;
using fixed::eq;
using fixed::lt;
using fixed::mask;
using fixed::select;

template <std::size_t N>
Mask equal_bytes(const std::array<std::uint8_t, N>& a,
                 const std::array<std::uint8_t, N>& b) {
    std::uint64_t difference = 0;
    for (std::size_t i = 0; i < N; ++i) difference |= a[i] ^ b[i];
    return eq(difference, 0);
}

template <std::size_t N>
void assign_bytes(std::array<std::uint8_t, N>& target, Mask condition,
                  const std::array<std::uint8_t, N>& source) {
    for (std::size_t i = 0; i < N; ++i)
        target[i] = static_cast<std::uint8_t>(select(condition, source[i], target[i]));
}

void assign_locator(Locator& target, Mask condition, const Locator& source) {
    target.page_id = select(condition, source.page_id, target.page_id);
    target.offset = static_cast<std::uint16_t>(select(condition, source.offset, target.offset));
    target.record_bytes = static_cast<std::uint16_t>(
        select(condition, source.record_bytes, target.record_bytes));
}

Mask zero_locator(const Locator& locator) {
    return eq(locator.page_id | locator.offset | locator.record_bytes, 0);
}

Mask real_locator(const Locator& locator) {
    return ~eq(locator.page_id, 0) & ~lt(locator.record_bytes, 8) &
           ~lt(fixed::record_bytes, locator.record_bytes) &
           ~lt(page_bytes, std::uint64_t{locator.offset} + locator.record_bytes);
}

struct Lane {
    std::array<std::uint8_t, 64> key{};
    std::uint64_t cursor = 0;
    Mask active = 0, error = 0, external = 0, root = 0, require_branch = 0;
    Hash expected{};
    Locator locator{}, storage_locator{};
    std::array<std::uint8_t, 31> embedded{};
    std::uint64_t embedded_length = 0;
};

Lane start_lane(const Hash& key, const Hash& root, const Locator& locator,
                const Hash& empty_root, Mask inherited_error) {
    Lane lane;
    for (std::size_t i = 0; i < key.size(); ++i) {
        lane.key[2 * i] = key[i] >> 4;
        lane.key[2 * i + 1] = key[i] & 15;
    }
    const auto empty = equal_bytes(root, empty_root);
    lane.error = inherited_error | (empty & ~zero_locator(locator)) |
                 (~empty & ~real_locator(locator));
    lane.active = ~empty & ~lane.error;
    lane.external = ~Mask{0};
    lane.root = ~Mask{0};
    lane.expected = root;
    lane.locator = locator;
    return lane;
}

void select_child(fixed::Child& target, Mask condition, const fixed::Child& source) {
    target.type = select(condition, source.type, target.type);
    target.length = select(condition, source.length, target.length);
    target.link_index = select(condition, source.link_index, target.link_index);
    assign_bytes(target.embedded, condition, source.embedded);
    assign_bytes(target.hash, condition, source.hash);
}

void step(Lane& lane, TraversalResult& result, const Page& page,
          std::uint8_t found, TrieKind role, std::size_t depth,
          const Hash& empty_root) {
    lane.error |= ~eq(found, 1);
    lane.error |= lane.active & (lt(lane.cursor, depth) | lt(64, lane.cursor));
    const auto due = lane.active & eq(lane.cursor, depth) & ~lane.error;
    const auto need_page = due & lane.external;
    const auto extracted = fixed::extract_record(page, lane.locator, need_page);
    const auto record = fixed::decode_record(extracted.bytes,
        select(need_page, lane.locator.record_bytes, 0), role, depth);
    fixed::NodeBytes node{};
    for (std::size_t i = 0; i < node.size(); ++i) {
        // i is public; the inline array is deliberately only 31 bytes wide.
        const auto embedded = i < lane.embedded.size() ? lane.embedded[i] : 0;
        node[i] = static_cast<std::uint8_t>(select(due,
            select(need_page, record.node[i], embedded), 0));
    }
    const auto length = select(due,
        select(need_page, record.length, lane.embedded_length), 0);
    const auto parsed = fixed::parse_node(node, length, role, depth);
    const auto digest = fixed::keccak_node(node, length);
    const auto branch = eq(parsed.kind, static_cast<std::uint64_t>(NodeKind::branch));
    const auto extension = eq(parsed.kind, static_cast<std::uint64_t>(NodeKind::extension));
    const auto leaf = eq(parsed.kind, static_cast<std::uint64_t>(NodeKind::leaf));
    const auto account_leaf = leaf & mask(role == TrieKind::account);
    const auto storage_empty = equal_bytes(parsed.storage_root, empty_root);
    const auto expected_links = parsed.hashed_children + (account_leaf & 1);
    auto metadata_ok = extracted.valid & record.valid & eq(record.kind, parsed.kind) &
                       eq(record.link_count, expected_links);
    // All link extents are checked, including siblings. Only the empty-storage
    // sentinel may be zero, and it must bind to the canonical account value.
    for (std::size_t i = 0; i < record.links.size(); ++i) {
        const auto allow_zero = account_leaf & storage_empty & eq(i, 0);
        const auto valid = (allow_zero & zero_locator(record.links[i])) |
                           (~allow_zero & real_locator(record.links[i]));
        metadata_ok &= ~lt(i, expected_links) | valid;
    }
    const auto authentication = equal_bytes(digest, lane.expected) &
                               (lane.root | ~lt(length, 32));
    const auto checked = parsed.valid & (~lane.require_branch | branch) &
                        (~need_page | (metadata_ok & authentication));
    lane.error |= due & ~checked;
    const auto commit = due & checked & ~lane.error;

    auto& slot = result.proof.slots[depth];
    const auto include = commit & need_page;
    slot[0] = static_cast<std::uint8_t>(select(include, length & 255, 0));
    slot[1] = static_cast<std::uint8_t>(select(include, length >> 8, 0));
    slot[2] = static_cast<std::uint8_t>(include & 1);
    slot[3] = 0;
    for (std::size_t i = 0; i < node.size(); ++i)
        slot[4 + i] = static_cast<std::uint8_t>(select(include & lt(i, length), node[i], 0));

    Mask path_matches = ~Mask{0};
    for (std::size_t i = 0; i < parsed.path.size(); ++i) {
        const auto key_nibble = depth + i < lane.key.size() ? lane.key[depth + i] : 0;
        path_matches &= ~lt(i, parsed.path_length) | eq(parsed.path[i], key_nibble);
    }
    fixed::Child child;
    const auto nibble = depth < lane.key.size() ? lane.key[depth] : 0;
    for (std::size_t i = 0; i < parsed.children.size(); ++i)
        select_child(child, branch & eq(i, nibble), parsed.children[i]);
    select_child(child, extension, parsed.child);
    Locator next_locator;
    for (std::size_t i = 0; i < record.links.size(); ++i)
        assign_locator(next_locator, eq(i, child.link_index), record.links[i]);
    const auto advance = commit & (branch | (extension & path_matches)) & ~eq(child.type, 0);
    const auto match_leaf = commit & leaf & path_matches;
    const auto next_depth = select(branch, depth + 1, depth + parsed.path_length);
    const auto progress_ok = lt(depth, next_depth) & ~lt(64, next_depth);
    lane.error |= advance & ~progress_ok;
    lane.active = select(due, advance & progress_ok, lane.active) & ~lane.error;
    lane.cursor = select(advance, next_depth, lane.cursor);
    lane.external = select(advance, eq(child.type, 2), lane.external);
    lane.root = select(advance, 0, lane.root);
    lane.require_branch = select(advance, extension, lane.require_branch);
    lane.embedded_length = select(advance, child.length, lane.embedded_length);
    assign_bytes(lane.expected, advance, child.hash);
    assign_bytes(lane.embedded, advance, child.embedded);
    assign_locator(lane.locator, advance, next_locator);
    result.present |= match_leaf;
    // Role is public. Account fields and storage values have distinct meanings.
    if (role == TrieKind::account) {
        result.nonce = select(match_leaf, parsed.nonce, result.nonce);
        assign_bytes(result.balance, match_leaf, parsed.balance);
        assign_bytes(result.storage_root, match_leaf, parsed.storage_root);
        assign_bytes(result.code_hash, match_leaf, parsed.code_hash);
        assign_locator(lane.storage_locator, match_leaf, record.links[0]);
    } else {
        assign_bytes(result.storage_value, match_leaf, parsed.storage_value);
    }
}

void finish(Lane& lane, TraversalResult& result) {
    lane.error |= lane.active;
    result.error = lane.error;
    result.present &= ~lane.error;
    result.nonce = select(lane.error, 0, result.nonce);
    const Hash zero{};
    assign_bytes(result.balance, lane.error, zero);
    assign_bytes(result.storage_root, lane.error, zero);
    assign_bytes(result.code_hash, lane.error, zero);
    assign_bytes(result.storage_value, lane.error, zero);
    for (auto& slot : result.proof.slots)
        for (auto& byte : slot) byte = static_cast<std::uint8_t>(select(lane.error, 0, byte));
}

struct Scratch {
    explicit Scratch(std::size_t count) : ids(count), pages(count), found(count) {}
    std::vector<std::uint64_t> ids;
    std::vector<Page> pages;
    std::vector<std::uint8_t> found;
};

void phase(PageReader& pages, std::vector<Lane>& lanes,
           std::vector<TraversalResult>& results, TrieKind role,
           TierProfile tiers, const Hash& empty_root, Scratch& scratch) {
    for (std::size_t depth = 0; depth < proof_rounds; ++depth) {
        for (std::size_t i = 0; i < lanes.size(); ++i) {
            const auto& lane = lanes[i];
            const auto need = lane.active & eq(lane.cursor, depth) &
                              ~lane.error & lane.external;
            scratch.ids[i] = select(need, lane.locator.page_id, 0);
        }
        pages.read_pages_batch(tier_for(role, depth, tiers), lanes.size(),
            scratch.ids.data(), scratch.pages.data(), scratch.found.data());
        for (std::size_t i = 0; i < lanes.size(); ++i)
            step(lanes[i], results[i], scratch.pages[i], scratch.found[i],
                 role, depth, empty_root);
    }
    for (std::size_t i = 0; i < lanes.size(); ++i) finish(lanes[i], results[i]);
}
}  // namespace

PathRequest make_path_request(const Address& address, const std::vector<Word>& slots) {
    PathRequest result;
    fixed::NodeBytes buffer{};
    for (std::size_t i = 0; i < address.size(); ++i) buffer[i] = address[i];
    result.account_key = fixed::keccak_node(buffer, address.size());
    result.storage_keys.resize(slots.size());
    for (std::size_t s = 0; s < slots.size(); ++s) {
        buffer = {};
        for (std::size_t i = 0; i < slots[s].size(); ++i) buffer[i] = slots[s][i];
        result.storage_keys[s] = fixed::keccak_node(buffer, slots[s].size());
    }
    return result;
}

BatchTraversal::BatchTraversal(Hash root, Locator locator, TierProfile tiers, BatchProfile batch)
    : state_root_(root), root_(locator), tiers_(tiers), batch_(batch) {
    if (tiers.account_top_depth > proof_rounds || tiers.storage_top_depth > proof_rounds)
        throw std::invalid_argument("MPT tier cutoff exceeds 65 depths");
    const auto max = std::numeric_limits<std::size_t>::max();
    if (batch.requests == 0 || batch.storage_slots == max ||
        batch.requests > max / (batch.storage_slots + 1))
        throw std::invalid_argument("MPT batch lane count is zero or overflows");
    const auto lanes = batch.requests * (batch.storage_slots + 1);
    if (lanes > batch.max_proof_bytes / sizeof(FixedProof) ||
        lanes > max / sizeof(TraversalResult) || lanes > max / sizeof(Lane) ||
        lanes > max / sizeof(Page))
        throw std::invalid_argument("MPT batch exceeds public buffer limit");
}

BatchResult BatchTraversal::run(PageReader& pages, const std::vector<PathRequest>& requests) const {
    if (requests.size() != batch_.requests)
        throw std::invalid_argument("MPT request count differs from public profile");
    for (const auto& request : requests)
        if (request.storage_keys.size() != batch_.storage_slots)
            throw std::invalid_argument("MPT slot count differs from public profile");
    const auto storage_count = batch_.requests * batch_.storage_slots;
    if (std::max(batch_.requests, storage_count) > pages.max_lanes())
        throw std::invalid_argument("MPT batch needs more lanes than the page reader has");
    const auto empty_root = empty_trie_root();
    // Allocate every phase buffer before admitting the first page read.
    BatchResult result{std::vector<TraversalResult>(batch_.requests),
                       std::vector<TraversalResult>(storage_count)};
    std::vector<Lane> accounts(batch_.requests), storage(storage_count);
    Scratch scratch(std::max(batch_.requests, storage_count));
    for (std::size_t q = 0; q < batch_.requests; ++q) {
        accounts[q] = start_lane(requests[q].account_key, state_root_, root_, empty_root, 0);
        result.accounts[q].storage_root = empty_root;
    }
    phase(pages, accounts, result.accounts, TrieKind::account, tiers_, empty_root, scratch);
    // Both phases use the same pinned manifest; no publication hook is exposed.
    for (std::size_t q = 0; q < batch_.requests; ++q) {
        for (std::size_t s = 0; s < batch_.storage_slots; ++s) {
            const auto i = q * batch_.storage_slots + s;
            storage[i] = start_lane(requests[q].storage_keys[s], result.accounts[q].storage_root,
                accounts[q].storage_locator, empty_root, result.accounts[q].error);
        }
    }
    if (batch_.storage_slots != 0)
        phase(pages, storage, result.storage, TrieKind::storage, tiers_, empty_root, scratch);
    return result;
}

Proof decode_proof(const FixedProof& fixed_proof) {
    Proof proof;
    for (const auto& slot : fixed_proof.slots) {
        const std::size_t length = slot[0] | (std::size_t{slot[1]} << 8);
        if (slot[2] > 1 || slot[3] != 0 || length > fixed::node_bytes ||
            (slot[2] == 0 && length != 0) || (slot[2] != 0 && length == 0))
            throw std::invalid_argument("invalid fixed MPT proof slot");
        for (std::size_t i = length; i < fixed::node_bytes; ++i)
            if (slot[4 + i] != 0) throw std::invalid_argument("nonzero MPT proof padding");
        if (slot[2]) proof.emplace_back(slot.begin() + 4, slot.begin() + 4 + length);
    }
    return proof;
}
}  // namespace ethereum_mpt
