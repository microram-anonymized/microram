// Fixed-work parser for one canonical MPT node and its packed record: opens
// exactly 17 outer RLP item slots, scans all child positions and locator
// candidates, and selects values with masks instead of branches.

#include "fixed_node.hpp"

namespace ethereum_mpt::fixed {
namespace {

struct Item {
    Mask valid = 0;
    Mask list = 0;
    std::uint64_t offset = 0;
    std::uint64_t payload = 0;
    std::uint64_t length = 0;
    std::uint64_t total = 0;
};

// All lengths produced here are at most 65538, including malformed prefixes.
// That bound keeps cursor arithmetic safe even while processing invalid input.
Item item_at(const NodeBytes& bytes, std::uint64_t offset,
             std::uint64_t limit) {
    const std::uint64_t prefix = byte_at(bytes, offset);
    const std::uint64_t second = byte_at(bytes, offset + 1);
    const std::uint64_t third = byte_at(bytes, offset + 2);
    const std::uint64_t fourth = byte_at(bytes, offset + 3);
    const Mask single = lt(prefix, 0x80);
    const Mask list = ~lt(prefix, 0xc0);
    const Mask long_form = (lt(0xb7, prefix) & lt(prefix, 0xc0)) |
                           lt(0xf7, prefix);
    const auto base = select(list, 0xc0, 0x80);
    const auto length_bytes = prefix - select(list, 0xf7, 0xb7);
    const auto long_length = select(eq(length_bytes, 1), second,
                                    (second << 8) | third);
    const auto length = select(single, 1,
        select(long_form, long_length, prefix - base));
    const auto header = select(single, 0,
        select(long_form, select(eq(length_bytes, 1), 2, 3), 1));
    const auto first = select(single, prefix,
        select(long_form, select(eq(length_bytes, 1), third, fourth), second));
    const auto total = header + length;
    Mask valid = lt(offset, limit) & ~lt(limit - offset, total);
    valid &= ~long_form | (lt(0, length_bytes) & ~lt(2, length_bytes) &
                          ~eq(second, 0) & ~lt(length, 56));
    // A one-byte string below 0x80 must use the byte itself as its RLP.
    valid &= ~(~single & ~list & eq(length, 1) & lt(first, 0x80));
    return {valid, list, offset, offset + header, length, total};
}

struct Reference {
    Child child;
    Mask valid;
};

Reference reference_at(const NodeBytes& bytes, const Item& item) {
    const Mask empty = ~item.list & eq(item.length, 0);
    const Mask embedded = item.list & lt(item.total, 32);
    const Mask hashed = ~item.list & eq(item.length, 32);
    const auto source = window<node_bytes, 33>(bytes, item.offset);
    Child child;
    child.type = select(embedded, 1, select(hashed, 2, 0));
    child.length = select(embedded, item.total, 0);
    for (std::size_t i = 0; i < child.embedded.size(); ++i)
        child.embedded[i] = static_cast<std::uint8_t>(select(
            embedded & lt(i, item.total), source[i], 0));
    for (std::size_t i = 0; i < child.hash.size(); ++i)
        child.hash[i] = static_cast<std::uint8_t>(select(hashed, source[i + 1], 0));
    return {child, item.valid & (empty | embedded | hashed)};
}

Mask scalar_valid(const NodeBytes& bytes, const Item& item,
                  std::uint64_t maximum) {
    return item.valid & ~item.list & ~lt(maximum, item.length) &
           (eq(item.length, 0) | ~eq(byte_at(bytes, item.payload), 0));
}

Word scalar_word(const NodeBytes& bytes, const Item& item) {
    const auto source = window<node_bytes, 32>(bytes, item.payload);
    std::array<std::uint8_t, 64> padded{};
    for (std::size_t i = 0; i < source.size(); ++i) padded[i + 32] = source[i];
    return window<64, 32>(padded, item.length);
}

Mask account_value(const NodeBytes& bytes, const Item& value, ParsedNode& node) {
    const auto end = value.payload + value.length;
    const auto outer = item_at(bytes, value.payload, end);
    Mask valid = value.valid & ~value.list & ~lt(110, value.length) &
                 outer.valid & outer.list & eq(outer.total, value.length);
    std::array<Item, 4> fields{};
    auto cursor = outer.payload;
    const auto field_end = outer.payload + outer.length;
    for (std::size_t i = 0; i < fields.size(); ++i) {
        fields[i] = item_at(bytes, cursor, field_end);
        valid &= fields[i].valid;
        cursor += fields[i].total;
    }
    valid &= eq(cursor, field_end);
    valid &= scalar_valid(bytes, fields[0], 8);
    valid &= scalar_valid(bytes, fields[1], 32);
    valid &= ~fields[2].list & eq(fields[2].length, 32);
    valid &= ~fields[3].list & eq(fields[3].length, 32);
    const auto nonce = window<node_bytes, 8>(bytes, fields[0].payload);
    for (std::size_t i = 0; i < nonce.size(); ++i)
        node.nonce = select(lt(i, fields[0].length),
                            (node.nonce << 8) | nonce[i], node.nonce);
    node.balance = scalar_word(bytes, fields[1]);
    node.storage_root = window<node_bytes, 32>(bytes, fields[2].payload);
    node.code_hash = window<node_bytes, 32>(bytes, fields[3].payload);
    return valid;
}

Mask storage_value(const NodeBytes& bytes, const Item& value, ParsedNode& node) {
    const auto inner = item_at(bytes, value.payload, value.payload + value.length);
    node.storage_value = scalar_word(bytes, inner);
    return value.valid & ~value.list & eq(inner.total, value.length) &
           scalar_valid(bytes, inner, 32) & ~eq(inner.length, 0);
}

std::uint64_t read16(const RecordBytes& bytes, std::size_t offset) {
    return std::uint64_t{bytes[offset]} | (std::uint64_t{bytes[offset + 1]} << 8);
}

}  // namespace

ParsedNode parse_node(const NodeBytes& bytes, std::uint64_t length,
                      TrieKind role, std::size_t depth) {
    ParsedNode node;
    const Mask bounded = ~lt(node_bytes, length);
    const auto outer = item_at(bytes, 0, select(bounded, length, 0));
    Mask valid = bounded & outer.valid & outer.list & eq(outer.total, length) &
                 ~lt(64, depth) &
                 (eq(static_cast<std::uint64_t>(role), 0) |
                  eq(static_cast<std::uint64_t>(role), 1));
    std::array<Item, 17> items{};
    const auto end = outer.payload + outer.length;
    auto cursor = outer.payload;
    std::uint64_t count = 0;
    for (std::size_t i = 0; i < items.size(); ++i) {
        const Mask active = lt(cursor, end);
        items[i] = item_at(bytes, cursor, end);
        valid &= ~active | items[i].valid;
        count += active & 1;
        cursor += select(active, items[i].total, 0);
    }
    valid &= eq(cursor, end);
    const Mask branch = eq(count, 17);
    const Mask short_node = eq(count, 2);
    valid &= branch | short_node;

    Mask branch_valid = lt(depth, 64) & ~items[16].list & eq(items[16].length, 0);
    std::uint64_t nonempty = 0, hashes = 0;
    for (std::size_t i = 0; i < node.children.size(); ++i) {
        auto reference = reference_at(bytes, items[i]);
        reference.child.link_index = hashes;
        node.children[i] = reference.child;
        branch_valid &= reference.valid;
        nonempty += (~eq(reference.child.type, 0)) & 1;
        hashes += eq(reference.child.type, 2) & 1;
    }
    branch_valid &= ~lt(nonempty, 2);

    const auto compact = window<node_bytes, 33>(bytes, items[0].payload);
    const std::uint64_t flags = compact[0] >> 4;
    const Mask odd = mask((flags & 1) != 0);
    const Mask leaf = mask((flags & 2) != 0);
    const Mask compact_size = lt(0, items[0].length) & ~lt(33, items[0].length);
    const auto path_length = select(compact_size,
        items[0].length * 2 - 2 + (flags & 1), 0);
    const auto remaining = select(~lt(64, depth), 64 - depth, 0);
    Mask path_valid = items[0].valid & ~items[0].list & compact_size &
                      ~lt(3, flags) & (odd | eq(compact[0] & 15, 0)) &
                      ~lt(64, path_length);
    for (std::size_t i = 0; i < node.path.size(); ++i) {
        // Both source nibbles are indexed only by this public loop counter.
        const auto odd_byte = compact[(i + 1) / 2];
        const auto even_byte = compact[(i + 2) / 2];
        const auto odd_nibble = (odd_byte >> (4 * ((i + 2) % 2))) & 15;
        const auto even_nibble = (even_byte >> (4 * ((i + 3) % 2))) & 15;
        node.path[i] = static_cast<std::uint8_t>(select(
            short_node & lt(i, path_length), select(odd, odd_nibble, even_nibble), 0));
    }
    auto extension = reference_at(bytes, items[1]);
    node.child = extension.child;
    const Mask extension_valid = extension.valid & ~eq(extension.child.type, 0) &
                                 lt(0, path_length) & lt(path_length, remaining);
    // The role is public, so the two value profiles may have distinct schedules.
    Mask value_valid;
    if (role == TrieKind::account)
        value_valid = account_value(bytes, items[1], node);
    else
        value_valid = storage_value(bytes, items[1], node);
    const Mask leaf_valid = value_valid & eq(path_length, remaining);
    valid &= (~branch | branch_valid) &
             (~short_node | (path_valid & select(leaf, leaf_valid, extension_valid)));
    node.valid = valid;
    node.kind = select(branch, static_cast<std::uint64_t>(NodeKind::branch),
        select(leaf, static_cast<std::uint64_t>(NodeKind::leaf),
                     static_cast<std::uint64_t>(NodeKind::extension)));
    node.path_length = select(short_node, path_length, 0);
    node.hashed_children = select(branch, hashes,
        select(~leaf & short_node, eq(extension.child.type, 2) & 1, 0));
    return node;
}

DecodedRecord decode_record(const RecordBytes& bytes,
                            std::uint64_t record_length,
                            TrieKind role, std::size_t depth) {
    DecodedRecord record;
    record.length = read16(bytes, 0);
    record.kind = bytes[2];
    record.link_count = bytes[4];
    Mask valid = lt(0, record.length) & ~lt(node_bytes, record.length) &
        ~lt(record_bytes, record_length) &
        eq(record_length, 8 + record.length + 12 * record.link_count) &
        ~lt(2, record.kind) & eq(bytes[3], static_cast<std::uint64_t>(role)) &
        ~lt(1, bytes[3]) & ~lt(16, record.link_count) &
        eq(bytes[5], depth) & ~lt(64, depth) & eq(bytes[6], 0) & eq(bytes[7], 0);
    for (std::size_t i = 0; i < record.node.size(); ++i)
        record.node[i] = static_cast<std::uint8_t>(select(lt(i, record.length), bytes[i + 8], 0));
    for (std::size_t i = 0; i < record.links.size(); ++i) {
        const auto link = window<record_bytes, 12>(bytes, 8 + record.length + 12 * i);
        std::uint64_t page = 0;
        for (std::size_t j = 0; j < 8; ++j) page |= std::uint64_t{link[j]} << (8 * j);
        const auto offset = std::uint64_t{link[8]} | (std::uint64_t{link[9]} << 8);
        const auto size = std::uint64_t{link[10]} | (std::uint64_t{link[11]} << 8);
        const Mask active = lt(i, record.link_count);
        const Mask empty = eq(page, 0) & eq(offset, 0) & eq(size, 0);
        const Mask extent = ~eq(page, 0) & ~lt(size, 8) & ~lt(record_bytes, size) &
                            ~lt(page_bytes, offset + size);
        valid &= ~active | empty | extent;
        record.links[i] = {select(active, page, 0),
            static_cast<std::uint16_t>(select(active, offset, 0)),
            static_cast<std::uint16_t>(select(active, size, 0))};
    }
    record.valid = valid;
    return record;
}

}  // namespace ethereum_mpt::fixed
