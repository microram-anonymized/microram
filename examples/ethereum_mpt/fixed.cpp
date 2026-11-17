// Fixed-work primitives for the private traversal: record extraction through a
// fixed-stage rotation network and a Keccak-256 that always runs four complete
// permutations (enough for the 532-byte maximum node), saving the digest under a
// mask at the true final block.

#include "fixed.hpp"

namespace ethereum_mpt::fixed {
namespace {

constexpr std::size_t keccak_rate = 136;
constexpr std::array<std::uint64_t, 24> round_constants{{
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL,
}};
constexpr std::array<unsigned, 25> rotations{{
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43,
    25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
}};

std::uint64_t rotate(std::uint64_t value, unsigned shift) {
    // Both shifts are in 0..63, including the public zero-rotation lane.
    return (value << shift) | (value >> ((64 - shift) & 63));
}

// Every round, lane index and rotation amount is public. Keep this private
// helper separate from the allocating, variable-work public codec API.
void permute(std::array<std::uint64_t, 25>& state) {
    for (const auto round_constant : round_constants) {
        std::array<std::uint64_t, 5> columns{};
        for (std::size_t x = 0; x < 5; ++x) {
            for (std::size_t y = 0; y < 5; ++y) columns[x] ^= state[x + 5 * y];
        }
        for (std::size_t x = 0; x < 5; ++x) {
            const auto delta = columns[(x + 4) % 5] ^ rotate(columns[(x + 1) % 5], 1);
            for (std::size_t y = 0; y < 5; ++y) state[x + 5 * y] ^= delta;
        }
        std::array<std::uint64_t, 25> moved{};
        for (std::size_t x = 0; x < 5; ++x) {
            for (std::size_t y = 0; y < 5; ++y) {
                moved[y + 5 * ((2 * x + 3 * y) % 5)] =
                    rotate(state[x + 5 * y], rotations[x + 5 * y]);
            }
        }
        for (std::size_t x = 0; x < 5; ++x) {
            for (std::size_t y = 0; y < 5; ++y) {
                state[x + 5 * y] = moved[x + 5 * y] ^
                    ((~moved[(x + 1) % 5 + 5 * y]) & moved[(x + 2) % 5 + 5 * y]);
            }
        }
        state[0] ^= round_constant;
    }
}

}  // namespace

ExtractedRecord extract_record(const Page& page, const Locator& locator, Mask need_page) {
    const auto page_id = select(need_page, locator.page_id, 0);
    const auto offset = select(need_page, locator.offset, 0);
    const auto length = select(need_page, locator.record_bytes, 0);
    const auto extent_ok = ~eq(page_id, 0) & ~lt(length, 8) &
                           ~lt(record_bytes, length) & ~lt(page_bytes, offset + length);
    ExtractedRecord result;
    result.valid = ~need_page | extent_ok;
    const auto extracted = window<page_bytes, record_bytes>(page, offset);
    for (std::size_t i = 0; i < record_bytes; ++i) {
        result.bytes[i] = static_cast<std::uint8_t>(
            select(need_page & extent_ok & lt(i, length), extracted[i], 0));
    }
    return result;
}

Hash keccak_node(const NodeBytes& bytes, std::uint64_t length) {
    const auto valid = ~lt(node_bytes, length);
    const auto bounded_length = select(valid, length, 0);
    const auto final_block = bounded_length / keccak_rate;
    // The final 12 bytes are public padding, so all four rate blocks can be
    // scanned directly without ever loading outside the 532-byte node input.
    std::array<std::uint8_t, 4 * keccak_rate> input{};
    for (std::size_t i = 0; i < node_bytes; ++i) input[i] = bytes[i];
    std::array<std::uint64_t, 25> state{};
    Hash result{};
    for (std::size_t block = 0; block < 4; ++block) {
        const auto take_digest = eq(block, final_block) & valid;
        for (std::size_t i = 0; i < keccak_rate; ++i) {
            const auto position = block * keccak_rate + i;
            auto byte = select(lt(position, bounded_length), input[position], 0);
            // Ethereum uses the original Keccak 0x01 suffix (SHA3 uses 0x06).
            byte ^= select(eq(position, bounded_length), 0x01, 0);
            byte ^= select(eq(block, final_block) & eq(i, keccak_rate - 1), 0x80, 0);
            state[i / 8] ^= byte << (8 * (i % 8));
        }
        permute(state);
        for (std::size_t i = 0; i < result.size(); ++i) {
            const auto byte = static_cast<std::uint8_t>(state[i / 8] >> (8 * (i % 8)));
            result[i] = static_cast<std::uint8_t>(select(take_digest, byte, result[i]));
        }
    }
    return result;
}

}  // namespace ethereum_mpt::fixed
