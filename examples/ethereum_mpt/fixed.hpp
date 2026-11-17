// Fixed-work building blocks for private traversal code: zero/all-ones masks
// with compiler value barriers, masked selection, fixed-address record
// extraction from a page, and fixed-permutation Keccak. Addresses and control
// flow depend only on public sizes, never on private bytes or offsets.

#pragma once

#include "packing.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace ethereum_mpt::fixed {

// Private local processing uses zero/all-ones masks, never C++ short circuiting.
using Mask = std::uint64_t;
inline constexpr std::size_t node_bytes = 532;
inline constexpr std::size_t record_bytes = 732;
using NodeBytes = std::array<std::uint8_t, node_bytes>;
using RecordBytes = std::array<std::uint8_t, record_bytes>;

// Keep the compiler from knowing that a selection mask is only zero/all ones.
// Otherwise it may replace arithmetic selection with conditional control flow.
inline std::uint64_t value_barrier(std::uint64_t value) {
#if defined(__GNUC__) || defined(__clang__)
    __asm__("" : "+r"(value));
    return value;
#else
#error "The private MPT example requires GCC or Clang value barriers"
#endif
}

// Barrier at mask creation as well as selection: Clang can otherwise unswitch
// a fixed scan on an invariant validity condition before the select barrier.
inline Mask mask(bool value) {
    return value_barrier(Mask{0} - static_cast<Mask>(value));
}
inline Mask eq(std::uint64_t lhs, std::uint64_t rhs) { return mask(lhs == rhs); }
inline Mask lt(std::uint64_t lhs, std::uint64_t rhs) { return mask(lhs < rhs); }

inline std::uint64_t select(Mask choose_yes, std::uint64_t yes, std::uint64_t no) {
    const auto opaque = value_barrier(choose_yes);
    return (yes & opaque) | (no & ~opaque);
}

// Every address is public, even for invalid offsets. Returns zero outside N.
template <std::size_t N>
std::uint8_t byte_at(const std::array<std::uint8_t, N>& bytes,
                     std::uint64_t offset) {
    std::uint64_t result = 0;
    for (std::size_t i = 0; i < N; ++i) {
        result |= select(eq(i, offset), bytes[i], 0);
    }
    return static_cast<std::uint8_t>(result);
}

namespace detail {
constexpr std::size_t padded_width(std::size_t size) {
    std::size_t result = 1;
    while (result < size) result *= 2;
    return result;
}
}  // namespace detail

// A fixed-stage barrel rotation followed by a fixed output scan. Both source
// alternatives at every stage have public addresses. The final mask removes
// padding and wrapped bytes, including when offset is an arbitrary uint64_t.
template <std::size_t N, std::size_t M>
std::array<std::uint8_t, M> window(const std::array<std::uint8_t, N>& bytes,
                                  std::uint64_t offset) {
    constexpr auto width = detail::padded_width(N > M ? N : M);
    std::array<std::uint8_t, width> current{};
    std::array<std::uint8_t, width> next{};
    for (std::size_t i = 0; i < N; ++i) current[i] = bytes[i];
    for (std::size_t shift = 1; shift < width; shift *= 2) {
        const auto rotate_mask = mask((offset & shift) != 0);
        for (std::size_t i = 0; i < width; ++i) {
            next[i] = static_cast<std::uint8_t>(select(
                rotate_mask, current[(i + shift) & (width - 1)], current[i]));
        }
        current = next;
    }
    const auto remaining = select(lt(offset, N), N - offset, 0);
    std::array<std::uint8_t, M> result{};
    for (std::size_t i = 0; i < M; ++i) {
        result[i] = static_cast<std::uint8_t>(select(lt(i, remaining), current[i], 0));
    }
    return result;
}

struct ExtractedRecord {
    RecordBytes bytes{};
    Mask valid = 0;
};

// A needed record requires a nonzero page ID and an 8..732-byte extent wholly
// inside the page. Invalid or unused records return zero bytes. Unused records
// are valid dummies; callers still check that their scheduled page was present.
ExtractedRecord extract_record(const Page& page, const Locator& locator, Mask need_page);

// Always performs four Keccak-f[1600] permutations, including for length zero
// and malformed length. Lengths above 532 return an all-zero digest. Bytes past
// length do not participate in the digest. This is original Ethereum Keccak.
Hash keccak_node(const NodeBytes& bytes, std::uint64_t length);

}  // namespace ethereum_mpt::fixed
