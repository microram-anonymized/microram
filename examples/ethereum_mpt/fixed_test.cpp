// Tests the fixed-work masks, extraction windows, record extraction and the
// fixed-permutation Keccak against the reference for every node length.

#include "fixed.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>
#include <string>

namespace ethereum_mpt {
namespace {

void expect_fixed(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("fixed helper test: ") + message);
}

void test_masks() {
    constexpr auto maximum = std::numeric_limits<std::uint64_t>::max();
    expect_fixed(fixed::mask(false) == 0 && fixed::mask(true) == maximum, "mask representation");
    const std::array<std::uint64_t, 6> values{{0, 1, 255, maximum / 2,
                                             maximum / 2 + 1, maximum}};
    for (const auto a : values) {
        for (const auto b : values) {
            expect_fixed(fixed::eq(a, b) == (a == b ? maximum : 0), "equality mask");
            expect_fixed(fixed::lt(a, b) == (a < b ? maximum : 0), "unsigned comparison mask");
            expect_fixed(fixed::select(0, a, b) == b &&
                             fixed::select(maximum, a, b) == a, "masked selection");
        }
    }
}

template <std::size_t N, std::size_t M>
void test_windows() {
    std::array<std::uint8_t, N> input{};
    for (std::size_t i = 0; i < N; ++i) input[i] = static_cast<std::uint8_t>(i * 71 + i / 256 + 1);
    for (std::uint64_t offset = 0; offset <= N + 1; ++offset) {
        const auto result = fixed::window<N, M>(input, offset);
        for (std::size_t i = 0; i < M; ++i) {
            const auto expected = offset < N && i < N - offset ? input[offset + i] : 0;
            expect_fixed(result[i] == expected, "fixed window, padding or wraparound");
        }
        expect_fixed(fixed::byte_at(input, offset) == (offset < N ? input[offset] : 0),
                     "fixed byte lookup");
    }
    for (const auto offset : {std::uint64_t{65535}, std::uint64_t{1} << 63,
                              std::numeric_limits<std::uint64_t>::max()}) {
        expect_fixed(fixed::window<N, M>(input, offset) == std::array<std::uint8_t, M>{},
                     "invalid window offset");
        expect_fixed(fixed::byte_at(input, offset) == 0, "invalid byte offset");
    }
}

void check_record(const Page& page, std::uint16_t offset, std::uint16_t length,
                  std::uint64_t page_id = 1, fixed::Mask needed = ~fixed::Mask{0}) {
    const auto result = fixed::extract_record(page, {page_id, offset, length}, needed);
    const bool valid = page_id != 0 && length >= 8 && length <= fixed::record_bytes &&
                       std::size_t{offset} + length <= page_bytes;
    expect_fixed(result.valid == fixed::mask(needed == 0 || valid), "record extent validation");
    for (std::size_t i = 0; i < result.bytes.size(); ++i) {
        const auto expected = needed != 0 && valid && i < length ? page[offset + i] : 0;
        expect_fixed(result.bytes[i] == expected, "record extraction or tail masking");
    }
}

void test_records() {
    Page page{};
    for (std::size_t i = 0; i < page.size(); ++i) page[i] = static_cast<std::uint8_t>(i * 71 + i / 256 + 1);
    // Exercise every page offset against lengths on both sides of all relevant
    // bounds. Separately sweep every legal length at the start and exact end of
    // a page and one byte past that end, covering every extent boundary.
    for (std::size_t offset = 0; offset <= page_bytes; ++offset) {
        for (const auto length : {0, 1, 7, 8, 9, 31, 32, 532, 731, 732, 733,
                                  static_cast<int>(page_bytes), 65535}) {
            check_record(page, static_cast<std::uint16_t>(offset), static_cast<std::uint16_t>(length));
        }
        check_record(page, static_cast<std::uint16_t>(offset), 732, 1, 0);
    }
    for (std::size_t length = 0; length <= fixed::record_bytes + 1; ++length) {
        check_record(page, 0, static_cast<std::uint16_t>(length));
        check_record(page, static_cast<std::uint16_t>(page_bytes - length),
                     static_cast<std::uint16_t>(length));
        check_record(page, static_cast<std::uint16_t>(page_bytes - length + 1),
                     static_cast<std::uint16_t>(length));
    }
    check_record(page, 65535, 65535);
    check_record(page, 65535, 65535, 1, 0);
    check_record(page, 0, 8, 0);
    check_record(page, 0, 8, std::numeric_limits<std::uint64_t>::max());
}

void test_fixed_keccak() {
    fixed::NodeBytes input{};
    for (std::size_t i = 0; i < input.size(); ++i) input[i] = static_cast<std::uint8_t>(i);
    // All 533 supported lengths include 135/136, 271/272, 407/408 and the
    // 532-byte limit. The reference codec has independent Keccak oracle vectors.
    for (std::size_t length = 0; length <= input.size(); ++length) {
        const auto expected = keccak256(input.data(), length);
        expect_fixed(fixed::keccak_node(input, length) == expected, "fixed Keccak digest");
        auto altered = input;
        for (std::size_t i = length; i < input.size(); ++i) altered[i] ^= 0xff;
        expect_fixed(fixed::keccak_node(altered, length) == expected, "Keccak ignores padded tail");
    }
    for (const auto length : {std::uint64_t{533}, std::uint64_t{544}, std::uint64_t{65535},
                              std::numeric_limits<std::uint64_t>::max()}) {
        expect_fixed(fixed::keccak_node(input, length) == Hash{}, "malformed Keccak length");
    }
}

}  // namespace
}  // namespace ethereum_mpt

void run_fixed_tests() {
    ethereum_mpt::test_masks();
    ethereum_mpt::test_windows<0, 2>();
    ethereum_mpt::test_windows<1, 1>();
    ethereum_mpt::test_windows<31, 33>();
    ethereum_mpt::test_windows<532, 32>();
    ethereum_mpt::test_windows<732, 192>();
    ethereum_mpt::test_records();
    ethereum_mpt::test_fixed_keccak();
}
