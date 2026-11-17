// The batch result-layout kernels (src/oram/table/cpu_byteslice_batch_layout.hpp)
// against scalar oracles: the sliced-to-rows merge with a secret take mask and
// a public lane range, ClearSliced, the found line, and the place-at-lane
// hashed extract (wide and narrow strides) against the row extractor.  Every
// value width the engine's batch uses -- one line to several 64-line
// segments, odd widths -- and every lane range shape (offsets and tails that
// are not multiples of eight).  These kernels decide which bytes of a batch's
// answer each lane receives, so an off-by-one here returns another lane's
// value.  The take flags are secret, so the kernels fold them with
// constant-time selects and register blends over the whole public lane range,
// never with a branch or a flag-dependent address.

#include "src/oram/table/cpu_byteslice_batch_layout.hpp"
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <algorithm>
#include <cstring>
#include <random>
#include <vector>

namespace bs = microram::byteslice;
using microram::byteslice::test_support::Expect;

namespace {

std::mt19937_64 rng(0x1A70u);

uint8_t Byte() { return static_cast<uint8_t>(rng()); }

void TestMerges() {
  for (size_t value_lines : {1u, 2u, 9u, 16u, 17u, 33u, 63u, 64u, 65u, 100u, 128u, 129u, 257u}) {
    const size_t row_stride = ((value_lines + 63) / 64) * 64;
    std::vector<uint8_t> sliced(value_lines * 64), rows(64 * row_stride);
    bs::Aligned64Ptr sliced_a = bs::AllocateAligned64(sliced.size());
    std::vector<uint8_t> rows_out(64 * row_stride);
    for (size_t lo : {0u, 1u, 7u, 8u, 21u, 40u}) {
      for (size_t hi : {lo + 1, lo + 3, lo + 8, lo + 13, size_t{42}, size_t{63}, size_t{64}}) {
        if (hi <= lo || hi > 64) continue;
        for (auto& b : sliced) b = Byte();
        for (auto& b : rows) b = Byte();
        uint64_t dense[64];
        for (auto& d : dense) d = rng() & 1;
        // The forwarding merge a chunked batch runs, against the byte-by-byte
        // definition of what it must produce: inside the public [lo, hi) range
        // a lane whose dense flag is set takes the accumulator's byte, and
        // every other byte -- outside the range, past value_lines, or with the
        // flag clear -- is left exactly as it was.
        rows_out = rows;
        bs::MergeSlicedIntoRowsScalar(sliced.data(), value_lines, dense, lo, hi,
                                      rows_out.data(), row_stride);
        for (size_t j = 0; j < 64; ++j) {
          const bool inside = j >= lo && j < hi;
          for (size_t v = 0; v < row_stride; ++v) {
            const uint8_t want = inside && v < value_lines && dense[j]
                                     ? sliced[v * 64 + j] : rows[j * row_stride + v];
            Expect(rows_out[j * row_stride + v] == want,
                   "sliced->rows merge byte");
          }
        }
      }
    }
    // ClearSliced clears exactly value_lines lines.
    std::memcpy(sliced_a.get(), sliced.data(), sliced.size());
    bs::ClearSliced(sliced_a.get(), value_lines);
    for (size_t i = 0; i < sliced.size(); ++i) Expect(sliced_a[i] == 0, "clear");
  }
  // The found line: bytes for the active lanes, zeros past them.
  for (size_t lanes : {0u, 1u, 9u, 64u}) {
    uint64_t flags[64];
    for (auto& f : flags) f = rng();
    alignas(64) uint8_t line[64];
    bs::StoreFlagLine(flags, lanes, line);
    for (size_t j = 0; j < 64; ++j)
      Expect(line[j] == (j < lanes ? (flags[j] & 1) : 0), "flag line byte");
  }
  std::puts("  merges ok");
}

// Eight lanes' buckets, each its own storage: value line v of lane j's bucket
// holds a recognisable byte per slot.  Both instantiations are covered: the
// WIDE one (`slots == 64`), which is what the batched cascade runs, against
// the permute extractor as an independent implementation; and the NARROW one
// at 48, 32 and 16 slots -- the generic byte-line stride this kernel also
// supports -- against the scalar definition of the byte it must place, since
// there is no narrow permute extractor to compare it with.
void TestPlaceAtLane() {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.tag_bytes = 16;
  alignas(64) uint8_t extract[512];
  for (size_t value_lines : {1u, 2u, 17u, 65u, 257u}) {
    layout.value_bytes = value_lines;
    for (unsigned slots : {64u, 48u, 32u, 16u}) {
      const bool narrow = slots != 64;
      const size_t stride = slots;
      const size_t bucket_bytes = (layout.key_bytes + value_lines) * stride;
      std::vector<bs::Aligned64Ptr> storage;
      const uint8_t* buckets[64];
      uint64_t matches[64], takes[64];
      for (size_t j = 0; j < 64; ++j) {
        storage.push_back(bs::AllocateAligned64(bucket_bytes + 64));
        for (size_t i = 0; i < bucket_bytes; ++i) storage.back()[i] = Byte();
        buckets[j] = storage.back().get();
        // A match at a random slot below the piece width, or a miss.  A take
        // implies a hit, as in the cascade (take = hit & !found): the
        // extractors' miss bytes are unspecified and differ between them.
        matches[j] = (rng() % 4 == 0) ? 0 : uint64_t{1} << (rng() % slots);
        takes[j] = (matches[j] != 0) & (rng() & 1);
      }
      for (size_t lo : {0u, 3u, 8u, 17u, 60u}) {
        for (size_t hi : {lo + 1, lo + 2, lo + 7, lo + 8, lo + 9, size_t{64}}) {
          if (hi <= lo || hi > 64) continue;
          bs::Aligned64Ptr sliced = bs::AllocateAligned64(value_lines * 64);
          bs::Aligned64Ptr ref = bs::AllocateAligned64(value_lines * 64);
          for (size_t i = 0; i < value_lines * 64; ++i) ref[i] = sliced[i] = Byte();
          if (narrow) {
            bs::ExtractHashedWaveIntoSliced<true>(buckets, matches, takes, lo, hi,
                layout.key_bytes, value_lines, slots, sliced.get());
          } else {
            bs::ExtractHashedWaveIntoSliced<false>(buckets, matches, takes, lo, hi,
                layout.key_bytes, value_lines, slots, sliced.get());
          }
          uint64_t sink = 0;
          for (size_t j = lo; j < hi; ++j) {
            uint8_t* bucket = const_cast<uint8_t*>(buckets[j]);
            if (narrow) {
              // The byte the kernel must place, straight from the layout:
              // value line v of lane j starts `key_bytes` lines in, at the
              // narrow stride, and the matched slot indexes within the line.
              const unsigned slot =
                  static_cast<unsigned>(_tzcnt_u64(matches[j]) & 63u);
              const uint8_t* value_lines_at = bucket + layout.key_bytes * stride;
              for (size_t v = 0; v < value_lines; ++v)
                extract[v] = value_lines_at[v * stride + slot];
            } else {
              bs::ExtractValueAndClearRealMaskByteSlicedPermute<false>(
                  bucket, &sink, layout, matches[j], extract);
            }
            if (takes[j]) for (size_t v = 0; v < value_lines; ++v) ref[v * 64 + j] = extract[v];
          }
          for (size_t v = 0; v < value_lines; ++v)
            for (size_t j = 0; j < 64; ++j)
              Expect(sliced[v * 64 + j] == ref[v * 64 + j], "place-at-lane byte");
        }
      }
    }
  }
  std::puts("  place at lane ok");
}

}  // namespace

int main() {
  TestMerges();
  TestPlaceAtLane();
  std::puts("cpu_byteslice_batch_layout_test passed");
}
