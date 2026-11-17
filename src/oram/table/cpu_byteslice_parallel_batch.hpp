#pragma once

// Parallel online batches: one batch of up to kMaxCombinedBatchLanes requests
// is split into contiguous tiles of at most 64 lanes, one per participant (the
// caller plus up to seven helper threads), all against one probe-plan
// snapshot.  Deduplication and forwarding (cpu_byteslice_batch_probe.hpp) must
// still see the whole batch: a repeated key in a later tile is a duplicate of
// the earlier tile's lane, and its answer is the state that lane left.  These
// are the thread-independent primitives that extend those relations across
// tiles: prepare all input banks, compute each owner's metadata, publish all
// probe banks, then forward owners in ANY order. Banks
// are immutable across readers; destinations belong exclusively to the owner.
// All memory indices and loop bounds below are public. Secret source indices
// drive register permutations only. Neither CD nor VP2INTERSECT is required.

#include <algorithm>
#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include "src/oram/table/cpu_byteslice_batch_config.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"

namespace microram {
namespace byteslice {

// Padded source encoding, NEVER a request ordinal when local width < 64.
inline constexpr uint16_t kNoParallelBatchSource = kMaxCombinedBatchLanes;

// Contiguous public ownership, with at most one item of imbalance. Padded
// source identities remain 64*t+j; Offset is the actual request ordinal.
struct BatchPartition {
  size_t items;
  size_t owners;
  size_t Count(size_t t) const {
    return items / owners + static_cast<size_t>(t < items % owners);
  }
  size_t Offset(size_t t) const {
    return t * (items / owners) + std::min(t, items % owners);
  }
};

struct alignas(64) ParallelBatchBanks {
  alignas(64) uint64_t key_lo[kMaxBatchLanes] = {};
  alignas(64) uint64_t key_hi[kMaxBatchLanes] = {};
  size_t lanes = 0;  // public active lanes in this tile
  size_t value_bytes = 0;
  // Public operation masks: writes/erases/inserting exchanges set presence;
  // writes and BOTH exchange forms supply values.
  uint64_t presence_setters = 0, sets_present = 0, value_suppliers = 0;
  Aligned64Ptr proposed;  // value_bytes full 64-byte lines
  Aligned64Ptr probe;     // value_bytes lines, meta line, raw found line

  void Resize(size_t bytes) {
    value_bytes = bytes;
    const size_t proposed_bytes =
        CheckedSizeMul(bytes, kMaxBatchLanes, "proposed bytes");
    const size_t probe_bytes = CheckedSizeMul(
        CheckedSizeAdd(bytes, 2, "probe lines"), kMaxBatchLanes, "probe bytes");
    proposed = AllocateAligned64(proposed_bytes);
    probe = AllocateAligned64(probe_bytes);
    std::memset(proposed.get(), 0, proposed_bytes);
    std::memset(probe.get(), 0, probe_bytes);
  }
  const uint8_t* ProposedLine(size_t v) const {
    return proposed.get() + v * kMaxBatchLanes;
  }
  const uint8_t* ProbeLine(size_t v) const {
    return probe.get() + v * kMaxBatchLanes;
  }
};

struct alignas(64) ParallelBatchMetadata {
  uint16_t representative[kMaxBatchLanes] = {};
  uint16_t presence_source[kMaxBatchLanes] = {};
  uint16_t value_source[kMaxBatchLanes] = {};
  uint64_t duplicates = 0, superseded = 0;
  uint64_t has_presence_setter = 0, sets_present = 0, has_value_supplier = 0;
  // Some EARLIER lane of the job holds this lane's key and makes it present (a
  // write or an inserting exchange).  After such a lane the key has had a live
  // copy, so no later tombstone of it is unshadowed -- the serial rule, which
  // the last setter alone cannot tell once an erase has followed the write.
  uint64_t earlier_sets_present = 0;
};

struct alignas(64) ParallelBatchResults {
  Aligned64Ptr previous_rows, insert_rows;
  size_t value_bytes = 0, row_stride = 0;
  uint64_t present = 0, erased = 0, original_probe_found = 0, unshadowed = 0;

  void Resize(size_t bytes) {
    value_bytes = bytes;
    row_stride = CheckedSizeAdd(bytes, 64, "result stride") & ~size_t{63};
    const size_t allocation =
        CheckedSizeMul(kMaxBatchLanes, row_stride, "result rows");
    previous_rows = AllocateAligned64(allocation);
    insert_rows = AllocateAligned64(allocation);
    std::memset(previous_rows.get(), 0, allocation);
    std::memset(insert_rows.get(), 0, allocation);
  }
  uint8_t* PreviousRow(size_t j) { return previous_rows.get() + j * row_stride; }
  uint8_t* InsertRow(size_t j) { return insert_rows.get() + j * row_stride; }
};

// Normalized keys and proposed inputs are snapshotted before any output copy.
// Public opcodes govern input loads: read/erase lanes may have null inputs.
// Clear padding on EVERY job, including when a former full tile becomes a tail.
inline void PrepareParallelBatchInputs(
    const KeyWords* keys, const BatchOp* ops, const uint8_t* insert,
    const uint8_t* const* inputs, size_t lanes, ParallelBatchBanks& bank) {
  assert(lanes <= kMaxBatchLanes);
  bank.lanes = lanes;
  bank.presence_setters = bank.sets_present = bank.value_suppliers = 0;
  std::memset(bank.key_lo, 0, sizeof(bank.key_lo));
  std::memset(bank.key_hi, 0, sizeof(bank.key_hi));
  std::memset(bank.proposed.get(), 0, bank.value_bytes * kMaxBatchLanes);
  for (size_t j = 0; j < lanes; ++j) {
    bank.key_lo[j] = keys[j].w0;
    bank.key_hi[j] = keys[j].w1;
    const bool write = ops[j] == BatchOp::kWrite ||
                       ops[j] == BatchOp::kReadThenWrite;
    const bool supplier = write || ops[j] == BatchOp::kExchange;
    const bool present = write ||
                        (ops[j] == BatchOp::kExchange && insert[j] != 0);
    bank.presence_setters |= uint64_t{present || ops[j] == BatchOp::kErase} << j;
    bank.sets_present |= uint64_t{present} << j;
    bank.value_suppliers |= uint64_t{supplier} << j;
    if (supplier) {
      for (size_t v = 0; v < bank.value_bytes; ++v) {
        bank.proposed.get()[v * kMaxBatchLanes + j] = inputs[j][v];
      }
    }
  }
}

inline void PublishParallelBatchProbe(const uint8_t* rows, size_t row_stride,
                                      const uint64_t* found,
                                      ParallelBatchBanks& bank) {
  assert(row_stride >= bank.value_bytes + 1);
  std::memset(bank.probe.get(), 0, (bank.value_bytes + 2) * kMaxBatchLanes);
  for (size_t j = 0; j < bank.lanes; ++j) {
    for (size_t v = 0; v <= bank.value_bytes; ++v) {
      bank.probe.get()[v * kMaxBatchLanes + j] = rows[j * row_stride + v];
    }
    bank.probe.get()[(bank.value_bytes + 1) * kMaxBatchLanes + j] =
        static_cast<uint8_t>(found[j] & 1u);
  }
}

// Each destination scans EVERY active tile and public eight-key group, even
// after finding a representative/setter/supplier. No updates to other owners.
inline void BuildParallelBatchMetadata(
    const ParallelBatchBanks* const* banks, size_t participants,
    size_t destination, size_t key_bytes, ParallelBatchMetadata& out) {
  assert(participants >= 1 && participants <= kMaxOnlineParticipants);
  // Encoder-produced keys are zero-extended above their width: 1..8 bytes in
  // key_lo alone, 9..16 in key_lo and key_hi.
  assert(destination < participants && key_bytes >= 1 &&
         key_bytes <= kMaxKeyBytes);
  const bool wide = key_bytes > 8;
  out = ParallelBatchMetadata{};
  const ParallelBatchBanks& own = *banks[destination];
  for (size_t base = 0; base < own.lanes; base += 8) {
    const size_t count = std::min(size_t{8}, own.lanes - base);
    // Reuse each source load for eight destination lanes. The relation panel
    // is private stack scratch, indexed only by public row/tile numbers.
    // Short tails retain the broadcast loop, avoiding panel setup overhead.
    uint64_t equality[8][kMaxOnlineParticipants];
    if (count == 8) {
      std::memset(equality, 0, sizeof(equality));
      for (size_t t = 0; t < participants; ++t) {
        const auto& source = *banks[t];
        for (size_t g = 0; g < (source.lanes + 7) / 8; ++g) {
          const __m512i lo = _mm512_load_si512(source.key_lo + 8 * g);
          const __m512i hi = wide
              ? _mm512_load_si512(source.key_hi + 8 * g) : _mm512_setzero_si512();
          for (size_t r = 0; r < count; ++r) {
            uint64_t bits = core::obliCmpEqMask64(
                lo, _mm512_set1_epi64(static_cast<long long>(own.key_lo[base + r])));
            if (wide)
              bits &= core::obliCmpEqMask64(hi,
                  _mm512_set1_epi64(static_cast<long long>(own.key_hi[base + r])));
            equality[r][t] |= bits << (8 * g);
          }
        }
      }
    }
    for (size_t r = 0; r < count; ++r) {
      const size_t j = base + r;
      uint64_t representative = destination * kMaxBatchLanes + j;
      uint64_t setter = kNoParallelBatchSource, supplier = kNoParallelBatchSource;
      uint64_t setter_present = 0, duplicate = 0, superseded = 0;
      uint64_t earlier_present = 0;
      for (size_t t = 0; t < participants; ++t) {
        const ParallelBatchBanks& source = *banks[t];
        uint64_t equal = 0;
        if (count == 8) {
          equal = equality[r][t];
        } else {
          const __m512i lo = _mm512_set1_epi64(static_cast<long long>(own.key_lo[j]));
          const __m512i hi = _mm512_set1_epi64(static_cast<long long>(own.key_hi[j]));
          for (size_t g = 0; g < (source.lanes + 7) / 8; ++g) {
            uint64_t bits = core::obliCmpEqMask64(
                _mm512_load_si512(source.key_lo + 8 * g), lo);
            if (wide)
              bits &= core::obliCmpEqMask64(
                  _mm512_load_si512(source.key_hi + 8 * g), hi);
            equal |= bits << (8 * g);
          }
        }
        equal &= LowMask64(static_cast<unsigned>(source.lanes));
        // Tile order is request order even for L < 64. Only the public relative
        // tile number selects the local earlier/later masks.
        const uint64_t earlier = equal & (t < destination ? ~uint64_t{0} :
            t == destination ? LowMask64(static_cast<unsigned>(j)) : 0);
        const uint64_t later = equal & (t > destination ? ~uint64_t{0} :
            t == destination ? ~LowMask64(static_cast<unsigned>(j + 1)) : 0);
        duplicate |= static_cast<uint64_t>(earlier != 0);
        superseded |= static_cast<uint64_t>(later != 0);
        earlier_present |=
            static_cast<uint64_t>((earlier & source.sets_present) != 0);
        const uint64_t first = t * kMaxBatchLanes + _tzcnt_u64(earlier);
        representative = core::obliSelectU64(
            representative, first, (earlier != 0) & (first < representative));

        const uint64_t setters = earlier & source.presence_setters;
        const uint64_t suppliers = earlier & source.value_suppliers;
        // Mask the index even on the no-match path: lzcnt(0)=64, and a C++
        // shift by the resulting -1 would be undefined before the CMOV.
        const uint64_t setter_lane = (63u - _lzcnt_u64(setters)) & 63u;
        const uint64_t supplier_lane = (63u - _lzcnt_u64(suppliers)) & 63u;
        setter = core::obliSelectU64(setter, t * kMaxBatchLanes + setter_lane,
                                     setters != 0);
        supplier = core::obliSelectU64(supplier, t * kMaxBatchLanes + supplier_lane,
                                       suppliers != 0);
        setter_present = core::obliSelectU64(
            setter_present, (source.sets_present >> setter_lane) & 1u, setters != 0);
      }
      out.representative[j] = static_cast<uint16_t>(representative);
      out.presence_source[j] = static_cast<uint16_t>(setter);
      out.value_source[j] = static_cast<uint16_t>(supplier);
      out.duplicates |= duplicate << j;
      out.superseded |= superseded << j;
      out.has_presence_setter |= uint64_t{setter != kNoParallelBatchSource} << j;
      out.sets_present |= setter_present << j;
      out.has_value_supplier |= uint64_t{supplier != kNoParallelBatchSource} << j;
      out.earlier_sets_present |= earlier_present << j;
    }
  }
}

// One independent full-tile propagation. Secret tile numbers are compared
// against the public loop variable, never used to choose a memory address.
// Loads and blended stores are pinned to prohibit masked-memory fusion.
inline void ForwardParallelBatchTile(
    const ParallelBatchBanks* const* banks, size_t participants,
    size_t destination, const ParallelBatchMetadata& metadata,
    ParallelBatchResults& out) {
  assert(participants >= 1 && participants <= kMaxOnlineParticipants);
  assert(destination < participants);
  const ParallelBatchBanks& own = *banks[destination];
  assert(out.value_bytes == own.value_bytes);
  alignas(64) uint8_t rep_lane[kMaxBatchLanes], rep_tile[kMaxBatchLanes];
  alignas(64) uint8_t input_lane[kMaxBatchLanes], input_tile[kMaxBatchLanes];
  for (size_t j = 0; j < kMaxBatchLanes; ++j) {
    rep_lane[j] = static_cast<uint8_t>(metadata.representative[j] & 63u);
    rep_tile[j] = static_cast<uint8_t>(metadata.representative[j] >> 6);
    input_lane[j] = static_cast<uint8_t>(metadata.value_source[j] & 63u);
    input_tile[j] = static_cast<uint8_t>(metadata.value_source[j] >> 6);
  }
  const __m512i rep_indices = core::obliLoad512(rep_lane);
  const __m512i rep_tiles = core::obliLoad512(rep_tile);
  const __m512i input_indices = core::obliLoad512(input_lane);
  const __m512i input_tiles = core::obliLoad512(input_tile);
  const uint64_t active = LowMask64(static_cast<unsigned>(own.lanes));
  __m512i found = _mm512_setzero_si512(), meta = _mm512_setzero_si512();
  // Precompute the register masks once for all value lines. Their array
  // indices are public source tiles; the arrays themselves contain secrets.
  std::array<__mmask64, kMaxOnlineParticipants> probe_take{}, input_take{};
  for (size_t t = 0; t < participants; ++t) {
    const ParallelBatchBanks& source = *banks[t];
    assert(source.value_bytes == own.value_bytes);
    const __m512i tile = _mm512_set1_epi8(static_cast<char>(t));
    const __mmask64 rep_take = core::obliCmpEqMask8(rep_tiles, tile);
    probe_take[t] = rep_take & ~metadata.has_value_supplier;
    input_take[t] = core::obliCmpEqMask8(input_tiles, tile) &
                    metadata.has_value_supplier;
    const __m512i found_line = core::obliLoad512(source.ProbeLine(own.value_bytes + 1));
    const __m512i meta_line = core::obliLoad512(source.ProbeLine(own.value_bytes));
    found = _mm512_mask_mov_epi8(found, rep_take,
        _mm512_permutexvar_epi8(rep_indices, found_line));
    meta = _mm512_mask_mov_epi8(meta, rep_take,
        _mm512_permutexvar_epi8(rep_indices, meta_line));
  }
  const uint64_t raw_found = core::obliTestMask8(found, _mm512_set1_epi8(1));
  const uint64_t probe_erased = core::obliTestMask8(
      meta, _mm512_set1_epi8(static_cast<char>(kMetaErased)));
  const uint64_t probe_unshadowed = core::obliTestMask8(
      meta, _mm512_set1_epi8(static_cast<char>(kMetaUnshadowed)));
  const uint64_t present = ((raw_found & ~probe_erased & ~metadata.has_presence_setter) |
      (metadata.sets_present & metadata.has_presence_setter)) & active;
  const uint64_t after = ((present & ~own.presence_setters) | own.sets_present) & active;
  out.present = present;
  out.erased = ~after & active;
  // The representative's original physical found bit, distinct from logical
  // presence.
  out.original_probe_found = raw_found & active;
  // The qualifier the serial chain gives the lane's tombstone
  // (ForwardBatchLane): the key's state before the job was no copy or an
  // unshadowed tombstone -- the REPRESENTATIVE's probe, which every lane of
  // the key reads -- and no earlier lane of the job made it present.  A read,
  // an erase or a non-inserting exchange between keeps the qualifier, as
  // serially.
  out.unshadowed = out.erased & ~metadata.earlier_sets_present &
                   (~raw_found | (probe_erased & probe_unshadowed));

  // Every consumed value byte and insertion meta byte is written below.
  // Padding and inactive rows are not inputs to forwarding or commit.
  alignas(64) uint8_t previous[kMaxBatchLanes], inserted[kMaxBatchLanes];
  for (size_t v = 0; v < own.value_bytes; ++v) {
    __m512i before = _mm512_setzero_si512();
    for (size_t t = 0; t < participants; ++t) {
      const ParallelBatchBanks& source = *banks[t];
      // Both banks are read at EVERY public source tile even if no lane
      // selects it, or all lanes select the other kind of source.
      const __m512i probe = core::obliLoad512(source.ProbeLine(v));
      const __m512i proposed = core::obliLoad512(source.ProposedLine(v));
      before = _mm512_mask_mov_epi8(before, probe_take[t],
          _mm512_permutexvar_epi8(rep_indices, probe));
      before = _mm512_mask_mov_epi8(before, input_take[t],
          _mm512_permutexvar_epi8(input_indices, proposed));
    }
    before = _mm512_maskz_mov_epi8(present, before);
    __m512i outgoing = _mm512_mask_mov_epi8(
        before, own.value_suppliers, core::obliLoad512(own.ProposedLine(v)));
    outgoing = _mm512_maskz_mov_epi8(after, outgoing);
    _mm512_store_si512(previous, core::obliPin512(before));
    _mm512_store_si512(inserted, core::obliPin512(outgoing));
    for (size_t j = 0; j < own.lanes; ++j) {
      out.PreviousRow(j)[v] = previous[j];
      out.InsertRow(j)[v] = inserted[j];
    }
  }
  for (size_t j = 0; j < own.lanes; ++j) {
    out.InsertRow(j)[own.value_bytes] = static_cast<uint8_t>(
        (0u - static_cast<unsigned>((out.erased >> j) & 1u)) & kMetaErased);
  }
}

}  // namespace byteslice
}  // namespace microram
