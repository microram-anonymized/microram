#pragma once

// Where one access's probes land: the publication-time addressing block, the
// per-access scratch it fills, and the vectorized pass between them.
//
// Every probe path (one access, a batch, the value workers) resolves probe
// addresses the same way, and the reason is not a coincidence of
// implementation: a cascade's cost is the load-to-load round
// trip
//
//     table i's key lines -> match -> found -> table i+1's address
//
// so the AES and the mixed-radix index arithmetic must not sit on it.  They are
// hoisted into ONE pass that runs before the cascade and resolves BOTH
// candidates of every hashed table -- the real bucket (this key under the
// table's routing nonce) and the dummy one (a never-repeating counter under the
// table's domain-separated dummy nonce).  The cascade then CMOVs between two
// pointers it already holds and touches exactly one of them, so the observable
// trace is unchanged; computing both unconditionally is also what keeps the
// work independent of whether the key has been found yet.
//
// THE ADDRESSING BLOCK IS PUBLIC.  Every field of ProbeAddressing is a function
// of the schedule alone -- table bases, index-map shapes and packed nonce words
// -- so it is built once when the set of live tables changes and is read, never
// written, per access.
//
// TWO STRAIGHT-LINE LOOPS, NOT A SWITCH PER CANDIDATE.  `hashed_pow2` holds the
// tables whose bucket count is a power of two (radix 1: every table of a
// fanout-2 level) and `hashed_mixed` the mixed-radix ones; each gets its own
// loop, so neither carries a branch the other's shape would need.
// `hashed_mixed` is empty when every level has fanout 2, and its loop does not
// run.
//
// THE AES BLOCKS ARE ASSEMBLED A WHOLE ZMM AT A TIME.  The candidate blocks of
// an access are `(aes_index + BP) ^ aes_template` lane for lane, where BP
// contains [0, 0, key.w0, key.w1, 0, 0, dummy_base, 0]. The template holds
// each table's real and dummy identity/label blocks at 8j and 8j+4; the index
// holds its dummy-counter offset at 8j+6. One add, xor and store assembles the
// two complete CBC messages for each table. All inputs remain public except
// for the stored key, whose bytes never select an address here.

#include <immintrin.h>

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"
#include "src/oram/table/cpu_byteslice_tags.hpp"

namespace microram {
namespace byteslice {

// What the per-access address pass needs of one hashed table, flattened at
// publication so the pass reads a 32-byte record instead of striding through a
// plan entry: the two bases, the index map's public shape, and where the
// candidate pair lands in the probe scratch.  `slot` is the table's position
// among the hashed tables, i.e. which AES block pair is its own; `table` is its
// position in the CASCADE, i.e. which candidate pair it writes.
//
// `data`/`masks` are the TABLE's own bases, not an arena's: a level that lives
// at an offset inside a shared arena folds that offset in here, once per
// publication, rather than adding it to both candidates on every access.
struct HashedProbeGeometry {
  uint8_t* data = nullptr;
  uint64_t* masks = nullptr;
  uint32_t table = 0;
  uint32_t slot = 0;
  unsigned index_bits = 0;
  unsigned radix = 1;
};

// The publication-time addressing block.  Filled by AddHashed in cascade order
// and closed by Finish; read by the per-access pass alone.
struct ProbeAddressing {
  std::vector<uint64_t> aes_template;
  std::vector<uint64_t> aes_index;
  std::vector<HashedProbeGeometry> hashed_pow2;
  std::vector<HashedProbeGeometry> hashed_mixed;
  size_t hashed = 0;  // hashed tables added so far, i.e. the next `slot`

  void Clear() {
    aes_template.clear();
    aes_index.clear();
    hashed_pow2.clear();
    hashed_mixed.clear();
    hashed = 0;
  }

  // Capacity for `tables` hashed tables, so that neither AddHashed nor Finish
  // allocates.  Clear() keeps it, which is what makes a recycled plan free.
  void Reserve(size_t tables) {
    aes_template.reserve(8 * tables + 16);
    aes_index.reserve(8 * tables + 16);
    hashed_pow2.reserve(tables);
    hashed_mixed.reserve(tables);
  }

  // What Reserve above asks for, for a caller that has to report the size of
  // a pool of these rather than allocate one.  Beside Reserve so the two
  // cannot drift.
  static size_t ReservedBytes(size_t tables) {
    return 2 * (8 * tables + 16) * sizeof(uint64_t) +
           2 * tables * sizeof(HashedProbeGeometry);
  }

  // Opens a block for exactly `hashed_tables` hashed tables: sizes the two word
  // arrays to whole zmm registers and zeroes them, so that AddHashed only
  // stores and the padding lanes are already the zeros the AES batch expects.
  // Whole zmm is what lets the per-access assembly run eight lanes at a time
  // with no tail.
  //
  // The count is public and both engines have it before they enumerate, which
  // is the point: growing the arrays per table instead costs a resize apiece on
  // the publication path, which is the request thread's.
  void Begin(size_t hashed_tables) {
    hashed = 0;
    const size_t words = ((2 * hashed_tables + 3) / 4) * 16;
    aes_template.assign(words, 0);
    aes_index.assign(words, 0);
    hashed_pow2.clear();
    hashed_mixed.clear();
  }

  // One hashed table, in cascade order, after Begin.  `table` is its cascade
  // position and `dummy_offset` the amount added to the access's dummy_base to
  // get this table's never-repeating counter.  The two hierarchies number their
  // dummies differently and both re-derive the counter in the cascade, so this
  // is the one place the two spellings have to agree.
  void AddHashed(uint32_t table, uint8_t* data, uint64_t* masks,
                 unsigned index_bits, unsigned radix, uint64_t real_high,
                 uint64_t dummy_high, uint64_t dummy_offset) {
    const size_t j = hashed++;
    assert(8 * hashed <= aes_template.size());
    aes_template[8 * j] = real_high;
    aes_template[8 * j + 1] = crypto::kAesRoutingLabel;
    aes_template[8 * j + 4] = dummy_high;
    aes_template[8 * j + 5] = crypto::kAesRoutingLabel;
    aes_index[8 * j + 6] = dummy_offset;
    HashedProbeGeometry g;
    g.data = data;
    g.masks = masks;
    g.table = table;
    g.slot = static_cast<uint32_t>(j);
    g.index_bits = index_bits;
    g.radix = radix;
    (radix == 1 ? hashed_pow2 : hashed_mixed).push_back(g);
  }
};

// The per-access scratch the pass writes and the cascade reads.  `bucket` and
// `mask` hold the [real, dummy] candidate pair of cascade entry i at 2i and
// 2i+1; the cascade CMOVs between them and touches exactly one.
// `Alloc` is std::allocator except for the online value workers' copies
// (LineAllocator), which another thread's critical path must not share.
template <template <class> class Alloc = std::allocator>
struct BasicProbeScratch {
  std::vector<uint64_t, Alloc<uint64_t>> blocks;  // four qwords per CBC message
  std::vector<uint64_t, Alloc<uint64_t>> tags;
  std::vector<uint8_t*, Alloc<uint8_t*>> bucket;
  std::vector<uint64_t*, Alloc<uint64_t*>> mask;

  // `tables` is the longest cascade and `hashed_tables` the most hashed tables
  // in one; both are public, and both are sized for the worst case a run can
  // reach so that a plan change never reallocates on the access path.
  void Resize(size_t tables, size_t hashed_tables) {
    const size_t aes_blocks = AesBlocks(hashed_tables);
    blocks.assign(4 * aes_blocks, 0);
    tags.assign(aes_blocks, 0);
    bucket.assign(2 * tables, nullptr);
    mask.assign(2 * tables, nullptr);
  }

  // Logical extents, kept beside Resize for both ordinary and line allocators.
  static std::array<size_t, 4> BufferSizes(size_t tables, size_t hashed_tables) {
    const size_t aes_blocks = AesBlocks(hashed_tables);
    return {4 * aes_blocks * sizeof(uint64_t), aes_blocks * sizeof(uint64_t),
            2 * tables * sizeof(uint8_t*), 2 * tables * sizeof(uint64_t*)};
  }
  static size_t Bytes(size_t tables, size_t hashed_tables) {
    size_t bytes = 0;
    for (size_t n : BufferSizes(tables, hashed_tables)) bytes += n;
    return bytes;
  }

 private:
  // The AES batch runs whole zmm registers, so the block count is rounded to
  // four whatever the cascade's shape.
  static size_t AesBlocks(size_t hashed_tables) {
    return (2 * hashed_tables + 3) & ~size_t{3};
  }
};
using ProbeScratch = BasicProbeScratch<>;

// The address pass: assemble the candidate AES blocks, hash them all in one
// batch, and apply each table's index map to both halves.
//
// Nothing here is on the cascade's critical path, and nothing here branches on
// the key: the loops are over a public plan, the AES batch has a fixed length,
// and both candidates of every table are resolved whether or not the cascade
// will choose them.
// INLINE (always_inline), not merely inline: this is the whole prologue of an
// access, its one call site per engine is a member function that is itself
// inlined into the cascade, and a real call here costs a vzeroupper plus the
// zmm and k spills the Win64 ABI clobbers across it -- the trap the cascade
// kernels in cpu_byteslice_probe.hpp also record.
template <bool MaterializeMasks = true, class Scratch>
INLINE void ResolveHashedProbeAddresses(const ProbeAddressing& a, KeyWords key,
                                        uint64_t dummy_base,
                                        size_t bucket_bytes,
                                        const AesTagKeys& aes_keys,
                                        Scratch& out) {
  const size_t h = a.hashed;
  if (h == 0) return;
  // Each candidate contains the labeled identity block and a full key block.
  // Dummy messages use (counter, 0) in the separate dummy identity domain.
  {
    const __m512i bp = _mm512_set_epi64(
        0, static_cast<long long>(dummy_base), 0, 0,
        static_cast<long long>(key.w1), static_cast<long long>(key.w0), 0, 0);
    const uint64_t* const tmpl = a.aes_template.data();
    const uint64_t* const idx = a.aes_index.data();
    uint64_t* const blocks = out.blocks.data();
    const size_t words = a.aes_template.size();  // a multiple of eight
    for (size_t w = 0; w < words; w += 8) {
      const __m512i v = _mm512_add_epi64(
          _mm512_loadu_si512(reinterpret_cast<const void*>(idx + w)), bp);
      _mm512_storeu_si512(
          reinterpret_cast<void*>(blocks + w),
          _mm512_xor_si512(
              v, _mm512_loadu_si512(reinterpret_cast<const void*>(tmpl + w))));
    }
  }
  AesTagsInterleaved(out.blocks.data(), 2 * h, out.tags.data(), aes_keys);
  // The index maps, one straight-line loop per map kind over the flattened
  // geometry.  A power-of-two table is the plain mask; ModSmallOdd(v, 1) == 0
  // made it so before too, through a switch per candidate.
  for (const HashedProbeGeometry& g : a.hashed_pow2) {
    const uint64_t low = LowMask64(g.index_bits);
    for (unsigned half = 0; half < 2; ++half) {
      const size_t b = static_cast<size_t>(out.tags[2 * g.slot + half] & low);
      out.bucket[2 * g.table + half] = g.data + b * bucket_bytes;
      if constexpr (MaterializeMasks) out.mask[2 * g.table + half] = g.masks + b;
    }
  }
  for (const HashedProbeGeometry& g : a.hashed_mixed) {
    for (unsigned half = 0; half < 2; ++half) {
      const uint64_t tag = out.tags[2 * g.slot + half];
      const size_t b = static_cast<size_t>(
          ApplyRadixIndexMap(tag, g.index_bits, g.radix, g.index_bits));
      out.bucket[2 * g.table + half] = g.data + b * bucket_bytes;
      if constexpr (MaterializeMasks) out.mask[2 * g.table + half] = g.masks + b;
    }
  }
}

// One cascade entry's chosen candidate, selected without branching on the
// secret `use_dummy`.  Both pointers are already in the scratch, so this is two
// CMOVs and nothing is recomputed.
struct ProbeTarget {
  uint8_t* bucket = nullptr;
  uint64_t* mask = nullptr;
};

INLINE ProbeTarget SelectProbeTarget(const ProbeScratch& s, size_t table,
                                     bool use_dummy) {
  ProbeTarget t;
  t.bucket = reinterpret_cast<uint8_t*>(core::obliSelectU64(
      reinterpret_cast<uintptr_t>(s.bucket[2 * table]),
      reinterpret_cast<uintptr_t>(s.bucket[2 * table + 1]), use_dummy));
  t.mask = reinterpret_cast<uint64_t*>(core::obliSelectU64(
      reinterpret_cast<uintptr_t>(s.mask[2 * table]),
      reinterpret_cast<uintptr_t>(s.mask[2 * table + 1]), use_dummy));
  return t;
}

}  // namespace byteslice
}  // namespace microram
