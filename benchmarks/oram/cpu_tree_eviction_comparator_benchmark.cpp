// The tree ORAM's eviction against EnigMap's oblivious Path ORAM eviction,
// in isolation.
//
// One EVICTION PASS = the plan plus the payload movement on one working set
// of the read-path engine (cpu_tree_read_path_oram.hpp): 64 A stash lanes
// and the path's 64 lanes, by (16 metadata byte lines + V payload byte
// lines).  The access reads the path, takes the target out and evicts along
// the same path, so a pass is the whole of an access's eviction.  Every arm
// produces a valid placement of the same entries and is timed on one core.
//
// THE GEOMETRY is the engine's for the capacity: Z = 4, binary, and the
// default rule's fold and stash registers (TreeGeometry::ForCapacity), or an
// explicit --fold / --stash-registers within the library's limits.  The
// path must fit one register (P <= 16): the arms model the one-register
// path, and a two-register geometry is refused.  The working set is the 64 A
// stash lanes (lane l at byte l of a stash line of 64 A bytes,
// TreeStorage::StashLine) and then the 64 path lanes, LEAF FIRST (position m
// in lanes 4m..4m+3).
//
//   read_path    the library's PlanReadPath<A, 1> on the metadata lines and
//                its data pass: RouteReadPathLine's body for one path
//                register, replicated so the stash is read from the working
//                set and written to Out (the engine routes it in place; the
//                instructions per line are the same).  value_in is null and
//                value_out a scratch buffer, so every value line gathers the
//                accessed entry's byte; the access lands it (found, or
//                created on the absent-target kind) in the lowest free stash
//                lane.  Checked against ReferenceReadPathEvict: every path
//                destination's source or dummy, every stash lane kept or
//                emptied, the landing lane, the gathered value, and the
//                found / leftover-count / overflow flags.
//   read_path_transposed
//                the read path with the path's transposition charged: what
//                one engine access does to the working set, minus the bucket
//                addresses and the position map.  The path is in the
//                engine's STORED BUCKET LAYOUT (src/oram/tree/DESIGN.md,
//                "Storage formats"): one contiguous buffer of the P buckets,
//                leaf-first position m at m x 64 C bytes (TreeStorage's
//                bucket stride), C = ceil((16 + V) / 16) chunks of 64 B,
//                byte k of slot z at offset 4k + z, the last chunk's
//                columns past 16 + V padding.  The stash stays in byte lines
//                as in read_path.  The pass is ReadPathPlane's synchronous
//                one-register pass (cpu_tree_read_path_oram.hpp) built from
//                the free functions its members call: BeginPass's prefetch
//                of each bucket's first chunks (the one loop replicated
//                here: in BeginPass it follows the address computation);
//                chunk 0, the metadata exactly, loaded and transposed in a
//                tile (LoadChunkInto, TransposeToLines4Exact<P>);
//                PlanReadPath<A, 1> on the tile and the stash; the metadata
//                lines routed in the tile (RouteReadPathLine<A, 1, true>),
//                transposed back and stored (TransposeToChunks4Exact<P>,
//                StoreChunkFrom); then each value chunk as RunValueChunk<A,
//                P, 0> runs it: LoadChunkInto with the prefetch
//                TreeKnobs::prefetch_ahead chunks ahead,
//                TransposeGroupForwardExact<P>, RouteReadPathLine<A, 1,
//                false> per byte line (routing, gather, landing),
//                WriteValueBytes, TransposeGroupInverseExact<P>,
//                StoreChunkFrom.  value_in null, value_out scratch, as in
//                read_path.  IN PLACE, as the engine: the path is stored
//                back where it was loaded and the stash routed where it is,
//                on the arm's own copy of each working set (built outside
//                the timer, so the other arms' inputs are untouched).  A
//                timed pass therefore sees its set's previous pass's output,
//                an access to the same leaf again.  No branch or address
//                depends on that, and the stash cannot fill up: path entries
//                never move to it, and the accessed entry it gains is found
//                there by the set's next pass (a created one included), so
//                it holds at most one entry more than the set's input.
//                Checked as read_path, after a scalar loop over the layout's
//                definition (not the engine's network) turns the output path
//                back into byte lines; the input path is built the same way.
//   enigmap      (only in cpu_tree_eviction_comparator_benchmark_enigmap,
//                built with MICRORAM_ENIGMAP_ARM and an EnigMap checkout from
//                benchmarks/baselines/fetch_enigmap.sh) EnigMap's oblivious
//                Path ORAM eviction, EvictPath in ods/oram/pathoram/oram.hpp
//                at odslib/EnigMap 4d0bfdb, on the same 64 A stash lanes and
//                Z x P path slots.  Entries are EnigMap's own element type,
//                TaggedT<StashedBlock<Block<payload>>>, in a std::vector, as
//                its stash keeps them.  Steps 1-6 are EvictPath's code with
//                its constants (Z, L) taken from our geometry: tag every
//                entry with the deepest level it may reach, ObliSort (its
//                recursive bitonic sort; every compare-exchange moves whole
//                entries), count each level, ObliSort again, pad each level
//                to Z with dummies, ObliSort a third time; then step 7 copies
//                v[0, Z P) to the path slots and every later entry to the
//                stash (lanes 1..64A-1, then an extended area: EnigMap's
//                stash holds Z (L+1) + 80 entries and keeps step 5's padding
//                entries in it).  The target is taken out first by the scan
//                of EnigMap's ReadBlockFromStash and leaves the eviction as a
//                purged entry (lane 0).  Changes, all in EnigMap's favour:
//                the tag is a branch-free prefix compare against our
//                per-level eligibility (EnigMap's GetDeepestShallowness loops
//                until the paths meet), the vector is reserved once (EnigMap
//                grows it by push_back), the compare-exchange of an entry is
//                EnigMap's obliSwap (one AVX blend pass; its generic CXCHG
//                copies the entry and does two CMOVs), and the payload's
//                CMOV, which EnigMap leaves to the block type, blends 64
//                bytes at a time.  One correctness patch: the sort
//                comparators' missing parentheses (see step 2), without which
//                a full stash and path keep entries greedy eviction would
//                place.  The placement is a valid greedy eviction but not the
//                read path's lane order (the sorts are not stable), so it is
//                checked by validity: every real entry exactly once, bytes
//                intact, each path entry eligible for its bucket, and the
//                same found / leftover-count / overflow flags as
//                ReferenceReadPathEvict (the leftover count of any maximal
//                greedy is the read path's).
//
// The read_path arms are oblivious in the library's sense: no branch or
// address depends on a position, uid or occupancy; compares and
// secret-masked moves go through core::obli*.  Loop bounds are the public
// geometry.  Timing therefore does not depend on the data; correctness does,
// so the first --verify-passes passes of every arm are checked as above.
//
// NOT TIMED: input generation; in read_path and enigmap, the transposition
// between the path's bucket layout and byte lines that the engine pays
// around the data pass (read_path_transposed times it); in every arm, the
// path's bucket addresses and the position map; read_path_transposed's
// scalar conversions into its layout (input generation) and back to byte
// lines (verification).
// NOT DONE by any arm: value write-in, and the payload of dummy
// destinations (only real destinations' payload and every destination's
// metadata are compared).
//
// Usage: cpu_tree_eviction_comparator_benchmark [--capacity N] [--value-bytes
//   V[,V...]] [--key-bytes K] [--passes P] [--seed S] [--verify-passes Q]
//   [--fold F] [--stash-registers A]
//   [--arm read_path|read_path_transposed|enigmap|all]
// --fold 0 and --stash-registers 0 (the defaults) take the default rule's
// fold and stash width for the capacity.  One JSON line per (arm, V).  The
// enigmap arm takes V = 8, 16, ..., 4096.  --key-bytes is a label: it is
// echoed as "key_bytes" in every JSON line, and no arm reads it (the working
// set carries 8-byte uids, and the geometry depends on the capacity, V, the
// fold and A alone).

#if MICRORAM_ENIGMAP_ARM
#include "common/osort.hpp"
#include "oram/common/block.hpp"
#endif

#include <immintrin.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "src/core/mov_intrinsics.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"
#include "src/oram/tree/cpu_tree_read_path_eviction.hpp"
#include "src/oram/tree/cpu_tree_read_path_oram.hpp"
#include "src/oram/tree/cpu_tree_transpose.hpp"

namespace {

namespace tr = microram::tree;
namespace core = microram::core;
using microram::byteslice::benchmark_support::SplitMix64;

constexpr unsigned kZ = tr::kBucketSlots;
constexpr unsigned kMaxLanes = 64 * tr::kMaxStashRegisters + 64;

// ---------------------------------------------------------------------------
// memory
// ---------------------------------------------------------------------------

struct FreeDeleter {
  void operator()(void* p) const { std::free(p); }
};
using Buf = std::unique_ptr<uint8_t, FreeDeleter>;
Buf AllocZero(size_t bytes) {
  bytes = (bytes + 63) / 64 * 64;
  void* p = std::aligned_alloc(64, bytes);
  if (p == nullptr) {
    std::fprintf(stderr, "allocation of %zu bytes failed\n", bytes);
    std::exit(2);
  }
  std::memset(p, 0, bytes);
  return Buf(static_cast<uint8_t*>(p));
}

// ---------------------------------------------------------------------------
// geometry facts the arms need (public)
// ---------------------------------------------------------------------------

struct Geo {
  unsigned buckets = 0;  // P: path buckets, leaf first in the working set
  unsigned leaf_bits = 0;
  unsigned fold = 1;
  uint8_t match_bits[tr::kMaxPathLevels] = {};
  size_t lines = 0;      // 16 + V
  size_t value_bytes = 0;
  size_t row_bytes = 0;  // lines rounded up to 64
  unsigned a = 3;             // stash registers
  unsigned stash_lanes = 0;   // 64 A: working-set lanes 0..64A-1
  unsigned lanes = 0;         // 64 A + 64: the path's lanes follow
  size_t chunks = 0;          // C: 64-byte chunks per stored bucket
  unsigned prefetch_ahead = 0;  // the engine's default (TreeKnobs)
};

// ---------------------------------------------------------------------------
// one working set, in both layouts
// ---------------------------------------------------------------------------

struct WorkingSet {
  Buf cols_s, cols_p;  // byte line i, lane = byte: lines x 64 A (stash), lines x 64 (path)
  Buf rows;            // lanes x row_bytes: entry-major
  uint64_t uid[kMaxLanes] = {}, pos[kMaxLanes] = {};  // as stored (real bit in pos)
  uint64_t target_uid = 0;
  bool has_target = false;
  uint64_t path_position = 0;
  // Whether the access creates the entry when absent, and the metadata the
  // accessed entry lands with.
  bool create = false;
  alignas(16) uint8_t land_meta[tr::kMetaBytes] = {};
  // read_path_transposed's own copy, built outside the timer and routed in
  // place: the path's P buckets in the stored layout (leaf first, bucket m
  // at tp_bucket[m]) and the stash lines.
  Buf tp_path, tp_stash;
  uint8_t* tp_bucket[tr::kMaxPathLevels] = {};
#if MICRORAM_ENIGMAP_ARM
  std::shared_ptr<void> enig_in;  // the enigmap arm's stash vector, built outside the timer
#endif
};

struct Rng {
  uint64_t s;
  uint64_t Next() { return SplitMix64(s); }
  double Uniform() { return static_cast<double>(Next() >> 11) * (1.0 / 9007199254740992.0); }
};

void Allocate(WorkingSet& w, const Geo& g) {
  w.cols_s = AllocZero(g.lines * g.stash_lanes);
  w.cols_p = AllocZero(g.lines * 64);
  w.rows = AllocZero(g.lanes * g.row_bytes);
}

// kind 0: no target (an eviction-only pass), 1: target present, 2: target
// named but absent (the access creates it).  `dense` overloads the stash
// to exercise overflow.
void Generate(WorkingSet& w, const Geo& g, Rng& rng, double load, int kind,
              bool dense) {
  std::memset(w.rows.get(), 0, g.lanes * g.row_bytes);
  const uint64_t leaf_mask =
      g.leaf_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << g.leaf_bits) - 1;
  w.path_position = rng.Next() & leaf_mask;
  // The stash holds min(32 A, 128) entries on average, around the 109-164
  // lanes its 2^-96 requirement asks (src/oram/tree/DESIGN.md, "Stash size").
  const double stash_p = dense ? 1.0 : std::min(0.5, 2.0 / g.a);
  const double path_p = dense ? 1.0 : load;
  bool any_real = false;
  unsigned real_lanes[kMaxLanes];
  unsigned n_real = 0;
  for (unsigned l = 0; l < g.lanes; ++l) {
    bool real = false;
    uint64_t leaf = 0;
    if (l < g.stash_lanes) {
      real = rng.Uniform() < stash_p;
      leaf = rng.Next() & leaf_mask;
      if ((rng.Next() & 1) != 0) {
        // Half the stash entries share a prefix of uniform length with the
        // path, so stash entries reach every position.
        const unsigned low = static_cast<unsigned>(rng.Next() % (g.leaf_bits + 1));
        const uint64_t low_mask = low >= 64 ? ~uint64_t{0} : (uint64_t{1} << low) - 1;
        leaf = ((w.path_position & ~low_mask) | (leaf & low_mask)) & leaf_mask;
      }
    } else {
      const unsigned b = (l - g.stash_lanes) / kZ;
      if (b < g.buckets) {
        real = rng.Uniform() < path_p;
        // An entry stored in a bucket of cumulative depth `need` shares that
        // many leading leaf bits with the path.
        const unsigned low = g.leaf_bits - g.match_bits[b];
        const uint64_t low_mask = low >= 64 ? ~uint64_t{0} : (uint64_t{1} << low) - 1;
        leaf = (w.path_position & ~low_mask) | (rng.Next() & low_mask);
        leaf &= leaf_mask;
      }
    }
    uint8_t* row = w.rows.get() + l * g.row_bytes;
    if (real) {
      w.uid[l] = rng.Next();
      w.pos[l] = tr::EncodeStoredPosition(leaf);
      std::memcpy(row, &w.uid[l], 8);
      std::memcpy(row + 8, &w.pos[l], 8);
      size_t i = tr::kMetaBytes;
      for (; i + 8 <= g.lines; i += 8) {
        const uint64_t r = rng.Next();
        std::memcpy(row + i, &r, 8);
      }
      for (; i < g.lines; ++i) row[i] = static_cast<uint8_t>(rng.Next());
      real_lanes[n_real++] = l;
      any_real = true;
    } else {
      w.uid[l] = 0;
      w.pos[l] = 0;
    }
  }
  w.has_target = kind != 0;
  if (kind == 1 && any_real) {
    w.target_uid = w.uid[real_lanes[rng.Next() % n_real]];
  } else {
    w.target_uid = rng.Next();
  }
  w.create = kind == 2;
  const uint64_t pos_new = tr::EncodeStoredPosition(rng.Next() & leaf_mask);
  std::memcpy(w.land_meta, &w.target_uid, 8);
  std::memcpy(w.land_meta + 8, &pos_new, 8);
  // byte-line layout: a stash line is 64 A bytes, a path line 64
  uint8_t* cs = w.cols_s.get();
  uint8_t* cp = w.cols_p.get();
  for (unsigned l = 0; l < g.lanes; ++l) {
    const uint8_t* row = w.rows.get() + l * g.row_bytes;
    const bool stash = l < g.stash_lanes;
    uint8_t* base = stash ? cs + l : cp + (l - g.stash_lanes);
    const size_t stride = stash ? g.stash_lanes : 64;
    for (size_t i = 0; i < g.lines; ++i) base[i * stride] = row[i];
  }
}

// ---------------------------------------------------------------------------
// outputs
// ---------------------------------------------------------------------------

// `extra`: the enigmap arm's stash entries past lane 64 A - 1 (EnigMap's
// stash holds Z (L+1) + 80 entries and keeps its padding entries there).
// `value`: the read path's value_out.
constexpr unsigned kExtraRows = 128;
struct Out {
  Buf cols_s, cols_p, rows, extra, value;
};
void Allocate(Out& o, const Geo& g) {
  o.cols_s = AllocZero(g.lines * g.stash_lanes);
  o.cols_p = AllocZero(g.lines * 64);
  o.rows = AllocZero(g.lanes * g.row_bytes);
  o.extra = AllocZero(kExtraRows * g.row_bytes);
  o.value = AllocZero(g.value_bytes);
}

struct PassResult {
  bool found = false;
  unsigned stash_count = 0;
  bool overflow = false;
};

using ArmFn = PassResult (*)(const Geo&, const WorkingSet&, Out&);

// ---------------------------------------------------------------------------
// arm 1: the read-path engine
// ---------------------------------------------------------------------------

// RouteReadPathLine<A, 1, Meta> (cpu_tree_read_path_oram.hpp) with value_in
// null and value_out set: the same instructions -- the permutes are the
// library's PermuteReadPathWords -- with the stash line read from `s` and
// written to `ds` and the path line from `p` to `dp`.
template <unsigned A, bool Meta>
INLINE void RouteLine(size_t i, const uint8_t* s, uint8_t* ds, const uint8_t* p,
                      uint8_t* dp, const tr::ReadPathPlan& plan,
                      const uint8_t* meta, uint8_t* byte) {
  constexpr unsigned W = 1 + A;
  __m512i x[W];
  x[0] = _mm512_load_si512(p);
  for (unsigned a = 0; a < A; ++a) x[1 + a] = core::obliLoad512(s + 64 * a);
  const __m512i d0 = tr::PermuteReadPathWords<W, 0>(x, plan.from[0], plan.index[0]);
  __m512i landing;
  if constexpr (Meta) {
    landing = core::obliPin512(_mm512_set1_epi8(static_cast<char>(meta[i])));
    for (unsigned a = 0; a < A; ++a) {
      x[1 + a] = core::obliMaskMov8(_mm512_setzero_si512(), plan.keep[a], x[1 + a]);
    }
  } else {
    const __m512i g =
        tr::PermuteReadPathWords<W, 0>(x, plan.target_from, plan.target_index);
    *byte = static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(g)));
    landing = g;
  }
  for (unsigned a = 0; a < A; ++a) {
    x[1 + a] = core::obliMaskMov8(x[1 + a], plan.land[a], landing);
    _mm512_store_si512(reinterpret_cast<void*>(ds + 64 * a), x[1 + a]);
  }
  _mm512_store_si512(reinterpret_cast<void*>(dp), d0);
}

template <unsigned A>
__attribute__((noinline)) PassResult RunReadPathA(const Geo& g, const WorkingSet& w,
                                                  Out& o) {
  tr::ReadPathEvictionInput in;
  in.stash_meta = w.cols_s.get();
  in.path_meta = reinterpret_cast<const __m512i*>(w.cols_p.get());
  in.target_uid = w.target_uid;
  in.has_target = w.has_target;
  in.create = w.create;
  in.erase = false;
  in.path_position = w.path_position;
  in.leaf_bits = g.leaf_bits;
  in.path_buckets = g.buckets;
  in.level_match_bits = g.match_bits;
  tr::ReadPathPlan plan;
  tr::PlanReadPath<A, 1>(in, &plan);
  const uint8_t* s = w.cols_s.get();
  const uint8_t* p = w.cols_p.get();
  uint8_t* ds = o.cols_s.get();
  uint8_t* dp = o.cols_p.get();
  constexpr size_t kStride = 64 * A;
  for (size_t i = 0; i < tr::kMetaBytes; ++i) {
    RouteLine<A, true>(i, s + kStride * i, ds + kStride * i, p + 64 * i, dp + 64 * i,
                       plan, w.land_meta, nullptr);
  }
  uint8_t* value_out = o.value.get();
  for (size_t i = tr::kMetaBytes; i < g.lines; ++i) {
    RouteLine<A, false>(i, s + kStride * i, ds + kStride * i, p + 64 * i, dp + 64 * i,
                        plan, w.land_meta, value_out + (i - tr::kMetaBytes));
  }
  PassResult r;
  r.found = plan.found;
  r.stash_count = plan.stash_count;
  r.overflow = plan.overflow;
  return r;
}

PassResult RunReadPath(const Geo& g, const WorkingSet& w, Out& o) {
  // public, fixed per run
  return g.a == 3 ? RunReadPathA<3>(g, w, o) : RunReadPathA<4>(g, w, o);
}

// ---------------------------------------------------------------------------
// arm 2: the read-path engine with the path's transposition
// ---------------------------------------------------------------------------

// One synchronous engine pass on a one-register path of P buckets
// (ReadPathPlane: BeginPass, TransposeFirstChunk, the plan, ApplyPass with
// RunValueChunk<A, P, 0>), on the stored-layout path at w.tp_bucket and the
// stash lines at w.tp_stash, in place.  Only the engine's free functions
// are called; the sequence is ApplyPassImpl<A, false>'s.
template <unsigned A, unsigned P>
__attribute__((noinline)) PassResult RunTransposedAP(const Geo& g, const WorkingSet& w,
                                                     Out& o) {
  constexpr unsigned kTile = tr::kReadPathBucketsPerRegister;
  constexpr size_t kCols = tr::kChunkColumns;
  const tr::TransposeTables4& tt = tr::DefaultTransposeTables4();
  uint8_t* const* bucket = w.tp_bucket;
  const size_t S = g.chunks;
  const size_t E = g.lines;
  const unsigned ahead = g.prefetch_ahead;
  // BeginPass: each bucket's first chunks in flight.
  for (unsigned i = 0; i < P; ++i) {
    for (size_t a = 0; a < ahead && a < S; ++a) {
      _mm_prefetch(reinterpret_cast<const char*>(bucket[i] + a * tr::kChunkBytes),
                   _MM_HINT_T0);
    }
  }
  // TransposeFirstChunk: chunk 0, the metadata exactly, as byte lines in the
  // tile for the planner.
  alignas(64) __m512i tile[kTile];
  tr::LoadChunkInto<kTile>(tile, bucket, P, 0, S, ahead);
  tr::TransposeToLines4Exact<P>(tile, tt);
  tr::ReadPathEvictionInput in;
  in.stash_meta = w.tp_stash.get();
  in.path_meta = tile;
  in.target_uid = w.target_uid;
  in.has_target = w.has_target;
  in.create = w.create;
  in.erase = false;
  in.path_position = w.path_position;
  in.leaf_bits = g.leaf_bits;
  in.path_buckets = g.buckets;  // P, at run time as in the engine's planner call
  in.level_match_bits = g.match_bits;
  tr::ReadPathPlan plan;
  tr::PlanReadPath<A, 1>(in, &plan);
  // ApplyPass: chunk 0's lines routed in the tile, transposed back, stored.
  tr::ReadPathContext<A> ctx;
  ctx.stash_lines = w.tp_stash.get();
  ctx.stash_line0 = 0;
  ctx.plan = &plan;
  ctx.meta = w.land_meta;
  ctx.value_in = nullptr;
  ctx.value_out = o.value.get();
  __m512i none = _mm512_setzero_si512();  // path register 1: none
  uint8_t* const stash0 = ctx.StashLineFor(0);
  for (size_t c = 0; c < kCols; ++c) {
    tr::RouteReadPathLine<A, 1, true>(c, stash0 + c * 64 * A, &tile[c], &none, ctx);
  }
  tr::TransposeToChunks4Exact<P>(tile, tt);
  tr::StoreChunkFrom(tile, bucket, P, 0);
  // Every value chunk as RunValueChunk<A, P, 0>: load, transpose, route +
  // gather + land each line, the gathered bytes out, transpose back, store.
  for (size_t t = 1; t < S; ++t) {
    const size_t base = t * kCols;
    const size_t cols = std::min<size_t>(kCols, E - base);
    uint8_t* const stash = ctx.StashLineFor(base);
    alignas(16) uint8_t bytes[kTile];
    __m512i r[kTile];
    tr::LoadChunkInto<kTile>(r, bucket, P, t, S, ahead);
    tr::TransposeGroupForwardExact<P>(tt, r);
    for (unsigned i = 0; i < kTile; ++i) {
      // `cols` is public: a partial last chunk's padding lines pass through.
      if (i < cols) {
        tr::RouteReadPathLine<A, 1, false>(base + i, stash + i * 64 * A, &r[i], &none,
                                           ctx, bytes + i);
      }
    }
    tr::WriteValueBytes(ctx.value_out + base - tr::kMetaBytes, bytes, cols);
    tr::TransposeGroupInverseExact<P>(tt, r);
    tr::StoreChunkFrom(r, bucket, P, t);
  }
  PassResult res;
  res.found = plan.found;
  res.stash_count = plan.stash_count;
  res.overflow = plan.overflow;
  return res;
}

template <unsigned A>
PassResult RunTransposedA(const Geo& g, const WorkingSet& w, Out& o) {
  // P is public, dispatched once per pass as the engine does.
  return tr::WithPathBuckets(g.buckets, [&](auto p) {
    return RunTransposedAP<A, decltype(p)::value>(g, w, o);
  });
}

PassResult RunReadPathTransposed(const Geo& g, const WorkingSet& w, Out& o) {
  return g.a == 3 ? RunTransposedA<3>(g, w, o) : RunTransposedA<4>(g, w, o);
}

// The arm's copy of a working set, outside the timer: the path from the
// entry rows into the stored layout by the layout's definition -- byte k of
// slot z of the bucket at leaf-first position m at m x 64 C + 4k + z, zero
// padding -- and the stash lines as they are.
void PrepareTransposed(const Geo& g, WorkingSet& w) {
  const size_t stride = g.chunks * tr::kChunkBytes;
  if (w.tp_path == nullptr) {
    w.tp_path = AllocZero(g.buckets * stride);
    w.tp_stash = AllocZero(g.lines * g.stash_lanes);
  }
  uint8_t* path = w.tp_path.get();
  std::memset(path, 0, g.buckets * stride);
  for (unsigned m = 0; m < g.buckets; ++m) {
    w.tp_bucket[m] = path + m * stride;
    for (unsigned z = 0; z < kZ; ++z) {
      const uint8_t* row = w.rows.get() + (g.stash_lanes + kZ * m + z) * g.row_bytes;
      for (size_t k = 0; k < g.lines; ++k) w.tp_bucket[m][kZ * k + z] = row[k];
    }
  }
  std::memcpy(w.tp_stash.get(), w.cols_s.get(), g.lines * g.stash_lanes);
}

// Verification only: the arm's output in Out's byte lines -- the path back
// from the stored layout by the same definition (lanes past 4P zero), the
// stash lines as routed.
void CollectTransposed(const Geo& g, const WorkingSet& w, Out& o) {
  uint8_t* cp = o.cols_p.get();
  std::memset(cp, 0, g.lines * 64);
  for (unsigned m = 0; m < g.buckets; ++m) {
    for (unsigned z = 0; z < kZ; ++z) {
      for (size_t k = 0; k < g.lines; ++k) {
        cp[k * 64 + kZ * m + z] = w.tp_bucket[m][kZ * k + z];
      }
    }
  }
  std::memcpy(o.cols_s.get(), w.tp_stash.get(), g.lines * g.stash_lanes);
}

// ---------------------------------------------------------------------------
// arm 3: EnigMap's EvictPath (MICRORAM_ENIGMAP_ARM builds only)
// ---------------------------------------------------------------------------

#if MICRORAM_ENIGMAP_ARM
namespace enig {

// The block's data: V payload bytes.  EnigMap's Block<T> holds T and asks T
// for DUMMY(), operator== and (outside an enclave) operator<<.
template <size_t V>
struct Payload {
  uint8_t b[V];
  static consteval Payload DUMMY() { return Payload{}; }
  bool operator==(const Payload&) const = default;
  friend std::ostream& operator<<(std::ostream& o, const Payload&) { return o; }
};

// EnigMap leaves a block type's CMOV to the type; this one blends 64 bytes at
// a time under a mask from the condition (found by ADL from EnigMap's
// templates, which call CMOV(cond, A.data, B.data)).
template <size_t V>
INLINE void CMOV(const uint64_t& cond, Payload<V>& a, const Payload<V>& b) {
  const __mmask8 m = static_cast<__mmask8>(0 - static_cast<unsigned>(cond != 0));
  size_t i = 0;
  for (; i + 64 <= V; i += 64) {
    const __m512i x = _mm512_loadu_si512(a.b + i);
    const __m512i y = _mm512_loadu_si512(b.b + i);
    _mm512_storeu_si512(a.b + i, _mm512_mask_blend_epi64(m, x, y));
  }
  for (; i + 8 <= V; i += 8) {
    uint64_t x, y;
    std::memcpy(&x, a.b + i, 8);
    std::memcpy(&y, b.b + i, 8);
    ::CMOV(cond, x, y);
    std::memcpy(a.b + i, &x, 8);
  }
}

template <size_t V>
using StashedBlock = _ORAM::StashedBlock::StashedBlock<_ORAM::Block::Block<Payload<V>>>;
template <size_t V>
using Tagged = TaggedT<StashedBlock<V>>;

// The sorts' compare-exchange: EnigMap's obliSwap over the whole entry.
template <size_t V>
INLINE void CXCHG(const uint64_t& cond, Tagged<V>& a, Tagged<V>& b) {
  obliSwap(cond != 0, a, b);
}

// EnigMap's stash after ReadPathToStash: the 64 A stash lanes, then the
// path's Z P slots, in lane order.  Address = uid, position = the stored word
// (the tag decodes it); empty lanes are EnigMap's dummies.
template <size_t V>
void Prepare(const Geo& g, WorkingSet& w) {
  auto st = std::make_shared<std::vector<StashedBlock<V>>>();
  const unsigned n = g.stash_lanes + kZ * g.buckets;
  st->reserve(n);
  for (unsigned l = 0; l < n; ++l) {
    StashedBlock<V> sb = StashedBlock<V>::DUMMY();
    if (tr::StoredPositionIsReal(w.pos[l])) {
      sb.oaddress.address = w.uid[l];
      sb.oaddress.position = w.pos[l];
      std::memcpy(sb.block.data.b, w.rows.get() + l * g.row_bytes + tr::kMetaBytes, V);
    }
    st->push_back(sb);
  }
  w.enig_in = st;
}

// Step 5's padding entries carry isDummy = false (so they sort ahead of the
// level's dummies) and only their address marks them empty.
template <size_t V>
INLINE uint64_t IsReal(const Tagged<V>& e) {
  return static_cast<uint64_t>(!e.isDummy) * (e.v.oaddress.address != _ORAM::DUMMY_ADDRESS);
}

// Writes one entry as a row of the arms' output: dummies get zero metadata.
template <size_t V>
INLINE void PutRow(const Tagged<V>& e, uint8_t* row) {
  uint64_t uid = e.v.oaddress.address, pos = e.v.oaddress.position, zero = 0;
  const uint64_t empty = IsReal<V>(e) ^ 1;
  ::CMOV(empty, uid, zero);
  ::CMOV(empty, pos, zero);
  std::memcpy(row, &uid, 8);
  std::memcpy(row + 8, &pos, 8);
  std::memcpy(row + tr::kMetaBytes, e.v.block.data.b, V);
}

template <size_t V>
__attribute__((noinline)) PassResult Run(const Geo& g, const WorkingSet& w, Out& o) {
  using SB = StashedBlock<V>;
  using TB = Tagged<V>;
  const auto& stash = *static_cast<const std::vector<SB>*>(w.enig_in.get());
  const uint64_t L_ = g.buckets - 1;  // EnigMap's tree height: levels 0..L_
  const uint64_t Z = kZ;

  // ReadBlockFromStash (EnigMap's BeginAccess): copy the target out.
  SB ret = SB::DUMMY();
  bool found = false;
  const uint64_t has = static_cast<uint64_t>(w.has_target);
  for (uint64_t i = 0; i < stash.size(); i++) {
    const bool isRightBlock = has * (stash[i].oaddress.address == w.target_uid);
    ::CMOV(isRightBlock, found, true);
    ::CMOV(isRightBlock, ret, stash[i]);
  }

  std::vector<TB> v;
  v.reserve(stash.size() + Z * (L_ + 1));
  // 1) Tag each entry with the deepest level it can reach (0 = leaf), dummies
  // and the (purged) target with L_+1; add one counter dummy per level.
  {
    const uint64_t path_word = w.path_position | tr::kRealPositionBit;
    for (uint64_t i = 0; i < stash.size(); i++) {
      const SB& si = stash[i];
      const uint64_t x = si.oaddress.position ^ path_word;
      const uint64_t bl = 64 - static_cast<uint64_t>(_lzcnt_u64(x));
      const uint64_t over = static_cast<uint64_t>(static_cast<int64_t>(g.leaf_bits - bl) >> 63);
      const uint64_t deep = g.leaf_bits - (bl + ((g.leaf_bits - bl) & over));
      uint64_t tag = 0;
      for (unsigned m = 0; m < g.buckets; ++m) tag += g.match_bits[m] > deep;
      const bool isTarget = has * (si.oaddress.address == w.target_uid);
      const bool isDummy = (si.oaddress.address == _ORAM::DUMMY_ADDRESS) + isTarget;
      ::CMOV(isDummy, tag, L_ + 1);
      v.push_back(TB{isDummy, tag, si});
    }
    for (uint64_t i = 0; i <= L_; i++) {
      v.push_back(TB{true, i, SB::DUMMY()});
    }
  }
  const uint64_t origSize = v.size();

  // 2) Sort with dummy buckets at the end of each level.  Correctness patch:
  // the upstream comparator (here and in step 6) reads `b1.tag == b2.tag *
  // !b1.isDummy * b2.isDummy`, which parses as `b1.tag == (b2.tag * ...)`;
  // with it a level's counter can sort ahead of its real entries and dense
  // passes leave 1-2 entries in the stash that greedy eviction places
  // (VerifyValid fails on them).  Only the parentheses are added; the
  // instructions per compare are the same.
  {
    auto cmp = [](const TB& b1, const TB& b2) {
      return (b1.tag < b2.tag) + ((b1.tag == b2.tag) * !b1.isDummy * b2.isDummy);
    };
    ObliSortBlocks<TB>(v, cmp);
  }

  // 3) Do a linear pass to count buckets:
  uint64_t count = 0;
  uint64_t currTag = 0;
  for (uint64_t i = 0; i < origSize; i++) {
    bool isEnd = v[i].isDummy * (currTag <= L_);
    ::CMOV(isEnd, v[i].v.oaddress.address, static_cast<_ORAM::Address>(count));
    ::CMOV(isEnd, currTag, currTag + 1);
    count += 1;
    ::CMOV(isEnd, count, (uint64_t)0);
  }

  // 4) Do a second sort to make v[0..L] be the counter buckets:
  {
    auto cmp = [L_ = L_](const TB& b1, const TB& b2) {
      return false + ((b1.isDummy == b2.isDummy) * (b1.tag < b2.tag)) +
             ((b1.isDummy) * (!b2.isDummy) * (b1.tag < L_ + 1)) +
             ((!b1.isDummy) * (b2.isDummy) * (b2.tag >= L_ + 1));
    };
    ObliSortBlocks<TB>(v, cmp);
  }

  // 5) Do a linear pass to add remaining dummy buckets:
  count = 0;
  for (uint64_t i = 0; i <= L_; i++) {
    const uint64_t target = (i + 1) * Z;
    count += v[i].v.oaddress.address;
    v[i].v.oaddress.address = _ORAM::DUMMY_ADDRESS;
    ::CMOV(count >= target, v[i].tag, L_ + 1);
    ::CMOV(count < target, count, count + 1);
    for (uint64_t z = 0; z < Z - 1; z++) {
      bool rem = count < target;
      ::CMOV(rem, count, count + 1);
      TB newDummy{false, i, SB::DUMMY()};
      ::CMOV(!rem, newDummy.tag, L_ + 1);
      v.push_back(newDummy);
    }
  }

  // 6) Sort to put all the buckets in the right position for eviction (the
  // comparator parenthesized as in step 2):
  {
    auto cmp = [](const TB& b1, const TB& b2) {
      return (b1.tag < b2.tag) + ((b1.tag == b2.tag) * !b1.isDummy * b2.isDummy);
    };
    ObliSortBlocks<TB>(v, cmp);
  }

  // 7) Level i's Z entries to its path slots; every entry past the path to
  // the stash, lanes 1..64A-1 and then `extra` (EnigMap copies until the
  // first isDummy entry, padding included); the target to lane 0.
  uint8_t* out = o.rows.get();
  const unsigned S = g.stash_lanes;
  for (uint64_t i = 0; i <= L_; i++) {
    const unsigned d0 = S + kZ * static_cast<unsigned>(i);
    for (uint64_t j = 0; j < Z; j++) PutRow<V>(v[i * Z + j], out + (d0 + j) * g.row_bytes);
  }
  for (unsigned d = S + kZ * g.buckets; d < g.lanes; ++d) {
    std::memset(out + d * g.row_bytes, 0, g.row_bytes);
  }
  uint64_t leftover = 0;
  for (uint64_t i = Z * (L_ + 1); i < v.size(); i++) leftover += IsReal<V>(v[i]);
  for (uint64_t i = Z * (L_ + 1), d = 1; i < v.size(); i++, d++) {
    PutRow<V>(v[i], d < S ? out + d * g.row_bytes : o.extra.get() + (d - S) * g.row_bytes);
  }
  TB t{!found, 0, ret};
  PutRow<V>(t, out);

  PassResult r;
  r.found = found;
  r.stash_count = static_cast<unsigned>(leftover);
  r.overflow = leftover > S - 1;
  return r;
}

template <typename F>
bool ForWidth(size_t v, F&& f) {
  switch (v) {
    case 8: f(std::integral_constant<size_t, 8>{}); return true;
    case 16: f(std::integral_constant<size_t, 16>{}); return true;
    case 32: f(std::integral_constant<size_t, 32>{}); return true;
    case 64: f(std::integral_constant<size_t, 64>{}); return true;
    case 128: f(std::integral_constant<size_t, 128>{}); return true;
    case 256: f(std::integral_constant<size_t, 256>{}); return true;
    case 512: f(std::integral_constant<size_t, 512>{}); return true;
    case 1024: f(std::integral_constant<size_t, 1024>{}); return true;
    case 2048: f(std::integral_constant<size_t, 2048>{}); return true;
    case 4096: f(std::integral_constant<size_t, 4096>{}); return true;
    default: return false;
  }
}

}  // namespace enig

PassResult RunEnigmap(const Geo& g, const WorkingSet& w, Out& o) {
  PassResult r;
  enig::ForWidth(g.value_bytes, [&](auto v) { r = enig::Run<decltype(v)::value>(g, w, o); });
  return r;
}
void PrepareEnigmap(const Geo& g, WorkingSet& w) {
  enig::ForWidth(g.value_bytes, [&](auto v) { enig::Prepare<decltype(v)::value>(g, w); });
}
#endif

// ---------------------------------------------------------------------------
// verification against ReferenceReadPathEvict
// ---------------------------------------------------------------------------

// The reference takes the working set in the read path's priority order --
// the path's 64 lanes, then the stash -- so lanes are mapped both ways.
unsigned OurLane(const Geo& g, unsigned ref_lane) {
  return ref_lane < 64 ? g.stash_lanes + ref_lane : ref_lane - 64;
}
tr::ReferenceReadPath ReadPathReference(const Geo& g, const WorkingSet& w) {
  uint64_t uid[kMaxLanes], pos[kMaxLanes];
  for (unsigned r = 0; r < g.lanes; ++r) {
    uid[r] = w.uid[OurLane(g, r)];
    pos[r] = w.pos[OurLane(g, r)];
  }
  return tr::ReferenceReadPathEvict(uid, pos, g.a, w.target_uid, w.has_target,
                                    w.create, false, w.path_position, g.leaf_bits,
                                    g.buckets, g.match_bits);
}

// Without overflow (the engine throws before writing): every path
// destination holds its reference source or is all zero; every stash lane
// is kept intact, emptied (zero metadata; its value bytes stay), or is the
// landing lane (the landing metadata and the accessed entry's value, zero if
// it was created); value_out is the accessed entry's value or zero.
bool VerifyReadPath(const Geo& g, const WorkingSet& w, const Out& o,
                    const PassResult& r, const char* arm, unsigned pass,
                    bool* saw_overflow) {
  const tr::ReferenceReadPath ref = ReadPathReference(g, w);
  if (ref.overflow) *saw_overflow = true;
  if (r.found != ref.found || r.stash_count != ref.stash_count ||
      r.overflow != ref.overflow || ref.path_entry_dropped) {
    std::fprintf(stderr,
                 "%s pass %u: flags differ (found %d/%d, leftovers %u/%u, "
                 "overflow %d/%d, path entry dropped %d)\n",
                 arm, pass, r.found, ref.found, r.stash_count, ref.stash_count,
                 r.overflow, ref.overflow, ref.path_entry_dropped);
    return false;
  }
  if (ref.overflow) return true;
  const uint8_t* target =
      ref.found ? w.rows.get() + OurLane(g, ref.target) * g.row_bytes : nullptr;
  const auto value = [&](size_t v) -> uint8_t {
    return target != nullptr ? target[tr::kMetaBytes + v] : 0;
  };
  for (size_t v = 0; v < g.value_bytes; ++v) {
    if (o.value.get()[v] != value(v)) {
      std::fprintf(stderr, "%s pass %u: value_out byte %zu differs\n", arm, pass, v);
      return false;
    }
  }
  for (unsigned d = 0; d < 64; ++d) {
    const unsigned src = ref.source[d];
    const uint8_t* want = src == tr::ReferenceReadPath::kNone
                              ? nullptr
                              : w.rows.get() + OurLane(g, src) * g.row_bytes;
    for (size_t i = 0; i < g.lines; ++i) {
      if (o.cols_p.get()[i * 64 + d] != (want != nullptr ? want[i] : 0)) {
        std::fprintf(stderr, "%s pass %u: path dest %u byte %zu differs (source %d)\n",
                     arm, pass, d, i, want != nullptr ? static_cast<int>(OurLane(g, src)) : -1);
        return false;
      }
    }
  }
  for (unsigned s = 0; s < g.stash_lanes; ++s) {
    const bool land = static_cast<int>(s) == ref.landing;
    for (size_t i = 0; i < g.lines; ++i) {
      const bool meta = i < tr::kMetaBytes;
      int want = -1;  // unspecified
      if (land) {
        want = meta ? w.land_meta[i] : value(i - tr::kMetaBytes);
      } else if (ref.keep[s]) {
        want = w.rows.get()[s * g.row_bytes + i];
      } else if (meta) {
        want = 0;
      }
      if (want >= 0 && o.cols_s.get()[i * g.stash_lanes + s] != want) {
        std::fprintf(stderr, "%s pass %u: stash lane %u byte %zu differs (%s)\n", arm,
                     pass, s, i, land ? "landing" : ref.keep[s] ? "kept" : "emptied");
        return false;
      }
    }
  }
  return true;
}

#if MICRORAM_ENIGMAP_ARM
// A valid eviction with any tie order (the enigmap arm): the same flags as
// ReferenceReadPathEvict (the leftover count of any maximal greedy is the
// read path's); without overflow, every
// real source lane lands exactly once with its bytes intact (the target in
// lane 0), every path destination is eligible for its bucket, and every
// other destination's metadata is zero.
bool VerifyValid(const Geo& g, const WorkingSet& w, const Out& o,
                 const PassResult& r, const char* arm, unsigned pass,
                 bool* saw_overflow) {
  const tr::ReferenceReadPath ref = ReadPathReference(g, w);
  const bool found = ref.found, overflow = ref.overflow;
  const unsigned stash_count = ref.stash_count;
  // The target's working-set lane.
  const unsigned target =
      found ? OurLane(g, static_cast<unsigned>(ref.target)) : kMaxLanes;
  if (overflow) *saw_overflow = true;
  if (r.found != found || r.stash_count != stash_count || r.overflow != overflow) {
    std::fprintf(stderr,
                 "%s pass %u: flags differ (found %d/%d, leftovers %u/%u, "
                 "overflow %d/%d)\n",
                 arm, pass, r.found, found, r.stash_count, stash_count,
                 r.overflow, overflow);
    return false;
  }
  if (overflow) return true;  // leftovers past lane 64A-1 are lost by every arm
  const unsigned S = g.stash_lanes;
  int bucket_of[kMaxLanes];
  for (auto& b : bucket_of) b = -1;
  for (unsigned m = 0; m < g.buckets; ++m) {
    for (unsigned q = 0; q < kZ; ++q) bucket_of[S + kZ * m + q] = static_cast<int>(m);
  }
  bool used[kMaxLanes] = {};
  // Destinations 0..lanes-1, then the extended stash (stash destinations too).
  for (unsigned d = 0; d < g.lanes + kExtraRows; ++d) {
    const uint8_t* row = d < g.lanes ? o.rows.get() + d * g.row_bytes
                                     : o.extra.get() + (d - g.lanes) * g.row_bytes;
    uint64_t uid, pos;
    std::memcpy(&uid, row, 8);
    std::memcpy(&pos, row + 8, 8);
    if (!tr::StoredPositionIsReal(pos)) {
      if (uid != 0 || pos != 0) {
        std::fprintf(stderr, "%s pass %u: dummy dest %u has metadata\n", arm, pass, d);
        return false;
      }
      continue;
    }
    unsigned src = kMaxLanes;
    for (unsigned l = 0; l < g.lanes; ++l) {
      if (tr::StoredPositionIsReal(w.pos[l]) && w.uid[l] == uid) src = l;
    }
    if (src == kMaxLanes || used[src] ||
        std::memcmp(row, w.rows.get() + src * g.row_bytes, g.lines) != 0) {
      std::fprintf(stderr, "%s pass %u: dest %u holds no intact unused source (lane %u)\n",
                   arm, pass, d, src);
      return false;
    }
    used[src] = true;
    if ((d == 0) != (src == target)) {
      std::fprintf(stderr, "%s pass %u: target misplaced (dest %u, source %u)\n", arm, pass, d, src);
      return false;
    }
    if (d >= S && d < g.lanes) {
      const uint64_t x = tr::StoredPositionLeaf(pos) ^ w.path_position;
      const unsigned bitlen = x == 0 ? 0u : 64u - static_cast<unsigned>(__builtin_clzll(x));
      const unsigned deep = bitlen > g.leaf_bits ? 0u : g.leaf_bits - bitlen;
      if (bucket_of[d] < 0 || deep < g.match_bits[bucket_of[d]]) {
        std::fprintf(stderr, "%s pass %u: dest %u not eligible (deepest %u)\n", arm, pass, d, deep);
        return false;
      }
    }
  }
  for (unsigned l = 0; l < g.lanes; ++l) {
    if (tr::StoredPositionIsReal(w.pos[l]) && !used[l]) {
      std::fprintf(stderr, "%s pass %u: source lane %u lost\n", arm, pass, l);
      return false;
    }
  }
  return true;
}
#endif

// ---------------------------------------------------------------------------
// driver
// ---------------------------------------------------------------------------

using PrepareFn = void (*)(const Geo&, WorkingSet&);
using CollectFn = void (*)(const Geo&, const WorkingSet&, Out&);

struct Arm {
  const char* name;
  ArmFn fn;
  const char* note;
  PrepareFn prepare = nullptr;  // per working set, outside the timer
  bool valid_only = false;      // verify validity, not the read path's lane order
  CollectFn collect = nullptr;  // verification only: the arm's output into Out
};

const Arm kArms[] = {
    {"read_path", RunReadPath,
     "plan = library PlanReadPath<A, 1>; data pass = RouteReadPathLine body "
     "replicated out of place (value_in null, value_out scratch); no "
     "transposition charged"},
    {"read_path_transposed", RunReadPathTransposed,
     "path in the stored bucket layout (P buckets x C chunks, slots "
     "interleaved), stash in byte lines; ReadPathPlane's pass minus "
     "addresses from the engine's free functions: LoadChunkInto + "
     "TransposeToLines4Exact, PlanReadPath<A, 1>, then per chunk "
     "TransposeGroupForwardExact + RouteReadPathLine + WriteValueBytes + "
     "TransposeGroupInverseExact + StoreChunkFrom; in place (value_in null, "
     "value_out scratch); transposition charged",
     PrepareTransposed, false, CollectTransposed},
#if MICRORAM_ENIGMAP_ARM
    {"enigmap", RunEnigmap,
     "EnigMap 4d0bfdb EvictPath steps 1-6 (three ObliSort passes over whole "
     "entries) + step 7 copy-out, after its ReadBlockFromStash scan; entries "
     "in a std::vector reserved once; obliSwap compare-exchange; checked for "
     "validity, not lane order",
     PrepareEnigmap, true},
#endif
};

std::vector<size_t> ParseList(const char* s) {
  std::vector<size_t> out;
  while (*s != '\0') {
    char* end = nullptr;
    out.push_back(std::strtoull(s, &end, 10));
    if (end == s) break;
    s = *end == ',' ? end + 1 : end;
  }
  return out;
}

}  // namespace

int main(int argc, char** argv) {
  size_t capacity = size_t{1} << 20;
  std::vector<size_t> value_list = {1024};
  size_t key_bytes = 32;  // a label only: echoed in the JSON, read by no arm
  uint64_t passes = 200000;
  uint64_t seed = 1;
  unsigned verify_passes = 1000;
  unsigned fold = 0;
  unsigned stash_registers = 0;
  std::string arm_name = "all";
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    const auto next = [&]() -> const char* {
      if (i + 1 >= argc) {
        std::fprintf(stderr, "missing value for %s\n", a.c_str());
        std::exit(2);
      }
      return argv[++i];
    };
    if (a == "--capacity") capacity = std::strtoull(next(), nullptr, 10);
    else if (a == "--value-bytes") value_list = ParseList(next());
    else if (a == "--key-bytes") key_bytes = std::strtoull(next(), nullptr, 10);
    else if (a == "--passes") passes = std::strtoull(next(), nullptr, 10);
    else if (a == "--seed") seed = std::strtoull(next(), nullptr, 10);
    else if (a == "--verify-passes") verify_passes = static_cast<unsigned>(std::strtoull(next(), nullptr, 10));
    else if (a == "--fold") fold = static_cast<unsigned>(std::strtoull(next(), nullptr, 10));
    else if (a == "--stash-registers") stash_registers = static_cast<unsigned>(std::strtoull(next(), nullptr, 10));
    else if (a == "--arm") arm_name = next();
    else {
      std::fprintf(stderr, "unknown flag %s\n", a.c_str());
      return 2;
    }
  }
  if (capacity < 128) capacity = 128;
  if (arm_name != "all" && arm_name != "read_path" &&
      arm_name != "read_path_transposed" && arm_name != "enigmap") {
    std::fprintf(stderr, "--arm must be read_path|read_path_transposed|enigmap|all\n");
    return 2;
  }
#if !MICRORAM_ENIGMAP_ARM
  if (arm_name == "enigmap") {
    std::fprintf(stderr, "the enigmap arm is in cpu_tree_eviction_comparator_benchmark_enigmap\n");
    return 2;
  }
#endif
  if (!__builtin_cpu_supports("avx512vbmi2")) {
    std::fprintf(stderr, "needs AVX512-VBMI2 (VPEXPANDB)\n");
    return 2;
  }

  for (const size_t value_bytes : value_list) {
    // The engine's geometry for the capacity: fold and stash registers 0
    // take the default rule's.
    tr::TreeShape shape;
    shape.stash_registers = stash_registers;
    tr::TreeGeometry tg;
    try {
      tg = tr::TreeGeometry::ForCapacity(capacity, fold, value_bytes, 0, shape);
    } catch (const std::exception& e) {
      std::fprintf(stderr, "no geometry for capacity %zu, V %zu: %s\n", capacity,
                   value_bytes, e.what());
      return 2;
    }
    Geo g;
    g.buckets = tg.path_buckets();
    if (g.buckets > tr::kReadPathBucketsPerRegister) {
      std::fprintf(stderr,
                   "capacity %zu at fold %u has a path of %u buckets, two "
                   "registers; the arms model a one-register path (at most "
                   "%u buckets): raise --fold\n",
                   capacity, tg.fold, g.buckets, tr::kReadPathBucketsPerRegister);
      return 2;
    }
    g.leaf_bits = tg.leaf_bits;
    g.fold = tg.fold;
    std::memcpy(g.match_bits, tg.path_match_bits, sizeof(g.match_bits));
    g.lines = tg.entry_bytes();
    g.value_bytes = value_bytes;
    g.row_bytes = (g.lines + 63) / 64 * 64;
    g.a = tg.shape.stash_registers;
    g.stash_lanes = 64 * g.a;
    g.lanes = g.stash_lanes + 64;
    g.chunks = tg.chunks();
    g.prefetch_ahead = tr::TreeKnobs{}.prefetch_ahead;
    const double load =
        static_cast<double>(tg.capacity()) / static_cast<double>(tg.slots());

    // Input pool for timing (ordinary sets of every pass kind) and one set
    // for verification.
    constexpr int kPool = 8;
    std::vector<WorkingSet> pool(kPool);
    Rng rng{seed * 0x9E3779B97F4A7C15ull + value_bytes};
    for (int k = 0; k < kPool; ++k) {
      Allocate(pool[k], g);
      Generate(pool[k], g, rng, load, k % 3, false);
    }
    WorkingSet vset;
    Allocate(vset, g);
    Out out;
    Allocate(out, g);

    for (const Arm& arm : kArms) {
      if (arm_name != "all" && arm_name != arm.name) continue;
      if (arm.prepare != nullptr) {
        for (WorkingSet& w : pool) arm.prepare(g, w);
      }
      // Verification: fresh sets, same sequence for every arm.
      bool ok = true;
      bool saw_overflow = false;
      Rng vrng{seed ^ 0xABCDEF12345ull};
      const unsigned vp = static_cast<unsigned>(std::min<uint64_t>(verify_passes, 1000000));
      for (unsigned p = 0; p < vp && ok; ++p) {
        const bool dense = p % 8 == 7;
        Generate(vset, g, vrng, load, static_cast<int>(p % 3), dense);
        if (arm.prepare != nullptr) arm.prepare(g, vset);
        const PassResult r = arm.fn(g, vset, out);
        if (arm.collect != nullptr) arm.collect(g, vset, out);
#if MICRORAM_ENIGMAP_ARM
        if (arm.valid_only) {
          ok = VerifyValid(g, vset, out, r, arm.name, p, &saw_overflow);
          continue;
        }
#endif
        ok = VerifyReadPath(g, vset, out, r, arm.name, p, &saw_overflow);
      }
      double ns = 0.0;
      if (ok && passes > 0) {
        for (uint64_t p = 0; p < std::min<uint64_t>(passes, 50); ++p) {
          (void)arm.fn(g, pool[p % kPool], out);
        }
        const auto t0 = std::chrono::steady_clock::now();
        unsigned sink = 0;
        for (uint64_t p = 0; p < passes; ++p) {
          const PassResult r = arm.fn(g, pool[p % kPool], out);
          sink += r.stash_count;
          asm volatile("" ::: "memory");
        }
        const double s = std::chrono::duration<double>(
                             std::chrono::steady_clock::now() - t0).count();
        ns = s * 1e9 / static_cast<double>(passes);
        asm volatile("" : : "r"(sink));
      }
      std::printf(
          "{\"arm\":\"%s\",\"capacity\":%zu,\"value_bytes\":%zu,"
          "\"key_bytes\":%zu,\"bucket_slots\":%u,\"path_levels\":%u,"
          "\"path_buckets\":%u,\"leaf_bits\":%u,\"fold\":%u,"
          "\"stash_registers\":%u,\"lanes\":%u,"
          "\"byte_lines\":%zu,\"ns_per_pass\":%.1f,\"passes\":%llu,"
          "\"verified_passes\":%u,\"verified_overflow_seen\":%s,"
          "\"status\":\"%s\",\"note\":\"%s\"}\n",
          arm.name, capacity, value_bytes, key_bytes, kZ, tg.path_levels(),
          g.buckets, g.leaf_bits, g.fold, g.a, g.lanes, g.lines, ns,
          static_cast<unsigned long long>(ok ? passes : 0), ok ? vp : 0u,
          saw_overflow ? "true" : "false", ok ? "ok" : "verify_failed", arm.note);
      std::fflush(stdout);
    }
  }
  return 0;
}
