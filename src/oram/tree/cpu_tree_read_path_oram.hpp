#pragma once

// THE TREE ORAM ENGINE (src/oram/tree/DESIGN.md): Path ORAM in its textbook
// schedule -- every access evicts the path it read and nothing else -- over
// four-slot buckets in a binary tree, with a working set of one or two path
// registers (a path of up to 16 or 32 buckets) and `A` stash registers.
//
// It knows nothing about keys.  An access names an entry by its uid and the
// leaf its position map says it is on, and hands in the fresh (uid, position)
// the entry will carry afterwards; CpuTreeMap (cpu_tree_map.hpp) is the layer
// that owns the position map and the PRF.
//
// ONE PASS PER ACCESS (DESIGN.md, "Read-path eviction").
//
//   * The path is stored in the working set LEAF FIRST, and the planner
//     (cpu_tree_read_path_eviction.hpp) gives path entries priority over
//     stash entries.  Path entries then only move down, never into the
//     stash, so the stash is not permuted: a destination path register takes
//     its sources from the stash and from path registers at or above it, and
//     a stash line changes only in the lane the accessed entry lands in --
//     the lowest free one, a SECRET lane, so every stash line of every stash
//     register is rewritten whole.
//   * The accessed entry's bytes are GATHERED from wherever it was (a
//     broadcast permute over each register pair, under the pair's
//     all-or-nothing mask), which is what `value_out` reads and what lands on
//     a read; a write lands `value_in` instead.
//
// THE TRACE (DESIGN.md, "Security").  Every address an access touches is a
// function of the leaf it was told to read and of the public geometry: the
// P buckets of that path, every chunk of each, in the same order, and the
// whole stash region line by line.  Which lane held the target, where an
// entry moves, whether the target existed at all and which lane it lands in
// are register data under masks and permute indices.  Every secret-masked
// move goes through the register-only forms of src/core/mov_intrinsics.hpp.
//
// THE FAILURE EVENT is a pass whose kept stash entries leave no lane free
// for the accessed entry -- more than `64 A - 1` -- and it throws
// StashOverflowError before the pass writes anything: the plan is computed
// from chunk 0 alone, and nothing is stored until it is accepted.  The
// caller that composes this engine with a position map (CpuTreeMap) has
// already updated the map, so it treats the exception as fatal to the
// instance.

#include <immintrin.h>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/tree/cpu_tree_layout.hpp"
#include "src/oram/tree/cpu_tree_payload_workers.hpp"
#include "src/oram/tree/cpu_tree_read_path_eviction.hpp"
#include "src/oram/tree/cpu_tree_transpose.hpp"

namespace microram {
namespace tree {

// The construction's failure event: a pass had more stash entries to keep
// than lanes to keep them in.  Thrown before the pass writes anything; see
// THE FAILURE EVENT.
struct StashOverflowError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

struct TreeKnobs {
  // Top levels folded into the stash region, so the root has 2^fold
  // children.  0 -- the default -- builds the default rule's fold for the
  // tree's depth (cpu_tree_layout.hpp's DefaultFold).
  unsigned fold = 0;
  // Halvings of the shape's target load (TreeShape::target_load), so each
  // unit doubles the tree slots per entry.  The load is what the stash tail
  // depends on, so the geometry carries it.
  unsigned leaf_scale = 0;
  // The sizing inputs and the stash width (cpu_tree_layout.hpp's TreeShape).
  // Must agree with the geometry's, which is where it is actually used; it
  // is here so a caller configures one struct.
  TreeShape shape;
  // Chunks ahead of the transposition to software-prefetch, per bucket.
  unsigned prefetch_ahead = 4;

  // ---------------------------------------------------------------------
  // The payload workers (DESIGN.md, "Parallel payload")
  // ---------------------------------------------------------------------
  //
  // Payload chunks are balanced across the selected workers (SliceLayout).
  // Public width selects none below payload_threshold, else
  // min(payload_max_threads, ceil(value_bytes / payload_threshold)): every
  // worker carries at most payload_threshold bytes of a slot while the cap
  // allows, and the slowest worker gates each access.  Zero runs
  // synchronously; the cap keeps large payloads within the core budget.
  unsigned payload_max_threads = 8;
  size_t payload_threshold = 32;
  // Microseconds a worker spins on the word it wants before it parks.  A
  // futex wake can cost several times a whole access, so a deployment either
  // dedicates the cores (spin long) or sizes this to its arrival gap.
  unsigned payload_spin_micros = 200;
  // Past the spin window, sleep on the word's cache line with MWAITX /
  // UMWAIT instead of parking (src/core/monitor_wait.hpp): the publisher's
  // store is the wake, no syscall, no IPI.  Off by default; a no-op where the
  // CPU does not offer it.  An option because deployed CPUs and hypervisors
  // differ in monitor-wait support.
  bool payload_monitor_wait = false;
  // Called once per worker thread at startup with the worker's index: where
  // to pin it.  A throw fails construction.
  std::function<void(unsigned)> payload_worker_init;
};

// Width and the core budget are public, so worker selection reveals no data.
inline unsigned PayloadThreadCount(size_t payload_size, const TreeKnobs& knobs) {
  const size_t t = knobs.payload_threshold;
  if (t == 0) throw std::invalid_argument("payload_threshold must be nonzero");
  if (payload_size < t) return 0;
  return static_cast<unsigned>(std::min<size_t>(
      knobs.payload_max_threads, payload_size / t + (payload_size % t != 0)));
}

// max = max(max, occupancy) as a hardened CMOV and an unconditional store:
// an `if (occupancy > max)` compiles to a conditional jump and a conditional
// store on two secrets.
inline void UpdateMaxOccupancy(unsigned occupancy, unsigned* max_occupancy) {
  *max_occupancy = static_cast<unsigned>(core::obliSelectU64(
      *max_occupancy, occupancy, occupancy > *max_occupancy));
}

// Both positions are leaves, below the geometry's leaves(): no bit at or
// above leaf_bits (Access's precondition).
struct TreeAccessRequest {
  uint64_t uid_old = 0;        // the entry to find
  uint64_t position_read = 0;  // the leaf whose path is read and evicted
  uint64_t uid_new = 0;        // what the landing lane will carry, ANY value
  uint64_t position_new = 0;   // the leaf it will carry, without the real bit
  bool write = false;          // land value_in instead of the found value
  bool create = false;         // land the entry even if nothing was found
  // Land nothing whatever was found: the entry is being erased.  It is a
  // flag rather than `uid_new == 0` because with the real bit in the
  // position (cpu_tree_layout.hpp) a uid of 0 is an ordinary uid.
  bool erase = false;
};

// THE CONFIGURATION BOUNDARY, in one place and BEFORE the engine reserves an
// arena or derives a slice layout, so an invalid hand-built geometry is
// rejected before its (possibly enormous) arena is asked for.  Returns the
// geometry so a member initializer can use it.
inline const TreeGeometry& ValidateReadPathConfiguration(const TreeGeometry& g,
                                                         const TreeKnobs& k) {
  // Fold 0 in the knobs asked the geometry for the default rule's fold,
  // which it carries; any other value must be the one built.
  if (k.fold != 0 && g.fold != k.fold) {
    throw std::invalid_argument("geometry.fold and knobs.fold disagree");
  }
  if (g.leaf_scale != k.leaf_scale) {
    throw std::invalid_argument("geometry.leaf_scale and knobs.leaf_scale disagree");
  }
  if (!g.shape.SameLayout(k.shape)) {
    throw std::invalid_argument("geometry.shape and knobs.shape disagree");
  }
  // The path must fit the working set and every size the arena derives must
  // be representable (cpu_tree_layout.hpp's ValidateGeometry); `ForCapacity`
  // guarantees both, a hand-built geometry guarantees neither.
  ValidateGeometry(g);
  RequireRuleStashRegisters(g.fold, g.leaf_bits, g.shape.stash_registers);
  // Fold 5's stash was measured only behind a one-register path, and the
  // requirement grows with the depth, so a deeper fold-5 tree is refused.
  if (g.fold == kMaxFold && g.path_buckets() > kReadPathBucketsPerRegister) {
    throw std::invalid_argument(
        "fold 5 needs a path of at most 16 buckets: its stash was measured "
        "only behind a one-register path");
  }
  if (g.chunk_begin != 0 || g.stored_chunks() != g.chunks()) {
    throw std::invalid_argument("a tree engine requires the whole entry geometry");
  }
  // A folded level is not stored, and its entries occupy the lanes the
  // stash's own tail needs.
  if (g.folded_slots() > g.shape.folded_slot_budget(g.fold)) {
    throw std::invalid_argument(
        "the folded levels of this geometry hold " +
        std::to_string(g.folded_slots()) +
        " slots, more of the stash than its budget leaves room for");
  }
  return g;
}

// What a plane applies in one pass: the plan, the landing entry's metadata,
// the value in and out, and -- on a payload worker -- the VALUE_READY word,
// released once the plane's slice of `value_out` is written
// (cpu_tree_payload_workers.hpp).
struct ReadPathPass {
  const ReadPathPlan* plan = nullptr;
  const uint8_t* meta = nullptr;      // the landing entry's 16 metadata bytes
  const uint8_t* value_in = nullptr;  // null: no write
  uint8_t* value_out = nullptr;       // null: no read-out
  std::atomic<uint64_t>* signal = nullptr;
  uint64_t signal_value = 0;
};

// Everything one byte line's routing needs beyond the line itself.
template <unsigned A>
struct ReadPathContext {
  uint8_t* stash_lines = nullptr;
  size_t stash_line0 = 0;
  const ReadPathPlan* plan = nullptr;
  const uint8_t* meta = nullptr;
  const uint8_t* value_in = nullptr;
  uint8_t* value_out = nullptr;
  INLINE uint8_t* StashLineFor(size_t i) const {
    return stash_lines + (i - stash_line0) * (64 * A);
  }
};

// One destination of a byte line, path register `b`'s or the gather's (b =
// 0): its source words x[F..W) (F = ReadPathFirstWord(b)) grouped into pairs
// from x[F] (ReadPathPlan), each pair one zero-masked VPERMT2B under its
// mask in `from`, OR-ed.  An odd last word is folded in by ONE merge-masked
// VPERMT2B whose first table is the accumulator -- tables (acc, x[W - 1]),
// indices 64 + lane under that word's mask -- which overwrites the
// accumulator in place, so it needs no copy and no OR.  Every destination
// lane has one source or none, so the accumulator's lanes under that mask
// are zero before the fold, and a lane with no source is in no mask and
// stays the zero the first, zero-masked, permute left: a dummy.
template <unsigned W, unsigned b>
INLINE __m512i PermuteReadPathWords(const __m512i* x, const uint64_t* from,
                                    __m512i index) {
  constexpr unsigned F = ReadPathFirstWord(b);
  constexpr unsigned kPairs = (W - F) / 2;
  static_assert(kPairs >= 1, "the first permute is a pair's, zero-masked");
  __m512i d = _mm512_maskz_permutex2var_epi8(from[0], x[F], index, x[F + 1]);
  for (unsigned q = 1; q < kPairs; ++q) {
    d = _mm512_or_si512(d, _mm512_maskz_permutex2var_epi8(
                               from[q], x[F + 2 * q], index, x[F + 2 * q + 1]));
  }
  if constexpr ((W - F) % 2 == 1) {
    d = _mm512_mask_permutex2var_epi8(d, from[kPairs], index, x[W - 1]);
  }
  return d;
}

// One byte line `i` through the pass.  `p0` and `p1` are the line in path
// registers 0 (positions 0..15, the deep end) and 1 (16..31), routed in
// place; B is how many the path has (ReadPathRegisters(P)).
//
// The source words are [path..., stash...] in priority order, and each
// destination and the gather are PermuteReadPathWords over theirs.  Per
// value line: B = 1, A = 3 is 2 + 2 permutes and 2 ORs; B = 1, A = 4 is 3 +
// 3 permutes and 2 ORs; B = 2, A = 3 is 3 + 2 + 3 permutes and 3 ORs; B = 2,
// A = 4 is 3 + 3 + 3 permutes and 5 ORs.
//
// A value line's gathered byte goes to `*byte` (non-null when the access
// reads out), which the caller writes to `value_out` once per chunk.
// `Gathered`: the line's byte was gathered already (a payload worker's
// gather-first pass) and is at `*byte`; it lands from there unless the
// access writes, and the line is routed without a second gather.
template <unsigned A, unsigned B, bool Meta, bool Gathered = false>
INLINE void RouteReadPathLine(size_t i, uint8_t* line, __m512i* p0,
                              __m512i* p1, const ReadPathContext<A>& c,
                              uint8_t* byte = nullptr) {
  constexpr unsigned W = B + A;
  const ReadPathPlan& plan = *c.plan;
  __m512i x[W];
  x[0] = *p0;
  if constexpr (B == 2) x[1] = *p1;
  for (unsigned a = 0; a < A; ++a) x[B + a] = core::obliLoad512(line + 64 * a);

  // The path destinations.  A destination lane in no pair's mask comes out
  // zero -- a dummy, on every line.
  const __m512i d0 = PermuteReadPathWords<W, 0>(x, plan.from[0], plan.index[0]);
  __m512i d1 = _mm512_setzero_si512();
  if constexpr (B == 2) {
    d1 = PermuteReadPathWords<W, 1>(x, plan.from[1], plan.index[1]);
  }

  // The landing entry's byte, and the stash.
  __m512i landing;
  if constexpr (Meta) {
    landing = core::obliPin512(_mm512_set1_epi8(static_cast<char>(c.meta[i])));
    // An entry that left the stash leaves an all-zero lane behind, as a
    // dummy destination on the path does.
    for (unsigned a = 0; a < A; ++a) {
      x[B + a] = core::obliMaskMov8(_mm512_setzero_si512(), plan.keep[a], x[B + a]);
    }
  } else if constexpr (Gathered) {
    const size_t v = i - kMetaBytes;
    landing = core::obliPin512(_mm512_set1_epi8(static_cast<char>(
        c.value_in != nullptr ? c.value_in[v] : *byte)));
  } else {
    const size_t v = i - kMetaBytes;
    // The gather: the target's byte in every lane, or zero when it was not
    // found (every pair mask is then zero).
    __m512i g = _mm512_setzero_si512();
    if (c.value_out != nullptr || c.value_in == nullptr) {
      g = PermuteReadPathWords<W, 0>(x, plan.target_from, plan.target_index);
    }
    if (byte != nullptr) {
      *byte = static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(g)));
    }
    landing = c.value_in != nullptr
                  ? core::obliPin512(
                        _mm512_set1_epi8(static_cast<char>(c.value_in[v])))
                  : g;
  }
  for (unsigned a = 0; a < A; ++a) {
    x[B + a] = core::obliMaskMov8(x[B + a], plan.land[a], landing);
    _mm512_store_si512(reinterpret_cast<void*>(line + 64 * a), x[B + a]);
  }
  *p0 = d0;
  if constexpr (B == 2) *p1 = d1;
}

// Whether a payload plane of `slice_chunks` chunks on a path of
// `path_buckets` buckets stages its slice and gathers first (PrepareSlice).
// Public geometry.  Only a short slice: staging stores the slice's byte
// lines and reads them back, and the gather reads the slice's stash lines
// once more before the routing does.  For a short slice the response gained
// by gathering early outweighs that extra work; for a long one (ten or more
// chunks per worker) it does not.  The limit of four chunks is a tuning
// constant chosen from value-width sweeps; four chunks at A = 4 keep ~20 KiB
// of staged and stash lines in flight, within L1.
inline constexpr size_t kReadPathMaxStagedChunks = 4;
inline constexpr bool ReadPathStagesSlice(unsigned path_buckets,
                                          size_t slice_chunks) {
  return path_buckets <= kReadPathBucketsPerRegister &&
         slice_chunks <= kReadPathMaxStagedChunks;
}

// The gather alone, for one path register: line `i`'s byte of the accessed
// entry (zero when it was not found), from the transposed path line at
// `path_line` and the line's stash registers at `line`.  The gather-first
// pass's first half; RouteReadPathLine<..., Gathered> is its second.
template <unsigned A>
INLINE uint8_t GatherReadPathLine(const __m512i* path_line, const uint8_t* line,
                                  const ReadPathPlan& plan) {
  __m512i x[1 + A];
  x[0] = core::obliLoad512(path_line);
  for (unsigned a = 0; a < A; ++a) x[1 + a] = core::obliLoad512(line + 64 * a);
  const __m512i g =
      PermuteReadPathWords<1 + A, 0>(x, plan.target_from, plan.target_index);
  return static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(g)));
}

// A chunk's gathered bytes, `cols` of them (public), to `value_out` in one
// store where the chunk is whole: two workers' slices of a 64-byte value
// share a cache line, so a store per byte line bounced it between them.
INLINE void WriteValueBytes(uint8_t* out, const uint8_t* bytes, size_t cols) {
  if (cols == 16) {
    _mm_storeu_si128(reinterpret_cast<__m128i*>(out),
                     _mm_loadu_si128(reinterpret_cast<const __m128i*>(bytes)));
  } else {
    std::memcpy(out, bytes, cols);
  }
}

// A PLANE: chunks [chunk_begin, chunk_begin + stored_chunks) of every
// bucket and the stash lines they carry, owned outright (cpu_tree_layout.hpp's
// A SLICE OF THE ENTRY).  The synchronous engine is one plane holding the
// whole entry; the threaded one is the metadata plane (chunk 0, which is the
// metadata exactly) on the caller plus one payload plane per worker.  Every
// plane applies the same plan to its own chunks.
class ReadPathPlane {
 public:
  using Plan = ReadPathPlan;
  using Pass = ReadPathPass;

  ReadPathPlane(const TreeGeometry& slice, const TreeKnobs& knobs)
      : storage_(TreeStorage::Create(slice)),
        prefetch_ahead_(knobs.prefetch_ahead) {
    std::memset(tile_, 0, sizeof(tile_));
    addr_.Init(storage_);
    // A short payload slice behind a one-register path gathers first
    // (PrepareSlice): its whole slice, transposed, and the bytes it gathers.
    if (slice.chunk_begin != 0 &&
        ReadPathStagesSlice(slice.path_buckets(), slice.stored_chunks())) {
      const size_t lines = slice.stored_chunks() * kReadPathBucketsPerRegister;
      prepared_lines_.reset(new PreparedLine[lines]);
      gathered_.assign(lines, 0);
    }
  }

  ReadPathPlane(const ReadPathPlane&) = delete;
  ReadPathPlane& operator=(const ReadPathPlane&) = delete;

  const TreeStorage& StorageForTest() const { return storage_; }
  size_t ArenaBytes() const { return storage_.arena_bytes(); }

  // Step 1 of a pass: this plane's buckets, leaf first, and its first chunks
  // in flight.  Public data only.
  void BeginPass(uint64_t position) {
    // Staged lines belong to the pass that staged them: a cancelled job
    // leaves them behind.
    prepared_ = false;
    LeafFirstBuckets(position);
    const unsigned P = storage_.geometry.path_buckets();
    const size_t S = storage_.geometry.stored_chunks();
    for (unsigned i = 0; i < P; ++i) {
      for (size_t a = 0; a < prefetch_ahead_ && a < S; ++a) {
        _mm_prefetch(reinterpret_cast<const char*>(bucket_[i] + a * kChunkBytes),
                     _MM_HINT_T0);
      }
    }
  }
  // A payload plane's whole slice loaded and transposed to byte lines while
  // its worker waits for the plan (public data only), so that the pass after
  // the plan begins at the permutes and gathers first.  A plane with no
  // staging (the metadata plane, or a two-register path) does nothing here
  // and runs the ordinary pass.
  void PrepareSlice() {
    if (prepared_lines_ == nullptr) return;
    const TreeGeometry& g = storage_.geometry;
    const size_t S = g.stored_chunks();
    const TransposeTables4& tt = DefaultTransposeTables4();
    WithPathBuckets(g.path_buckets(), [&](auto p) {
      constexpr unsigned P0 = decltype(p)::value;
      for (size_t t = 0; t < S; ++t) {
        __m512i r[kReadPathBucketsPerRegister];
        const bool more = t + prefetch_ahead_ < S;
        for (unsigned i = 0; i < P0; ++i) {
          r[i] = _mm512_load_si512(
              reinterpret_cast<const void*>(bucket_[i] + t * kChunkBytes));
          if (more) {
            _mm_prefetch(reinterpret_cast<const char*>(
                             bucket_[i] + (t + prefetch_ahead_) * kChunkBytes),
                         _MM_HINT_T0);
          }
        }
        for (unsigned i = P0; i < kReadPathBucketsPerRegister; ++i) {
          r[i] = _mm512_setzero_si512();
        }
        TransposeGroupForwardExact<P0>(tt, r);
        PreparedLine* out = prepared_lines_.get() + t * kReadPathBucketsPerRegister;
        for (unsigned i = 0; i < kReadPathBucketsPerRegister; ++i) {
          _mm512_store_si512(&out[i].v, r[i]);
        }
      }
    });
    prepared_ = true;
  }

  // The plane holding chunk 0 only: load and transpose it, so the planner
  // can read both path registers' metadata lines out of the tile.
  void TransposeFirstChunk() {
    if (Upper()) {
      TransposeFirstChunkImpl<true>();
    } else {
      TransposeFirstChunkImpl<false>();
    }
  }
  const __m512i* PathMetaLines() const { return tile_; }
  const uint8_t* StashMetaLines() const { return storage_.StashLine(0); }

  // The rest of the pass on this plane's chunks.  A is public and fixed for
  // the life of the ORAM, and so is whether the path reaches register 1.
  void ApplyPass(const ReadPathPass& job) {
    if (storage_.geometry.shape.stash_registers == 4) {
      if (Upper()) return ApplyPassImpl<4, true>(job);
      return ApplyPassImpl<4, false>(job);
    }
    if (Upper()) return ApplyPassImpl<3, true>(job);
    ApplyPassImpl<3, false>(job);
  }

 private:
  bool Upper() const {
    return storage_.geometry.path_buckets() > kReadPathBucketsPerRegister;
  }

  // The path's buckets, LEAF FIRST: position `m` is the bucket the planner
  // fills at step `m`, `m` levels above the leaf -- PathAddressing's
  // root-first list reversed.
  void LeafFirstBuckets(uint64_t position) {
    const unsigned P = storage_.geometry.path_buckets();
    uint8_t* root_first[kMaxPathLevels];
    addr_.Buckets(position, root_first);
    for (unsigned m = 0; m < P; ++m) bucket_[m] = root_first[P - 1 - m];
  }

  // Path register 0's tile is tile_[0..15], register 1's tile_[16..31].
  // Without register 1 its tile stays the zeros of the constructor, which
  // the planner reads as sixteen empty buckets.
  template <bool Upper>
  void TransposeFirstChunkImpl() {
    const TreeGeometry& g = storage_.geometry;
    constexpr unsigned kLive = Upper ? 2 * kReadPathBucketsPerRegister
                                     : kReadPathBucketsPerRegister;
    LoadChunkInto<kLive>(tile_, bucket_, g.path_buckets(), 0,
                         g.stored_chunks(), prefetch_ahead_);
    TransposeTiles<Upper, true>(g.path_buckets());
  }
  template <bool Upper, bool ToLines>
  INLINE void TransposeTiles(unsigned P) {
    const TransposeTables4& t = DefaultTransposeTables4();
    WithPathBuckets(Upper ? kReadPathBucketsPerRegister : P, [&](auto p) {
      if constexpr (ToLines) {
        TransposeToLines4Exact<decltype(p)::value>(tile_, t);
      } else {
        TransposeToChunks4Exact<decltype(p)::value>(tile_, t);
      }
    });
    if constexpr (Upper) {
      WithPathBuckets(P - kReadPathBucketsPerRegister, [&](auto p) {
        if constexpr (ToLines) {
          TransposeToLines4Exact<decltype(p)::value>(
              tile_ + kReadPathBucketsPerRegister, t);
        } else {
          TransposeToChunks4Exact<decltype(p)::value>(
              tile_ + kReadPathBucketsPerRegister, t);
        }
      });
    }
  }

  static INLINE void Signal(const ReadPathPass& job) {
    if (job.signal != nullptr) {
      job.signal->store(job.signal_value, std::memory_order_release);
    }
  }

  template <unsigned A, bool Upper>
  void ApplyPassImpl(const ReadPathPass& job) {
    const TreeGeometry& g = storage_.geometry;
    const unsigned P = g.path_buckets();
    const size_t S = g.stored_chunks();
    const size_t E = g.entry_bytes();
    const size_t first = g.chunk_begin;
    constexpr size_t kCols = kChunkColumns;
    ReadPathContext<A> ctx;
    ctx.stash_lines = storage_.stash_lines;
    ctx.stash_line0 = storage_.stash_line0;
    ctx.plan = job.plan;
    ctx.meta = job.meta;
    ctx.value_in = job.value_in;
    ctx.value_out = job.value_out;
    if (prepared_) {
      prepared_ = false;
      ApplyPreparedPass<A>(job, ctx);
      return;
    }
    size_t t_begin = 0;
    if (first == 0) {
      // The entry's chunk 0 is the metadata exactly and is already
      // transposed in the tile for the planner, so it is routed there.
      uint8_t* const stash = ctx.StashLineFor(0);
      for (size_t c = 0; c < kCols; ++c) {
        RouteReadPathLine<A, Upper ? 2 : 1, true>(
            c, stash + c * 64 * A, &tile_[c],
            &tile_[kReadPathBucketsPerRegister + c], ctx);
      }
      if (S == 1) Signal(job);
      TransposeTiles<Upper, false>(P);
      StoreChunkFrom(tile_, bucket_, P, 0);
      t_begin = 1;
    }
    if (t_begin == S) return;
    // Every later chunk is value only, and runs through registers
    // (RunValueChunk), dispatched once on the path's length.  The plane's
    // slice of the value is complete after its last chunk's routing, which
    // is where the signal goes out -- before that chunk's write-back.
    if constexpr (Upper) {
      WithPathBuckets(P - kReadPathBucketsPerRegister, [&](auto p1) {
        for (size_t t = t_begin; t < S; ++t) {
          RunValueChunk<A, kReadPathBucketsPerRegister, decltype(p1)::value>(
              t, S, E, first, ctx, t + 1 == S ? &job : nullptr);
        }
      });
    } else {
      WithPathBuckets(P, [&](auto p0) {
        for (size_t t = t_begin; t < S; ++t) {
          RunValueChunk<A, decltype(p0)::value, 0>(
              t, S, E, first, ctx, t + 1 == S ? &job : nullptr);
        }
      });
    }
  }

  // Arena chunk `t` (entry chunk `first + t`, value only), start to finish.
  // Path register 1's tile (`P1` buckets, none on a path of at most 16)
  // stays in registers from its load to its store; register 0's (`P0`) is
  // sixteen more registers than the file has room for beside it, so with two
  // tiles it is staged through `tile_` once each way.  On one tile it stays
  // in registers too.  `signal` non-null: release it after the routing.
  template <unsigned A, unsigned P0, unsigned P1>
  INLINE void RunValueChunk(size_t t, size_t S, size_t E, size_t first,
                            const ReadPathContext<A>& ctx,
                            const ReadPathPass* signal) {
    constexpr size_t kCols = kChunkColumns;
    constexpr unsigned kTile = kReadPathBucketsPerRegister;
    const TransposeTables4& tt = DefaultTransposeTables4();
    const size_t base = (first + t) * kCols;
    const size_t cols = std::min<size_t>(kCols, E - base);
    const size_t off = t * kChunkBytes;
    const bool more = t + prefetch_ahead_ < S;
    const size_t poff = (t + prefetch_ahead_) * kChunkBytes;
    const auto load = [&](__m512i* r, unsigned from, unsigned n) {
      for (unsigned i = 0; i < n; ++i) {
        r[i] = _mm512_load_si512(
            reinterpret_cast<const void*>(bucket_[from + i] + off));
        if (more) {
          _mm_prefetch(reinterpret_cast<const char*>(bucket_[from + i] + poff),
                       _MM_HINT_T0);
        }
      }
      for (unsigned i = n; i < kTile; ++i) r[i] = _mm512_setzero_si512();
    };
    const auto store = [&](const __m512i* r, unsigned from, unsigned n) {
      for (unsigned i = 0; i < n; ++i) {
        _mm512_store_si512(reinterpret_cast<void*>(bucket_[from + i] + off),
                           r[i]);
      }
    };
    uint8_t* const stash = ctx.StashLineFor(base);
    alignas(16) uint8_t bytes[kTile];
    uint8_t* const out = ctx.value_out != nullptr ? bytes : nullptr;
    if constexpr (P1 == 0) {
      __m512i r[kTile];
      load(r, 0, P0);
      TransposeGroupForwardExact<P0>(tt, r);
      __m512i none = _mm512_setzero_si512();
      for (unsigned i = 0; i < kTile; ++i) {
        // `cols` is public: a partial last chunk's padding lines pass through.
        if (i < cols) {
          RouteReadPathLine<A, 1, false>(base + i, stash + i * 64 * A,
                                             &r[i], &none, ctx,
                                             out != nullptr ? out + i : nullptr);
        }
      }
      if (out != nullptr) WriteValueBytes(ctx.value_out + base - kMetaBytes, out, cols);
      if (signal != nullptr) Signal(*signal);
      TransposeGroupInverseExact<P0>(tt, r);
      store(r, 0, P0);
    } else {
      {
        __m512i r0[kTile];
        load(r0, 0, kTile);
        TransposeGroupForwardExact<kTile>(tt, r0);
        for (unsigned i = 0; i < kTile; ++i) _mm512_store_si512(tile_ + i, r0[i]);
      }
      __m512i r[kTile];
      load(r, kTile, P1);
      TransposeGroupForwardExact<P1>(tt, r);
      for (unsigned i = 0; i < kTile; ++i) {
        if (i < cols) {
          __m512i p0 = _mm512_load_si512(tile_ + i);
          RouteReadPathLine<A, 2, false>(base + i, stash + i * 64 * A, &p0,
                                            &r[i], ctx,
                                            out != nullptr ? out + i : nullptr);
          _mm512_store_si512(tile_ + i, p0);
        }
      }
      if (out != nullptr) WriteValueBytes(ctx.value_out + base - kMetaBytes, out, cols);
      if (signal != nullptr) Signal(*signal);
      TransposeGroupInverseExact<P1>(tt, r);
      store(r, kTile, P1);
      {
        __m512i r0[kTile];
        for (unsigned i = 0; i < kTile; ++i) r0[i] = _mm512_load_si512(tile_ + i);
        TransposeGroupInverseExact<kTile>(tt, r0);
        store(r0, 0, kTile);
      }
    }
  }

  // A payload plane's pass after PrepareSlice, GATHER FIRST: every line's
  // byte of the accessed entry out of the transposed slice and the stash,
  // `value_out` written and the signal released, and only then the
  // routing, the inverse transposition and the write-back -- which the
  // caller does not wait for.  The same plan, the same stores in the same
  // order as RunValueChunk's, so the trace is unchanged; only when the
  // signal goes out moves.
  template <unsigned A>
  void ApplyPreparedPass(const ReadPathPass& job, const ReadPathContext<A>& ctx) {
    const TreeGeometry& g = storage_.geometry;
    const size_t S = g.stored_chunks();
    const size_t E = g.entry_bytes();
    const size_t first = g.chunk_begin;
    constexpr size_t kCols = kChunkColumns;
    constexpr unsigned kTile = kReadPathBucketsPerRegister;
    const PreparedLine* const lines = prepared_lines_.get();
    uint8_t* const gathered = gathered_.data();
    if (ctx.value_out != nullptr || ctx.value_in == nullptr) {
      for (size_t t = 0; t < S; ++t) {
        const size_t base = (first + t) * kCols;
        const size_t cols = std::min<size_t>(kCols, E - base);
        const uint8_t* const stash = ctx.StashLineFor(base);
        for (unsigned i = 0; i < kTile; ++i) {
          if (i < cols) {
            gathered[t * kTile + i] = GatherReadPathLine<A>(
                &lines[t * kTile + i].v, stash + i * 64 * A, *ctx.plan);
          }
        }
        if (ctx.value_out != nullptr) {
          WriteValueBytes(ctx.value_out + base - kMetaBytes, gathered + t * kTile,
                          cols);
        }
      }
    }
    Signal(job);
    const TransposeTables4& tt = DefaultTransposeTables4();
    WithPathBuckets(g.path_buckets(), [&](auto p) {
      constexpr unsigned P0 = decltype(p)::value;
      for (size_t t = 0; t < S; ++t) {
        const size_t base = (first + t) * kCols;
        const size_t cols = std::min<size_t>(kCols, E - base);
        uint8_t* const stash = ctx.StashLineFor(base);
        __m512i r[kTile];
        for (unsigned i = 0; i < kTile; ++i) {
          r[i] = core::obliLoad512(&lines[t * kTile + i].v);
        }
        __m512i none = _mm512_setzero_si512();
        for (unsigned i = 0; i < kTile; ++i) {
          if (i < cols) {
            RouteReadPathLine<A, 1, false, true>(base + i, stash + i * 64 * A,
                                                 &r[i], &none, ctx,
                                                 gathered + t * kTile + i);
          }
        }
        TransposeGroupInverseExact<P0>(tt, r);
        for (unsigned i = 0; i < P0; ++i) {
          _mm512_store_si512(
              reinterpret_cast<void*>(bucket_[i] + t * kChunkBytes), r[i]);
        }
      }
    });
  }

  TreeStorage storage_;
  unsigned prefetch_ahead_;
  PathAddressing addr_;
  alignas(64) __m512i tile_[2 * kReadPathBucketsPerRegister];
  uint8_t* bucket_[kMaxPathLevels] = {};
  // Gather first (PrepareSlice): the slice's byte lines, chunk by chunk, and
  // the accessed entry's bytes gathered from them; `prepared_` while the
  // lines are this pass's.
  struct alignas(64) PreparedLine {
    __m512i v;
  };
  std::unique_ptr<PreparedLine[]> prepared_lines_;
  std::vector<uint8_t> gathered_;
  bool prepared_ = false;
};

class CpuReadPathOram {
 public:
  // The worker count from the knobs (PayloadThreadCount); CpuTreeMap builds
  // its tree this way.
  CpuReadPathOram(const TreeGeometry& geometry, const TreeKnobs& knobs = {})
      : CpuReadPathOram(geometry, knobs,
                        PayloadThreadCount(geometry.value_bytes, knobs)) {}

  // Explicit K: 0 is the synchronous engine, one plane.
  CpuReadPathOram(const TreeGeometry& geometry, const TreeKnobs& knobs,
                  unsigned payload_workers)
      : CpuReadPathOram(geometry, knobs, payload_workers, WorkerKnobsFrom(knobs)) {}

  // Explicit K and worker knobs, for tests: the pool's stage observer and
  // thread-creation fault are only reachable this way.
  CpuReadPathOram(const TreeGeometry& geometry, const TreeKnobs& knobs,
                  unsigned payload_workers, PayloadWorkerKnobs worker_knobs)
      // Validated BEFORE any plane's arena is reserved.
      : geometry_(ValidateReadPathConfiguration(geometry, knobs)),
        knobs_(knobs),
        layout_(SliceLayout::For(geometry.chunks(), payload_workers)) {
    planes_.reserve(layout_.ranges.size());
    for (const SliceLayout::Range& r : layout_.ranges) {
      planes_.push_back(std::make_unique<ReadPathPlane>(
          geometry_.ForSlice(r.begin, r.count), knobs_));
    }
    if (layout_.payload_planes() == 0) return;
    std::vector<ReadPathPlane*> payload;
    for (size_t i = 1; i < planes_.size(); ++i) payload.push_back(planes_[i].get());
    pool_ = std::make_unique<PayloadWorkerPoolT<ReadPathPlane>>(
        std::move(payload), std::move(worker_knobs));
    for (unsigned j = 0; j < 2; ++j) {
      pool_->slot(j).value_copy.assign(geometry_.value_bytes, 0);
    }
  }

  ~CpuReadPathOram() {
    if (pool_ != nullptr && published_ != 0) {
      try {
        pool_->WaitDone(published_);
      } catch (...) {
        // A failed worker is already stopped; the pool joins it either way.
      }
    }
  }

  CpuReadPathOram(const CpuReadPathOram&) = delete;
  CpuReadPathOram& operator=(const CpuReadPathOram&) = delete;

  const TreeGeometry& geometry() const { return geometry_; }
  const TreeKnobs& knobs() const { return knobs_; }
  size_t Capacity() const { return geometry_.capacity(); }
  size_t ValueBytes() const { return geometry_.value_bytes; }
  size_t ArenaBytes() const {
    size_t total = 0;
    for (const auto& p : planes_) total += p->ArenaBytes();
    return total;
  }
  // Lanes the stash region has; the accessed entry needs one of them free.
  unsigned StashCapacity() const { return geometry_.stash_capacity(); }
  uint64_t AccessCount() const { return access_count_; }
  // SECRET, for measurements and tests, kept with a hardened CMOV
  // (UpdateMaxOccupancy): the stash region's occupancy after the last pass,
  // its maximum, and the overflows a caller caught.
  unsigned StashOccupancy() const { return stash_occupancy_; }
  unsigned MaxStashOccupancy() const { return max_stash_occupancy_; }
  uint64_t Overflows() const { return overflows_; }
  bool Threaded() const { return pool_ != nullptr; }
  unsigned PayloadPlanes() const { return layout_.payload_planes(); }
  const ReadPathPlane& plane(size_t i) const { return *planes_[i]; }
  size_t PlaneCount() const { return planes_.size(); }
  core::MonitorWaitKind MonitorWaitKind() const {
    return pool_ != nullptr ? pool_->monitor_wait_kind()
                            : core::MonitorWaitKind::kNone;
  }
  // Every worker has retired every job published so far; storage is well
  // defined to a reader only after this.
  void Drain() {
    if (pool_ != nullptr && published_ != 0) pool_->WaitDone(published_);
  }
  // The threaded form copies `value_in` into the job before it is published
  // (no caller memory is referenced after the access returns), so an aliased
  // exchange buffer is safe; the synchronous one writes a value line out and
  // reads the same line of the input right after, so it is not.
  bool CapturesValueInput() const { return pool_ != nullptr; }
  // The metadata plane: the whole entry in the synchronous engine.
  const TreeStorage& StorageForTest() const { return planes_[0]->StorageForTest(); }

  // One access: read path `position_read`, take the entry `uid_old` out of
  // the working set, evict everything else as deep as it goes with path
  // entries first, write the path back, and land (uid_new, position_new,
  // value) -- the found value, or `value_in` under `write` -- in the lowest
  // free stash lane iff something was found or `create` is set, and the
  // access does not `erase`.  `value_out` receives the value before the
  // write, or zeros if nothing was found.  Returns found.
  //
  // PRECONDITION: `position_read` and `position_new` are below
  // geometry().leaves().  A higher bit is not masked off: the path read is
  // that of the low leaf_bits, but the planner compares the full position,
  // so no entry of that path is placed and the pass silently drops them.
  // CpuTreeMap draws every position below leaves(); checked builds assert it.
  bool Access(const TreeAccessRequest& req, const uint8_t* value_in,
              uint8_t* value_out) {
    assert(req.position_read < geometry_.leaves() &&
           req.position_new < geometry_.leaves());
    if (pool_ != nullptr) return AccessThreaded(req, value_in, value_out);
    const bool found = SerialPass(req, req.write ? value_in : nullptr, value_out);
    ++access_count_;
    return found;
  }

 private:
  static PayloadWorkerKnobs WorkerKnobsFrom(const TreeKnobs& knobs) {
    PayloadWorkerKnobs wk;
    wk.spin_micros = knobs.payload_spin_micros;
    wk.monitor_wait = knobs.payload_monitor_wait;
    wk.init = knobs.payload_worker_init;
    return wk;
  }

  // The plan from the metadata plane's lines, and the failure event before
  // anything is written; then the landing entry's metadata.  The land masks
  // are zero when nothing lands, so those bytes only reach a real lane.
  void Plan(ReadPathPlane& meta_plane, const TreeAccessRequest& req,
            ReadPathPlan* plan, uint8_t* meta) {
    ReadPathEvictionInput in;
    in.stash_meta = meta_plane.StashMetaLines();
    in.path_meta = meta_plane.PathMetaLines();
    in.target_uid = req.uid_old;
    in.has_target = true;
    in.create = req.create;
    in.erase = req.erase;
    in.path_position = req.position_read;
    in.leaf_bits = geometry_.leaf_bits;
    in.path_buckets = geometry_.path_buckets();
    in.level_match_bits = geometry_.path_match_bits;
    const bool two = ReadPathRegisters(in.path_buckets) == 2;
    if (geometry_.shape.stash_registers == 4) {
      if (two) {
        PlanReadPath<4, 2>(in, plan);
      } else {
        PlanReadPath<4, 1>(in, plan);
      }
    } else if (two) {
      PlanReadPath<3, 2>(in, plan);
    } else {
      PlanReadPath<3, 1>(in, plan);
    }
    // The one permitted secret-dependent branch: the failure event itself.
    if (plan->overflow) {
      ++overflows_;
      throw StashOverflowError(
          "tree ORAM stash overflow: no stash lane free for the accessed "
          "entry (the tree ORAM's failure event)");
    }
    stash_occupancy_ = plan->occupancy;
    UpdateMaxOccupancy(stash_occupancy_, &max_stash_occupancy_);
    const uint64_t pos_new = EncodeStoredPosition(req.position_new);
    std::memcpy(meta, &req.uid_new, 8);
    std::memcpy(meta + 8, &pos_new, 8);
  }

  // One pass with every plane on the caller.
  bool SerialPass(const TreeAccessRequest& req, const uint8_t* value_in,
                  uint8_t* value_out) {
    for (auto& p : planes_) p->BeginPass(req.position_read);
    ReadPathPlane& meta_plane = *planes_[0];
    meta_plane.TransposeFirstChunk();
    ReadPathPlan plan;
    alignas(16) uint8_t meta[kMetaBytes];
    Plan(meta_plane, req, &plan, meta);
    ReadPathPass pass;
    pass.plan = &plan;
    pass.meta = meta;
    pass.value_in = value_in;
    pass.value_out = value_out;
    for (auto& p : planes_) p->ApplyPass(pass);
    return plan.found;
  }

  // ONE ACCESS, THREADED (cpu_tree_payload_workers.hpp).  Publish the leaf
  // (the workers' loads go out while this thread transposes chunk 0 and
  // plans), plan, publish the plan (or nothing: an overflow is a cancelled
  // job, retired below), route chunk 0 here, and return when every worker's
  // slice of the value is written -- their write-backs run on.
  bool AccessThreaded(const TreeAccessRequest& req, const uint8_t* value_in,
                      uint8_t* value_out) {
    if (pool_->Failed()) {
      throw std::runtime_error(
          "tree ORAM payload worker failed; this instance cannot accept "
          "further accesses");
    }
    const uint64_t job = published_ + 1;
    try {
      return AccessThreadedUnguarded(req, value_in, value_out, job);
    } catch (...) {
      // The workers wait for this job's plan word; `run_pass` is false
      // unless the plan went out, so publishing it retires a cancelled job.
      if (published_ >= job) {
        pool_->PublishPlan(job);
        try {
          pool_->WaitDone(job);
        } catch (...) {
          // The pool latches a worker's failure and refuses the next access.
        }
      }
      throw;
    }
  }

  bool AccessThreadedUnguarded(const TreeAccessRequest& req,
                               const uint8_t* value_in, uint8_t* value_out,
                               uint64_t job) {
    PayloadJobSlotT<ReadPathPlane>& slot = pool_->slot(job);
    slot.read_leaf = req.position_read;
    slot.run_pass = false;
    const bool write = req.write && value_in != nullptr;
    if (write) {
      std::memcpy(slot.value_copy.data(), value_in, geometry_.value_bytes);
    }
    published_ = job;
    pool_->PublishLeaves(job);

    ReadPathPlane& meta_plane = *planes_[0];
    meta_plane.BeginPass(req.position_read);
    meta_plane.TransposeFirstChunk();
    Plan(meta_plane, req, &slot.plan, slot.meta);
    slot.pass.plan = &slot.plan;
    slot.pass.meta = slot.meta;
    slot.pass.value_in = write ? slot.value_copy.data() : nullptr;
    slot.pass.value_out = value_out;
    slot.pass.signal = nullptr;
    slot.run_pass = true;
    pool_->PublishPlan(job);
    // Chunk 0 is metadata only, so the metadata plane never touches a value
    // byte here.
    meta_plane.ApplyPass(slot.pass);
    ++access_count_;
    pool_->WaitValueReady(job);
    return slot.plan.found;
  }

  TreeGeometry geometry_;
  TreeKnobs knobs_;
  SliceLayout layout_;
  std::vector<std::unique_ptr<ReadPathPlane>> planes_;
  std::unique_ptr<PayloadWorkerPoolT<ReadPathPlane>> pool_;
  uint64_t published_ = 0;
  uint64_t access_count_ = 0;
  uint64_t overflows_ = 0;
  unsigned stash_occupancy_ = 0;
  unsigned max_stash_occupancy_ = 0;
};

}  // namespace tree
}  // namespace microram
