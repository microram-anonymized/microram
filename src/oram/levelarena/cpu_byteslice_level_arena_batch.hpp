#pragma once

// THE LEVEL-ARENA BATCH PATH: one participant's scratch, and the wave cascade
// that probes a whole tile of lanes against one plan.  DESIGN.md ("Batches
// and near/far placement") states the contract; this header implements the
// cascade, the engine header the API and the chunking.
//
// WHY A BATCH IS NOT A LOOP OF ACCESSES.  Table i's key lines decide table
// i+1's address, so one access is a chain of serially dependent DRAM misses
// and nothing the core does can overlap them.  `m` accesses issued together
// are the same chain `m` times side by side: the cascade runs a WAVE over the
// lanes at each entry -- all lanes' matches, then all lanes' next targets and
// prefetches, then all lanes' extracts -- so one DRAM-resident table costs one
// round trip for the whole tile instead of one per lane.  This engine's dense
// side gains twice over, and that is the part that is specific to it: a dense
// entry is scanned in FULL by every access, so its key lines are loaded once
// per bucket and matched against every lane from registers, and its value
// lines are extracted for all lanes with one permute per line.  The serial
// cascade pays `(r0 s)/2 + s` buckets per access for the dense prefix
// (which is why the scalar path's default insertion unit is one bucket: a
// longer unit lengthens the scan every access pays); a batch LOADS them once
// per chunk. Large chunks also share direct-slot key matching; extraction is one permute per value line. The remaining
// per-lane gate, freshness and removal bookkeeping is unchanged.
//
// WHAT IS REUSED AND WHAT IS NOT.  Everything engine-independent lives in
// `table/`: `DedupBatchLanes`, `ResolveHashedProbeAddressesBatch`,
// `ExtractDenseWave`, `ExtractHashedWaveIntoSliced`, `ForwardBatchLane` and
// the parallel-tile banks are called from here unchanged.  What is written
// here is the cascade LOOP, because this engine's plan has its own shape:
// every tier is an ordinary entry of the plan, the only removable table
// is the current online-stash unit -- which is a multi-bucket RUN whenever
// `s > 1` -- and the dense prefix is `q + 2` entries of up to `r0 s` buckets
// each rather than a FIFO of one-bucket stashes.
//
// SECURITY, which is the same statement the serial cascade makes.  Per chunk:
// every dense bucket of the plan scanned once per lane, exactly one bucket of
// every hashed table touched per lane, `m * tables` dummy counters consumed,
// the same AES blocks, prefetches and extracts whatever the keys are.  A lane
// that repeats an EARLIER lane's key does not probe for real -- two equal keys
// hash to one bucket under one nonce, and a repeated bucket is the statement
// that two requests were equal -- so it starts out `found` with its gate shut
// and issues an independent dummy at every hashed table, exactly like a lane
// whose key was found at the top.  Its answer comes from the forwarding chain
// instead.  Every memory index below is a PUBLIC lane number; the secrets --
// which lanes are duplicates, of which earlier lane, what matched where --
// live in registers and drive CMOVs and permute controls.
//
// REMOVAL IS DEFERRED: the extract
// writes its mask clear into a per-bucket scratch word, the wave ORs the
// removable run's matches into those words, and they are applied once after
// the cascade.  Lanes holding distinct keys match disjoint slots and duplicate
// lanes are gated to zero, so the word applied is the one the serial path
// would have left -- and no lane's cascade stores into a table another
// participant is reading.

#include <immintrin.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/core/release_guard.hpp"
#include "src/oram/table/cpu_byteslice_probe_plan.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_bytes.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"
#include "src/oram/table/cpu_byteslice_batch_config.hpp"
#include "src/oram/table/cpu_byteslice_batch_layout.hpp"
#include "src/oram/table/cpu_byteslice_batch_probe.hpp"
#include "src/oram/table/cpu_byteslice_dense_match.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_parallel_batch.hpp"
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "src/oram/table/cpu_byteslice_probe_addresses.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

enum class BatchStage : size_t {
  kPrepare, kMetadata, kAddresses, kDense, kMerge, kCascade, kForward,
  kCommit, kJoinedPhase, kCount
};
inline constexpr size_t kBatchStages = static_cast<size_t>(BatchStage::kCount);
inline const char* BatchStageName(size_t stage) {
  constexpr const char* names[] = {"prepare", "metadata", "addresses", "dense",
      "merge", "cascade", "forward", "commit", "joined-phase"};
  return names[stage];
}
struct BatchStageStats {
  uint64_t nanos = 0, calls = 0, max_nanos = 0;
};
// One writer per participant; read only between calls. Profiling is opt-in:
// clock reads can materially affect short jobs and are not dispatch inputs.
struct alignas(64) BatchWorkStats {
  std::array<BatchStageStats, kBatchStages> stages{};
};
class BatchStageTimer {
 public:
  explicit BatchStageTimer(BatchStageStats* stats) : stats_(stats) {
    if (stats_) start_ = std::chrono::steady_clock::now();
  }
  ~BatchStageTimer() {
    if (!stats_) return;
    const uint64_t nanos = static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - start_).count());
    stats_->nanos += nanos;
    ++stats_->calls;
    stats_->max_nanos = std::max(stats_->max_nanos, nanos);
  }
 private:
  BatchStageStats* stats_;
  std::chrono::steady_clock::time_point start_;
};

// HOW A BATCH IS EXECUTED.  The two shapes differ in who runs the cascade and
// in nothing else: both dedup, probe one plan under one reader epoch, forward
// in lane order and commit in lane order, and both must produce the answers a
// serial sequence of the same requests would.
// A deployment tuning choice: cache topology and core placement determine
// whether chunked execution or parallel tiles are faster.
enum class BatchExecutionShape : uint8_t {
  // ONE THREAD, one tile, `batch_lanes` lanes at a time.  This is the shape
  // every correctness fixture is written against, because it has no
  // interleaving to reason about, and it is the control the parallel shape
  // is compared with.
  kChunkedCascade,
  // ONE TILE PER PARTICIPANT, `batch_lanes` lanes each, probed and forwarded
  // side by side and committed by the request thread in lane order.  The
  // combined width is `participants * batch_lanes`.
  kParallelTiles,
};

inline const char* BatchExecutionShapeName(BatchExecutionShape shape) {
  return shape == BatchExecutionShape::kChunkedCascade ? "chunked"
                                                       : "parallel-tiles";
}

// WHERE A LANE'S PROBE RESULT LANDS.  Both enumerators are implemented: the
// default (`kSlicedPlaceAtLane`, which places each lane's value straight into
// a byte-sliced accumulator) and the row-per-lane control (`kRows`).
//
// The vocabulary is `BatchResultLayout` and not a second enum on purpose:
// "the hashed extract places each lane's byte at its own accumulator column"
// is one idea, and a private spelling of it would be one more thing to keep
// in step with the kernels in `table/` that implement it.

// ---------------------------------------------------------------------------
// One participant's tile
// ---------------------------------------------------------------------------

class BatchClearMasks {
 public:
  void Resize(size_t size) {
    size_ = size;
    data_ = AllocateAligned64(
        CheckedSizeMul(size, sizeof(uint64_t), "batch masks"));
    std::fill(begin(), end(), uint64_t{0});
  }
  size_t size() const { return size_; }
  uint64_t* begin() { return reinterpret_cast<uint64_t*>(data_.get()); }
  uint64_t* end() { return begin() + size_; }
  uint64_t& operator[](size_t i) { assert(i < size_); return begin()[i]; }
 private:
  size_t size_ = 0;
  Aligned64Ptr data_;
};

// Everything one thread needs to carry `kMaxBatchLanes` lanes from a caller's
// requests to the entries they insert, allocated ONCE at construction: a batch
// on the request path must not reach the allocator, and the byte bill must be
// able to predict this without knowing how wide a particular call is.  The
// lane arrays are always 64 wide whatever `batch_lanes` is set to, because the
// eight-lane extract groups read a whole group and the mask words are 64 bits
// either way; `lanes` is how many of them a given job uses.
struct LevelArenaBatchTile {
  // ---- the requests of the job in flight, copied so the two request forms
  // (byte keys and word keys) share one path ----
  std::vector<KeyWords> key;
  std::vector<BatchOp> op;
  std::vector<uint8_t> insert;
  std::vector<const uint8_t*> value_in;
  std::vector<uint8_t*> value_out;
  size_t lanes = 0;

  // ---- the cascade's per-lane registers ----
  std::vector<uint64_t> found, gate, match, take, run_take, dense_taken;
  std::vector<uint8_t*> bucket, next_bucket;
  std::vector<uint64_t*> mask, next_mask;

  BatchProbeScratch probe;   // the 2h candidate pair of every lane
  BatchDedup dedup;          // who repeats whom inside this tile
  BatchForwardState forward; // the sliced state of the lanes already run

  // Lane j's HASHED result at `j * row_stride` -- value bytes then meta,
  // zeros on a miss -- for `kRows`; the DENSE result of every layout, and the
  // hashed one under `kSlicedPlaceAtLane`, is in `sliced` (value line v,
  // lane j at byte j).
  Aligned64Ptr rows;
  // THE SLICED ACCUMULATOR IS THE PARALLEL BANK's probe buffer, whose first
  // `layout.value_bytes` lines have exactly this shape (value lines, then the
  // meta line; the found line follows them).  So a participant running the
  // sliced layout PUBLISHES its probe result by accumulating into it, with no
  // copy at all.  The chunked shape uses the same buffer as ordinary scratch: a tile
  // is sized once and which shape runs it is a per-call choice.
  uint8_t* sliced = nullptr;
  Aligned64Ptr extract;       // one row, the permute extractor's target
  Aligned64Ptr slots;         // 64 bytes: the dense wave's index vector
  Aligned64Ptr insert_value;  // what the chunked path's current lane inserts
  size_t row_stride = 0;      // value + meta, rounded up to a whole line

  // One word per bucket of the REMOVABLE run (the current online-stash unit,
  // `s` buckets), accumulated during the cascade and applied after it.  Sized
  // from the geometry rather than fixed at 32 words, because this engine's
  // insertion unit is a tuning axis and the batch path favours a longer one
  // than the scalar path (a 4096-entry unit is 64 buckets).
  // Separate full cache lines even for a one-bucket unit. Workers never
  // update adjacent mask words in the canonical ring concurrently.
  BatchClearMasks clear_masks;
  uint64_t sink = 0;  // where a non-removable table's mask clear goes

  // ---- the parallel-tile banks (table/cpu_byteslice_parallel_batch.hpp) ----
  // Untouched by the chunked shape, which has one tile and forwards from its
  // own `dedup`/`rows` directly.
  ParallelBatchBanks banks;
  ParallelBatchMetadata metadata;
  ParallelBatchResults results;

  uint8_t* Row(size_t j) { return rows.get() + j * row_stride; }
  const uint8_t* Row(size_t j) const { return rows.get() + j * row_stride; }

  // `max_tables` is the longest cascade the publisher can hand out and
  // `arena_slots` the most hashed tables in one; `unit_buckets` is the
  // removable run's length.  All three are public geometry.
  //
  // THE ALIGNED BUFFERS ARE BOUGHT THROUGH THE TALLYING ALLOCATOR and the
  // result is compared against this tile's own static predictor before
  // `Resize` returns, which is the rule every owning class in this engine
  // follows: a buffer added here and not to `Bytes` below is a
  // construction failure in every fixture that builds an engine, rather than
  // a bill that is quietly short.  The vectors and the four sub-objects are
  // tallied beside the call that allocates them, because they size
  // themselves; each of those has its own `Bytes` predictor next to its own
  // `Resize`, for the same reason.
  void Resize(size_t max_tables, size_t arena_slots, const Layout& layout,
              size_t user_value_bytes, size_t unit_buckets) {
    constexpr size_t n = kMaxBatchLanes;
    bytes_ = LevelArenaByteBill();
    row_stride =
        CheckedSizeAdd(layout.value_bytes, 63, "batch row stride") & ~size_t{63};
    key.assign(n, KeyWords{});
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(KeyWords));
    op.assign(n, BatchOp::kRead);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(BatchOp));
    insert.assign(n, 0);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t));
    value_in.assign(n, nullptr);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(const uint8_t*));
    value_out.assign(n, nullptr);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t*));
    found.assign(n, 0);
    gate.assign(n, 0);
    match.assign(n, 0);
    take.assign(n, 0);
    run_take.assign(n, 0);
    dense_taken.assign(n, 0);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint64_t), 6);
    bucket.assign(n, nullptr);
    next_bucket.assign(n, nullptr);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t*), 2);
    mask.assign(n, nullptr);
    next_mask.assign(n, nullptr);
    bytes_.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint64_t*), 2);
    clear_masks.Resize(unit_buckets);
    bytes_.AddAligned64(
        ByteRole::kBatchScratch,
        CheckedSizeMul(unit_buckets, sizeof(uint64_t), "batch masks"));
    probe.Resize(n, max_tables, arena_slots);
    bytes_.AddPlain(ByteRole::kBatchScratch,
                    BatchProbeScratch::Bytes(n, max_tables, arena_slots));
    forward.Resize(user_value_bytes);
    bytes_.AddAligned64(ByteRole::kBatchScratch,
                        CheckedSizeMul(CheckedSizeAdd(user_value_bytes, 2, "forward lines"),
                                       n, "forward bytes"));
    bytes_.AddAligned64(ByteRole::kBatchScratch, user_value_bytes);
    rows = AllocateTallied(CheckedSizeMul(n, row_stride, "batch rows"),
                            ByteRole::kBatchScratch, &bytes_);
    std::memset(rows.get(), 0, CheckedSizeMul(n, row_stride, "batch rows"));
    extract = AllocateTallied(row_stride, ByteRole::kBatchScratch, &bytes_);
    slots = AllocateTallied(n, ByteRole::kBatchScratch, &bytes_);
    std::memset(slots.get(), 0, n);
    insert_value =
        AllocateTallied(user_value_bytes, ByteRole::kBatchScratch, &bytes_);
    banks.Resize(user_value_bytes);
    bytes_.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(user_value_bytes, n, "proposed bytes"));
    bytes_.AddAligned64(
        ByteRole::kBatchScratch,
        CheckedSizeMul(CheckedSizeAdd(user_value_bytes, 2, "probe lines"),
                       n, "probe bytes"));
    results.Resize(user_value_bytes);
    bytes_.AddAligned64(ByteRole::kBatchScratch,
                        CheckedSizeMul(n, ParallelResultStride(user_value_bytes), "result rows"), 2);
    // AFTER the bank exists, and checked rather than reasoned about: the
    // accumulator needs `layout.value_bytes` lines and the bank holds
    // `user_value_bytes + 2` of them, which is one more by construction.
    if (layout.value_bytes + 1 != user_value_bytes + 2) {
      throw std::logic_error(
          "level arena: the stored value width is not the user's plus its "
          "meta line, so the sliced accumulator does not fit the probe bank");
    }
    sliced = banks.probe.get();
    ExpectPredictedBytes(bytes_, Bytes(max_tables, arena_slots, layout,
                                       user_value_bytes, unit_buckets),
                         "a batch tile");
  }

  // What one tile costs, for the engine's buffer bill.  It is a `Bytes`
  // predictor of the same kind every other owning component has,
  // and `Resize` checks itself against it.
  static LevelArenaByteBill Bytes(size_t max_tables, size_t arena_slots,
                                  const Layout& layout,
                                  size_t user_value_bytes,
                                  size_t unit_buckets) {
    constexpr size_t n = kMaxBatchLanes;
    const size_t row_stride =
        CheckedSizeAdd(layout.value_bytes, 63, "batch row stride") & ~size_t{63};
    LevelArenaByteBill bill;
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(KeyWords));
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(BatchOp));
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t));
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(const uint8_t*));
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t*));
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint64_t), 6);
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint8_t*), 2);
    bill.AddPlain(ByteRole::kBatchScratch, n * sizeof(uint64_t*), 2);
    bill.AddAligned64(
        ByteRole::kBatchScratch,
        CheckedSizeMul(unit_buckets, sizeof(uint64_t), "batch masks"));
    bill.AddPlain(ByteRole::kBatchScratch,
                  BatchProbeScratch::Bytes(n, max_tables, arena_slots));
    bill.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(CheckedSizeAdd(user_value_bytes, 2, "forward lines"),
                                       n, "forward bytes"));
    bill.AddAligned64(ByteRole::kBatchScratch, user_value_bytes);  // proposed
    bill.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(n, row_stride, "batch rows"));  // rows
    bill.AddAligned64(ByteRole::kBatchScratch, row_stride);        // extract
    bill.AddAligned64(ByteRole::kBatchScratch, n);                 // slots
    bill.AddAligned64(ByteRole::kBatchScratch, user_value_bytes);  // insert
    // The parallel banks and results, which every tile owns whatever shape it
    // is run in -- a tile is sized once and the shape is a per-call choice.
    // The second of the banks is also the sliced accumulator; see `sliced`.
    bill.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(user_value_bytes, n, "proposed bytes"));
    bill.AddAligned64(
        ByteRole::kBatchScratch,
        CheckedSizeMul(CheckedSizeAdd(user_value_bytes, 2, "probe lines"),
                       n, "probe bytes"));
    bill.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(n, ParallelResultStride(user_value_bytes), "result rows"), 2);
    return bill;
  }

  const LevelArenaByteBill& bytes() const { return bytes_; }

 private:
  // ParallelBatchResults::Resize's own rounding, spelled once.
  static size_t ParallelResultStride(size_t user_value_bytes) {
    return CheckedSizeAdd(user_value_bytes, 64, "result stride") & ~size_t{63};
  }

  LevelArenaByteBill bytes_;
};

// ---------------------------------------------------------------------------
// The address pass
// ---------------------------------------------------------------------------

// Every lane's candidate pair for every entry of `plan`.  A DENSE entry's
// candidates are the table itself and are written per lane here; the hashed
// ones are one AES call over all lanes, which is the width the eight-chain
// VAES loop was written for and which one access never reaches.
//
// Unlike the serial path this does not memoize the dense half per plan epoch.
// It is `m` pointer stores per dense entry -- ten per access at a 64-lane
// chunk -- against a per-tile memo that would have to be invalidated from the
// request thread and read from a participant's.
inline void PrepareLevelArenaBatchAddresses(const ProbePlan& plan, size_t m,
                                            uint64_t dummy_base,
                                            size_t bucket_bytes,
                                            const AesTagKeys& aes_keys,
                                            LevelArenaBatchTile& tile) {
  const size_t all_tables = plan.tables.size();
  for (size_t i = plan.first_live; i < all_tables; ++i) {
    const TableEntry& t = plan.tables[i];
    if (t.kind != TableKind::kDense) continue;
    for (size_t j = 0; j < m; ++j) {
      uint8_t** b = tile.probe.LaneBuckets(j) + 2 * i;
      uint64_t** k = tile.probe.LaneMasks(j) + 2 * i;
      b[0] = b[1] = t.data;
      k[0] = k[1] = t.masks;
    }
  }
  ResolveHashedProbeAddressesBatch(plan.addressing, tile.key.data(), m,
                                   dummy_base, all_tables, bucket_bytes,
                                   aes_keys, tile.probe);
}

// ---------------------------------------------------------------------------
// The cascade
// ---------------------------------------------------------------------------

// Probes lanes [0, tile.lanes) of `tile` against `plan`, newest window first.
// Candidate addresses were prepared with disjoint dummy-counter runs for
// every lane/participant; this pass only selects among those addresses.
//
// On return, lane j's probe result is
//   - `tile.sliced` column j (value lines then meta) under kSlicedPlaceAtLane,
//   - `tile.Row(j)` under kRows,
// with `tile.found[j]` its found bit -- all three garbage for a duplicate
// lane, which is exactly the case the forwarding chain replaces.  The
// removable run's clears are ACCUMULATED in `tile.clear_masks` and are not
// applied here: applying them is the one store the cascade makes into the
// plan's storage, and it belongs to the thread that owns the epoch.
inline void ProbeLevelArenaBatchLanes(const ProbePlan& plan,
                                      const Layout& layout,
                                      BatchResultLayout result_layout,
                                      LevelArenaBatchTile& tile,
                                      ProbeFamilyAudit* audit,
                                      size_t resume_at = 0) {
  const size_t m = tile.lanes;
  if (m == 0) return;
  const bool seeded = resume_at != 0;
  const size_t first = seeded ? resume_at : plan.first_live;
  const TableEntry* const tables = plan.tables.data() + first;
  const size_t n = plan.tables.size() - first;
  const size_t bucket_bytes = layout.BucketBytes();
  const size_t key_bytes = layout.key_bytes;
  const size_t value_lines = layout.value_bytes;  // value + meta
  uint8_t* const slots = tile.slots.get();
  uint8_t* const sliced = tile.sliced;
  uint8_t* const extract = tile.extract.get();
  uint8_t* const rows = tile.rows.get();
  const size_t row_stride = tile.row_stride;
  const bool place_at_lane =
      result_layout == BatchResultLayout::kSlicedPlaceAtLane;
  (void)audit;

  // Every engine-published dense bucket is internally unique: current units
  // clear before reinsertion, frozen units preserve that invariant, and tiers
  // are disjoint drains of deduplicated rebuild sources. See the checked audit
  // below. Narrow direct recovery uses complete
  // stored-key equality under this uniqueness contract; 16-byte recovery does
  // too unless kWideKeySegmentMatch is on, where its two halves match
  // independently (MatchUniqueDenseSlots<8, 2>).
  const size_t cross_min_lanes = key_bytes == 16 ? 64 : 32;
  bool cross_match = kNativeDenseCrossMatch && m >= cross_min_lanes &&
                     (key_bytes == 4 || key_bytes == 8 || key_bytes == 16);
  if (cross_match) {
    // Direct slots pay off only once enough dense work amortizes packing
    // and dispatch, so they are gated on a PUBLIC dense-bucket count
    // (saturated to avoid overflow); the wide path keeps a ceiling as well,
    // a tuning constant to re-derive per target. Under kWideKeySegmentMatch 16-byte recovery is approximate;
    // its false-match bound (analysis/bound_certification/ERROR_ACCOUNTING.md)
    // counts buckets holding the key and does not rely on this ceiling.
    size_t dense_buckets = 0;
    constexpr size_t cap = (size_t{1} << 16) + 1;
    for (size_t i = 0; i < n; ++i) {
      if (tables[i].kind != TableKind::kDense) continue;
      dense_buckets += std::min(tables[i].num_buckets, cap - dense_buckets);
    }
    cross_match = dense_buckets >= 16 && (key_bytes != 16 || dense_buckets < cap);
  }
  DenseMatchQueries queries;
  if (cross_match) {
    if (key_bytes == 4) PrepareDenseMatchQueries<4, 1>(tile.key.data(), m, queries);
    else if (key_bytes == 8) PrepareDenseMatchQueries<8, 1>(tile.key.data(), m, queries);
    else PrepareDenseMatchQueries<8, 2>(tile.key.data(), m, queries);
  }

  // A resumed prefix scan has already seeded sliced/found/dense_taken and
  // private removals. Initialize only the suffix's target and row fallback.
  const uint64_t duplicates = tile.dedup.duplicates;
  for (size_t j = 0; j < m; ++j) {
    const uint64_t dup = (duplicates >> j) & 1u;
    if (!seeded) {
      tile.found[j] = dup;
      tile.dense_taken[j] = 0;
    }
    if (!place_at_lane) std::memset(rows + j * row_stride, 0, value_lines);
    if (n != 0) {
      const uint64_t use_dummy = seeded
          ? tile.found[j] & uint64_t{tables[0].kind == TableKind::kHashed}
          : dup;
      tile.gate[j] = use_dummy - 1;
      if (seeded) {
        const ProbeTarget target = SelectLaneProbeTarget(
            tile.probe, j, first, use_dummy != 0);
        tile.bucket[j] = target.bucket;
        tile.mask[j] = target.mask;
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
        if (audit != nullptr && use_dummy == 0 &&
            tables[0].kind == TableKind::kHashed)
          audit->RecordRealProbe(tables[0].nonce_family_id, tile.key[j]);
#endif
      } else {
        tile.bucket[j] = tables[0].data;
        tile.mask[j] = tables[0].masks;
      }
    }
  }
  if (!seeded) {
    if (place_at_lane) ClearSliced(sliced, value_lines);
    std::fill(tile.clear_masks.begin(), tile.clear_masks.end(), uint64_t{0});
  }

  for (size_t i = 0; i < n; ++i) {
    const TableEntry& here = tables[i];
    if (here.kind == TableKind::kDense) {
      // ---- THE DENSE WAVE ----
      //
      // Every lane scans the same buckets.  A multi-bucket run -- this
      // engine's online-stash unit, its partially assembled prefix and every
      // complete one -- is ordered oldest to newest, so the entry's answer is
      // the LAST match in it: each bucket blends under its own hit and the
      // later blend overwrites the earlier one.  `found` is the lane's state
      // before the WHOLE entry, so a lane found higher up takes nothing here
      // whatever matches, and every bucket and every line is read regardless.
      const size_t buckets = here.num_buckets;
      // The removable run's clears are accumulated one word per bucket, and
      // the vector is sized from the geometry's `s`.  Checked rather than
      // assumed: the alternative to this comparison is an out-of-bounds store
      // if the plan ever published a removable table of another length.
      if (here.removable && buckets > tile.clear_masks.size()) {
        throw std::logic_error(
            "level arena: the removable dense run is longer than the "
            "online-stash unit this batch tile was sized for");
      }
      // "Any hit anywhere in this entry", zeroed per ENTRY rather than folded
      // into the first bucket's pass, so that an entry with no buckets at all
      // could not carry the previous entry's hits into `found`.
      for (size_t j = 0; j < m; ++j) tile.run_take[j] = 0;
      for (size_t b = 0; b < buckets; ++b) {
        const uint8_t* const bucket = here.data + b * bucket_bytes;
        const uint64_t real_mask = here.masks[b];
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
        // Audit only: occupancy and key-dependent branches are forbidden in
        // production. Check the actual immutable and removable bucket sources,
        // not just the query's selected match, including small/fallback batches.
        for (uint64_t remaining = real_mask; remaining != 0; remaining &= remaining - 1) {
          const unsigned slot = unsigned(_tzcnt_u64(remaining));
          const KeyWords key = ReadSlotKey(bucket, slot, key_bytes);
          if (MatchMaskByteSlicedTree(bucket, real_mask, layout, key) != (uint64_t{1} << slot))
            throw std::logic_error("level arena: duplicate live key in dense bucket");
        }
#endif
        __m512i lines[16];
        uint64_t cross_hits = 0;
        if (cross_match) {
          if (key_bytes == 4)
            cross_hits = MatchUniqueDenseSlots<4, 1>(bucket, real_mask, queries, m, slots);
          else if (key_bytes == 8)
            cross_hits = MatchUniqueDenseSlots<8, 1>(bucket, real_mask, queries, m, slots);
          else
            cross_hits = MatchUniqueDenseSlots<8, 2>(bucket, real_mask, queries, m, slots);
        } else {
          for (size_t l = 0; l < key_bytes; ++l)
            lines[l] = core::obliLoad512(bucket + l * kBucketCapacity);
        }
        uint64_t take_mask = 0;
        for (size_t j = 0; j < m; ++j) {
          uint64_t match;
          if (cross_match) {
            match = (uint64_t{1} << slots[j]) &
                    (uint64_t{0} - ((cross_hits >> j) & 1u)) & tile.gate[j];
          } else {
            match = MatchMaskFromKeyLines(lines, key_bytes, real_mask,
                                          tile.key[j]) & tile.gate[j];
            // tzcnt(0) = 64; a fallback miss selects byte zero.
            slots[j] = static_cast<uint8_t>(_tzcnt_u64(match) & 63u);
          }
          // A miss leaves the accumulator alone, regardless of its slot byte.
          const uint64_t hit = static_cast<uint64_t>(match != 0);
          take_mask |= (hit & (tile.found[j] ^ 1u)) << j;
          tile.run_take[j] |= hit;
          // Removal survives only in the CURRENT online-stash unit; every
          // other dense table is a rebuild source and a probe may not mutate
          // one.  Public per-table property, and an independent word per
          // bucket of the run.
          if (here.removable) tile.clear_masks[b] |= match;
        }
        ExtractDenseWave(bucket, key_bytes, value_lines, slots, take_mask,
                         sliced);
        for (size_t j = 0; j < m; ++j) {
          tile.dense_taken[j] |= (take_mask >> j) & 1u;
        }
      }
      for (size_t j = 0; j < m; ++j) tile.found[j] |= tile.run_take[j];
    } else {
      // ---- A HASHED TABLE: one key-derived bucket per lane.  The match wave
      // comes first so that the select wave below can put the NEXT table's
      // misses in flight before this one's values are extracted. ----
      for (size_t j = 0; j < m; ++j) {
        const uint64_t match =
            MatchMaskByteSlicedTree(tile.bucket[j], *tile.mask[j], layout,
                                    tile.key[j]) &
            tile.gate[j];
        const uint64_t hit = static_cast<uint64_t>(match != 0);
        tile.match[j] = match;
        tile.take[j] = hit & (tile.found[j] ^ 1u);
        tile.found[j] |= hit;
      }
    }

    const bool last = i + 1 >= n;
    if (!last) {
      const TableEntry& next = tables[i + 1];
      const uint64_t hashed =
          static_cast<uint64_t>(next.kind == TableKind::kHashed);
      // ---- THE SELECT WAVE: every lane's next target, with every line the
      // next probe will read prefetched before any extract runs, so the next
      // table's misses are all in flight together. ----
      for (size_t j = 0; j < m; ++j) {
        const uint64_t use_dummy = tile.found[j] & hashed;
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
        // Audit only: `use_dummy` derives from `found`, so branching on it is
        // exactly the leak the rest of this loop CMOVs around.
        if (audit != nullptr && use_dummy == 0 && hashed != 0) {
          audit->RecordRealProbe(next.nonce_family_id, tile.key[j]);
        }
#endif
        const ProbeTarget target =
            SelectLaneProbeTarget(tile.probe, j, first + i + 1, use_dummy != 0);
        tile.next_bucket[j] = target.bucket;
        tile.next_mask[j] = target.mask;
        if (hashed) {
          // The mask word, the key lines and the value lines, lane-major so a
          // bucket's contiguous lines keep their DRAM row open.  Not only the
          // key lines: in this engine a hashed table is preceded and followed
          // by dense ones -- the prefix above it, its own tier below -- so
          // prefetching value lines from inside a hashed extract, which is the
          // serial cascade's device, would almost never fire.
          _mm_prefetch(reinterpret_cast<const char*>(target.mask), _MM_HINT_T0);
          for (size_t l = 0; l < key_bytes + value_lines; ++l) {
            _mm_prefetch(
                reinterpret_cast<const char*>(target.bucket +
                                              l * kBucketCapacity),
                _MM_HINT_T0);
          }
        }
      }
    }

    if (here.kind == TableKind::kHashed) {
      // ---- THE EXTRACT WAVE for the hashed table; the next bucket's lines
      // were all prefetched by the select wave.  Nothing is cleared: the only
      // removable table in this engine is the dense online-stash unit. ----
      if (place_at_lane) {
        ExtractHashedWaveIntoSliced<false>(
            const_cast<const uint8_t* const*>(tile.bucket.data()),
            tile.match.data(), tile.take.data(), 0, m, key_bytes, value_lines,
            kBucketCapacity, sliced);
      } else {
        for (size_t j = 0; j < m; ++j) {
          ExtractValueAndClearRealMaskByteSlicedPermute<false>(
              tile.bucket[j], &tile.sink, layout, tile.match[j], extract);
          core::obliAssignBytes(rows + j * row_stride, extract, value_lines,
                                tile.take[j]);
        }
      }
    }
    if (last) break;
    // Advance the lanes.
    const uint64_t hashed =
        static_cast<uint64_t>(tables[i + 1].kind == TableKind::kHashed);
    for (size_t j = 0; j < m; ++j) {
      const uint64_t use_dummy = tile.found[j] & hashed;
      tile.gate[j] = use_dummy - 1;  // 0 -> all-ones, 1 -> zero
      tile.bucket[j] = tile.next_bucket[j];
      tile.mask[j] = tile.next_mask[j];
    }
  }

  // A lane took its value from at most one entry.  Under kSlicedPlaceAtLane
  // every take -- dense or hashed -- already landed in the accumulator, which
  // started the chunk zeroed, and there is nothing to reconcile.  Under kRows
  // the dense takes are in the accumulator and the hashed ones in the rows,
  // and `dense_taken` says which; it is secret and reaches only a CMOV.
  if (!place_at_lane) {
    MergeSlicedIntoRowsScalar(sliced, value_lines, tile.dense_taken.data(), 0,
                              m, rows, row_stride);
  }
}

// Preallocated producer-owned publication banks. Query groups are global
// 64-lane groups, independent of the balanced request-owner partition.
class LevelArenaBucketBatch {
 public:
  void Resize(unsigned capacity, size_t value_bytes) {
    stride_ = CheckedSizeMul(CheckedSizeAdd(value_bytes, 2, "partial lines"),
                              kMaxBatchLanes, "partial bytes");
    keys.resize(capacity * kMaxBatchLanes);
    bytes_.AddPlain(ByteRole::kBatchScratch, keys.size() * sizeof(KeyWords));
    for (unsigned w = 0; w < capacity; ++w)
      partial_[w] = AllocateTallied(
          CheckedSizeMul(capacity, stride_, "partial rows"),
          ByteRole::kBatchScratch, &bytes_);
    ExpectPredictedBytes(bytes_, Bytes(capacity, value_bytes), "bucket batch");
  }
  static LevelArenaByteBill Bytes(unsigned capacity, size_t value_bytes) {
    LevelArenaByteBill bill;
    bill.AddPlain(ByteRole::kBatchScratch,
                  capacity * kMaxBatchLanes * sizeof(KeyWords));
    bill.AddAligned64(ByteRole::kBatchScratch,
                      CheckedSizeMul(capacity,
                          CheckedSizeMul(CheckedSizeAdd(value_bytes, 2, "partial lines"),
                                         kMaxBatchLanes, "partial bytes"),
                          "partial rows"), capacity);
    return bill;
  }
  const LevelArenaByteBill& bytes() const { return bytes_; }
  uint8_t* Partial(unsigned worker, size_t group) const {
    return partial_[worker].get() + group * stride_;
  }
  std::vector<KeyWords> keys;
 private:
  size_t stride_ = 0;
  std::array<Aligned64Ptr, kMaxOnlineParticipants> partial_;
  LevelArenaByteBill bytes_;
};

// The first dense region is scanned in reverse entry order and forward bucket
// order: oldest to newest. Contiguous worker ranges preserve that total order,
// so reducing workers in ascending order needs no per-lane freshness ranks.
inline size_t InitialDenseEnd(const ProbePlan& plan, size_t* buckets) {
  *buckets = 0;
  size_t end = plan.first_live;
  while (end < plan.tables.size() &&
         plan.tables[end].kind == TableKind::kDense) {
    *buckets += plan.tables[end++].num_buckets;
  }
  return end;
}

inline void ScanLevelArenaBucketRange(
    const ProbePlan& plan, size_t end, size_t bucket_count, const Layout& layout,
    size_t requests, unsigned worker, unsigned workers,
    LevelArenaBucketBatch& scratch, LevelArenaBatchTile& tile) {
  const BatchPartition partition{bucket_count, workers};
  const size_t begin = partition.Offset(worker);
  const size_t limit = begin + partition.Count(worker);
  const size_t key_bytes = layout.key_bytes;
  const size_t value_lines = layout.value_bytes;
  const size_t groups = (requests + 63) / 64;
  std::fill(tile.clear_masks.begin(), tile.clear_masks.end(), uint64_t{0});
  // Keep the existing wide-key per-request exposure bound across the ENTIRE
  // plan, not per shard. Amortization is instead based on this worker's work.
  size_t dense_buckets = 0;
  constexpr size_t cap = (size_t{1} << 16) + 1;
  for (size_t i = plan.first_live; i < plan.tables.size(); ++i)
    if (plan.tables[i].kind == TableKind::kDense)
      dense_buckets += std::min(plan.tables[i].num_buckets, cap - dense_buckets);
  for (size_t g = 0; g < groups; ++g) {
    const size_t lanes = std::min(size_t{64}, requests - 64 * g);
    const KeyWords* keys = scratch.keys.data() + 64 * g;
    uint8_t* partial = scratch.Partial(worker, g);
    ClearSliced(partial, value_lines + 1);
    uint64_t found = 0;
    const bool cross = kNativeDenseCrossMatch &&
        (key_bytes == 4 || key_bytes == 8 || key_bytes == 16) &&
        lanes >= (key_bytes == 16 ? 64u : 32u) &&
        partition.Count(worker) >= 16 && (key_bytes != 16 || dense_buckets < cap);
    DenseMatchQueries queries;
    if (cross) {
      if (key_bytes == 4) PrepareDenseMatchQueries<4, 1>(keys, lanes, queries);
      else if (key_bytes == 8) PrepareDenseMatchQueries<8, 1>(keys, lanes, queries);
      else PrepareDenseMatchQueries<8, 2>(keys, lanes, queries);
    }
    size_t at = 0;
    for (size_t i = end; i-- > plan.first_live;) {
      const TableEntry& table = plan.tables[i];
      if (table.removable && table.num_buckets > tile.clear_masks.size())
        throw std::logic_error("level arena: bucket scan removal buffer is too small");
      const size_t low = begin > at ? std::min(begin - at, table.num_buckets) : 0;
      const size_t high = limit > at ? std::min(limit - at, table.num_buckets) : 0;
      for (size_t b = low; b < high; ++b) {
        const uint8_t* bucket = table.data + b * layout.BucketBytes();
        const uint64_t real = table.masks[b];
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
        for (uint64_t remaining = real; remaining; remaining &= remaining - 1) {
          const unsigned slot = unsigned(_tzcnt_u64(remaining));
          const KeyWords key = ReadSlotKey(bucket, slot, key_bytes);
          if (MatchMaskByteSlicedTree(bucket, real, layout, key) != (uint64_t{1} << slot))
            throw std::logic_error("level arena: duplicate live key in dense bucket");
        }
#endif
        __m512i lines[16];
        uint64_t hits = 0, clear = 0;
        uint8_t* slots = tile.slots.get();
        if (cross) {
          if (key_bytes == 4)
            hits = MatchUniqueDenseSlots<4, 1>(bucket, real, queries, lanes, slots);
          else if (key_bytes == 8)
            hits = MatchUniqueDenseSlots<8, 1>(bucket, real, queries, lanes, slots);
          else hits = MatchUniqueDenseSlots<8, 2>(bucket, real, queries, lanes, slots);
          // Immutable prefix buckets only need hits and extraction. For the
          // removable unit, combine eight slot bits at a time in registers;
          // no per-query scalar mask reconstruction on the full-width path.
          if (table.removable) {
            __m512i clears = _mm512_setzero_si512();
            for (size_t j = 0; j < lanes; j += 8) {
              const __m512i indices = core::obliPin512(_mm512_cvtepu8_epi64(
                  _mm_loadl_epi64(reinterpret_cast<const __m128i*>(slots + j))));
              clears = _mm512_or_si512(clears, _mm512_maskz_sllv_epi64(
                  static_cast<__mmask8>(hits >> j), _mm512_set1_epi64(1), indices));
            }
            clear = _mm512_reduce_or_epi64(clears);
          }
        } else {
          for (size_t k = 0; k < key_bytes; ++k)
            lines[k] = core::obliLoad512(bucket + 64 * k);
          for (size_t j = 0; j < lanes; ++j) {
            const uint64_t match = MatchMaskFromKeyLines(lines, key_bytes, real, keys[j]);
            slots[j] = static_cast<uint8_t>(_tzcnt_u64(match) & 63u);
            hits |= uint64_t{match != 0} << j;
            clear |= match;
          }
        }
        if (table.removable) tile.clear_masks[b] |= clear;
        ExtractDenseWave(bucket, key_bytes, value_lines, slots, hits, partial);
        found |= hits;
      }
      at += table.num_buckets;
    }
    _mm512_store_si512(partial + value_lines * 64,
        core::obliMaskMov8(_mm512_setzero_si512(), found, _mm512_set1_epi8(1)));
  }
}

inline void MergeLevelArenaBucketResults(
    const LevelArenaBucketBatch& scratch, unsigned workers, size_t offset,
    const Layout& layout, LevelArenaBatchTile& tile) {
  assert(tile.lanes > 0 && tile.lanes <= kMaxBatchLanes);
  ClearSliced(tile.sliced, layout.value_bytes);
  uint64_t found = 0;
  // An owner's contiguous <=64 lanes overlap at most two global groups.
  for (size_t g = offset / 64; g <= (offset + tile.lanes - 1) / 64; ++g) {
    alignas(64) uint8_t indices[64] = {};
    uint64_t active = 0;
    for (size_t j = 0; j < tile.lanes; ++j) {
      indices[j] = static_cast<uint8_t>((offset + j) & 63u);
      active |= uint64_t{(offset + j) / 64 == g} << j;
    }
    active &= ~tile.dedup.duplicates;
    const __m512i index = core::obliLoad512(indices);
    for (unsigned w = 0; w < workers; ++w) {
      const uint8_t* partial = scratch.Partial(w, g);
      const __m512i flags = _mm512_permutexvar_epi8(index,
          core::obliLoad512(partial + layout.value_bytes * 64));
      const uint64_t take = active & core::obliTestMask8(flags, _mm512_set1_epi8(1));
      found |= take;
      for (size_t v = 0; v < layout.value_bytes; ++v) {
        const __m512i value = _mm512_permutexvar_epi8(index,
            core::obliLoad512(partial + 64 * v));
        const __m512i merged = _mm512_mask_mov_epi8(
            core::obliLoad512(tile.sliced + 64 * v), take, value);
        _mm512_store_si512(tile.sliced + 64 * v, core::obliPin512(merged));
      }
    }
  }
  for (size_t j = 0; j < tile.lanes; ++j) {
    tile.found[j] = ((found | tile.dedup.duplicates) >> j) & 1u;
    tile.dense_taken[j] = (found >> j) & 1u;
  }
}

// The one store the cascade makes into the plan's storage: the removable run's
// matched slots, cleared once, by the thread that holds the reader epoch.
// `tiles` is every participant's, because a combined job's lanes are spread
// over them and the run is one table.
inline void ApplyLevelArenaBatchRemovals(const ProbePlan& plan,
                                         LevelArenaBatchTile* const* tiles,
                                         size_t participants) {
  for (size_t i = plan.first_live; i < plan.tables.size(); ++i) {
    const TableEntry& t = plan.tables[i];
    if (!t.removable) continue;
    for (size_t p = 0; p < participants; ++p) {
      if (t.num_buckets <= tiles[p]->clear_masks.size()) continue;
      throw std::logic_error(
          "level arena: the removable dense run is longer than a batch "
          "tile's clear masks");
    }
    for (size_t b = 0; b < t.num_buckets; ++b) {
      uint64_t clear = 0;
      for (size_t p = 0; p < participants; ++p) {
        clear |= tiles[p]->clear_masks[b];
      }
      t.masks[b] &= ~clear;
    }
  }
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
