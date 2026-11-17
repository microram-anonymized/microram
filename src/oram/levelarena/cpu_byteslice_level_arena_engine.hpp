#pragma once

// THE LEVEL-ARENA ENGINE: the hierarchical ORAM behind ByteMap.  One request
// thread (the REQUESTER) probes and inserts; the hashed levels' rebuild state
// machines (LevelState) are driven either by that same thread at its flush
// (the INLINE EXECUTOR) or by owner threads of their own.  This header owns
// construction, the public access/batch/initialization API, the probe
// cascade and the executors; the per-level machinery lives in the headers it
// includes.  src/oram/levelarena/DESIGN.md is the design document: geometry,
// carries, publication, the numbered threading rules this file cites, and
// the security and capacity contracts.
//
// Vocabulary (defined in DESIGN.md): a CARRY is a full table forwarded from
// one level into the next level's INBOX; a level of fanout b builds PARTIAL
// tables P_1..P_b over b carries, the last of which is its outgoing carry;
// the DENSE PREFIX is the requester's ring of
// frozen online-stash units scanned in full by every access; a TIER is the
// small residual table published right after a hashed main, holding what did
// not fit in it; a FAMILY is the public nonce coordinate a table is hashed
// under.
//
// THE TWO SHAPES ARE ONE ENGINE.  `Options::owner_threads` is the only
// difference: at zero the requester runs every level itself, one share per
// flush in deadline order (or, with FlushPolicy::kSettle, a round robin to
// quiescence, which is what the correctness fixtures mostly use); above zero
// the levels are divided into that many contiguous groups (PlanLevelGroups,
// or Options::groups) and each group gets an owner thread running the owner
// loop (cpu_byteslice_level_arena_owner.hpp).  Nothing about a level, a
// merge or a publication changes between them -- the same `LevelState::Step` runs in both -- and that is deliberate: the
// threaded engine has to be comparable with the inline one for the same
// workload, which is how a fixture can say the two agree rather than only that
// neither crashed.
//
// WHAT AN ACCESS IS.  It enters the reader epoch, snapshots exactly one probe
// plan, probes one bucket of every hashed table in it and every bucket of
// every dense one, leaves the epoch, and then inserts exactly one entry into
// the current online-stash unit.  Every access inserts, whatever it found: a
// read re-inserts what it took, a miss inserts a tombstone for the key it
// looked for, an erase inserts a tombstone with a zero value.  That
// uniformity is the point -- an access's effect on memory must not depend on
// what it found -- and it is also what keeps the probe audit quiet, since the
// next access to the same key finds it at the top of the cascade and issues
// dummies below.  The one exception is a blind write (WriteStored): it skips
// the probe cascade and the reader epoch and only inserts.  Whether an
// operation is a blind write is public (it is the operation code), and the
// blind path itself never branches on whether the key exists; older copies
// of the key are superseded by the merges' freshness-aware deduplication.
//
// WHY THE EXECUTOR RUNS AT THE FLUSH AND NOT INSIDE THE PROBE.  Reclamation
// compares an OBSERVED reader epoch against a retirement threshold, so an
// owner that ran inside an access would stamp `e + 1` on everything it retired
// and free nothing until that access left.  The flush is the one point in an
// access where the epoch is provably closed (the requester may wait only
// with its epoch closed: threading rule 7), so that is where the levels are
// driven.
//
// DETERMINISTIC ROUND ROBIN.  A settle's sweep steps levels 1, 2, ... L in
// order and repeats while any of them moved; a share orders them by deadline
// and stops when its touch budget is spent.  Nothing inline is timed, so both
// are deterministic.
// Because a sweep runs low levels first, a carry published at level l is
// consumed by level l+1 in the SAME sweep -- which is why a level normally
// prepares speculatively one sweep and merges the next, and why
// preparation is always enabled when no ready merge takes priority.
//
// THE CASCADE makes every plan entry one step -- a hashed table is one
// key-derived bucket, a dense table is all of its buckets, and a step's match
// selects the next step's address -- except that a hashed main and the dense
// tier published right after it are ONE step: the tier's match and extract
// run while the main bucket is in flight, and the main's extract runs after
// the next bucket's prefetches (see the comment above `Cascade`).

#include <immintrin.h>

#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <functional>
#include <type_traits>
#include <array>
#include <limits>
#include <memory>
#include <mutex>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/core/release_guard.hpp"
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/table/cpu_byteslice_probe_plan.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_batch.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_batch_workers.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_value_workers.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_boundary.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/rebuild/cpu_byteslice_initialization.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_event.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_level.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_placement.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_rebuild_params.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_probe.hpp"
#include "src/oram/table/cpu_byteslice_probe_addresses.hpp"
#include "src/oram/table/cpu_byteslice_stored_key.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// Reserve the whole public lane/table rectangle before generating addresses.
// Dummy counters occupy the low 64-bit input word, not the packed family's
// 48-bit ordinal. Empty reservations consume nothing and have no first input.
inline uint64_t ReserveDummyCounters(uint64_t& used, uint64_t lanes,
                                     uint64_t tables) {
  if (lanes == 0 || tables == 0) return 0;
  if (tables > (std::numeric_limits<uint64_t>::max() - used) / lanes) {
    throw std::overflow_error("level arena: dummy counter range exhausted");
  }
  const uint64_t base = used + 1;
  used += lanes * tables;
  return base;
}

class LevelArenaEngine {
 public:
  // What the requester does at a flush, once the prefix it has just frozen is
  // somebody else's problem.
  enum class FlushPolicy {
    // INLINE: run one SHARE of the rebuild (Options::inline_work_factor) --
    // pieces in deadline order until the share is spent, a phase half done
    // included -- so the request thread's worst call is one share and not a
    // top compaction.  THREADED: hand the prefix
    // over and go, so that the rebuild actually overlaps the requester --
    // which is the only reason to have owner threads at all.
    kAuto,
    // Settle before returning, in BOTH shapes: drive (inline) or wait for
    // (threaded) every level to quiescence.  A flush that completes the
    // prefix a top compaction was waiting for then pays for that whole
    // compaction, which grows linearly with the capacity, so this is a
    // fixture setting and an A/B control rather than a way to run.
    kSettle,
    // Never settle.  The requester drives (inline) or waits (threaded) only
    // when it MUST, which is when it has no free prefix slot left.
    // That is the backpressure path, and it is also the only way to observe
    // the hierarchy with work outstanding.
    kHandOver,
  };

  struct Options {
    LevelArenaGeometry::Params geometry = [] {
      LevelArenaGeometry::Params params;
      params.tier_buckets = 0;  // resolve against max_accesses before allocation
      return params;
    }();
    // The USER key width, 1..64 bytes; 16 and wider is hashed to 16 stored
    // bytes, narrower is stored verbatim (StoredKeyBytes).
    size_t key_bytes = 8;
    size_t value_bytes = 16;  // the USER value width
    // Online access limit and the horizon used to size stash depths
    // (cpu_byteslice_level_arena_stash.hpp).
    // Initialization is separate. A request/chunk that would exceed this
    // limit throws before its probes or removals; accepted work can drain.
    // Construction rejects lifetimes whose seeded/speculative coordinates
    // or complete windows do not fit, before allocating table storage.
    uint64_t max_accesses = uint64_t{1} << 32;
    // AES normalization calls for user keys of 16 bytes or more, including
    // initialization, StoredKey(), and failed attempts. Unset allows one full
    // initialization plus max_accesses calls. Reservations are never refunded.
    std::optional<uint64_t> max_key_normalizations;
    // All routing-message evaluations, including repeats, padding and failed
    // attempts. Exhaustion is terminal and may interrupt accepted work.
    // The default is an arithmetic ceiling, not a cryptographic target.
    uint64_t max_routing_evaluations = std::numeric_limits<uint64_t>::max();
    // The master secret every tag key and dummy is derived from.  UNSET draws
    // a fresh one when the engine is CONSTRUCTED, so two engines built from
    // one Options, or from copies of it, never share one: two engines under
    // one secret would put equal keys at equal relative real-probe buckets
    // and draw the same dummy positions, so an observer of both could
    // correlate their accesses.  Pin it only to
    // make a run reproduce: a fixture, a benchmark.
    std::optional<crypto::SecretKeySeed> secret_seed;
    // See FlushPolicy.  The default resolves per shape, because the same
    // answer is not right for both: the inline executor has nobody else to run
    // the levels, and a threaded one that settled at every flush would have
    // owner threads and no overlap.
    FlushPolicy flush_policy = FlushPolicy::kAuto;

    // ---- the synchronous storage mode ------------------------------------

    // ONE REGION PER LEVEL, MERGED IN PLACE BY THE REQUEST THAT COMPLETES A
    // PREFIX (cpu_byteslice_level_arena_synchronous.hpp).  The same geometry,
    // jobs, residual routing and publications as the inline executor, so the
    // same certified bounds, in 8/7 against 135/56 main buckets per top
    // bucket at B = D = 8 (DESIGN.md); what it
    // gives up is overlap, since that request pays for every merge the prefix
    // triggers, a top compaction included.  Needs no owner threads, helpers
    // or lanes, and refuses FlushPolicy::kHandOver: every flush settles.
    bool synchronous = false;

    // ---- owner threads ----------------------------------------------------

    // How many owner threads drive the hierarchy.  ZERO is the inline
    // executor and has no threads at all.  Otherwise the levels are divided
    // into this many contiguous groups, each with a thread: `groups` below
    // when it is given, else the load heuristic's division (PlanLevelGroups
    // in cpu_byteslice_level_arena_rebuild_params.hpp), which balances the
    // groups' modeled demand.  It may not exceed `geometry.levels`: a thread
    // with no level would park forever and still cost a staging plan record.
    unsigned owner_threads = 0;
    // AN EXPLICIT DIVISION, highest group first, for a tuner or a fixture
    // (LevelArenaRebuildParams::groups).  Empty -- the default -- lets the
    // heuristic choose; otherwise it must hold exactly `owner_threads`
    // contiguous groups covering every level (ValidateLevelGroups).
    std::vector<LevelGroupPlan> groups;
    // WHEN the owner threads start, which is a question only because an
    // initialization cannot coexist with them ("this engine is untouched" is
    // not a property one thread can establish about storage several are
    // driving).  False starts them in the constructor, which is
    // what a caller that never bulk-loads wants.  True builds the group
    // drivers but leaves the threads unstarted until `StartOwnerThreads()`,
    // so a caller can `Initialize` first and then run.  It is NOT a
    // quiescence protocol -- the refusal stands unchanged, and what this
    // moves is the moment the first owner exists, not what an owner may
    // observe.  An engine left deferred has no owner to run its levels, so
    // whoever sets this owes the call.
    bool defer_owner_start = false;
    // How long an owner with nothing to do spins before it sleeps.  The
    // default (kLevelArenaOwnerSpinMicros, whose comment gives the reason)
    // is a calibration constant: waking a sleeping owner costs a futex wake
    // and a reschedule on the request thread's critical path, so a short spin
    // first avoids it whenever work arrives soon.  Zero parks immediately, which is a control and what
    // a fixture that means to catch an owner asleep wants; tune it per host.
    //
    // THE REQUESTER WAITING FOR A PREFIX SLOT SPINS THE SAME WINDOW.  A parked
    // requester has to be woken by level 1's publication, and at saturation
    // that wake would otherwise dominate level 1's cost per publication.
    uint64_t owner_spin_nanos =
        uint64_t{kLevelArenaOwnerSpinMicros} * 1000;
    // How long a parked owner or requester sleeps before it looks again
    // anyway.  The event protocol does not need this -- no wake is lost by
    // construction (cpu_byteslice_level_arena_event.hpp) -- so it is a safety
    // net, and its use is COUNTED rather than silent.
    unsigned park_retry_micros = 1000;

    // ---- preemptible phases ----------------------------------------------

    // THE REQUEST RATE THE REBUILD'S PIECES ARE SIZED FOR, in accesses per
    // second.  Every owner group cuts its phases into pieces no longer than
    // its SLICE LIMIT at this rate (GroupSliceLimitNanos) and stops a phase
    // between two pieces when its event is signalled, visiting its members
    // earliest deadline first, so a member whose deadline is near waits for
    // one piece rather than for a whole phase (a whole top phase is
    // proportional to the capacity; a piece is bounded by the slice limit).
    // 0 -- the default -- is the rate one sequential
    // requester saturates at on this geometry (SaturatedOnlineRate), which is
    // the fastest the windows ever close.  The output is byte-identical at
    // any finite nonnegative rate. The inline executor ignores it.
    double slice_target_rate = 0.0;
    // Pieces of at most this many bucket touches in every group, overriding
    // `slice_target_rate`: a fixture's knob for forcing many stops.  0 uses
    // the rate.
    size_t slice_touches = 0;
    // THE INLINE EXECUTOR'S SHARE PER FLUSH, as a
    // multiple of the rebuild's average work per flush
    // (LevelArenaFlushTouches), finite and positive. The resulting share must
    // fit the 64-bit touch counter. A flush runs pieces, earliest
    // deadline first, until it has spent this share, and leaves the rest -- a
    // phase half done included -- for the next flush.  Above 1 it keeps up on
    // average; backpressure still runs shares until a prefix slot frees.
    // FlushPolicy::kSettle drives every flush to quiescence instead.  Owner
    // threads ignore it.
    double inline_work_factor = kLevelArenaInlineWorkFactor;

    // ---- lanes and helper threads ----------------------------------------

    // THE MOST LANES A LEVEL'S STAGES RUN AT, and the table size below which
    // a level takes one (LevelLaneConfig).  A lane is a private stash array
    // of the full certified depth per level that takes lanes, so it is part
    // of the byte bill.  The output is byte-identical at every lane count:
    // lanes are contiguous runs of a stage's work and their stashes fold back
    // in lane order.  With one thread per group they run one after another;
    // what they buy is the ability to run on several.
    LevelLaneConfig lanes;
    // HELPER THREADS for the group that owns the top:
    // they run lanes of its shared phases, so the top's stages run on this
    // many threads plus the owner.  0 -- the default -- has none.  Only a job
    // with lanes (`lanes` above) shares; with none in that group the helpers
    // are not started.  Owner threads only.  HeuristicRebuildParams chooses
    // helpers and lanes together from a thread budget.
    unsigned top_helpers = 0;
    // HELPER THREADS for the group that owns LEVEL 1, when that is not the
    // top's group: the same lane sharing, for the other end of the hierarchy.
    // Level 1 is the rebuild's bottleneck whenever its finish is heavy (the
    // direct plan's offers), and its
    // owner cannot borrow the top's helpers.  Its jobs need lanes (`lanes`,
    // with a `min_buckets` its tables reach).  0 -- the default -- has none.
    unsigned bottom_helpers = 0;
    // THE COST MODEL the defaults above are chosen by: the division when
    // `groups` is empty, and the slice rate when `slice_target_rate` is 0
    // (LevelArenaRebuildCost; built-in calibration constants by default, a
    // target's own fit from `python -m analysis.oram_bench fit-rebuild`).
    LevelArenaRebuildCost rebuild_cost;
    // Time every rebuild piece by kind and stage class (LevelMergeJob::
    // EnableStageTiming): a measurement's switch, two clock reads per piece.
    bool time_rebuild_stages = false;
    // PRE-ROUTING (LevelState::Wiring::preroute): false never starts a
    // preparation before its carry is available, at any level, inline or
    // with owners.  Only when preparation runs changes -- the kernels, the
    // slots and the published tables are the same.  A measurement's control;
    // the synchronous mode has nothing to turn off and ignores it.
    bool preroute = true;
    // THE PER-MERGE LOG (cpu_byteslice_level_arena_merge_log.hpp): the last
    // this-many jobs of every level, with their stamps and, under
    // `time_rebuild_stages`, their work by phase and class.  Zero -- the
    // default -- keeps none and takes no stamp.  Incremental storage only.
    size_t merge_log_capacity = 0;
    // A DEADLOCK DETECTOR, not a deadline.  The REQUESTER's waits are
    // bounded by it, so that a protocol bug reports what every level was
    // waiting for instead of hanging a test suite: one backpressure wait for
    // a prefix slot (each spin and park cut at the deadline), and in a drain
    // or settle a stretch in which no owner is seen to move (a drain that
    // keeps moving, through a long top preparation say, does not expire).
    // Expiry throws std::runtime_error before the access mutates anything,
    // and the engine stays usable.  Waits that cannot be abandoned -- a
    // worker leaving its init hook, a batch or value pool's join -- use it
    // only above kAbortWaitFloorMillis and end the process on expiry.
    unsigned wait_limit_millis = 120 * 1000;
    // Run once on each owner thread, with its group index, before it drives
    // anything -- thread naming, affinity, a fixture's instrumentation.  A
    // hook that throws is a CONSTRUCTION failure and not a surprise for the
    // first access: the constructor waits for every worker to pass it, then
    // cancels, joins and rethrows.
    std::function<void(unsigned)> worker_init;
    // The same, on each of the top group's HELPER threads (index 0 ..
    // top_helpers - 1), which a caller placing the rebuild must place too: a
    // helper is created by the thread that starts the owners, so without this
    // it inherits that thread's affinity -- a pinned request thread's single
    // core included.
    std::function<void(unsigned)> helper_init;

    // THE NEAR/FAR BOUNDARY: the largest level whose rebuild is NEAR
    // work, meaning it wants to share the request thread's cache domain.
    // Zero -- the default -- leaves the grouping unconstrained;
    // any other level makes sure NO GROUP STRADDLES the boundary, so that
    // each group can be placed as a unit by `worker_init`.
    //
    // It is an explicit LEVEL and never a request to go and look at the host,
    // because the division it produces is part of what the engine is built
    // with, and a division that depended on which machine built the engine
    // would make two hosts disagree about one configuration.  `AutoNearMaxLevel` in
    // cpu_byteslice_level_arena_placement.hpp is what a caller that wants the
    // host's answer calls, once, before it builds anything.
    unsigned near_max_level = 0;

    // Online value columns. Default zero retains the inline value cascade.
    // Value workers need a dense prefix of at most ValueProgress::kMaxRun
    // (4096) buckets, prefix_flushes * stash_buckets; the constructor refuses
    // a longer one with std::invalid_argument.
    unsigned value_workers = 0;
    unsigned value_tail = 2;
    ValueKernel value_kernel = ValueKernel::kAuto;
    uint64_t value_spin_nanos = 200000;
    bool value_pause = true;
    bool value_monitor_wait = false;
    bool value_demote = false;
    bool value_profile = false;
    bool value_serial = false;  // deterministic split executor for validation
    std::function<void(unsigned)> value_thread_init;

    // ---- the batch path (DESIGN.md, "Batches and near/far placement") ----

    // The widest chunk `AccessBatch` cuts a caller's batch into, in lanes,
    // 1..64 (one mask word of lanes).  A chunk is one reader epoch and one
    // wave of overlapped misses per probed table; the width that pays is a
    // HOST property -- how many outstanding lines one core's miss handling
    // holds -- so it is a knob to sweep rather than a constant.  1 makes
    // `AccessBatch` a loop of serial accesses with the same answers, which is
    // what an A/B compares against.  In `kParallelTiles` this is the width
    // PER PARTICIPANT.
    unsigned batch_lanes = 16;
    BatchExecutionShape batch_execution = BatchExecutionShape::kChunkedCascade;
    // Opt-in bucket-owned scan of the initial dense prefix.
    bool batch_bucket_scan = false;
    bool batch_profile = false;
    // How many tiles this engine is BUILT for, the calling thread included.
    // It is a construction parameter and not a per-call one because each tile
    // is preallocated scratch and each helper is a persistent thread; a
    // caller may then run narrower with `SetBatchParticipants`.
    unsigned batch_participants = 1;
    // Where a lane's probe result lands.  Public and fixed per instance; it
    // changes instruction streams, never trace shape.
    BatchResultLayout batch_result_layout =
        BatchResultLayout::kSlicedPlaceAtLane;
    // How long a participant with no phase to run spins before it sleeps.
    // Phases of one call are microseconds apart, so a participant that
    // parked between them would hold up the REQUEST thread rather than the
    // rebuild; the default is the same window the owners use and its use is
    // counted rather than silent.
    uint64_t batch_spin_nanos = uint64_t{kLevelArenaOwnerSpinMicros} * 1000;
    // Run once on each batch participant (index >= 1; participant 0 is the
    // calling thread) before it takes any phase.  Same contract as
    // `worker_init`, and the hook a caller pins the near class with.
    std::function<void(unsigned)> batch_thread_init;
  };

  static constexpr const char* kAccessOverlapError =
      "level arena: two accesses overlapped on one reader epoch; requests "
      "must be serialized (threading rule 1)";

  explicit LevelArenaEngine(const Options& options)
      : LevelArenaEngine(options, options.secret_seed.has_value()
                                      ? *options.secret_seed
                                      : crypto::SecretKeySeed::Random()) {}

 private:
  // The one seed both key schedules come from, resolved once by the public
  // constructor and gone when construction ends -- see the note by
  // `threaded_` on why the engine keeps no copy.
  LevelArenaEngine(const Options& options, const crypto::SecretKeySeed& seed)
      : threaded_(options.owner_threads != 0),
        synchronous_(ValidSynchronous(options)),
        flush_action_(ResolveFlushAction(options.flush_policy, threaded_,
                                         synchronous_)),
        slice_touches_(options.slice_touches),
        inline_work_factor_(options.inline_work_factor),
        lanes_(options.lanes),
        time_rebuild_stages_(options.time_rebuild_stages),
        preroute_(options.preroute),
        merge_log_capacity_(options.merge_log_capacity),
        park_retry_(options.park_retry_micros),
        requester_spin_nanos_(options.owner_spin_nanos),
        wait_limit_(options.wait_limit_millis),
        geometry_(CheckedLifetimeGeometry(options)),
        layout_(LevelArenaStoredLayout(options.key_bytes,
                                       options.value_bytes, geometry_)),
        sizing_(geometry_, options.max_accesses),
        max_accesses_(options.max_accesses),
        max_key_normalizations_(ResolveKeyNormalizationLimit(options, geometry_)),
        user_key_bytes_(options.key_bytes),
        user_value_bytes_(options.value_bytes),
        routing_budget_(options.max_routing_evaluations),
        aes_keys_(MakeAesTagKeys(crypto::DeriveRoutingAesRoundKeys(seed),
                                 &routing_budget_)),
        key_hash_keys_(DeriveStoredKeyHashKeys(seed)),
        near_max_level_(options.near_max_level),
        batch_lanes_(options.batch_lanes),
        batch_participants_(options.batch_participants),
        participant_capacity_(options.batch_participants),
        batch_execution_(options.batch_execution),
        batch_bucket_scan_(options.batch_bucket_scan),
        batch_profile_enabled_(options.batch_profile),
        result_layout_(options.batch_result_layout),
        // The division of the levels is settled before anything else, because
        // two things are sized from it -- the plan pool's staging records (one
        // per owner thread) and the request and batch scratch -- and it
        // decides which neighbour each level has to wake.
        // With a near/far boundary it also settles which groups can be placed
        // together, which is why the boundary is resolved above it.
        groups_(ResolveLevelGroups(options, geometry_, layout_)),
        arenas_(synchronous_ ? nullptr
                             : std::make_unique<LevelArenaSet>(geometry_,
                                                               layout_)),
        dense_(geometry_, layout_),
        publisher_(LevelArenaPublisherConfig(geometry_, groups_.size(),
                                             synchronous_)) {
    if (user_key_bytes_ < 1 || user_key_bytes_ > kMaxUserKeyBytes) {
      throw std::invalid_argument(
          "level arena: the user key width must be 1..64 bytes");
    }
    if (user_value_bytes_ == 0) {
      throw std::invalid_argument("level arena: a value needs a byte");
    }
    if (layout_.key_bytes < 1 || layout_.key_bytes > kMaxKeyBytes) {
      throw std::invalid_argument("level arena: stored key_bytes must be 1..16");
    }
    if (!RoutingDigitFits(layout_)) {
      throw std::invalid_argument(
          "level arena: this geometry's tag cannot carry a radix digit");
    }
    ValidateBatchOptions(options);
    // A value worker's progress word names the winning bucket of a dense run
    // in 12 bits (ValueProgress::kMaxRun), and the longest dense run a probe
    // plan holds is a complete prefix of r0 s buckets.  Refused here, before
    // any thread starts, rather than by every probe that meets such a run.
    if (options.value_workers != 0 &&
        geometry_.DensePrefixBuckets() > ValueProgress::kMaxRun) {
      throw std::invalid_argument(
          "level arena: value workers need a dense prefix of at most 4096 "
          "buckets (prefix_flushes * stash_buckets, where stash_buckets is "
          "online_stash_entries / 64)");
    }
    BuildBoundaries();
    BuildOwnerRuntime();
    BuildScratch();
    // Before the levels, whose piece budget they set (GroupBudget).
    if (threaded_) {
      if (!(options.slice_target_rate >= 0.0) ||
          !std::isfinite(options.slice_target_rate)) {
        throw std::invalid_argument(
            "level arena: the slice target rate must be finite and "
            "nonnegative (zero selects the modeled rate)");
      }
      options.rebuild_cost.Validate();
      long_waits_.levels =
          std::make_unique<BlockedLevel[]>(kMaxLongWaits * geometry_.Levels());
      long_waits_.dense = std::make_unique<BlockedDense[]>(kMaxLongWaits);
      slice_nanos_per_line_ = options.rebuild_cost.SliceNanosPerLine();
      slice_target_rate_ =
          options.slice_target_rate > 0.0
              ? options.slice_target_rate
              : SaturatedOnlineRate(geometry_, layout_, options.rebuild_cost);
    } else {
      if (!(inline_work_factor_ > 0.0) ||
          !std::isfinite(inline_work_factor_)) {
        throw std::invalid_argument(
            "level arena: the inline executor's share per flush must be "
            "finite and positive; FlushPolicy::kSettle settles every flush "
            "instead");
      }
      inline_flush_touches_ = CheckedTouchBudget(
          inline_work_factor_ *
          LevelArenaFlushTouches(geometry_, layout_, sizing_));
      inline_order_.resize(geometry_.Levels());
      inline_deadlines_.resize(geometry_.Levels() + 1);
    }
    BuildLevels();
    AllocateScratch();
    BuildBatchTiles();
    // Check the ladder's buffer prediction against component tallies after
    // construction. This checks model consistency, not total allocation.
    bytes_ = LevelArenaEngineBytes(geometry_, layout_, sizing_, groups_.size(),
                                   participant_capacity_, batch_bucket_scan_,
                                   lanes_, synchronous_);
    ExpectPredictedBytes(TalliedBufferBytes(), bytes_, "this engine");
    if (synchronous_) {
      sync_->PublishEmptyTop();
    } else {
      levels_[geometry_.TopLevel()]->PublishEmptyTop();
    }
    // LAST, and with its own unwinding: a constructor that throws gets no
    // destructor, so anything already running has to be stopped and joined
    // here or it outlives the storage it is driving.  The batch
    // participants are started even on an inline engine -- they probe, they
    // do not rebuild, so they are independent of `owner_threads`.
    try {
      if (threaded_) {
        BuildGroupDrivers(options);
        BuildHelpers(options);
        // Building a driver allocates; only StartOwners makes a thread, so a
        // deferred engine is fully built and merely not yet running.
        owner_init_ = options.worker_init;
        helper_init_ = options.helper_init;
        if (!options.defer_owner_start) StartOwners(options.worker_init);
      }
      StartBatchParticipants(options);
      // Under the probe audit too: the audit is the requester's, and the
      // workers' real/dummy choices are a function of the progress it
      // publishes.
      if (options.value_workers) {
        ValueWorkerPool::Config c;
        c.workers = options.value_workers;
        c.serial = options.value_serial;
        c.tail = options.value_tail;
        c.kernel = options.value_kernel;
        c.spin_nanos = options.value_spin_nanos;
        c.pause = options.value_pause;
        c.monitor_wait = options.value_monitor_wait;
        c.demote = options.value_demote;
        c.init = options.value_thread_init;
        c.wait_limit_millis = static_cast<unsigned>(AbortWaitLimit().count());
        c.profile = options.value_profile;
        value_profile_enabled_ = options.value_profile;
        value_pool_ = std::make_unique<ValueWorkerPool>(c, layout_, *aes_keys_,
            publisher_.max_tables(), LiveTableSlots(geometry_, synchronous_));
        bytes_.Add(ValueWorkerPool::BufferBytes(options.value_workers, layout_,
            publisher_.max_tables(), LiveTableSlots(geometry_, synchronous_)));
      }
    } catch (...) {
      StopBatchParticipants();
      StopOwners();
      CancelLevels();
      throw;
    }
  }

 public:
  LevelArenaEngine(const LevelArenaEngine&) = delete;
  LevelArenaEngine& operator=(const LevelArenaEngine&) = delete;

  // The division an engine built from `options` will have, without building
  // it: what a caller placing the owner threads needs before construction.
  static std::vector<LevelGroupPlan> PlannedLevelGroups(const Options& options) {
    const LevelArenaGeometry geometry(ResolveLevelArenaTierGeometry(
        options.geometry, options.max_accesses));
    return ResolveLevelGroups(
        options, geometry,
        LevelArenaStoredLayout(options.key_bytes, options.value_bytes,
                               geometry));
  }

  // SHUTDOWN, in threading rule 8's order: stop accepting work, wake every wait so none of
  // them hangs, join every worker, and only THEN touch a lease or release
  // anything -- no arena may be freed while a worker lease or a reader
  // snapshot can still refer to it.
  ~LevelArenaEngine() {
    try { DrainPendingValue(); } catch (...) { /* pool already joined */ }
    value_pool_.reset();
    // The participants first: they hold no lease, but they may be inside a
    // plan, and nothing may be released while a probing thread is in it.
    StopBatchParticipants();
    StopOwners();
    CancelLevels();
  }

  // ---- public geometry ----------------------------------------------------

  const LevelArenaGeometry& geometry() const { return geometry_; }
  const Layout& layout() const { return layout_; }
  const LevelArenaStashSizing& sizing() const { return sizing_; }
  size_t UserKeyBytes() const { return user_key_bytes_; }
  size_t ValueBytes() const { return user_value_bytes_; }
  bool RehashesKeys() const { return user_key_bytes_ >= kMaxKeyBytes; }
  uint64_t Capacity() const { return geometry_.CapacityEntries(); }
  // Level storage: main arenas, retained tier holes, masks and the pool.
  // The dense ring, jobs, plans and scratch are separate modeled buffers.
  size_t ArenaBytes() const {
    return synchronous_ ? SynchronousLevels::ArenaBytes(geometry_, layout_)
                        : CheckedSizeAdd(geometry_.ArenaBytes(layout_),
                                         LevelArenaSet::TierPayloadBytes(
                                             geometry_, layout_),
                                         "arena and tier pool bytes");
  }

  // Modeled buffers by role, not total heap allocation or resident memory.
  // Component objects, wiring containers and runtime overhead are excluded;
  // see cpu_byteslice_level_arena_bytes.hpp for the accounting boundary.
  const LevelArenaByteBill& BufferByteBill() const { return bytes_; }
  // Compatibility spelling, with the same buffer-only contract.
  const LevelArenaByteBill& ByteBill() const { return BufferByteBill(); }

  // How the levels are driven.  `owner_groups()` is one even inline, because
  // the plan pool's staging records are sized per executing thread either way
  // and the inline executor is one such thread.
  bool threaded() const { return threaded_; }
  // Start the owner threads a deferred construction did not.  Idempotent, and
  // a no-op on an inline engine, so a caller may put it in front of every
  // entry point rather than tracking which one comes first.  It is the only
  // thing standing between a deferred engine and a hierarchy nobody drives,
  // so it must not be forgotten; `Initialize` is the one call that belongs
  // BEFORE it.
  //
  // A START THAT THROWS IS TERMINAL.  A thread that could not be created, or
  // a hook that threw, leaves only some groups running, and a hierarchy with a
  // level nobody drives would hang the first drain.  So every thread already
  // started is stopped and joined, the original exception is latched, and
  // this call and every later one re-raise it.  There is no restart.
  void StartOwnerThreads() {
    routing_budget_.RequireAvailable();
    if (!threaded_ || owners_started_) return;
    if (failure_) std::rethrow_exception(failure_);
    try {
      StartOwners(owner_init_);
    } catch (...) {
      StopOwners();
      LatchFailure(std::current_exception(), "");
      throw;
    }
  }
  size_t owner_groups() const { return groups_.size(); }
  // The boundary the grouping was planned against; 0 when the near/far split
  // is off, which is the default.
  unsigned near_max_level() const { return near_max_level_; }
  const LevelGroupPlan& owner_group(size_t i) const { return groups_.at(i); }
  // Only with the hierarchy quiesced: a group's counters are its thread's.
  const LevelGroup& group_driver(size_t i) const { return *drivers_.at(i); }
  // The helper threads the top's group really started (0 when no job of that
  // group has lanes), and the lane configuration every level was built with.
  unsigned top_helper_threads() const { return helper_count_; }
  const LevelLaneConfig& lane_config() const { return lanes_; }
  // Lanes the top group's helpers ran; 0 without helpers.
  uint64_t helper_lanes() const {
    return helpers_ == nullptr ? 0 : helpers_->lanes_run();
  }
  // The same for level 1's group (Options::bottom_helpers).
  unsigned bottom_helper_threads() const { return bottom_helper_count_; }
  uint64_t bottom_helper_lanes() const {
    return bottom_helpers_ == nullptr ? 0 : bottom_helpers_->lanes_run();
  }
  const OwnerWaitStats& requester_waits() const { return requester_waits_; }
  // Slow-path-only backpressure episodes and their total nanoseconds; see
  // RecordBackpressure.
  struct RequesterBackpressure {
    WaitCounter episodes;
    WaitCounter nanos;
  };
  const RequesterBackpressure& requester_backpressure() const {
    return requester_backpressure_;
  }
  // THE LEAST BOUND ON A WAIT THAT CANNOT BE ABANDONED: every owner, helper,
  // batch participant or value worker leaving its init hook, and a batch or
  // value pool's join.  A thread still inside cannot be joined or released,
  // so expiry ends the process; the wait limit, a deadlock detector a caller
  // may set small, bounds these only when it is longer (AbortWaitLimit).
  static constexpr unsigned kAbortWaitFloorMillis = 120 * 1000;
  // WHAT THE LONGEST REQUESTER WAITS WERE WAITING ON, for the stall
  // report.  A backpressure wait that passes kLongWaitNanos
  // records BlockedDiagnosis()'s numbers once, while it is still waiting; the
  // first kMaxLongWaits are kept.  The wait is inside an access, so the
  // record goes into storage reserved at construction and is formatted here,
  // as BlockedDiagnosis() would have read it.  Diagnostic only, and torn in
  // the way that report always is with owner threads running.
  static constexpr uint64_t kLongWaitNanos = 10 * 1000 * 1000;
  static constexpr size_t kMaxLongWaits = 16;
  std::vector<std::string> long_waits() const {
    std::vector<std::string> out;
    for (size_t i = 0; i < long_waits_.count; ++i) {
      out.push_back(FormatBlocked(&long_waits_.levels[i * geometry_.Levels()],
                                  long_waits_.dense[i]));
    }
    return out;
  }
  uint64_t owner_failures() const {
    return runtime_ == nullptr ? 0 : runtime_->failures();
  }
  std::string first_owner_failure() const {
    return runtime_ == nullptr ? std::string() : runtime_->first_failure();
  }
  // The requester's own failure latch, in either shape: a step of the INLINE
  // executor that threw, or a batch interrupted after its probes had removed
  // entries.  Empty while healthy.  Once set it is permanent, and every later
  // access, batch and drain re-raises the exception it holds, as an owner's
  // failure is re-raised with threads: the state it left can be
  // missing entries, and an engine that went on answering would answer from
  // that state without saying so.
  const std::string& first_failure() const { return failure_what_; }
  // Whether this engine refuses further work: the requester's latch above or
  // an owner's (first_owner_failure).  Either is permanent.  On the
  // requester's thread, like first_failure().
  bool Failed() const noexcept {
    return routing_budget_.exhausted() || (value_pool_ && value_pool_->Failed()) ||
           failure_ != nullptr || (runtime_ != nullptr && runtime_->failed());
  }

  // ONLINE accesses and stash flushes, from zero.  A direct initialization
  // seeds the ring's own counters to the synthetic run it stands for, which
  // is the scheduling coordinate every level's deadlines are read against,
  // so it is subtracted here rather than left out there: the public contract
  // is that initialization leaves the online count at zero.
  uint64_t AccessCount() const {
    return dense_.positions() - seeded_positions_;
  }
  // The same preflight for the backpressure wait: with owner threads, wait
  // now for the prefix slot that `accesses` more inserts would complete, so
  // that none of those accesses can be refused for one after an earlier one
  // has committed.  A slot, once free, stays free until this thread takes
  // it.  Inline nothing is waited for here (the inline flush drives the
  // levels and throws only when none can move); a unit found full is
  // flushed either way.  Call it after RequireAccessBudget.
  void SecurePrefixSlots(size_t accesses) {
    if (dense_.UnitFillsWithin(accesses)) SecureInserts(accesses);
  }
  // Preflight for adapters that compose several accesses (e.g. a key-changing
  // callback). The single-requester/no-reentry contract keeps this budget
  // stable until those accesses complete. This does not reserve crypto calls.
  void RequireAccessBudget(uint64_t accesses) const {
    RequireHealthy();
    const uint64_t used = AccessCount();
    if (used > max_accesses_ || accesses > max_accesses_ - used) {
      throw std::overflow_error("level arena: max_accesses would be exceeded");
    }
    if (accesses > std::numeric_limits<uint64_t>::max() - dense_.positions()) {
      throw std::overflow_error("level arena: access position range exhausted");
    }
  }
  // Single-requester accounting, also used by const StoredKey(). Parallel
  // batches reserve on that requester before dispatching any conversions.
  // Reserved inputs, an upper bound on actual calls even after rollback.
  uint64_t KeyNormalizationCount() const { return key_normalizations_; }
  uint64_t MaxKeyNormalizations() const { return max_key_normalizations_; }
  // Thread-safe reservation count; it includes in-flight work and is never
  // reset by initialization rollback. Distinct messages <= count <= limit.
  uint64_t RoutingEvaluationCount() const { return routing_budget_.count(); }
  uint64_t MaxRoutingEvaluations() const { return routing_budget_.limit(); }
  void RequireKeyNormalizationBudget(uint64_t inputs) const {
    if (!RehashesKeys()) return;
    if (inputs > max_key_normalizations_ - key_normalizations_) {
      throw std::overflow_error("level arena: key normalization budget exhausted");
    }
  }
  uint64_t FlushCount() const {
    return dense_.flushes() - seeded_flushes_;
  }
  size_t StashSize() const { return dense_.stash_size(); }
  const DensePrefixRing& dense() const { return dense_; }
  const LevelArenaPublisher& publisher() const { return publisher_; }
  LevelArenaPublisher& publisher() { return publisher_; }
  const LevelState& level(unsigned l) const {
    if (synchronous_) {
      throw std::logic_error(
          "level arena: a synchronous engine has no level state machines; "
          "see synchronous_levels()");
    }
    return *levels_.at(l);
  }
  unsigned ValueWorkers() const { return value_pool_ ? value_pool_->count() : 0; }
  struct ValueRequestTiming {
    uint64_t samples = 0, publish = 0, boundary = 0, tail = 0, wait = 0;
    uint64_t drains = 0, drain_ticks = 0, inserts = 0, insert_ticks = 0;
  };
  const ValueRequestTiming& ValueRequestProfile() const { return value_request_timing_; }
  ValueTiming ValueWorkerProfile(unsigned i) const { return value_pool_->timing(i); }
  bool PendingValue() const { return pending_bucket_ != nullptr; }

  bool synchronous() const { return synchronous_; }
  // The synchronous mode's levels, or null.
  const SynchronousLevels* synchronous_levels() const { return sync_.get(); }
  // The last TopMergeLog::kCapacity top merges' lifecycle records
  // (oldest first), in every mode.  Read after the run drains
  // (drain_rebuilds()): see cpu_byteslice_level_arena_top_log.hpp.
  std::vector<TopMergeRecord> TopMergeRecords() const {
    return top_log_.Snapshot();
  }
  // The per-merge log's records of `level` (oldest first), empty without the
  // log.  Read after the run drains, as the top's are.
  std::vector<LevelMergeRecord> LevelMergeRecords(unsigned level) const {
    if (merge_log_ == nullptr) return {};
    return merge_log_->Snapshot(level);
  }
  bool preroute() const { return preroute_; }
  const LevelArenaSet& arenas() const { return *Arenas(); }
  LevelArenaSet& arenas() { return *Arenas(); }

  uint64_t ProbeAuditViolations() const {
    return publisher_.audit().violations();
  }
  uint64_t RealProbes() const { return publisher_.audit().real_probes(); }

  // ---- direct initialization (DESIGN.md, "Direct initialization") -------

  // ONE-SHOT DIRECT INITIALIZATION.  Builds the TOP out of `count` input
  // records instead of writing them one access at a time: the records are
  // scattered over the top's own final region at its ordinary load and routed
  // there in place, so nothing walks the ladder and no staging table is
  // allocated.  Every other level stays empty, and its counters are seeded to
  // the values an ordinary run would have reached at this state -- which is
  // the whole correctness argument, because the state IS reachable (H =
  // D B^(L-1) complete prefixes, every non-top digit zero, the top at its
  // full digit D).
  //
  // `first` is a SINGLE-PASS input iterator whose dereference yields an
  // `InitializationEntry` -- a `UserKeyBytes()`-wide key and a
  // `ValueBytes()`-wide value, consumed before the increment.  Only
  // dereference and pre-increment are used and the iterator is never
  // replayed, so a generated input needs storage for exactly one record.
  //
  // `count` is public and at most `Capacity()`; it need not fill the table.
  // Empty input is a no-op and leaves the engine as the constructor left it.
  // At widths >=16 the entire count is reserved against the normalization
  // limit before iterator consumption. Logical rollback never refunds it.
  //
  // ONLY kDistinct, which is the caller's PROMISE that no stored key repeats
  // and not a resolution rule.  It is what makes the route's kNoDedup exact,
  // the same way "A holds each key at most once" makes it exact for an
  // ordinary top preparation.  The duplicate-resolving policies need an input
  // ordinal carried through routing and an ordered residual pass, which
  // nothing here implements; they are refused rather than
  // quietly treated as distinct, because a duplicate under kDistinct does not
  // fail -- it publishes the key twice.
  //
  // Legal only on an untouched engine, only once, and only with exclusive
  // access.  `AccessCount()` still reports online accesses from zero; the
  // seeded positions live in the dense ring's own counter.
  template <class InputIterator>
  void Initialize(InputIterator first, size_t count,
                  InitializationPolicy policy =
                      InitializationPolicy::kDistinct) {
    if (policy != InitializationPolicy::kDistinct) {
      throw std::invalid_argument(
          "level arena: only InitializationPolicy::kDistinct is implemented");
    }
    if (count > Capacity()) {
      throw std::invalid_argument(
          "level arena: an initialization's count exceeds Capacity()");
    }
    // INLINE ONLY, and refused rather than serialized: the owner threads are
    // running, and "this engine is untouched" is not a property one thread
    // can establish about storage several are driving.  Nothing is lost --
    // an initialization is a construction-time act -- and the alternative
    // would be a quiescence protocol whose only caller is this one.
    //
    // BEFORE the empty-input early return, so that whether this engine will
    // accept an initialization at all does not depend on how long the input
    // is: a caller that got silence for `count == 0` and a refusal for
    // `count == 1` would have learned the rule the hard way.  A failed start
    // joined its owners, so it is the latch that refuses here.
    RequireHealthy();
    RequireNoOwnerRunning("Initialize");
    RequirePristineForInitialization();
    if (count == 0) return;
    ReserveKeyNormalizations(count);

    // Records per destination bucket is the LOAD: 32 of a 64-entry bucket, so
    // count <= Capacity() = 32T is exactly "the input fits at that load".
    const auto scatter = [&](TableView main) {
      const InitialLoadPlan load =
          PlanInitialLoad(main.num_buckets, kBucketCapacity / 2, count);
      ScatterInitialRecords(main, load, first, [this](const uint8_t* key) {
        return EncodeReservedKey(key);
      });
    };
    if (synchronous_) {
      sync_->PublishInitialTop(scatter);
    } else {
      levels_[geometry_.TopLevel()]->PublishInitialTop(scatter);
    }

    // ...and then the counters the same run would have reached.  They are
    // seeded AFTER the publication, because an iterator that threw leaves
    // nothing published and this engine still pristine: nothing is
    // published until all records and metadata are valid, so a failed
    // initialization rolls back completely.
    const InitialSeed seed = DirectInitializationSeed(geometry_);
    for (unsigned l = 1; l < geometry_.Levels(); ++l) {
      if (synchronous_) {
        sync_->SeedAcceptedCarries(l, seed.level_carries[l]);
      } else {
        levels_[l]->SeedAcceptedCarries(seed.level_carries[l]);
      }
    }
    dense_.SeedDirectInitialization(seed);
    seeded_positions_ = seed.access_offset;
    seeded_flushes_ = seed.stash_flushes;
    initialized_ = true;
  }

  // ---- the public operations ----------------------------------------------

  // What the probe found, beyond whether it found anything: whether that entry
  // is a tombstone, and whether it is one with no older live copy of its key
  // (kMetaUnshadowed, meaningful only with the tombstone bit).  Both secret.
  struct FoundFlags {
    bool erased = false;
    bool unshadowed = false;
  };

  // WHETHER A TOMBSTONE THIS ACCESS INSERTS MAY BE MARKED UNSHADOWED: when its
  // probe found nothing, or found a tombstone that is itself unshadowed.  The
  // entry found is the freshest copy of the key, so in the second case every
  // older copy is that tombstone or older than it, and none of those is live
  // -- the new tombstone inherits the qualifier instead of losing it, so a
  // second miss on one key stays droppable at the top.  A found LIVE entry
  // clears it, and so does a found shadowing tombstone.  The caller ands in
  // whether it is inserting a tombstone at all.  Bitwise: all three are secret.
  static unsigned NoOlderLiveCopy(bool found, const FoundFlags& flags) {
    return static_cast<unsigned>(!found) |
           (static_cast<unsigned>(flags.erased) &
            static_cast<unsigned>(flags.unshadowed));
  }

  // WHETHER THE PROBE FOUND A LIVE COPY: found, and not a tombstone.  Both
  // flags are secret and the result is only their conjunction, so they meet
  // in a register select rather than in `&&`: the compiler can neither branch
  // on `found` alone nor split a caller's branch on the result into one
  // branch per flag.
  static bool Present(bool found, const FoundFlags& flags) {
    return core::obliSelectU64(found, 0, flags.erased) != 0;
  }

  bool ReadStored(KeyWords key, uint8_t* value_out) {
    FoundFlags flags;
    const bool found = Probe(key, value_out, /*zero_value_on_miss=*/true,
                             &flags);
    // A miss inserts a TOMBSTONE for the key it looked for, which is what
    // makes an absent read cost and leak what a present one does -- and what
    // keeps the next read of that key from repeating its bucket in every
    // family that survived.  Both flags are secret, so they are combined
    // bitwise and never with `||`.
    const unsigned insert_erased = static_cast<unsigned>(flags.erased) |
                                   static_cast<unsigned>(!found);
    InsertOnlineStash(key, value_out, /*real=*/true, insert_erased != 0,
                      /*unshadowed=*/
                      (insert_erased & NoOlderLiveCopy(found, flags)) != 0);
    return Present(found, flags);
  }

  // Explicitly probe before replacing the value. Use ExchangeStored when
  // the caller needs the previous value or presence result.
  void ReadThenWriteStored(KeyWords key, const uint8_t* value) {
    (void)Probe(key, discard_value_.get(), /*zero_value_on_miss=*/false,
                nullptr);
    InsertOnlineStash(key, value, /*real=*/true, /*erased=*/false,
                      /*unshadowed=*/false);
  }

  // No cascade, no reader epoch, no existence-dependent branch.  The dense
  // builder needs each UNIT internally unique, and the ordinary probe is
  // what would otherwise have cleared this key's older copy there; every older
  // frozen or published copy is resolved by the merge's own deduplication,
  // exactly as a probed write's would be.
  void WriteStored(KeyWords key, const uint8_t* value) {
    DrainPendingValue();
    // The one public operation that does not go through Probe, and therefore
    // the one that has to begin the access itself -- before the clear, which
    // removes an entry exactly as a probe does.
    BeginAccess();
    dense_.ClearFromCurrentUnit(key);
    InsertOnlineStash(key, value, /*real=*/true, /*erased=*/false,
                      /*unshadowed=*/false);
  }

  // Compatibility spelling; blind writes also replace existing keys.
  void WriteWithoutProbeStored(KeyWords key, const uint8_t* value) {
    WriteStored(key, value);
  }

  // Invoke once after the lookup, then commit either the updated value or a
  // source tombstone for a key-changing access. The callback must not reenter
  // this instance: Probe has removed the source and scratch is borrowed here.
  template <class Update>
  bool AccessStored(KeyWords key, uint8_t* value, Update&& update,
                    bool erase_source = false) {
    FoundFlags flags;
    const bool found = Probe(key, exchange_value_.get(),
                             /*zero_value_on_miss=*/true, &flags);
    const unsigned present = static_cast<unsigned>(found) &
                             (static_cast<unsigned>(flags.erased) ^ 1u);
    std::memcpy(value, exchange_value_.get(), user_value_bytes_);
    try {
      update(value, present != 0);
    } catch (...) {
      // Complete this access with the original logical contents. Restoring
      // a miss must preserve its tombstone, including the freshness flag.
      const unsigned erased = present ^ 1u;
      InsertOnlineStash(key, exchange_value_.get(), /*real=*/true,
                        erased != 0,
                        (erased & NoOlderLiveCopy(found, flags)) != 0);
      throw;
    }
    InsertOnlineStash(key, erase_source ? zero_value_.get() : value,
                      /*real=*/true, /*erased=*/erase_source,
                      (static_cast<unsigned>(erase_source) &
                       NoOlderLiveCopy(found, flags)) != 0);
    return present != 0;
  }

  bool EraseStored(KeyWords key) {
    FoundFlags flags;
    const bool found = Probe(key, discard_value_.get(),
                             /*zero_value_on_miss=*/false, &flags);
    InsertOnlineStash(key, zero_value_.get(), /*real=*/true, /*erased=*/true,
                      /*unshadowed=*/NoOlderLiveCopy(found, flags) != 0);
    return Present(found, flags);
  }

  bool EraseStored(KeyWords key, uint8_t* old_out) {
    FoundFlags flags;
    const bool found = Probe(key, old_out, /*zero_value_on_miss=*/true,
                             &flags);
    InsertOnlineStash(key, zero_value_.get(), /*real=*/true, /*erased=*/true,
                      /*unshadowed=*/NoOlderLiveCopy(found, flags) != 0);
    return Present(found, flags);
  }

  bool ExchangeStored(KeyWords key, const uint8_t* value, uint8_t* old_out,
                      bool insert) {
    // The proposed value is copied out BEFORE the probe writes old_out: a
    // caller may pass one buffer as both, and the probe's write would
    // otherwise destroy the value about to be stored.
    std::memcpy(exchange_value_.get(), value, user_value_bytes_);
    FoundFlags flags;
    const bool found = Probe(key, old_out, /*zero_value_on_miss=*/true,
                             &flags);
    const unsigned present = static_cast<unsigned>(found) &
                             (static_cast<unsigned>(flags.erased) ^ 1u);
    const unsigned store = present | static_cast<unsigned>(insert);
    core::obliAssignBytes(exchange_value_.get(), old_out, user_value_bytes_,
                          store ^ 1u);
    const unsigned unshadowed = NoOlderLiveCopy(found, flags) & (store ^ 1u);
    InsertOnlineStash(key, exchange_value_.get(), /*real=*/true,
                      /*erased=*/store == 0, /*unshadowed=*/unshadowed != 0);
    return present != 0;
  }

  // The wide-key forms. A user key above 8 bytes is stored verbatim up to 15
  // bytes and normalized to a 16-byte stored key from 16 (StoredKeyBytes).
  // 9..15-byte keys always compare exactly; see kWideKeySegmentMatch for 16.
  // Even a standalone normalization spends the lifetime budget; const does
  // not permit concurrent callers. Reserve before AES and never refund on
  // later failure.
  KeyWords StoredKey(const uint8_t* key) const {
    routing_budget_.RequireAvailable();
    ReserveKeyNormalizations(1);
    return EncodeReservedKey(key);
  }

  bool Read(const uint8_t* key, uint8_t* value_out) {
    RequireAccessBudget(1);
    return ReadStored(StoredKey(key), value_out);
  }
  void Write(const uint8_t* key, const uint8_t* value) {
    RequireAccessBudget(1);
    WriteStored(StoredKey(key), value);
  }
  void ReadThenWrite(const uint8_t* key, const uint8_t* value) {
    RequireAccessBudget(1);
    ReadThenWriteStored(StoredKey(key), value);
  }
  void WriteWithoutProbe(const uint8_t* key, const uint8_t* value) {
    RequireAccessBudget(1);
    WriteWithoutProbeStored(StoredKey(key), value);
  }
  bool Erase(const uint8_t* key) {
    RequireAccessBudget(1);
    return EraseStored(StoredKey(key));
  }
  bool Erase(const uint8_t* key, uint8_t* old_out) {
    RequireAccessBudget(1);
    return EraseStored(StoredKey(key), old_out);
  }
  bool Exchange(const uint8_t* key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    RequireAccessBudget(1);
    return ExchangeStored(StoredKey(key), value, old_out, insert);
  }

  // The <= 8-byte forms, refused rather than reinterpreted on a wide instance.
  bool Read(uint64_t key, uint8_t* value_out) {
    return ReadStored(Narrow(key), value_out);
  }
  void Write(uint64_t key, const uint8_t* value) {
    WriteStored(Narrow(key), value);
  }
  void ReadThenWrite(uint64_t key, const uint8_t* value) {
    ReadThenWriteStored(Narrow(key), value);
  }
  void WriteWithoutProbe(uint64_t key, const uint8_t* value) {
    WriteWithoutProbeStored(Narrow(key), value);
  }
  bool Erase(uint64_t key) { return EraseStored(Narrow(key)); }
  bool Erase(uint64_t key, uint8_t* old_out) {
    return EraseStored(Narrow(key), old_out);
  }
  bool Exchange(uint64_t key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    return ExchangeStored(Narrow(key), value, old_out, insert);
  }

  // ---- the batch API -----------------------------------------------------
  //
  // INDEPENDENT REQUESTS, ORDERED BY LANE.  A batch serves `n` requests whose
  // answers are the ones the SAME SEQUENCE of scalar calls would have given:
  // a write is visible to a later lane's read of its key, an erase to a later
  // lane's exchange, and so on.  What is NOT promised is serial program
  // equivalence: a lane's key, input and descriptor must not alias or depend
  // on another lane's output buffers.  When to read an input is the execution
  // shape's choice: the parallel tiles read every input before any output is
  // written, while the default chunked cascade reads a lane's input at that
  // lane's turn, after earlier lanes wrote theirs, and loads a later chunk's
  // keys after an earlier chunk's outputs.  With aliased buffers the result
  // therefore depends on the shape.  A write or exchange may overlap its OWN
  // `value_in` and `value_out`, including partially.
  //
  // Per request: `op` and `insert` are PUBLIC, `key` is `UserKeyBytes()`
  // wide, `value_in` is read by write and exchange lanes, and a non-null
  // `value_out` receives the key's value BEFORE that lane's own operation --
  // zeros when absent or erased -- for every operation including a write.
  // `found_out[i]`, when `found_out` is non-null, is whether request i's key
  // was present and not a tombstone before it ran.  Repeated keys are legal.
  //
  // Calls on one engine must still be serialized by the caller: threading
  // rule 1 permits ONE requester, the reader epoch refuses a second rather than
  // corrupting under it, and a batch does not change that -- it is one
  // requester issuing several requests at once, not several requesters.
  void AccessBatch(size_t n, const BatchRequest* requests, uint8_t* found_out) {
    AccessBatchImpl(n, requests, found_out);
  }
  void AccessBatch(size_t n, const BatchRequest64* requests,
                   uint8_t* found_out) {
    AccessBatchImpl(n, requests, found_out);
  }

  const BatchWorkStats& batch_profile(unsigned participant) const {
    return batch_profiles_.at(participant);
  }

  unsigned batch_lanes() const { return batch_lanes_; }
  unsigned batch_participants() const { return batch_participants_; }
  // The pool this engine was BUILT with, which is the ceiling on the above.
  unsigned batch_participant_capacity() const { return participant_capacity_; }
  BatchExecutionShape batch_execution() const { return batch_execution_; }
  BatchResultLayout batch_result_layout() const { return result_layout_; }
  // The widest combined job: one chunk in the chunked shape, one job over
  // every active tile in the parallel one.
  size_t MaxCombinedBatchLanes() const {
    return batch_execution_ == BatchExecutionShape::kParallelTiles
               ? size_t{batch_lanes_} * batch_participants_
               : size_t{batch_lanes_};
  }

  void SetBatchLanes(unsigned lanes) {
    if (lanes < 1 || lanes > kMaxBatchLanes) {
      throw std::invalid_argument(
          "level arena: batch lanes must be in [1, 64]");
    }
    batch_lanes_ = lanes;
  }

  // Between calls only, and never above the pool this engine was built with:
  // a participant is a preallocated tile and a persistent thread, and both
  // are construction-time decisions.
  void SetBatchParticipants(unsigned participants) {
    if (participants < 1 || participants > participant_capacity_) {
      throw std::invalid_argument(
          "level arena: batch participants must be in [1, "
          "batch_participant_capacity()]");
    }
    batch_participants_ = participants;
  }

  // What the participants' waits cost, for the benchmark's report.  Participant 0 is
  // the request thread's own wait for the others to retire a phase; the rest
  // are the helpers' waits for a phase to arrive.  Exact only between calls.
  const OwnerWaitStats& batch_waits(unsigned participant) const {
    if (participants_ == nullptr) {
      throw std::logic_error("level arena: this engine has no batch pool");
    }
    return participants_->waits(participant);
  }

  // ---- the executor -------------------------------------------------------

  // One deterministic sweep over every level, low to high.  Public because
  // the executor fixtures drive it directly -- a held reader across a publication is
  // exactly an owner stepping while an access is inside its epoch, which no
  // access path of its own can produce.
  bool StepOnce() {
    RequireHealthy();
    DrainPendingValue();
    bool paused = false;
    return SweepInline(PhaseYield{}, &paused, /*in_shares=*/false);
  }
  // Sweep until nothing moves.  Returns whether anything did.
  bool RunOwners() {
    RequireInline("RunOwners");
    bool any = false;
    size_t sweeps = 0;
    while (StepOnce()) {
      any = true;
      if (++sweeps > kMaxSweepsPerRun) {
        throw std::runtime_error(
            "level arena: the inline executor is not converging: " +
            BlockedDiagnosis());
      }
    }
    return any;
  }

  // Every accepted prefix merged as far as it will go.  Not "the hierarchy is
  // empty": a drain completes accepted work, it does not invent the carries a
  // half-full level is waiting for.
  //
  // Inline it is the sweep loop; with owner threads it is the quiescence
  // protocol at the top of cpu_byteslice_level_arena_owner.hpp, which is the
  // only way one thread can establish that several others have nothing left to
  // do.  Either way it leaves the hierarchy in the same state, and that is
  // what lets a fixture compare the two.
  void Drain() {
    RequireHealthy();
    DrainPendingValue();
    // A unit found full is frozen first, so that accepted work is never left
    // behind it when an exhausted request horizon forbids another access.  An
    // engine that has not failed does not leave one: a wait for a prefix slot
    // is refused before the access inserts (BeginAccess), and a flush that
    // throws after an insert is latched (FlushAfterInsert).  This is a guard.
    if (dense_.UnitFull()) FreezeFullUnit();
    if (!threaded_) {
      RunOwners();
      return;
    }
    AwaitQuiescence();
  }

  uint64_t sweeps() const { return sweeps_; }
  // The inline executor's share of the rebuild per flush, in bucket touches
  // (Options::inline_work_factor); 0 with owner threads.
  uint64_t inline_flush_touches() const { return inline_flush_touches_; }
  // The request rate the owner groups' pieces are sized for
  // (Options::slice_target_rate, resolved); 0 inline.
  double slice_target_rate() const { return slice_target_rate_; }
  // Flush shares that ended because the share was spent rather than because
  // nothing was left to do: the flushes that really left work behind.
  uint64_t inline_shares_spent() const { return inline_shares_spent_; }
  // The touches every flush share has charged (PieceTouches), lifetime: set
  // against inline_flush_touches() per flush, it says whether the share's
  // estimate (LevelArenaFlushTouches) matches what the pieces cost.
  uint64_t inline_touches_charged() const { return inline_touches_charged_; }
  // The cascade the LAST access ran, sampled inside its epoch: the plan it
  // really probed, which a sample taken before the access cannot promise.
  size_t LastProbeTables() const { return last_probe_tables_; }
  size_t LastProbeBuckets() const { return last_probe_buckets_; }
  // The main (hashed) tables among them, and the lifetime total over every
  // probing request: one plan's count per scalar access, `m` times it per
  // batch chunk of `m` lanes.
  size_t LastProbeMains() const { return last_probe_mains_; }
  uint64_t ProbeMains() const { return probe_mains_; }

  // What every level is waiting for, in one line per level: the stall
  // report, and the reason a stuck hierarchy says which dependency it is stuck
  // on rather than "the rebuild is behind".
  //
  // WITH OWNER THREADS IT IS ONLY EXACT WHEN THE HIERARCHY IS QUIESCENT, and
  // the one place that calls it anyway is the deadlock report: a hierarchy
  // that has stopped is by definition not quiescent, and a torn number naming
  // the dependency it stopped on is better than no report at all.  Nothing in
  // the engine acts on it.
  std::string BlockedDiagnosis() const {
    std::string out;
    for (unsigned l = 1; l <= geometry_.Levels() && synchronous_; ++l) {
      out += "level " + std::to_string(l) + " ordinal " +
             std::to_string(sync_->ordinal(l)) + "; ";
    }
    std::vector<BlockedLevel> levels(synchronous_ ? 0 : geometry_.Levels());
    BlockedDense dense;
    RecordBlocked(levels.data(), &dense);
    return out + FormatBlocked(levels.data(), dense);
  }

  // ---- diagnostics --------------------------------------------------------

  // The length of the cascade the NEXT access would run, which is the composed
  // plan's live half.  Taken inside a reader epoch, like every other read of
  // a plan.
  size_t ProbeListLength() {
    AccessEpoch epoch(this);
    const ProbePlan* plan = ComposedPlan();
    return plan->tables.size() - plan->first_live;
  }

  // The shapes of every table the next access would probe, newest first.  A
  // snapshot, taken inside the epoch and carrying no storage pointer, so it
  // stays valid after the epoch closes (ProbePlanSnapshot).
  //
  // `scope` is not a convenience: counting a hashed table's occupancy reads
  // every mask word of a level -- megabytes at the production point -- and it
  // happens inside the reader epoch, holding up every retirement meanwhile.
  // The default counts the dense tables alone.
  ProbePlanSnapshot PlanSnapshot(
      OccupancyScope scope = OccupancyScope::kDense) {
    AccessEpoch epoch(this);
    return SnapshotOf(*ComposedPlan(), scope);
  }

 private:
  // BlockedDiagnosis()'s numbers.  RecordBlocked reads them without
  // allocating, which is what lets a backpressure wait inside an access keep
  // them (long_waits); FormatBlocked turns them into the report's text.
  // `levels` has one entry per level, and neither touches it in the
  // synchronous mode, which reports its ordinals itself.
  struct BlockedLevel {
    uint64_t ordinal = 0;
    unsigned next_digit = 0;
    LevelBlock block = LevelBlock::kIdle;
    bool pending = false;
  };
  struct BlockedDense {
    uint64_t taken = 0;
    uint64_t complete = 0;
    uint64_t consumed = 0;
    uint64_t reclaimed = 0;
    size_t free_records = 0;
  };
  void RecordBlocked(BlockedLevel* levels, BlockedDense* dense) const {
    for (unsigned l = 1; l <= geometry_.Levels() && !synchronous_; ++l) {
      const LevelState& level = *levels_[l];
      BlockedLevel& out = levels[l - 1];
      out.ordinal = level.ordinal();
      out.next_digit = level.next_digit();
      out.block = level.last_block();
      out.pending = level.has_pending_job();
    }
    dense->taken = dense_.taken();
    dense->complete = dense_.complete_prefixes();
    dense->consumed = dense_.consumed();
    dense->reclaimed = dense_.reclaimed();
    dense->free_records = publisher_.free_records();
  }
  std::string FormatBlocked(const BlockedLevel* levels,
                            const BlockedDense& dense) const {
    std::string out;
    for (unsigned l = 1; l <= geometry_.Levels() && !synchronous_; ++l) {
      const BlockedLevel& level = levels[l - 1];
      out += "level " + std::to_string(l) + " ordinal " +
             std::to_string(level.ordinal) + " next digit " +
             std::to_string(level.next_digit) + ": " +
             LevelBlockName(level.block);
      if (level.pending) out += " (job pending)";
      out += "; ";
    }
    out += "dense taken " + std::to_string(dense.taken) + "/" +
           std::to_string(dense.complete) + " consumed " +
           std::to_string(dense.consumed) + " reclaimed " +
           std::to_string(dense.reclaimed) + "; plan records " +
           std::to_string(dense.free_records) + " free";
    return out;
  }

  // THE REQUESTER'S READER EPOCH, CLOSED AND ANNOUNCED ON EVERY EXIT.  Leaving
  // an epoch is the one event that can free a retired bank, a retired inbox
  // or a plan record (threading rule 8), so an owner registered as an epoch waiter
  // has to hear about every close -- not only the ones at the end of an
  // ordinary access, but a diagnostic's and an exception's as well.  Missing
  // one leaves that owner asleep until the next access or its park retry.
  //
  // Leave, THEN notify: the members are destroyed in reverse order, so the
  // guard leaves the epoch before `announce_` looks for waiters.  An owner
  // told first would find the epoch unchanged.  The announcement is armed
  // only once the guard has entered: a refused entry (a second requester, an
  // exhausted counter) closed nothing and has nothing to say.
  class AccessEpoch {
   public:
    explicit AccessEpoch(LevelArenaEngine* engine)
        : guard_(engine->publisher_.epoch(), kAccessOverlapError) {
      announce_.engine = engine;
      ArenaPauseAt(ArenaPause::kInsideReaderEpoch, 0);
    }

    AccessEpoch(const AccessEpoch&) = delete;
    AccessEpoch& operator=(const AccessEpoch&) = delete;

   private:
    struct Announce {
      LevelArenaEngine* engine = nullptr;
      ~Announce() {
        if (engine != nullptr) engine->NoteEpochClosed();
      }
    };
    Announce announce_;         // destroyed LAST: notifies
    ReaderEpoch::Guard guard_;  // destroyed FIRST: leaves
  };

  // What a flush does once its unit is frozen (FlushPolicy).
  enum class FlushAction : uint8_t { kNone, kShare, kSettle };
  static FlushAction ResolveFlushAction(FlushPolicy policy, bool threaded,
                                       bool synchronous) {
    if (synchronous) return FlushAction::kSettle;
    switch (policy) {
      case FlushPolicy::kSettle: return FlushAction::kSettle;
      case FlushPolicy::kHandOver: return FlushAction::kNone;
      case FlushPolicy::kAuto: break;
    }
    return threaded ? FlushAction::kNone : FlushAction::kShare;
  }

  // The division the engine is built with: the caller's, checked, or the
  // load heuristic's.  With helpers and lanes the top's group is planned on
  // its helpers' threads too.  The inline executor is one group.
  static std::vector<LevelGroupPlan> ResolveLevelGroups(
      const Options& options, const LevelArenaGeometry& geometry,
      const Layout& layout) {
    const unsigned levels = geometry.Levels();
    if (options.owner_threads == 0) {
      if (!options.groups.empty()) {
        throw std::invalid_argument(
            "level arena: an explicit division needs owner threads");
      }
      return {LevelGroupPlan{1, levels}};
    }
    if (!options.groups.empty()) {
      if (options.groups.size() != options.owner_threads) {
        throw std::invalid_argument(
            "level arena: an explicit division must hold one group per "
            "owner thread");
      }
      ValidateLevelGroups(levels, options.groups);
      const unsigned boundary = std::min(options.near_max_level, levels);
      if (boundary != 0 && options.groups.size() > 1) {
        for (const LevelGroupPlan& group : options.groups) {
          if (group.first <= boundary && group.last > boundary) {
            throw std::invalid_argument(
                "level arena: an explicit group straddles the near/far "
                "boundary");
          }
        }
      }
      return options.groups;
    }
    const unsigned top_threads =
        options.lanes.lanes > 1 ? 1 + options.top_helpers : 1;
    return PlanLevelGroups(
        geometry, layout, options.owner_threads,
        std::min(options.near_max_level, levels), top_threads,
        options.rebuild_cost,
        LevelResidualInputs{options.max_accesses});
  }

  LevelArenaSet* Arenas() const {
    if (arenas_ == nullptr) {
      throw std::logic_error(
          "level arena: a synchronous engine has no slot arenas");
    }
    return arenas_.get();
  }

  // The synchronous mode's refusals, checked before anything is built.
  static bool ValidSynchronous(const Options& options) {
    if (!options.synchronous) return false;
    if (options.owner_threads != 0 || options.top_helpers != 0 ||
        options.bottom_helpers != 0 || options.lanes.lanes > 1) {
      throw std::invalid_argument(
          "level arena: the synchronous mode runs every merge on the "
          "requester; it takes no owner threads, helpers or lanes");
    }
    if (options.flush_policy == FlushPolicy::kHandOver) {
      throw std::invalid_argument(
          "level arena: the synchronous mode settles every flush and cannot "
          "hand work over");
    }
    return true;
  }

  static constexpr size_t kMaxUserKeyBytes = 64;
  static constexpr size_t kMaxSweepsPerRun = 1u << 20;
  KeyWords Narrow(uint64_t key) const {
    return NarrowStoredKey(key, user_key_bytes_);
  }
  void ReserveKeyNormalizations(uint64_t inputs) const {
    RequireKeyNormalizationBudget(inputs);
    if (RehashesKeys()) key_normalizations_ += inputs;
  }
  KeyWords EncodeReservedKey(const uint8_t* key) const {
    return EncodeStoredKey(key, user_key_bytes_, key_hash_keys_);
  }

  // ---- construction -------------------------------------------------------

  static uint64_t ResolveKeyNormalizationLimit(
      const Options& options, const LevelArenaGeometry& geometry) {
    if (options.max_key_normalizations) return *options.max_key_normalizations;
    const uint64_t capacity = geometry.CapacityEntries();
    if (capacity > std::numeric_limits<uint64_t>::max() - options.max_accesses) {
      throw std::overflow_error("level arena: key normalization limit overflow");
    }
    return capacity + options.max_accesses;
  }

  static LevelArenaGeometry CheckedLifetimeGeometry(const Options& options) {
    LevelArenaGeometry geometry(ResolveLevelArenaTierGeometry(
        options.geometry, options.max_accesses));
    RequireLifetimeFits(geometry, options.max_accesses);
    return geometry;
  }

  size_t GroupOf(unsigned level) const {
    for (size_t i = 0; i < groups_.size(); ++i) {
      if (groups_[i].holds(level)) return i;
    }
    throw std::logic_error("level arena: that level belongs to no group");
  }

  // The event of the group that owns `level`, whichever group signals it.
  // A neighbour in the signaller's own group needs no WAKE -- a thread cannot
  // be asleep and running at once (see LevelState::Wiring) -- but the signal
  // is what stops a phase running later in the same round.  Without it, a
  // level that hands a credit or a carry to a neighbour the round has
  // already visited leaves that neighbour waiting behind the whole of the
  // next phase, and a one-owner engine then stalls the requester for a
  // whole phase.
  OwnerEvent* WakeFor(unsigned level) {
    if (!threaded_ || level < 1 || level > geometry_.Levels()) return nullptr;
    return events_[GroupOf(level)].get();
  }

  void BuildBoundaries() {
    if (synchronous_) return;
    boundaries_.resize(geometry_.Levels() + 1);
    receivers_.resize(geometry_.Levels() + 1);
    producers_.resize(geometry_.Levels() + 1);
    for (unsigned l = 2; l <= geometry_.Levels(); ++l) {
      boundaries_[l] = std::make_unique<LevelBoundary>(arenas_->At(l));
      // The receiver's constructor issues the initial credits, which is the
      // one program point that runs once by construction (threading rule 3).
      receivers_[l] = std::make_unique<BoundaryReceiver>(*boundaries_[l]);
      // ...and the producer at l - 1 is the only thing that may spend them.
      producers_[l - 1] = std::make_unique<BoundaryProducer>(*boundaries_[l]);
    }
  }

  // The events and the shared cancellation/quiescence state.  Built even when
  // `threaded_` is false -- at a cost of one object -- so that every path
  // below can ask the runtime a question instead of asking first whether there
  // is one; nothing ever signals an event nobody waits on, because the levels'
  // wake pointers are null in that mode.
  void BuildOwnerRuntime() {
    if (!threaded_) return;
    events_.reserve(groups_.size());
    std::vector<OwnerEvent*> all;
    all.reserve(groups_.size() + 1);
    for (size_t i = 0; i < groups_.size(); ++i) {
      events_.push_back(std::make_unique<OwnerEvent>());
      all.push_back(events_.back().get());
    }
    requester_event_ = std::make_unique<OwnerEvent>();
    all.push_back(requester_event_.get());
    // The helpers park on their own event, and it is woken with everything
    // else on a stop or a failure.  One per helper set.
    helper_event_ = std::make_unique<OwnerEvent>();
    all.push_back(helper_event_.get());
    bottom_helper_event_ = std::make_unique<OwnerEvent>();
    all.push_back(bottom_helper_event_.get());
    runtime_ = std::make_unique<OwnerRuntime>(groups_.size(), std::move(all));
  }

  // The piece budget of group `g`'s members: the group's slice limit in
  // bucket touches.  Inline a piece is the size of one share: the share is
  // checked between pieces, so a coarser piece would overrun it by that
  // piece.
  SubtaskBudget GroupBudget(size_t g) const {
    if (!threaded_) return SubtaskBudgetForTouches(inline_flush_touches_);
    if (slice_touches_ != 0) return SubtaskBudgetForTouches(slice_touches_);
    return SubtaskBudgetForTouches(SliceTouches(
        GroupSliceLimitNanos(geometry_, groups_.at(g), slice_target_rate_),
        layout_, slice_nanos_per_line_));
  }

  // THE TRANSIENT HALF OF 5's ACCOUNTING: one range table PER LEVEL, sized
  // from that level's widest pass (LevelArenaEngineBytes says why it is not
  // per executing thread).  Index 0 is unused, as everywhere levels index.
  void BuildScratch() {
    scratch_.resize(geometry_.Levels() + 1);
    for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
      scratch_[l] = std::make_unique<LevelMergeScratch>(
          layout_, MaxLevelMergeRangeBuckets(geometry_, sizing_, l),
          MaxLevelDfsAllocation(geometry_, sizing_, l));
    }
  }

  void BuildGroupDrivers(const Options& options) {
    drivers_.reserve(groups_.size());
    for (size_t i = 0; i < groups_.size(); ++i) {
      LevelGroup::Wiring wiring;
      wiring.index = static_cast<unsigned>(i);
      wiring.levels = groups_[i];
      for (unsigned l = groups_[i].first; l <= groups_[i].last; ++l) {
        wiring.members.push_back(levels_[l].get());
      }
      wiring.publisher = &publisher_;
      wiring.runtime = runtime_.get();
      wiring.event = events_[i].get();
      wiring.spin_nanos = options.owner_spin_nanos;
      wiring.park_retry = park_retry_;
      drivers_.push_back(std::make_unique<LevelGroup>(wiring));
    }
  }

  // The top's group gets `top_helpers` helper threads over its shared jobs,
  // lowest level first, and level 1's group -- when it is another group --
  // `bottom_helpers`.  Every job of the group with lanes is attached; a set
  // exists only if one is.
  void BuildHelpers(const Options& options) {
    const size_t top = GroupOf(geometry_.TopLevel());
    helpers_ = BuildHelperSet(top, options.top_helpers, helper_event_.get(),
                              options);
    if (helpers_ != nullptr) helper_count_ = options.top_helpers;
    if (options.bottom_helpers == 0) return;
    const size_t bottom = GroupOf(1);
    if (bottom == top) {
      throw std::invalid_argument(
          "level arena: level 1 shares the top's owner group, whose helpers "
          "are top_helpers; bottom_helpers are for a group of its own");
    }
    bottom_helpers_ = BuildHelperSet(bottom, options.bottom_helpers,
                                     bottom_helper_event_.get(), options);
    if (bottom_helpers_ != nullptr) {
      bottom_helper_count_ = options.bottom_helpers;
    }
  }

  std::unique_ptr<LevelHelpers> BuildHelperSet(size_t group, unsigned count,
                                               OwnerEvent* event,
                                               const Options& options) {
    if (count == 0) return nullptr;
    LevelHelpers::Wiring wiring;
    wiring.group = static_cast<unsigned>(group);
    for (unsigned l = groups_[group].first; l <= groups_[group].last; ++l) {
      LevelMergeJob& job = levels_[l]->job();
      if (job.lanes() <= 1) continue;
      job.AttachHelpers(event, events_[group].get(), GroupBudget(group));
      wiring.jobs.push_back(&job);
    }
    if (wiring.jobs.empty()) return nullptr;
    wiring.runtime = runtime_.get();
    wiring.event = event;
    wiring.spin_nanos = options.owner_spin_nanos;
    wiring.park_retry = park_retry_;
    return std::make_unique<LevelHelpers>(wiring);
  }

  // Like the owners: each helper runs its init hook first, and the caller
  // waits for every hook, so a hook that throws is a construction failure.
  // The hook's index runs over the top's helpers, then level 1's.
  void StartHelpers() {
    helper_threads_.reserve(helper_count_ + bottom_helper_count_);
    const auto start = [this](LevelHelpers* set, unsigned count,
                              unsigned first_index) {
      if (set == nullptr) return;
      for (unsigned i = 0; i < count; ++i) {
        helper_threads_.emplace_back(
            [this, set, index = first_index + i, init = helper_init_] {
              try {
                if (init) init(index);
              } catch (...) {
                RecordOwnerFailure(set->group(), "its helper-init hook");
                NoteWorkerStarted();
                return;
              }
              NoteWorkerStarted();
              try {
                set->Run();
              } catch (...) {
                RecordOwnerFailure(set->group(), "a helper thread");
              }
            });
      }
    };
    start(helpers_.get(), helper_count_, 0);
    start(bottom_helpers_.get(), bottom_helper_count_, helper_count_);
    if (helper_threads_.empty()) return;
    AwaitWorkerInit();
    runtime_->RethrowIfFailed();
  }

  void StartOwners(const std::function<void(unsigned)>& worker_init) {
    threads_.reserve(drivers_.size());
    for (size_t i = 0; i < drivers_.size(); ++i) {
      threads_.emplace_back([this, i, init = worker_init] {
        const unsigned index = static_cast<unsigned>(i);
        try {
          if (init) init(index);
        } catch (...) {
          RecordOwnerFailure(index, "its worker-init hook");
          NoteWorkerStarted();
          return;
        }
        NoteWorkerStarted();
        try {
          drivers_[i]->Run();
        } catch (...) {
          RecordOwnerFailure(index, "its owner loop");
        }
      });
    }
    AwaitWorkerInit();
    // A hook that threw is a construction failure, not a surprise for the
    // first access.  The caller's own exception is re-raised, so a
    // fixture that threw `std::runtime_error("no")` catches that.
    runtime_->RethrowIfFailed();
    StartHelpers();
    owners_started_ = true;
  }

  // Idempotent, and safe to call on a half-built engine: it is the unwinding
  // path of a throwing constructor as well as the destructor's.
  void StopOwners() {
    if (runtime_ != nullptr) runtime_->Stop();
    for (std::thread& worker : threads_) {
      if (worker.joinable()) worker.join();
    }
    threads_.clear();
    for (std::thread& helper : helper_threads_) {
      if (helper.joinable()) helper.join();
    }
    helper_threads_.clear();
  }

  // Give every unpublished destination back, so that a shutdown leaves no slot
  // leased.  Nothing is published here: a prepared merge's output was
  // never announced and its sources are still live.  It may run only after
  // every owner thread has been joined -- a lease can be abandoned only once
  // every task referring to it has stopped (threading rule 8).
  void CancelLevels() {
    if (!threads_.empty() || !helper_threads_.empty()) {
      std::fprintf(stderr,
                   "level arena: leases cancelled with owner threads still "
                   "running; a lease may be abandoned only after every task "
                   "referring to it has stopped (threading rule 8).\n");
      std::abort();
    }
    for (const std::unique_ptr<LevelState>& level : levels_) {
      if (level != nullptr) level->Cancel();
    }
  }

  void RecordOwnerFailure(unsigned group, const char* where) {
    std::string what = "level arena: owner group " + std::to_string(group) +
                       " failed in " + where;
    try {
      throw;
    } catch (const std::exception& error) {
      what += ": ";
      what += error.what();
    } catch (...) {
      what += ": a non-std exception";
    }
    runtime_->Fail(std::current_exception(), what);
  }

  void NoteWorkerStarted() {
    {
      std::lock_guard<std::mutex> lock(init_mutex_);
      ++workers_started_;
    }
    workers_started_changed_.notify_all();
  }

  // Every worker has run its init hook, so a hook that threw is a
  // CONSTRUCTION failure rather than something the first access
  // discovers.
  //
  // A hook that never returns ENDS THE PROCESS, and that is the honest
  // outcome rather than a harsh one.  The only other thing this could do is
  // throw -- and the constructor's unwinding then joins the threads, which is
  // a join on a thread that is still inside the hook, which is the same hang
  // with no message attached.  Detaching instead would leave a thread holding
  // `this` after the engine's storage is gone.  So it says what happened and
  // stops, in the style of every other "there is nothing to roll back to"
  // failure in this engine.  Its bound is AbortWaitLimit, never less than
  // kAbortWaitFloorMillis: a small wait limit must not turn a slow hook or a
  // slow thread start on a loaded host into the end of the process.
  void AwaitWorkerInit() {
    std::unique_lock<std::mutex> lock(init_mutex_);
    if (workers_started_changed_.wait_for(lock, AbortWaitLimit(), [this] {
          return workers_started_ == threads_.size() + helper_threads_.size();
        })) {
      return;
    }
    lock.unlock();
    std::fprintf(stderr,
                 "level arena: an owner or helper thread did not start in "
                 "time (its init hook, if any, never returned), so it can be "
                 "neither joined nor released and this engine cannot be "
                 "constructed or destroyed.\n");
    std::abort();
  }

  // The bound of the waits that end the process on expiry (thread start and
  // the pools' joins): the wait limit, but never less than
  // kAbortWaitFloorMillis.  Both are nonnegative counts, compared unsigned:
  // a signed 64-bit maximum compiles to VPMAXSQ here, which the timing test
  // does not measure, so the instruction census would refuse it.
  std::chrono::milliseconds AbortWaitLimit() const {
    const uint64_t limit = static_cast<uint64_t>(wait_limit_.count());
    return std::chrono::milliseconds(static_cast<int64_t>(
        std::max<uint64_t>(limit, kAbortWaitFloorMillis)));
  }

  // Component buffer tallies. Boundary and requester buffers still use their
  // predictors here: this is a consistency check, not an allocator census.
  LevelArenaByteBill TalliedBufferBytes() const {
    LevelArenaByteBill bill;
    if (synchronous_) bill.Add(sync_->bytes());
    else bill.Add(arenas_->bytes());
    for (unsigned l = 1; l <= geometry_.Levels() && !synchronous_; ++l) {
      bill.Add(levels_[l]->job_bytes());
      bill.Add(LevelBoundary::Bytes(geometry_.storage().At(l).inbox_count()));
    }
    bill.Add(dense_.bytes());
    bill.Add(publisher_.bytes());
    for (const std::unique_ptr<LevelMergeScratch>& scratch : scratch_) {
      if (scratch != nullptr) bill.Add(scratch->bytes());
    }
    bill.Add(RequestScratchBytes(geometry_, layout_, groups_.size(),
                                 synchronous_));
    for (const std::unique_ptr<LevelArenaBatchTile>& tile : tiles_) {
      bill.Add(tile->bytes());
    }
    bill.Add(bucket_batch_.bytes());
    return bill;
  }

  // An initialization reproduces the state a run reaches after H prefixes, so
  // it may only run on a state no run has moved: one access, one flush or one
  // published carry and the counters it would seed are no longer true.  Every
  // condition here is PUBLIC -- access counts, flush counts, carry ordinals --
  // and none of them is secret.
  void RequirePristineForInitialization() const {
    if (initialized_) {
      throw std::logic_error("level arena: this engine is already initialized");
    }
    if (dense_.positions() != 0 || dense_.flushes() != 0 ||
        dense_.stash_size() != 0) {
      throw std::logic_error(
          "level arena: this engine has already served accesses");
    }
    if (synchronous_ && !sync_->Pristine()) {
      throw std::logic_error(
          "level arena: this engine's hierarchy has already moved");
    }
    for (unsigned l = 1; l <= geometry_.Levels() && !synchronous_; ++l) {
      const LevelState& level = *levels_[l];
      // The top's ordinal is zero while it holds only the empty table the
      // constructor published; every other level's is zero until it accepts.
      if (level.ordinal() != 0 || level.has_pending_job() ||
          level.ready_carries() != 0) {
        throw std::logic_error(
            "level arena: this engine's hierarchy has already moved");
      }
    }
  }

  void RequireInline(const char* what) const {
    if (!threaded_) return;
    throw std::logic_error(
        std::string("level arena: ") + what +
        " drives the levels from the calling thread, and this engine has owner "
        "threads of its own; use Drain()");
  }

  // Weaker than RequireInline on purpose, and the difference is the whole
  // point of `defer_owner_start`.  StepOnce and RunOwners drive the levels
  // themselves, so they need an engine that has no owners AT ALL.  An
  // initialization needs only that no owner has started YET: what it refuses
  // is a second actor touching the storage while one thread calls this
  // pristine, and an unstarted thread is not an actor.
  void RequireNoOwnerRunning(const char* what) const {
    if (threads_.empty()) return;
    throw std::logic_error(
        std::string("level arena: ") + what +
        " is a construction-time act and this engine's owner threads are "
        "already running; build it with defer_owner_start and call "
        "StartOwnerThreads() afterwards");
  }

  void AllocateScratch() {
    probe_.Resize(publisher_.max_tables(),
                  LiveTableSlots(geometry_, synchronous_));
    probe_scratch_ = AllocateAligned64(layout_.value_bytes);
    probe_scratch2_ = AllocateAligned64(layout_.value_bytes);
    probe_run_ = AllocateAligned64(layout_.value_bytes);
    discard_value_ = AllocateAligned64(user_value_bytes_);
    zero_value_ = AllocateAligned64(user_value_bytes_);
    exchange_value_ = AllocateAligned64(user_value_bytes_);
    std::memset(zero_value_.get(), 0, user_value_bytes_);
  }

  void BuildLevels() {
    if (synchronous_) {
      SynchronousLevels::Wiring wiring;
      wiring.geometry = &geometry_;
      wiring.sizing = &sizing_;
      wiring.layout = layout_;
      wiring.aes_keys = aes_keys_.get();
      wiring.publisher = &publisher_;
      wiring.dense = &dense_;
      wiring.top_log = &top_log_;
      wiring.time_stages = time_rebuild_stages_;
      wiring.scratch.resize(geometry_.Levels() + 1, nullptr);
      for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
        wiring.scratch[l] = scratch_[l].get();
      }
      sync_ = std::make_unique<SynchronousLevels>(wiring);
      return;
    }
    levels_.resize(geometry_.Levels() + 1);
    if (merge_log_capacity_ != 0) {
      merge_log_ = std::make_unique<LevelMergeLog>(geometry_.Levels(),
                                                   merge_log_capacity_);
      dense_.EnableCompletionStamps();
    }
    for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
      LevelState::Wiring wiring;
      wiring.geometry = &geometry_;
      wiring.sizing = &sizing_;
      wiring.publisher = &publisher_;
      wiring.arena = &arenas_->At(l);
      wiring.receiver = l >= 2 ? receivers_[l].get() : nullptr;
      wiring.producer = l < geometry_.Levels() ? producers_[l].get() : nullptr;
      wiring.dense = l == 1 ? &dense_ : nullptr;
      wiring.scratch = scratch_[l].get();
      wiring.aes_keys = aes_keys_.get();
      wiring.layout = layout_;
      wiring.budget = GroupBudget(GroupOf(l));
      wiring.lanes = LevelLaneCount(geometry_, l, lanes_);
      wiring.top_log = &top_log_;
      wiring.merge_log = merge_log_.get();
      wiring.preroute = preroute_;
      // Whom this level wakes: the neighbour's group, this level's own
      // included (WakeFor), and nobody when there are no threads.
      wiring.wake_receiver = WakeFor(l + 1);
      wiring.wake_producer = WakeFor(l - 1);
      wiring.wake_requester = l == 1 ? requester_event_.get() : nullptr;
      levels_[l] = std::make_unique<LevelState>(l, wiring);
      levels_[l]->job().EnableStageTiming(time_rebuild_stages_);
    }
  }

  // ---- the batch path ----------------------------------------------------

  void ValidateBatchOptions(const Options& options) {
    if (options.batch_lanes < 1 || options.batch_lanes > kMaxBatchLanes) {
      throw std::invalid_argument(
          "level arena: batch lanes must be in [1, 64]");
    }
    if (options.batch_participants < 1 ||
        options.batch_participants > kMaxOnlineParticipants) {
      throw std::invalid_argument(
          "level arena: batch participants must be in [1, 8]");
    }
    // Checked BEFORE the shape is used below, because every later test of it
    // is an equality against one enumerator: an out-of-range value would fall
    // through every one of them and silently select the other shape.  Its
    // siblings -- lanes, participants and the result layout -- are all
    // validated here, so this one being unchecked was an omission.
    if (options.batch_execution != BatchExecutionShape::kChunkedCascade &&
        options.batch_execution != BatchExecutionShape::kParallelTiles) {
      throw std::invalid_argument(
          "level arena: batch_execution must be kChunkedCascade or "
          "kParallelTiles");
    }
    if (options.batch_bucket_scan &&
        options.batch_execution != BatchExecutionShape::kParallelTiles) {
      throw std::invalid_argument("level arena: bucket scans need parallel tiles");
    }
    if (options.batch_execution == BatchExecutionShape::kChunkedCascade &&
        options.batch_participants != 1) {
      // REFUSED rather than ignored.  The chunked shape is the control the
      // parallel shape is compared with, and a control that quietly
      // allocated idle threads would be measuring something else.
      throw std::invalid_argument(
          "level arena: the chunked batch shape runs on the calling thread "
          "alone; ask for kParallelTiles to spend participants");
    }
  }

  void BuildBatchTiles() {
    if (batch_bucket_scan_)
      bucket_batch_.Resize(participant_capacity_, user_value_bytes_);
    tiles_.reserve(participant_capacity_);
    tile_pointers_.reserve(participant_capacity_);
    for (unsigned t = 0; t < participant_capacity_; ++t) {
      tiles_.push_back(std::make_unique<LevelArenaBatchTile>());
      tiles_.back()->Resize(publisher_.max_tables(),
                            LiveTableSlots(geometry_, synchronous_),
                            layout_, user_value_bytes_,
                            geometry_.StashBuckets());
      tile_pointers_.push_back(tiles_.back().get());
      banks_[t] = &tiles_.back()->banks;
    }
  }

  void StartBatchParticipants(const Options& options) {
    BatchWorkerPool::Config config;
    config.participants = participant_capacity_;
    config.spin_nanos = options.batch_spin_nanos;
    config.park_retry = park_retry_;
    config.wait_limit = AbortWaitLimit();
    config.thread_init = options.batch_thread_init;
    participants_ = std::make_unique<BatchWorkerPool>(config);
  }

  void StopBatchParticipants() { participants_.reset(); }

  ProbeFamilyAudit* Audit() {
    return ProbeFamilyAudit::Enabled() ? &publisher_.audit() : nullptr;
  }

  void LoadBatchLane(LevelArenaBatchTile& tile, size_t j,
                     const BatchRequest& request) {
    tile.key[j] = EncodeReservedKey(request.key);
    tile.op[j] = request.op;
    tile.insert[j] = static_cast<uint8_t>(request.insert);
    tile.value_in[j] = request.value_in;
    tile.value_out[j] = request.value_out;
  }

  void LoadBatchLane(LevelArenaBatchTile& tile, size_t j,
                     const BatchRequest64& request) {
    tile.key[j] = Narrow(request.key);
    tile.op[j] = request.op;
    tile.insert[j] = static_cast<uint8_t>(request.insert);
    tile.value_in[j] = request.value_in;
    tile.value_out[j] = request.value_out;
  }

  template <class Request>
  void AccessBatchImpl(size_t n, const Request* requests, uint8_t* found_out) {
    RequireHealthy();
    DrainPendingValue();
    if (n == 0) return;
    if (requests == nullptr) {
      throw std::invalid_argument("level arena: a batch needs its requests");
    }
    const size_t width = MaxCombinedBatchLanes();
    const auto blind_write = [&](size_t lane) {
      return requests[lane].op == BatchOp::kWrite &&
             requests[lane].value_out == nullptr && found_out == nullptr;
    };
    for (size_t base = 0; base < n;) {
      if (blind_write(base)) {
        Write(requests[base].key, requests[base].value_in);
        ++base;
        continue;
      }
      // Write may leave payload insertion with the value workers. Finish it
      // and retry any pending full-unit flush before calculating room, so
      // the remaining width is positive and counts public lane positions.
      DrainPendingValue();
      BeginAccess();
      // Supersession and eager removal span the entire job, including all
      // parallel tiles. End that job at the next frozen-unit boundary: a
      // later lane must not remove or suppress a record from an earlier cut.
      // Public operation/output descriptors may end the chunk sooner.
      const size_t remaining = dense_.unit_entries() - dense_.stash_size();
      const size_t limit = std::min({width, n - base, remaining});
      size_t m = 1;
      while (m < limit && !blind_write(base + m)) ++m;
      // Once per CHUNK and not once per call, which is the scalar path's
      // cadence (`Probe` asks at every access): a caller that hands over a
      // million requests should learn that an owner has failed at the next
      // chunk boundary rather than at the end of its batch.
      BeginBatchJob(m);
      // Narrow requests reject on wide instances without using the hash key.
      // Byte requests reserve the whole chunk before any participant runs.
      if constexpr (std::is_same_v<Request, BatchRequest>) {
        ReserveKeyNormalizations(m);
      }
      uint8_t* const found = found_out != nullptr ? found_out + base : nullptr;
      if (batch_execution_ == BatchExecutionShape::kChunkedCascade) {
        RunBatchChunk(m, requests + base, found);
      } else {
        RunBatchJob(m, requests + base, found);
      }
      base += m;
    }
  }

  // ONE CHUNK ON ONE THREAD: dedup, one reader epoch over one plan, then the
  // forwarding chain and the inserts in lane order OUTSIDE it.  The order is
  // load bearing and is the serial path's: an insert may wait for a free
  // dense prefix slot, and waiting with a reader epoch open is what
  // threading rule 7 forbids and what would make every retirement this engine owes wait for
  // one caller's backpressure.
  //
  // FROM THE REMOVALS TO THE LAST INSERT IS ONE UNIT.  Every lane's match
  // leaves the current online-stash unit before any lane's insert puts it
  // back, so a throw in between drops every lane not yet inserted.
  // BeginBatchJob has already secured what the inserts need, which is why
  // nothing in between should throw; if something does, the engine is failed
  // rather than left answering without those entries (FailAfterRemovals).
  template <class Request>
  void RunBatchChunk(size_t m, const Request* requests, uint8_t* found_out) {
    LevelArenaBatchTile& tile = *tiles_[0];
    tile.lanes = m;
    for (size_t j = 0; j < m; ++j) LoadBatchLane(tile, j, requests[j]);
    DedupBatchLanes(tile.key.data(), m, layout_.key_bytes, &tile.dedup);
    bool removing = false;
    bool froze = false;
    try {
      {
        AccessEpoch epoch(this);
        const ProbePlan& plan = *ComposedPlan();
        const uint64_t dummy_base = ClaimBatchDummies(plan, m);
        PrepareLevelArenaBatchAddresses(plan, m, dummy_base,
                                        layout_.BucketBytes(), *aes_keys_,
                                        tile);
        ProbeLevelArenaBatchLanes(plan, layout_, result_layout_,
                                  tile, Audit());
        LevelArenaBatchTile* one[1] = {&tile};
        removing = true;
        ApplyLevelArenaBatchRemovals(plan, one, 1);
      }
      froze = CommitBatchChunk(tile, found_out);
    } catch (...) {
      if (removing) FailAfterRemovals();
      throw;
    }
    if (froze) FlushAfterInsert(/*freeze=*/false);
  }

  // THE FORWARDING CHAIN AND THE INSERTS, in lane order.  A lane that repeats
  // an earlier lane's key did not probe; its answer is the state that lane
  // LEFT, which is what the serial sequence would have found in the current
  // online stash.  Returns whether an insert froze a unit.
  bool CommitBatchChunk(LevelArenaBatchTile& tile, uint8_t* found_out) {
    const uint64_t duplicates = tile.dedup.duplicates;
    const uint64_t superseded = tile.dedup.superseded;
    const bool sliced = result_layout_ == BatchResultLayout::kSlicedPlaceAtLane;
    bool froze = false;
    for (size_t j = 0; j < tile.lanes; ++j) {
      BatchLaneInsert insert;
      insert.value = tile.insert_value.get();
      const uint8_t* const probe =
          sliced ? tile.sliced + j : tile.Row(j);
      const size_t stride = sliced ? kMaxBatchLanes : 1;
      const bool present = ForwardBatchLane(
          tile.op[j], tile.insert[j] != 0, probe, stride, tile.found[j],
          ((duplicates >> j) & 1u) != 0, tile.dedup.prev[j], tile.value_in[j],
          tile.value_out[j], j, tile.forward, &insert);
      if (found_out != nullptr) found_out[j] = static_cast<uint8_t>(present);
      froze |= InsertBatchLane(tile.key[j], insert,
                               /*superseded=*/((superseded >> j) & 1u) != 0);
    }
    return froze;
  }

  BatchStageStats* Profile(unsigned participant, BatchStage stage) {
    return batch_profile_enabled_
        ? &batch_profiles_[participant].stages[static_cast<size_t>(stage)] : nullptr;
  }

  template <class Fn>
  void RunBatchPhase(unsigned active, Fn&& fn) {
    BatchStageTimer timer(Profile(0, BatchStage::kJoinedPhase));
    participants_->RunPhase(active, std::forward<Fn>(fn));
  }

  // ONE COMBINED JOB OVER `active` TILES: prepare, probe and forward on the
  // participants, commit on this thread.  The phase boundaries are full
  // joins, because each phase reads what the previous wrote into ANOTHER
  // participant's bank -- the dedup spans the whole job, not one tile.
  // Bucket scans split probing into two joined phases; all phase failures
  // still join before releasing the reader epoch and its borrowed plan.  The
  // removals, the forward and the commit are one unit, as in RunBatchChunk.
  template <class Request>
  void RunBatchJob(size_t m, const Request* requests, uint8_t* found_out) {
    const unsigned active = batch_bucket_scan_
        ? static_cast<unsigned>(std::min<size_t>(batch_participants_, m))
        : static_cast<unsigned>((m + batch_lanes_ - 1) / batch_lanes_);
    const BatchPartition partition{m, active};
    RunBatchPhase(active, [&](unsigned t) {
      BatchStageTimer timer(Profile(t, BatchStage::kPrepare));
      LevelArenaBatchTile& tile = *tiles_[t];
      const size_t offset = partition.Offset(t);
      tile.lanes = partition.Count(t);
      for (size_t j = 0; j < tile.lanes; ++j) {
        LoadBatchLane(tile, j, requests[offset + j]);
      }
      PrepareParallelBatchInputs(tile.key.data(), tile.op.data(),
                                 tile.insert.data(), tile.value_in.data(),
                                 tile.lanes, tile.banks);
    });
    bool removing = false;
    bool froze = false;
    try {
      {
        AccessEpoch epoch(this);
        const ProbePlan& plan = *ComposedPlan();
        const uint64_t dummy_base = ClaimBatchDummies(plan, m);
        size_t dense_buckets = 0;
        const size_t dense_end = InitialDenseEnd(plan, &dense_buckets);
        const bool bucket_scan = batch_bucket_scan_ && active > 1 && dense_buckets > 1;
        if (bucket_scan) {
          // The prepare join publishes keys. The coordinator packs each global
          // group once; no workers write different columns of the same line.
          std::fill(bucket_batch_.keys.begin() + m,
                    bucket_batch_.keys.begin() + ((m + 63) / 64) * 64, KeyWords{});
          for (unsigned t = 0; t < active; ++t)
            std::copy_n(tiles_[t]->key.data(), tiles_[t]->lanes,
                        bucket_batch_.keys.data() + partition.Offset(t));
          const unsigned workers = static_cast<unsigned>(
              std::min<size_t>(active, dense_buckets));
          RunBatchPhase(active, [&](unsigned t) {
            PrepareBatchTile(t, active, plan, dummy_base, partition.Offset(t));
            if (t < workers) {
              BatchStageTimer timer(Profile(t, BatchStage::kDense));
              ScanLevelArenaBucketRange(plan, dense_end, dense_buckets, layout_,
                                       m, t, workers, bucket_batch_, *tiles_[t]);
            } else
              std::fill(tiles_[t]->clear_masks.begin(), tiles_[t]->clear_masks.end(), 0);
          });
          RunBatchPhase(active, [&](unsigned t) {
            LevelArenaBatchTile& tile = *tiles_[t];
            {
              BatchStageTimer timer(Profile(t, BatchStage::kMerge));
              MergeLevelArenaBucketResults(bucket_batch_, workers, partition.Offset(t),
                                           layout_, tile);
            }
            BatchStageTimer timer(Profile(t, BatchStage::kCascade));
            ProbeLevelArenaBatchLanes(plan, layout_, result_layout_, tile, Audit(), dense_end);
            PublishBatchTile(tile);
          });
        } else {
          RunBatchPhase(active, [&](unsigned t) {
            ProbeBatchTile(t, active, plan, dummy_base, partition.Offset(t));
          });
        }
        removing = true;
        ApplyLevelArenaBatchRemovals(plan, tile_pointers_.data(), active);
      }
      // Forwarding reads immutable banks only.  Insertion may wait for a dense
      // prefix slot, so both this phase and the commit are outside the epoch.
      RunBatchPhase(active, [&](unsigned t) {
        LevelArenaBatchTile& tile = *tiles_[t];
        BatchStageTimer timer(Profile(t, BatchStage::kForward));
        ForwardParallelBatchTile(banks_.data(), active, t, tile.metadata,
                                 tile.results);
      });
      froze = CommitBatchJob(active, found_out);
    } catch (...) {
      if (removing) FailAfterRemovals();
      throw;
    }
    if (froze) FlushAfterInsert(/*freeze=*/false);
  }

  void PrepareBatchTile(unsigned t, unsigned active, const ProbePlan& plan,
                      uint64_t dummy_base, size_t request_offset) {
    LevelArenaBatchTile& tile = *tiles_[t];
    // The dedup spans the JOB: a lane is a duplicate when an earlier lane of
    // any tile holds its key, so this reads every participant's bank.
    {
      BatchStageTimer timer(Profile(t, BatchStage::kMetadata));
      BuildParallelBatchMetadata(banks_.data(), active, t, layout_.key_bytes,
                                 tile.metadata);
    }
    BatchStageTimer timer(Profile(t, BatchStage::kAddresses));
    tile.dedup.duplicates = tile.metadata.duplicates;
    const uint64_t base =
        dummy_base + request_offset * plan.tables.size();
    PrepareLevelArenaBatchAddresses(plan, tile.lanes, base,
                                    layout_.BucketBytes(), *aes_keys_, tile);
  }

  void ProbeBatchTile(unsigned t, unsigned active, const ProbePlan& plan,
                      uint64_t dummy_base, size_t request_offset) {
    PrepareBatchTile(t, active, plan, dummy_base, request_offset);
    BatchStageTimer timer(Profile(t, BatchStage::kCascade));
    LevelArenaBatchTile& tile = *tiles_[t];
    ProbeLevelArenaBatchLanes(plan, layout_, result_layout_, tile,
                              Audit());
    PublishBatchTile(tile);
  }

  void PublishBatchTile(LevelArenaBatchTile& tile) {
    if (result_layout_ == BatchResultLayout::kSlicedPlaceAtLane) {
      // The value and meta lines were accumulated in the bank itself; only
      // the found line is left to store.
      StoreFlagLine(tile.found.data(), tile.lanes,
                    tile.banks.probe.get() +
                        (user_value_bytes_ + 1) * kMaxBatchLanes);
    } else {
      PublishParallelBatchProbe(tile.rows.get(), tile.row_stride,
                                tile.found.data(), tile.banks);
    }
  }

  // Returns whether an insert froze a unit.
  bool CommitBatchJob(unsigned active, uint8_t* found_out) {
    BatchStageTimer timer(Profile(0, BatchStage::kCommit));
    size_t at = 0;
    bool froze = false;
    for (unsigned t = 0; t < active; ++t) {
      LevelArenaBatchTile& tile = *tiles_[t];
      ParallelBatchResults& results = tile.results;
      for (size_t j = 0; j < tile.lanes; ++j, ++at) {
        if (tile.value_out[j] != nullptr) {
          std::memcpy(tile.value_out[j], results.PreviousRow(j),
                      user_value_bytes_);
        }
        if (found_out != nullptr) {
          found_out[at] = static_cast<uint8_t>((results.present >> j) & 1u);
        }
        // `unshadowed` is already resolved per lane here -- the tile forward
        // computed it from the same three bits `InsertBatchLane` spells out,
        // against the whole JOB's dedup rather than one tile's -- so it is
        // passed through rather than derived a second time.
        froze |= InsertAndFreeze(
            tile.key[j], results.InsertRow(j),
            /*real=*/((tile.metadata.superseded >> j) & 1u) == 0,
            /*erased=*/((results.erased >> j) & 1u) != 0,
            /*unshadowed=*/((results.unshadowed >> j) & 1u) != 0);
      }
    }
    return froze;
  }

  // THE UNSHADOWED QUALIFIER COMES FROM THE FORWARDING CHAIN, which gives
  // each lane the one the serial access would (ForwardBatchLane): a lane that
  // repeats an earlier lane's key sees the entry that lane left, qualifier
  // included, so a probe's `!found` is never taken for "no copy" once an
  // earlier lane of the chunk has written one -- that lane's live entry
  // clears the qualifier, as serially.  A lane that does not repeat one sees
  // its own probe, and every earlier CHUNK's inserts were already in the
  // online stash when this one probed (the composed plan's dense prefix IS
  // the live stash), so its probe means what it means serially.
  bool InsertBatchLane(KeyWords key, const BatchLaneInsert& insert,
                       bool superseded) {
    return InsertAndFreeze(key, insert.value, /*real=*/!superseded,
                           insert.erased, insert.unshadowed);
  }

  // The dummy counters a chunk of `m` lanes consumes, and the plan counters
  // the benchmark reports.  `m * tables` is a PUBLIC amount: it is a function of the
  // lane count and the plan and of nothing a key decides.
  uint64_t ClaimBatchDummies(const ProbePlan& plan, size_t m) {
    const uint64_t base =
        ReserveDummyCounters(dummy_counter_, m, plan.tables.size());
    last_probe_tables_ = plan.tables.size() - plan.first_live;
    last_probe_buckets_ = plan.probe_buckets + plan.prefix_buckets;
    last_probe_mains_ = plan.hashed.size();
    probe_mains_ += m * plan.hashed.size();
    return base;
  }

  // ---- the access path ----------------------------------------------------
  //
  // AN ACCESS REMOVES BEFORE IT INSERTS.  Its probe clears its key's match
  // from the current online-stash unit (and an unprobed write clears it
  // itself), and only afterwards does its insert put the key back.  So
  // everything that can REFUSE -- a failed engine, a flush that has to wait
  // for a prefix slot -- is done here, before the removal; after it, an
  // exception would take the key's newest value with it, or report an access
  // as failed that has taken effect.  What can still throw after the insert
  // is a failure, and it is latched (FlushAfterInsert).

  // A failure the requester has latched, or an owner's.
  void RequireHealthy() const {
    routing_budget_.RequireAvailable();
    if (failure_) std::rethrow_exception(failure_);
    if (threaded_) RequireOwnersHealthy();
    if (value_pool_) value_pool_->CheckHealthy();
  }

  // THE SLOT THIS ACCESS'S OWN INSERT NEEDS IS SECURED HERE, with owner
  // threads, ahead of the probe and never at the insert: the insert that
  // completes a prefix freezes its unit at once, that freeze waits for a free
  // prefix slot, and the wait can expire at the wait limit (a deadlock
  // detector; the condition it detected may have cleared by the next access).
  // A wait refused at the insert would find the probe's removal already
  // applied.  Waiting before the probe instead leaves a refused access
  // unapplied and the engine usable.  The wait is the one the freeze would have
  // done, moved ahead of the probe; the freeze then finds the slot free.
  // Inline, nothing here waits: the inline freeze drives the levels itself
  // and has no wall-clock limit, and its order is the one the replay oracles
  // model.
  //
  // A UNIT FOUND FULL IS FLUSHED HERE TOO, before the probe: `Insert` refuses
  // a full unit rather than clamping it.  An engine that has not failed no
  // longer leaves one -- the wait above is refused before the insert, and a
  // flush that throws after an insert is latched (FlushAfterInsert) -- so
  // this is a guard.
  //
  // The ordinary access executes one compare of the unit cursor here, as it
  // always has; it is true only for the one access in a unit whose insert
  // fills it (or a unit found full), and only that access runs SecureInserts.
  void BeginAccess() {
    RequireAccessBudget(1);
    if (dense_.UnitFillsWithin(1)) SecureInserts(1);
  }

  // The rare half of BeginAccess and SecurePrefixSlots: flush a unit found
  // full (the guard above), then, with owner threads, wait for the prefix
  // slots `accesses` more inserts would complete.  A public count: the ring's
  // cursor and the number of accesses.  A slot already free needs no wait
  // and no reclamation.  Out of line, so that the access path's code is the
  // compare and a call it does not take.
  __attribute__((noinline)) void SecureInserts(size_t accesses) {
    if (dense_.UnitFull()) FlushUnit();
    if (!threaded_) return;
    const uint64_t completions = dense_.PrefixesCompletedBy(accesses);
    if (completions != 0 && !dense_.HasPrefixSlots(completions)) {
      AwaitPrefixSlots(completions);
    }
  }

  // A BATCH APPLIES EVERY LANE'S REMOVAL BEFORE ANY LANE'S INSERT, so its
  // inserts' flushes cannot be allowed to refuse: a refusal at lane j would
  // drop every later lane whose match was already cleared.  What such a
  // flush can wait for is a prefix slot, and only when it completes a prefix;
  // the count of those is public (the lane count and the ring's cursor), so
  // the slots are secured here, before the probes.  A slot, once free, stays
  // free until this thread takes it.
  //
  // AccessBatchImpl has already normalized a pending full unit and capped
  // the whole job at its next boundary. It can complete at most one prefix,
  // so all slots needed by the commit can be secured before any removal.
  void BeginBatchJob(size_t lanes) {
    RequireAccessBudget(lanes);
    const uint64_t completions = dense_.PrefixesCompletedBy(lanes);
    if (completions != 0) AwaitPrefixSlots(completions);
  }

  // Latch the first failure; later ones are consequences.  `what` empty
  // keeps the exception's own message as the description.
  void LatchFailure(std::exception_ptr error, const std::string& what) {
    if (failure_) return;
    failure_ = error;
    failure_what_ = what;
    if (failure_what_.empty()) {
      try {
        std::rethrow_exception(error);
      } catch (const std::exception& e) {
        failure_what_ = e.what();
      } catch (...) {
        failure_what_ = "a non-std exception";
      }
    }
  }

  // A batch that threw after its removals: whatever it had not yet inserted
  // is gone, so this engine may not answer again.  Called from a catch
  // handler; the exception raised names the cause, and is the one every
  // later call re-raises.
  [[noreturn]] void FailAfterRemovals() {
    std::string what =
        "level arena: a batch failed after its probes had removed entries "
        "from the online stash, so entries are lost and this engine accepts "
        "no further work: ";
    try {
      throw;
    } catch (const std::exception& error) {
      what += error.what();
    } catch (...) {
      what += "a non-std exception";
    }
    LatchFailure(std::make_exception_ptr(std::runtime_error(what)), what);
    std::rethrow_exception(failure_);
  }

  // ---- inserting and flushing ---------------------------------------------

  void InsertOnlineStash(KeyWords key, const uint8_t* value, bool real,
                         bool erased, bool unshadowed) {
    if (!value_pool_) {
      dense_.Insert(key, value, real, erased, unshadowed);
      if (dense_.UnitFull()) FlushAfterInsert(/*freeze=*/true);
      return;
    }
    // Unconditional forwarding, including Write/Erase, misses and tail hits.
    // Only owned bytes survive the scalar call. Workers have joined already.
    const uint64_t started = value_profile_enabled_ ? ValueStamp() : 0;
    pending_bucket_ = dense_.NextInsertBucket();
    pending_slot_ = dense_.NextInsertSlot();
    value_pool_->Stage(value);
    dense_.Insert<false>(key, nullptr, real, erased, unshadowed);
    if (value_profile_enabled_) { ++value_request_timing_.inserts;
      value_request_timing_.insert_ticks += ValueStamp() - started; }
    if (dense_.UnitFull()) FlushAfterInsert(/*freeze=*/true);
  }

  // THE FLUSH AFTER AN INSERT THAT HAS TAKEN EFFECT: a scalar access's, or
  // a batch commit's (which froze its own units, `freeze` false).  Nothing
  // here is a refusal -- with owner threads the slot a freeze needs was
  // secured before the probe (BeginAccess, BeginBatchJob) -- so what can
  // still throw is a failure: the inline executor finding no level
  // able to move, a rebuild step, a value worker, a settle's wait.  It is
  // latched, as a batch's failure after its removals is, so that failed()
  // says so and no caller takes an applied access for a refused one.
  void FlushAfterInsert(bool freeze) {
    try {
      if (freeze) FreezeFullUnit();
      AfterFlush();
    } catch (...) {
      LatchFailure(std::current_exception(), "");
      throw;
    }
  }

  void DrainPendingValue() {
    if (!pending_bucket_) return;
    const uint64_t started = value_profile_enabled_ ? ValueStamp() : 0;
    value_pool_->Begin(nullptr, {}, 0, 0, pending_bucket_, pending_slot_, nullptr);
    pending_bucket_ = nullptr;
    ValueWorkerPool::Guard guard{value_pool_.get()};
    value_pool_->Finish(nullptr, 0);
    if (value_profile_enabled_) { ++value_request_timing_.drains;
      value_request_timing_.drain_ticks += ValueStamp() - started; }
  }


  // One entry into the current unit, and the unit frozen if that filled it.
  // The unit has room: BeginAccess flushes a unit it finds full before the
  // probe removes anything.  Returns whether it froze; the SETTLE, if the policy
  // wants one, is the caller's, because a batch runs it once after its last
  // insert rather than between two lanes.
  bool InsertAndFreeze(KeyWords key, const uint8_t* value, bool real,
                       bool erased, bool unshadowed) {
    dense_.Insert(key, value, real, erased, unshadowed);
    if (!dense_.UnitFull()) return false;
    FreezeFullUnit();
    return true;
  }

  // The flush: the one point at which this thread's reader epoch is provably
  // closed, and therefore the one place it may wait (threading rule 7) and the one place
  // the owners may run.
  void FlushUnit() {
    FreezeFullUnit();
    AfterFlush();
  }

  void FreezeFullUnit() {
    DrainPendingValue();
    if (publisher_.epoch().Inside()) {
      // Structural -- every access's epoch is closed before it inserts --
      // but checked, because if it were ever false the executor below would
      // stamp `e + 1` on everything it retired and free nothing, and the
      // requester would wait for a slot only it could release.
      throw std::logic_error(
          "level arena: a flush ran inside its own reader epoch, so nothing "
          "it retires can ever be reclaimed");
    }
    AwaitPrefixSlots(dense_.PrefixesCompletedBy(0));
    const bool completed = dense_.FreezeUnit();
    // ONLY WHEN A PREFIX COMPLETED, because that is the only thing level 1 can
    // act on -- at the default r0 = 8, seven flushes out of eight give it
    // nothing, and signalling anyway would be eight times the cross-thread
    // wakeups for the same work.  And AFTER the freeze, never before:
    // FreezeUnit's release store is what makes the finished prefix's buckets,
    // masks and slot generation visible, and a signal that ran first would
    // announce a prefix level 1 may not see (threading rule 8).
    if (completed && threaded_) events_[GroupOf(1)]->Signal();
  }

  // What the flush policy asks for after a freeze (flush_action_).
  void AfterFlush() {
    switch (flush_action_) {
      case FlushAction::kShare: RunFlushShare(); return;
      case FlushAction::kSettle: Settle(); return;
      case FlushAction::kNone: return;
    }
  }

  // Every level to quiescence: driven here inline, awaited with owners.
  void Settle() {
    if (!threaded_) {
      RunOwners();
      return;
    }
    AwaitQuiescence();
  }

  // One sweep with each level's phases asking `yield` between pieces.  A
  // step that stopped a phase ends the sweep there (`*paused`): the inline
  // executor's share of this flush is spent.  `in_shares` orders the levels
  // earliest deadline first, merges before preparations, which is what a
  // share runs; otherwise it is the plain sweep, low to high, which is
  // what StepOnce and a settle run.
  bool SweepInline(const PhaseYield& yield, bool* paused, bool in_shares) {
    RequireInline("StepOnce");
    RequireHealthy();
    // The requester's own reclamations come first, and they run HERE rather
    // than after the sweep because a level can be blocked on one of them: a
    // plan record the pool has not taken back, or a prefix slot only the
    // requester may free (threading rule 7).  `Observed()` is what an acquire load of
    // the reader epoch has actually reached, never a threshold.
    //
    // ReclaimPlans returns before it locks the publication mutex when no
    // retired plan is pending (a relaxed count: a stale zero only delays a
    // reclamation to the next sweep), so a sweep with nothing to reclaim
    // takes no lock here.
    bool progressed = false;
    try {
      const uint64_t safe = publisher_.epoch().Observed();
      progressed = dense_.ReclaimPrefixes(safe) != 0;
      progressed |= publisher_.ReclaimPlans(safe) != 0;
      if (synchronous_) {
        // Every complete prefix, merged as far as it carries, and its slot
        // back at once: the epoch is closed, so nothing it retired is read.
        if (sync_->MergeCompletedPrefixes() != 0) {
          progressed = true;
          ReclaimRequesterOwned();
        }
      } else if (!in_shares) {
        for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
          const LevelStepResult step =
              levels_[l]->Step(LevelStepMode::kAny, yield);
          progressed |= step.progressed;
          if (step.paused) {
            *paused = true;
            break;
          }
        }
      } else {
        // IN SHARES, EARLIEST DEADLINE FIRST, merges before preparations --
        // the owner groups' kDeadline order.  Low levels first would let their
        // speculative preparations take every share while the top's job ran
        // out its window, and backpressure then makes one flush pay for the
        // rest of it.
        for (unsigned l = 1; l <= geometry_.Levels(); ++l) {
          inline_order_[l - 1] = l;
          inline_deadlines_[l] = levels_[l]->NextJobDeadline();
        }
        for (size_t i = 1; i < geometry_.Levels(); ++i) {
          const unsigned m = inline_order_[i];
          size_t j = i;
          while (j > 0 &&
                 inline_deadlines_[inline_order_[j - 1]] > inline_deadlines_[m]) {
            inline_order_[j] = inline_order_[j - 1];
            --j;
          }
          inline_order_[j] = m;
        }
        bool moved = false;
        for (LevelStepMode mode :
             {LevelStepMode::kMergeFirst, LevelStepMode::kAny}) {
          for (unsigned i = 0; i < geometry_.Levels() && !*paused; ++i) {
            const LevelStepResult step =
                levels_[inline_order_[i]]->Step(mode, yield);
            moved |= step.progressed;
            *paused = step.paused;
          }
          if (moved || *paused) break;
        }
        progressed |= moved;
      }
    } catch (...) {
      // A THROWING STEP IS TERMINAL, here as on an owner thread.  A level
      // that threw mid-merge still holds what it took -- its carry, its
      // destination, a job half run -- and nothing in this engine retries a
      // merge under a fresh nonce (DESIGN.md), so whatever the next sweep
      // made of that state would be unreviewed.  Latched with the original
      // exception, which every later call re-raises.
      LatchFailure(std::current_exception(), "");
      throw;
    }
    ++sweeps_;
    return progressed;
  }


  // THE INLINE FLUSH'S SHARE (Options::inline_work_factor): sweeps, earliest
  // deadline first, until the pieces run have cost `inline_flush_touches_` or
  // nothing moves.  The cursor keeps a phase stopped here, so the next flush
  // resumes it where this one left off.  Returns whether anything moved.
  bool RunFlushShare() {
    uint64_t touched = 0;
    PhaseYield yield;
    yield.touches = &touched;
    yield.touch_limit = inline_flush_touches_;
    bool any = false;
    size_t sweeps = 0;
    while (touched < inline_flush_touches_) {
      bool paused = false;
      if (!SweepInline(yield, &paused, /*in_shares=*/true)) break;
      any = true;
      if (paused) {
        ++inline_shares_spent_;
        break;
      }
      if (++sweeps > kMaxSweepsPerRun) {
        throw std::runtime_error(
            "level arena: the inline executor is not converging: " +
            BlockedDiagnosis());
      }
    }
    inline_touches_charged_ += touched;
    return any;
  }

  // ---- the requester's waits ---------------------------------------------

  // The two reclamations this thread owns.  The prefix slots are the
  // requester's alone (threading rule 7); the plan records are anybody's, and this is
  // the requester's share of them.
  void ReclaimRequesterOwned() {
    const uint64_t safe = publisher_.epoch().Observed();
    dense_.ReclaimPrefixes(safe);
    publisher_.ReclaimPlans(safe);
  }

  // The dense ring's backpressure: until `completions` more prefixes can complete.  The
  // requester's epoch is closed, so it may wait.  Inline, it drives the
  // levels itself.  With owner threads, what it waits for is a notification
  // from level 1 that a prefix it published can now be freed; only this
  // thread may free one, so the reclamation runs here on every pass.
  // REQUEST-CORRELATED BACKPRESSURE: this is the requester's only
  // rebuild stall, so the time between finding no slot and getting one is
  // exactly the delay rebuild imposed on the request in progress.  Recorded
  // only here, on the slow path, so the fast path (`HasPrefixSlots` true at
  // once) reads no clock and touches no atomic; a caller attributes a request
  // by reading the pair before and after it, all on the requester thread.
  void RecordBackpressure(std::chrono::steady_clock::time_point began,
                          std::chrono::steady_clock::time_point ended) {
    requester_backpressure_.episodes.Bump();
    requester_backpressure_.nanos.Add(static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(ended - began)
            .count()));
  }

  void AwaitPrefixSlots(uint64_t completions) {
    if (!threaded_) {
      if (dense_.HasPrefixSlots(completions)) return;  // fast path: no clock
      const std::chrono::steady_clock::time_point inline_began =
          std::chrono::steady_clock::now();
      while (!dense_.HasPrefixSlots(completions)) {
        // In shares: the first one that frees a slot is enough, and a whole
        // settle could run a top compaction for it.
        const bool moved = RunFlushShare();
        if (!moved) {
          throw std::runtime_error(
              "level arena: no free dense prefix slot and no level can "
              "progress: " + BlockedDiagnosis());
        }
      }
      RecordBackpressure(inline_began, std::chrono::steady_clock::now());
      return;
    }
    ReclaimRequesterOwned();
    if (dense_.HasPrefixSlots(completions)) return;
    // Nothing can come back unless some level moves, and the chain that
    // unblocks level 1 can run anywhere above it, so this wakes everybody.  It
    // is once per backpressure event and not once per access.
    runtime_->WakeAll();
    const std::chrono::steady_clock::time_point began =
        std::chrono::steady_clock::now();
    const std::chrono::steady_clock::time_point deadline = began + wait_limit_;
    bool logged = false;
    for (;;) {
      RequireOwnersHealthy();
      // Read BEFORE the predicate, as every waiter in this engine does.
      const uint64_t generation = requester_event_->Generation();
      ReclaimRequesterOwned();
      const std::chrono::steady_clock::time_point now =
          std::chrono::steady_clock::now();
      if (dense_.HasPrefixSlots(completions)) {
        RecordBackpressure(began, now);
        return;
      }
      if (!logged && long_waits_.count < kMaxLongWaits &&
          now - began > std::chrono::nanoseconds(kLongWaitNanos)) {
        // Into storage reserved at construction: this is inside an access.
        const size_t i = long_waits_.count++;
        RecordBlocked(&long_waits_.levels[i * geometry_.Levels()],
                      &long_waits_.dense[i]);
        logged = true;
      }
      if (now > deadline) {
        throw std::runtime_error(
            "level arena: no free dense prefix slot after waiting for the "
            "owner threads: " + BlockedDiagnosis());
      }
      // Each spin and park ends at the deadline at the latest, so that the
      // limit bounds the whole wait whatever owner_spin_nanos and
      // park_retry_micros are.  Short of the deadline both are the options'.
      const std::chrono::nanoseconds left =
          std::chrono::duration_cast<std::chrono::nanoseconds>(deadline - now);
      const uint64_t spin = std::min<uint64_t>(
          requester_spin_nanos_, static_cast<uint64_t>(left.count()));
      const std::chrono::microseconds retry = std::min(
          park_retry_, std::chrono::ceil<std::chrono::microseconds>(left));
      requester_event_->Wait(generation, spin, retry,
                             [this] { return runtime_->cancelled(); },
                             &requester_waits_);
    }
  }

  // Each round requires a no-work acknowledgement from every group and no
  // progress since its request. Reclaim requester-owned state before starting
  // the round, so owners cannot wait on a resource only this thread returns.
  //
  // THE WAIT LIMIT BOUNDS A STALL, NOT THE DRAIN.  A drain waits out every
  // phase in flight, a speculative top preparation included, and that is
  // linear in the capacity.  So a round is cut at an eighth of the limit to
  // look at OwnerActivity, and the deadline restarts whenever it has moved;
  // only a whole limit in which no owner was seen to move throws.
  void AwaitQuiescence() {
    using Clock = std::chrono::steady_clock;
    const Clock::duration look = std::max<Clock::duration>(
        wait_limit_ / 8, std::chrono::milliseconds(1));
    Clock::time_point deadline = Clock::now() + wait_limit_;
    uint64_t seen = OwnerActivity();
    for (;;) {
      RequireOwnersHealthy();
      ReclaimRequesterOwned();
      const OwnerRuntime::DrainRound round = runtime_->BeginDrainRound();
      runtime_->WakeAll();
      const bool quiet = runtime_->AwaitDrainRound(
          round, std::min(deadline, Clock::now() + look));
      RequireOwnersHealthy();
      if (quiet) return;
      const Clock::time_point now = Clock::now();
      const uint64_t activity = OwnerActivity();
      if (activity != seen) {
        seen = activity;
        deadline = now + wait_limit_;
      } else if (now > deadline) {
        throw std::runtime_error(
            "level arena: the owner threads did not reach quiescence: " +
            BlockedDiagnosis());
      }
    }
  }

  // WHAT THE OWNERS HAVE VISIBLY DONE, for the drain's stall bound, from
  // counters they keep anyway: polls that moved something, a running phase
  // answering a signal between two pieces (stopped or declined; every drain
  // round signals every group, so a phase in flight answers at its next
  // piece), and lanes the helpers finished.  Monotone; any change is
  // progress.  A thread stuck inside one piece, or a group parked on helpers
  // that do not move, changes none of them.
  uint64_t OwnerActivity() const {
    uint64_t activity = runtime_->progress();
    for (const std::unique_ptr<LevelGroup>& driver : drivers_) {
      activity += driver->preemptions() + driver->preemptions_declined() +
                  driver->stops_for_credit();
    }
    if (helpers_ != nullptr) activity += helpers_->lanes_run();
    if (bottom_helpers_ != nullptr) activity += bottom_helpers_->lanes_run();
    return activity;
  }

  // An owner's failure becomes the requester's on its next call, with the
  // original exception rather than a description of it, and a shutdown in
  // progress is reported rather than waited out.
  void RequireOwnersHealthy() const {
    runtime_->RethrowIfFailed();
    if (runtime_->stopping()) {
      throw std::runtime_error(
          "level arena: this engine is shutting down; no further work is "
          "accepted");
    }
  }

  // Called by the REQUESTER right after it leaves a reader epoch, which is the
  // one event that can free a retired bank, a retired inbox or a plan record
  // (threading rule 8) -- always through AccessEpoch, so that no close, diagnostic
  // or exceptional, goes unannounced.  In the steady state it is one load of
  // a line nobody writes: an owner registers only when its whole group is
  // down to something the epoch is the only cure for.
  void NoteEpochClosed() {
    if (threaded_ && runtime_->HasEpochWaiters()) runtime_->WakeAll();
  }

  // The plan this access probes, with the dense half brought up to date.  It
  // is stale exactly when a publication has happened since (a new epoch, which
  // a recycled plan object gets too) or this thread has flushed since.
  ProbePlan* ComposedPlan() {
    ProbePlan* plan = publisher_.CurrentPlan();
    if (plan->epoch != prefix_epoch_ || prefix_flushes_ != dense_.flushes()) {
      dense_.FillDensePrefix(plan);
      prefix_epoch_ = plan->epoch;
      prefix_flushes_ = dense_.flushes();
#ifndef NDEBUG
      // The publication boundary validated the WORKER's half; this is the only
      // point at which the composed view exists, and the two halves meet
      // exactly where the dense consumption mark says they do.  Checked here
      // rather than per access, because the composed view changes only when
      // this branch runs.
      assert(PlanWindowsLaminar(*plan, plan->first_live) &&
             "the composed probe order is not laminar");
#endif
    }
    return plan;
  }

  // Both halves are table/'s shared resolvers: the dense memo and the hashed
  // AES pass.  The dense
  // PREFIX is in neither -- its entries move with every flush and Probe()
  // writes them itself.
  void ResolveProbeAddresses(const ProbePlan& plan, KeyWords key,
                             uint64_t dummy_base) {
    ResolveDenseProbeAddresses(plan, &candidate_epoch_, probe_);
    ResolveHashedProbeAddresses(plan.addressing, key, dummy_base,
                                layout_.BucketBytes(), *aes_keys_, probe_);
  }

  bool Probe(KeyWords key, uint8_t* value_out, bool zero_value_on_miss,
             FoundFlags* found_out) {
    BeginAccess();
    // Mark the access live, snapshot exactly one plan, probe exactly that
    // one.  The guard's compare-exchange also REJECTS a second concurrent
    // access: the epoch is one odd/even word, so two readers would drive it
    // even under both and let an owner reclaim underneath them (threading rule 1).
    // It leaves the epoch and THEN tells a waiting owner, on the way out.
    AccessEpoch epoch(this);
    const ProbePlan& plan = *ComposedPlan();
    for (size_t i = plan.first_live; i < plan.prefix_slots; ++i) {
      const TableEntry& t = plan.tables[i];
      probe_.bucket[2 * i] = t.data;
      probe_.bucket[2 * i + 1] = t.data;
      probe_.mask[2 * i] = t.masks;
      probe_.mask[2 * i + 1] = t.masks;
    }
    // Public and fixed for the engine's life.
    if (value_pool_) {
      return Cascade<true>(plan, key, value_out, zero_value_on_miss,
                           found_out);
    }
    return Cascade<false>(plan, key, value_out, zero_value_on_miss,
                          found_out);
  }

  template <bool SplitValues, bool PrefetchNext>
  INLINE void ExtractCascadeValue(uint8_t* bucket, uint64_t* mask, uint64_t match,
      uint8_t* out, const uint8_t* next, bool prefix, bool next_full = false) {
    if constexpr (SplitValues) {
      if (prefix) {
        out[user_value_bytes_] = ExtractMeta(bucket, layout_, match);
        *mask &= ~match;
        if constexpr (PrefetchNext) {
          // The next entry's value lines too when it is the requester's tail.
          const size_t lines = next_full ? layout_.MetaLine() : layout_.key_bytes;
          for (size_t l = 0; l < lines; ++l)
            _mm_prefetch(reinterpret_cast<const char*>(next + l * 64), _MM_HINT_T0);
          _mm_prefetch(reinterpret_cast<const char*>(next + layout_.MetaLine() * 64), _MM_HINT_T0);
        }
        return;
      }
    }
    ExtractValueAndClearRealMaskByteSlicedPermute<PrefetchNext>(bucket, mask,
        layout_, match, out, next);
  }

  // WHETHER ENTRY i OF THE LIVE CASCADE IS A JOINT GROUP: a hashed main with
  // its own second tier right after it.  A public property of the plan --
  // TierEntry publishes a tier right behind its main with the same window and
  // tier == 1, and PlanWindowsLaminar rejects any other placement -- and the
  // width bound is the geometry's (kMaxResidualStashBuckets), checked here
  // only because the joint step keeps one match mask per tier bucket.
  static bool TierFollows(const TableEntry* tables, size_t n, size_t i) {
    return i + 1 < n && tables[i].kind == TableKind::kHashed &&
           tables[i + 1].tier == 1 &&
           tables[i + 1].kind == TableKind::kDense &&
           tables[i + 1].num_buckets != 0 &&
           tables[i + 1].num_buckets <= kMaxResidualStashBuckets;
  }

  // A group's tier, ahead of its step: the mask words and every bucket's key
  // lines, which is what the tier's match -- the first thing the step does --
  // reads.  The value and meta lines are left to the tier's extract right
  // after it: they are cache-resident, and prefetching them as well would
  // compete with the next main bucket's lines for the core's fill buffers.
  INLINE void PrefetchJointTier(const TableEntry& tier) const {
    _mm_prefetch(reinterpret_cast<const char*>(tier.masks), _MM_HINT_T0);
    _mm_prefetch(reinterpret_cast<const char*>(tier.masks + tier.num_buckets - 1),
                 _MM_HINT_T0);
    const size_t bucket_bytes = layout_.BucketBytes();
    for (size_t b = 0; b < tier.num_buckets; ++b) {
      for (size_t l = 0; l < layout_.key_bytes; ++l) {
        _mm_prefetch(reinterpret_cast<const char*>(
                         tier.data + b * bucket_bytes + l * kBucketCapacity),
                     _MM_HINT_T0);
      }
    }
  }

  // A group's tier extract, with its matches, at the top of the step: every
  // bucket is extracted whatever matched, the last match winning the run (a
  // dense run's rule), in the tier entry's own mode -- `prefix`
  // (below the value-worker boundary) is the meta byte alone, else the full
  // value -- into probe_scratch2_, ungated.  Nothing else in a group's step
  // uses that scratch: the group's main is hashed, so it has no dense run.
  // Never removable in a published plan, so its mask clears go to the sink;
  // the choice is still made from the entry's public flag.
  template <bool SplitValues>
  INLINE void ExtractJointTierValue(const TableEntry& tier,
                                    const uint64_t* match, bool prefix) {
    const size_t bucket_bytes = layout_.BucketBytes();
    uint8_t* const out = probe_scratch2_.get();
    uint8_t* const run = probe_run_.get();
    for (size_t b = 0; b < tier.num_buckets; ++b) {
      uint64_t* const target = tier.removable ? tier.masks + b : &mask_sink_;
      ExtractCascadeValue<SplitValues, false>(tier.data + b * bucket_bytes,
          target, match[b], b == 0 ? out : run, nullptr, prefix);
      if (b == 0) continue;
      const uint64_t hit_b = static_cast<uint64_t>(match[b] != 0);
      if (SplitValues && prefix) {
        core::obliAssignBytes(out + user_value_bytes_, run + user_value_bytes_,
                              1, hit_b);
      } else {
        core::obliAssignBytes(out, run, layout_.value_bytes, hit_b);
      }
    }
  }

  // Its blend, after the main's: the value under `take` (the tier hit, and
  // nothing fresher, and the main did not), and the tombstone flags latched
  // under the same gate.
  template <bool SplitValues>
  INLINE void BlendJointTier(bool prefix, uint64_t take, uint8_t* value_out,
                             uint64_t* taken_flags) {
    uint8_t* const out = probe_scratch2_.get();
    if (!(SplitValues && prefix)) {
      core::obliAssignBytes(value_out, out, user_value_bytes_, take);
    }
    TakeTombstoneFlags(out, user_value_bytes_, take, taken_flags);
  }

  // A FULL-MODE GROUP IN REGISTERS: a group whose main and tier are both
  // extracted in full (no value workers, or both in the requester's tail),
  // with values of at most 128 bytes -- a public property of the plan and
  // layout.  Its extracts leave the values in registers
  // (ExtractValueToRegistersAndClearRealMaskByteSlicedPermute), and one blend
  // writes value_out, in place of two scratch round trips and two blends.
  template <bool SplitValues>
  bool GroupInRegisters(size_t i, size_t boundary) const {
    return layout_.value_bytes <= 128 && (!SplitValues || i >= boundary);
  }

  // The tier's half: every bucket, the last match winning.
  INLINE void ExtractJointTierRegisters(const TableEntry& tier,
                                        const uint64_t* match, __m512i v[2]) {
    const size_t bucket_bytes = layout_.BucketBytes();
    for (size_t b = 0; b < tier.num_buckets; ++b) {
      uint64_t* const target = tier.removable ? tier.masks + b : &mask_sink_;
      __m512i t[2];
      ExtractValueToRegistersAndClearRealMaskByteSlicedPermute<false>(
          tier.data + b * bucket_bytes, target, layout_, match[b], t);
      if (b == 0) {
        v[0] = t[0];
        v[1] = t[1];
        continue;
      }
      const uint64_t lanes = uint64_t{0} - static_cast<uint64_t>(match[b] != 0);
      v[0] = core::obliMaskMov8(v[0], lanes, t[0]);
      v[1] = core::obliMaskMov8(v[1], lanes, t[1]);
    }
  }

  // The group's one blend: the tier's value where the tier hit and the main
  // did not (`tier_sel`), else the main's, into value_out under `take` -- the
  // main's take OR the tier's, which exclude each other -- and the chosen
  // meta byte's tombstone flags latched under the same gate.  The two
  // entries' blends, composed.
  INLINE void BlendGroupRegisters(const __m512i vm[2], const __m512i vt[2],
                                  uint64_t tier_sel, uint64_t take,
                                  uint8_t* value_out,
                                  uint64_t* taken_flags) const {
    const uint64_t tier_lanes = uint64_t{0} - tier_sel;
    const __m512i vg[2] = {core::obliMaskMov8(vm[0], tier_lanes, vt[0]),
                           core::obliMaskMov8(vm[1], tier_lanes, vt[1])};
    const uint64_t select = uint64_t{0} - take;
    const size_t user = user_value_bytes_;
    for (size_t c = 0; c * 64 < user; ++c) {
      const unsigned chunk =
          static_cast<unsigned>(user - c * 64 < 64 ? user - c * 64 : 64);
      const uint64_t lane_bits = _bzhi_u64(~uint64_t{0}, chunk);
      const __mmask64 lane = _cvtu64_mask64(lane_bits);
      const __m512i current = core::obliPin512(
          _mm512_maskz_loadu_epi8(lane, value_out + c * 64));
      const __m512i blended =
          core::obliMaskMov8(current, lane_bits & select, vg[c]);
      _mm512_mask_storeu_epi8(value_out + c * 64, lane, blended);
    }
    // The meta byte rides one past the user value (TakeTombstoneFlags).
    const __m512i meta = _mm512_permutexvar_epi8(
        _mm512_set1_epi8(static_cast<char>(user & 63)), vg[user >> 6]);
    const uint64_t flags_here = static_cast<uint64_t>(
        static_cast<uint8_t>(_mm_cvtsi128_si32(_mm512_castsi512_si128(meta))) &
        (kMetaErased | kMetaUnshadowed));
    core::CMOV8(take != 0, *taken_flags, flags_here);
  }

  // THE CASCADE.  Newest window first.  Above the entry where the key was
  // found the probes are real; at and below it they are dummies at
  // independent pseudorandom buckets, so the number and shape of the probes
  // is a function of the plan alone.  The result is blended out of every
  // probe without branching on which one hit.
  //
  // Every entry is one step and a step's match selects the next step's
  // address, except a JOINT GROUP.  A tier is a fixed-address table scanned
  // with the real key and never gated, so the address it "selects" for the
  // table after it depends only on `found`; probed as a step of its own, its
  // match, and with no value workers the main's whole value extract before
  // it, would sit on the dependency chain between one main bucket's arrival
  // and the next main bucket's request.  So a hashed main and the tier
  // published right after it (TierFollows) are ONE STEP, in this order:
  //   1. the tier's match, every bucket, real key, no gate, and then its
  //      extract, in the tier entry's own mode (meta only below the
  //      value-worker boundary, the full value at or above it), ungated --
  //      all before the main's key lines are touched, so it runs while the
  //      main's load is in flight and leaves the window after the next
  //      bucket's prefetches to the main's extract alone;
  //   2. the main's match under its gate; the group hits if either does;
  //   3. with value workers, ONE publication: the fields as of after the
  //      tier -- or after the main, when the requester's tail starts at the
  //      tier (a split group);
  //   4. the next step's real or dummy target, from the group's `found`: its
  //      mask and key lines are prefetched here, and again with its other
  //      lines from inside the main's extract;
  //   5. the main's extract, and the two blends and latches under the
  //      entries' own take gates: the main's `hit AND nothing fresher`, then
  //      the tier's `tier hit AND nothing fresher AND the main did not hit`
  //      (one register blend for a full-mode group, GroupInRegisters);
  //   6. the NEXT group's tier mask and key lines, publicly.  Only those:
  //      prefetching every tier line would compete with the next main bucket
  //      for the core's fill buffers.
  // The order of steps 1 and 4 is a performance choice: with the tier's
  // extract after the main's, its cache-resident lines would queue behind the
  // next bucket's value prefetches; and the next bucket's key lines are
  // prefetched twice because a first prefetch can be dropped (a page walk or
  // a full fill buffer).  The buckets and lines read, and the real/dummy
  // decision at every hashed table, are those of one step per entry (the
  // group's `found` is the `found` after its tier), and the order of the
  // tier's reads relative to the main's is a function of the plan alone.  A
  // main and its tier hold disjoint keys, so at most one of them can match;
  // the tier's take is gated on the main's miss anyway.
  template <bool SplitValues>
  bool Cascade(const ProbePlan& plan, KeyWords key, uint8_t* value_out,
               bool zero_value_on_miss, FoundFlags* found_out) {
    const size_t first = plan.first_live;
    const TableEntry* const tables = plan.tables.data() + first;
    const size_t n = plan.tables.size() - first;
    // Candidate pairs and dummy offsets are indexed by the ABSOLUTE position
    // in the array, which is what the addressing block was built against.
    const uint64_t dummy_base =
        ReserveDummyCounters(dummy_counter_, 1, plan.tables.size());

    ResolveProbeAddresses(plan, key, dummy_base);
    last_probe_tables_ = n;
    last_probe_buckets_ = plan.probe_buckets + plan.prefix_buckets;
    last_probe_mains_ = plan.hashed.size();
    probe_mains_ += plan.hashed.size();
    if (zero_value_on_miss) std::memset(value_out, 0, user_value_bytes_);

    size_t boundary = n;
    std::optional<ValueWorkerPool::Guard> job_guard;
    bool sample = false;
    uint64_t published = 0, bounded = 0;
    if constexpr (SplitValues) {
      sample = value_profile_enabled_ && ValueSample(value_pool_->sequence() + 1);
      if (sample) published = ValueStamp();
      // Entry zero is the mutable unit. It must remain worker-owned while
      // its preceding insertion is committed at this job's start. The
      // forwarded bytes were staged at that insertion (null here).
      boundary = n - std::min<size_t>(value_pool_->tail(), n - 1);
      value_pool_->Begin(&plan, key, dummy_base, boundary, pending_bucket_,
                         pending_slot_, nullptr);
      pending_bucket_ = nullptr;
      job_guard.emplace();
      job_guard->pool = value_pool_.get();
    }
    size_t winner_entry = 0, winner_bucket = 0;
    unsigned winner_slot = 0;
    uint64_t found = 0;        // 0/1
    uint64_t taken_flags = 0;  // the tombstone flags of the entry taken
    uint8_t* current_bucket = probe_.bucket[2 * first];
    uint64_t* current_mask = probe_.mask[2 * first];
    bool current_removable = tables[0].removable;
    size_t current_extra = DenseExtraBuckets(tables[0]);
    // Dummy targets have a zero gate, so their register-only key comparison
    // can use the original key too. Addresses still use independent dummies.
    uint64_t current_gate = ~uint64_t{0};
    const size_t bucket_bytes = layout_.BucketBytes();
    // A group's tier match masks, kept for its extract after the next
    // step's prefetches.  TierFollows bounds the width.
    uint64_t tier_match[kMaxResidualStashBuckets];
    if (TierFollows(tables, n, 0)) {
      PrefetchJointTier(tables[1]);
    }
    for (size_t i = 0;;) {
      // PUBLIC: whether this step is a group.
      const bool grouped = TierFollows(tables, n, i);
      const bool in_registers = grouped && GroupInRegisters<SplitValues>(i, boundary);
      __m512i tier_value[2];
      // 1. THE TIER, before the main's lines.  The real key and no gate:
      // use_dummy = found & hashed is zero for a dense table.  A run, newest
      // bucket last, so the last match wins.
      uint64_t tier_hit = 0;
      size_t tier_bucket = 0;
      unsigned tier_slot = 0;
      if (grouped) {
        const TableEntry& tier = tables[i + 1];
        for (size_t b = 0; b < tier.num_buckets; ++b) {
          const uint64_t m = MatchMaskByteSlicedTree(
              tier.data + b * bucket_bytes, tier.masks[b], layout_, key);
          tier_match[b] = m;
          const uint64_t hit_b = static_cast<uint64_t>(m != 0);
          if constexpr (SplitValues) {
          tier_bucket = core::obliSelectU64(tier_bucket, b, hit_b);
          tier_slot = static_cast<unsigned>(core::obliSelectU64(tier_slot,
              static_cast<unsigned>(_tzcnt_u64(m)) & 63, hit_b));
          }
          tier_hit |= hit_b;
        }
        // ... and its extract, ungated; blended in step 5.
        if (in_registers) {
          ExtractJointTierRegisters(tier, tier_match, tier_value);
        } else {
          ExtractJointTierValue<SplitValues>(tier, tier_match,
                                             i + 1 < boundary);
        }
      }
      // 2. The step's own entry -- a group's main, or an entry on its own,
      // a dense run included.
      //
      // A MULTI-BUCKET DENSE RUN.  Its buckets are ordered oldest to newest --
      // a prefix's units, and a unit's buckets, are written in that order --
      // so the entry's answer is the LAST match in the run, not the first: one
      // key may legitimately appear once per unit it was written in.  Run
      // BEFORE bucket 0's extract, into scratch of its own, so that `hit` --
      // and with it the gate the NEXT entry's address selection needs -- is
      // known before the next step's prefetches.  Every bucket is visited
      // whatever matched, and every blend is gated on a register mask,
      // because the extract's miss contract is UNSPECIFIED bytes rather than
      // zeros.  Removal survives only in the CURRENT online-stash unit; every
      // other dense table is a rebuild source and a probe may not mutate one.
      const uint64_t match =
          MatchMaskByteSlicedTree(current_bucket, *current_mask, layout_,
                                  key) &
          current_gate;
      uint64_t run_hit = 0;
      size_t run_bucket = 0;
      unsigned run_slot = static_cast<unsigned>(_tzcnt_u64(match)) & 63;
      if (current_extra != 0) {
        for (size_t b = 1; b <= current_extra; ++b) {
          uint8_t* const bucket = current_bucket + b * bucket_bytes;
          const uint64_t m =
              MatchMaskByteSlicedTree(bucket, current_mask[b], layout_,
                                      key) &
              current_gate;
          uint64_t* const target =
              current_removable ? current_mask + b : &mask_sink_;
          ExtractCascadeValue<SplitValues, false>(bucket, target, m,
              probe_scratch2_.get(), nullptr, i < boundary);
          const uint64_t hit_b = static_cast<uint64_t>(m != 0);
          if constexpr (SplitValues) {
            if (i < boundary) core::obliAssignBytes(probe_run_.get() + user_value_bytes_,
                probe_scratch2_.get() + user_value_bytes_, 1, hit_b);
            else core::obliAssignBytes(probe_run_.get(), probe_scratch2_.get(), layout_.value_bytes, hit_b);
          } else core::obliAssignBytes(probe_run_.get(), probe_scratch2_.get(), layout_.value_bytes, hit_b);
          if constexpr (SplitValues) {
          run_bucket = core::obliSelectU64(run_bucket, b, hit_b);
          run_slot = static_cast<unsigned>(core::obliSelectU64(run_slot,
              static_cast<unsigned>(_tzcnt_u64(m)) & 63, hit_b));
          }
          run_hit |= hit_b;
        }
      }
      const uint64_t hit = static_cast<uint64_t>(match != 0) | run_hit;
      const uint64_t take = hit & (found ^ 1);
      if constexpr (SplitValues) {
      winner_entry = core::obliSelectU64(winner_entry, i, take);
      winner_bucket = core::obliSelectU64(winner_bucket, run_bucket, take);
      winner_slot = static_cast<unsigned>(core::obliSelectU64(winner_slot, run_slot, take));
      }
      found |= hit;
      // The tier folded in after the main, as if it were the next step.
      uint64_t tier_take = 0;
      if (grouped) {
        if constexpr (SplitValues) {
          // 3, A SPLIT GROUP: the tail starts at the tier, so publish
          // here, after the main.
          if (i + 1 == boundary) {
            value_pool_->Publish(i + 1, found, winner_entry, winner_bucket,
                                 winner_slot, true);
            if (sample) bounded = ValueStamp();
          }
        }
        tier_take = tier_hit & (found ^ 1);
        if constexpr (SplitValues) {
        winner_entry = core::obliSelectU64(winner_entry, i + 1, tier_take);
        winner_bucket = core::obliSelectU64(winner_bucket, tier_bucket, tier_take);
        winner_slot = static_cast<unsigned>(core::obliSelectU64(winner_slot, tier_slot, tier_take));
        }
        found |= tier_hit;
      }
      // The next STEP: after this entry, or after its tier.  The tier's own
      // cascade position keeps its (unused) dummy counter, which only has
      // to never repeat.
      const size_t next_index = i + (grouped ? 2 : 1);
      if constexpr (SplitValues) {
        // 3. Publish after this step's last entry: before the next hashed
        // entry, which the workers wait on, and at the boundary.
        if (next_index == boundary ||
            (next_index < boundary &&
             tables[next_index].kind == TableKind::kHashed)) {
          value_pool_->Publish(next_index, found, winner_entry,
                               winner_bucket, winner_slot,
                               next_index == boundary);
          if (sample && next_index == boundary) bounded = ValueStamp();
        }
      }
      uint64_t* const clear_target =
          current_removable ? current_mask : &mask_sink_;

      if (next_index < n) {
        const TableEntry& next = tables[next_index];
        // 4. The next step's target, from the group's `found`.
        const uint64_t hashed =
            static_cast<uint64_t>(next.kind == TableKind::kHashed);
        const uint64_t use_dummy = found & hashed;
#ifdef MICRORAM_BYTESLICE_PROBE_AUDIT
        // Only under the audit: `use_dummy` derives from `found`, so
        // branching on it is exactly the leak the rest of this loop CMOVs
        // around.
        if (use_dummy == 0 && hashed != 0) {
          publisher_.audit().RecordRealProbe(next.nonce_family_id, key);
        }
#endif
        const uint64_t next_gate = use_dummy - 1;  // 0 -> all-ones, 1 -> zero
        const ProbeTarget next_target =
            SelectProbeTarget(probe_, first + next_index, use_dummy != 0);
        _mm_prefetch(reinterpret_cast<const char*>(next_target.mask),
                     _MM_HINT_T0);
        for (size_t l = 0; l < layout_.key_bytes; ++l) {
          _mm_prefetch(reinterpret_cast<const char*>(next_target.bucket +
                                                     l * kBucketCapacity),
                       _MM_HINT_T0);
        }
        // 5. This entry's extract, carrying the next step's prefetches.
        if (in_registers) {
          __m512i main_value[2];
          ExtractValueToRegistersAndClearRealMaskByteSlicedPermute<true>(
              current_bucket, clear_target, layout_, match, main_value,
              next_target.bucket);
          BlendGroupRegisters(main_value, tier_value, tier_hit & (hit ^ 1),
                              take | tier_take, value_out, &taken_flags);
        } else {
          ExtractCascadeValue<SplitValues, true>(current_bucket, clear_target,
              match, probe_scratch_.get(), next_target.bucket, i < boundary,
              next_index >= boundary);
          if (current_extra != 0) {
            if constexpr (SplitValues) {
              if (i < boundary) core::obliAssignBytes(probe_scratch_.get() + user_value_bytes_,
                  probe_run_.get() + user_value_bytes_, 1, run_hit);
              else core::obliAssignBytes(probe_scratch_.get(), probe_run_.get(), layout_.value_bytes, run_hit);
            } else core::obliAssignBytes(probe_scratch_.get(), probe_run_.get(), layout_.value_bytes, run_hit);
          }
          if constexpr (SplitValues) {
            if (i >= boundary) core::obliAssignBytes(value_out, probe_scratch_.get(), user_value_bytes_, take);
          } else core::obliAssignBytes(value_out, probe_scratch_.get(), user_value_bytes_, take);
          TakeTombstoneFlags(probe_scratch_.get(), user_value_bytes_, take,
                             &taken_flags);
          if (grouped) {
            BlendJointTier<SplitValues>(i + 1 < boundary, tier_take,
                                        value_out, &taken_flags);
          }
        }
        // 6. The next group's tier, publicly: mask and key lines.
        if (TierFollows(tables, n, next_index)) {
          PrefetchJointTier(tables[next_index + 1]);
        }
        current_bucket = next_target.bucket;
        current_mask = next_target.mask;
        current_removable = next.removable;
        current_extra = DenseExtraBuckets(next);
        current_gate = next_gate;
        i = next_index;
      } else if (in_registers) {
        __m512i main_value[2];
        ExtractValueToRegistersAndClearRealMaskByteSlicedPermute<false>(
            current_bucket, clear_target, layout_, match, main_value);
        BlendGroupRegisters(main_value, tier_value, tier_hit & (hit ^ 1),
                            take | tier_take, value_out, &taken_flags);
        break;
      } else {
        ExtractCascadeValue<SplitValues, false>(current_bucket, clear_target,
            match, probe_scratch_.get(), nullptr, i < boundary);
        if (current_extra != 0) {
          if constexpr (SplitValues) {
            if (i < boundary) core::obliAssignBytes(probe_scratch_.get() + user_value_bytes_,
                probe_run_.get() + user_value_bytes_, 1, run_hit);
            else core::obliAssignBytes(probe_scratch_.get(), probe_run_.get(), layout_.value_bytes, run_hit);
          } else core::obliAssignBytes(probe_scratch_.get(), probe_run_.get(), layout_.value_bytes, run_hit);
        }
        if constexpr (SplitValues) {
          if (i >= boundary) core::obliAssignBytes(value_out, probe_scratch_.get(), user_value_bytes_, take);
        } else core::obliAssignBytes(value_out, probe_scratch_.get(), user_value_bytes_, take);
        TakeTombstoneFlags(probe_scratch_.get(), user_value_bytes_, take,
                           &taken_flags);
        if (grouped) {
          BlendJointTier<SplitValues>(i + 1 < boundary, tier_take,
                                      value_out, &taken_flags);
        }
        break;
      }
    }
    if constexpr (SplitValues) {
      const uint64_t waited = sample ? ValueStamp() : 0;
      value_pool_->Finish(value_out, found & static_cast<uint64_t>(winner_entry < boundary));
      if (sample) {
        ++value_request_timing_.samples; value_request_timing_.publish += published;
        value_request_timing_.boundary += bounded;
        value_request_timing_.tail += waited - bounded;
        value_request_timing_.wait += ValueStamp() - waited;
      }
    }
    if (found_out != nullptr) {
      found_out->erased = (taken_flags & kMetaErased) != 0;
      found_out->unshadowed = (taken_flags & kMetaUnshadowed) != 0;
    }
    return found != 0;
  }

  // NOT the whole Options: it carries `secret_seed`, the 128-bit master secret
  // both key schedules are derived from, and nothing after construction needs
  // it.  Keeping it would leave the one value an attacker with a core dump
  // wants alive for the engine's whole life, for one bool's convenience.
  const bool threaded_;
  const bool synchronous_;
  const FlushAction flush_action_;
  const size_t slice_touches_;
  const double inline_work_factor_;
  const LevelLaneConfig lanes_;
  const bool time_rebuild_stages_;
  const bool preroute_;
  const size_t merge_log_capacity_;
  // The owners' slice rate and the inline executor's share per flush in
  // touches, each 0 in the other shape.  Set once the geometry and layout
  // exist (constructor body).
  double slice_target_rate_ = 0.0;
  // A piece's line, for its touch budget (LevelArenaRebuildCost::
  // slice_line_picos).
  double slice_nanos_per_line_ = kSliceNanosPerTouchLine;
  uint64_t inline_flush_touches_ = 0;
  uint64_t inline_shares_spent_ = 0;
  uint64_t inline_touches_charged_ = 0;
  // The flush share's level order and the deadlines it sorts by, sized once
  // (a flush may not allocate).
  std::vector<unsigned> inline_order_;
  std::vector<uint64_t> inline_deadlines_;
  const std::chrono::microseconds park_retry_;
  const uint64_t requester_spin_nanos_;
  const std::chrono::milliseconds wait_limit_;
  LevelArenaGeometry geometry_;
  Layout layout_;
  LevelArenaStashSizing sizing_;
  const uint64_t max_accesses_;
  const uint64_t max_key_normalizations_;
  mutable uint64_t key_normalizations_ = 0;
  size_t user_key_bytes_;
  size_t user_value_bytes_;
  RoutingEvaluationBudget routing_budget_;
  std::unique_ptr<AesTagKeys> aes_keys_;
  crypto::AesRoundKeys key_hash_keys_;
  // The placement and batch configuration.  The first is const because the
  // grouping is derived from it; the next two are the only knobs a caller may
  // move between calls.
  const unsigned near_max_level_;
  unsigned batch_lanes_;
  unsigned batch_participants_;
  const unsigned participant_capacity_;
  const BatchExecutionShape batch_execution_;
  const bool batch_bucket_scan_;
  const bool batch_profile_enabled_;
  std::array<BatchWorkStats, kMaxOnlineParticipants> batch_profiles_;
  LevelArenaBucketBatch bucket_batch_;
  const BatchResultLayout result_layout_;

  // Settled before the publisher, the scratch and the levels, all three of
  // which are sized or wired from it.
  const std::vector<LevelGroupPlan> groups_;

  // Owns the residual pool as well as the arenas; outlives all references below.
  std::unique_ptr<LevelArenaSet> arenas_;  // null in the synchronous mode
  DensePrefixRing dense_;
  LevelArenaPublisher publisher_;
  std::vector<std::unique_ptr<LevelBoundary>> boundaries_;
  std::vector<std::unique_ptr<BoundaryReceiver>> receivers_;
  std::vector<std::unique_ptr<BoundaryProducer>> producers_;
  // One per level, indexed by level; see BuildScratch.
  std::vector<std::unique_ptr<LevelMergeScratch>> scratch_;
  std::vector<std::unique_ptr<LevelState>> levels_;
  std::unique_ptr<SynchronousLevels> sync_;  // the synchronous mode only
  TopMergeLog top_log_;  // before BuildLevels wires it
  std::unique_ptr<LevelMergeLog> merge_log_;  // null unless asked for

  // The owner threads.  All empty when `threaded_` is false; `groups_` is
  // not, because the staging records are per executing thread either way.  Declared
  // after everything they drive so that destruction tears them down first --
  // though the destructor joins explicitly rather than relying on that.
  std::vector<std::unique_ptr<OwnerEvent>> events_;
  std::unique_ptr<OwnerEvent> requester_event_;
  std::unique_ptr<OwnerRuntime> runtime_;
  std::vector<std::unique_ptr<LevelGroup>> drivers_;
  std::vector<std::thread> threads_;
  // The top group's helper threads (Options::top_helpers), their event and
  // their shared loop state.  Joined with the owners.
  std::unique_ptr<OwnerEvent> helper_event_;
  std::unique_ptr<LevelHelpers> helpers_;
  unsigned helper_count_ = 0;
  // Level 1's group's helpers (Options::bottom_helpers), on their own event.
  std::unique_ptr<OwnerEvent> bottom_helper_event_;
  std::unique_ptr<LevelHelpers> bottom_helpers_;
  unsigned bottom_helper_count_ = 0;
  std::vector<std::thread> helper_threads_;
  // Set when every owner and helper started and ran its hook; a partial
  // start never sets it (StartOwnerThreads).
  bool owners_started_ = false;
  // Kept only for a deferred start; empty and unread on an engine that
  // started its owners in the constructor.
  std::function<void(unsigned)> owner_init_;
  std::function<void(unsigned)> helper_init_;
  std::mutex init_mutex_;
  std::condition_variable workers_started_changed_;
  size_t workers_started_ = 0;  // init_mutex_
  // The requester's park statistics, readable by diagnostic observers.
  OwnerWaitStats requester_waits_;
  RequesterBackpressure requester_backpressure_;
  // long_waits()' records: the first kMaxLongWaits waits, each with one entry
  // per level, allocated at construction with owner threads (only their
  // waits are recorded).
  struct LongWaitLog {
    std::unique_ptr<BlockedLevel[]> levels;
    std::unique_ptr<BlockedDense[]> dense;
    size_t count = 0;
  };
  LongWaitLog long_waits_;

  // The batch path: one tile per participant, the pool that runs the
  // phases on them, and the bank pointers the cross-tile dedup and forward
  // read.  Declared after everything they probe, like the owner threads, and
  // torn down first by an explicit stop in the destructor.
  std::vector<std::unique_ptr<LevelArenaBatchTile>> tiles_;
  std::vector<LevelArenaBatchTile*> tile_pointers_;
  std::array<const ParallelBatchBanks*, kMaxOnlineParticipants> banks_{};
  std::unique_ptr<BatchWorkerPool> participants_;

  // The request thread's probe scratch.  One owner, so none of it is atomic.
  ValueRequestTiming value_request_timing_;
  bool value_profile_enabled_ = false;
  std::unique_ptr<ValueWorkerPool> value_pool_;
  uint8_t* pending_bucket_ = nullptr;
  size_t pending_slot_ = 0;
  ProbeScratch probe_;
  Aligned64Ptr probe_scratch_;
  Aligned64Ptr probe_scratch2_;
  Aligned64Ptr probe_run_;
  Aligned64Ptr discard_value_;
  Aligned64Ptr zero_value_;
  Aligned64Ptr exchange_value_;
  uint64_t mask_sink_ = 0;  // where a non-removable table's clear goes
  uint64_t dummy_counter_ = 0;
  uint64_t prefix_epoch_ = ~uint64_t{0};
  uint64_t prefix_flushes_ = ~uint64_t{0};
  uint64_t candidate_epoch_ = ~uint64_t{0};
  size_t last_probe_tables_ = 0;
  size_t last_probe_buckets_ = 0;
  size_t last_probe_mains_ = 0;
  uint64_t probe_mains_ = 0;
  uint64_t sweeps_ = 0;
  LevelArenaByteBill bytes_;
  bool initialized_ = false;
  // What an initialization seeded the dense ring's counters to, zero unless
  // one ran.  AccessCount and FlushCount report from them.
  uint64_t seeded_positions_ = 0;
  uint64_t seeded_flushes_ = 0;
  // The requester's failure latch (first_failure()).  Written and read on the
  // requester's thread only: the inline executor and the batch commit both
  // run there, and an owner's failure has its own latch in `runtime_`.
  std::exception_ptr failure_;
  std::string failure_what_;
};

// PUTS A REBUILD'S PARAMETERS ON AN ENGINE'S OPTIONS: the division, helpers,
// lanes, slice rate, inline share and near/far boundary, whoever chose them
// (HeuristicRebuildParams, a tuner).  Everything else on `options` is left as
// it was.
inline void ApplyRebuildParams(const LevelArenaRebuildParams& params,
                               LevelArenaEngine::Options* options) {
  options->owner_threads = static_cast<unsigned>(params.groups.size());
  options->groups = params.groups;
  options->top_helpers = params.top_helpers;
  options->lanes = params.lanes;
  options->slice_target_rate = params.slice_target_rate;
  options->inline_work_factor = params.inline_work_factor;
  options->near_max_level = params.near_max_level;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
