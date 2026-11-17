#pragma once

// The HIERARCHICAL engine's public adapters: `Options`, `ByteMap` and the
// `detail::BasicMap` template the typed maps are built from.
//
// This header exists so that the tree ORAM (`tree_oram.hpp`) can be built on
// top of `ByteMap` -- it uses one as its position map -- while the umbrella
// header `oram.hpp` can define the typed `Map` over the HYBRID of the two.
// Include `<cpu_byteslice_oram/oram.hpp>`; this is its lower half.
//
// WHICH ENGINE EACH INSTANTIATION RUNS.  `ByteMap<true>`, the default, is the
// PER-LEVEL ARENA engine of `src/oram/levelarena/` (design:
// src/oram/levelarena/DESIGN.md): rebuilds run on background owner threads,
// overlapped with accesses, against immutable published tables.
// `ByteMap<false>` is the same engine in its SYNCHRONOUS storage mode
// (levelarena/cpu_byteslice_level_arena_synchronous.hpp): the same planner,
// jobs, residual routing and certified bounds, each level merged in place in
// one region by the request that completes a prefix -- about half the main
// storage, and no overlap: that request pays for every merge it triggers.
//
// VOCABULARY used throughout (defined in src/oram/levelarena/DESIGN.md):
//   level        one size class of hashed tables, 1..L, L the TOP;
//   fanout / B   how many carries a non-top level absorbs before it carries
//                its merged contents up; D, the top digit, is the top's;
//   carry        the merged table one level hands to the next;
//   online stash the records the most recent accesses wrote, scanned in full
//                by every access; it fills in units of s buckets (a FLUSH);
//   dense prefix r0 flushed units, scanned in full, which become level 1's
//                input; q of them may be outstanding;
//   tier         a level's fixed-width RESIDUAL stash, holding records that
//                overflowed their main bucket during a rebuild;
//   owner        a background thread that runs the rebuilds of a contiguous
//                GROUP of levels; a helper widens one group's routing lanes.
//
// The knobs are spelled `deamortized_` for both instantiations.  The
// geometry, batch, seed and wait-limit knobs configure both; the thread knobs
// (owner threads, helpers, lanes, divisions, budgets, slices, placement
// hooks) only the incremental one, and the synchronous one ignores them.

#include <cpu_byteslice_oram/default_rule.hpp>
#include <cpu_byteslice_oram/access.hpp>
#include "src/core/release_guard.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
// The certified-bound table: public layer only, never from src/ (see its
// header: the certification's probes must not reach it).
#include "src/oram/levelarena/cpu_byteslice_level_arena_certification.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_placement.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_engine.hpp"
#include "src/oram/rebuild/cpu_byteslice_initialization.hpp"
#include "src/oram/table/cpu_byteslice_host_cores.hpp"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <limits>
#include <memory>
#include <new>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace cpu_byteslice_oram {

namespace la = microram::byteslice::levelarena;

// Direct initialization (src/oram/rebuild/DESIGN.md, "Initialize directly into
// the final table"), re-exported so a caller never names an internal namespace.  `initialize` on a hierarchical
// map builds its largest level straight from an input stream instead of one
// online write per record; `InitializationEntry` is what a BYTE map's iterator
// yields, and a typed map's iterator yields a pair-like {Key, T} instead.
using InitializationPolicy = microram::byteslice::InitializationPolicy;
using InitializationEntry = microram::byteslice::InitializationEntry;
// The batch API's request (ByteMap::access_batch): a public operation code
// and `insert` flag, the key, the value to store, and where the value found
// goes.  Re-exported so a caller never names an internal namespace, and under
// the same names the internal fixtures use, so one batch description drives
// both the public adapter and the engine directly.
using BatchOp = microram::byteslice::BatchOp;
using BatchRequest = microram::byteslice::BatchRequest;
// WHERE A LANE'S PROBE RESULT LANDS (src/oram/table/cpu_byteslice_batch_config.hpp).
// Public and fixed per instance; it changes instruction streams, never trace
// shape.  `kSlicedPlaceAtLane`, the default, keeps results byte-sliced and
// needs no transpose; `kRows` is the row-major reference layout.
// BatchExecutionShape picks chunked (one thread) or parallel-tile execution;
// BankFirst and ValueKernel are explained at the Options fields that take
// them.
using BatchResultLayout = microram::byteslice::BatchResultLayout;
using BatchExecutionShape = la::BatchExecutionShape;
using BankFirst = la::BankFirst;
using ValueKernel = microram::byteslice::ValueKernel;
// THE COMPLETE BYTE BILL, by role (arena, dense prefixes, scratch,
// participant buffers, plan pool, bookkeeping), with requested and
// allocator-rounded bytes kept apart; the geometry's arena bytes alone are not
// the engine's footprint.  `ByteMap::byte_bill()` returns one.
using LevelArenaByteBill = la::LevelArenaByteBill;
using LevelArenaByteRole = la::ByteRole;
inline constexpr size_t kLevelArenaByteRoles = la::kByteRoleCount;
inline const char* LevelArenaByteRoleName(LevelArenaByteRole role) {
  return la::ByteRoleName(role);
}
// `Options::deamortized_near_max_level`'s "ask this host" sentinel: let the
// map put the near/far class boundary where THIS host's last-level cache puts
// it, once, before it plans a geometry.  Both spellings name one constant.
inline constexpr unsigned kLevelArenaNearMaxLevelAuto = la::kNearMaxLevelAuto;
inline constexpr unsigned kNearMaxLevelAuto = kLevelArenaNearMaxLevelAuto;
// Batch limits: the most lanes in one SIMD tile (a participant's chunk), the
// most batch participants (caller included), and the most requests that may
// share one probe snapshot across all participants.
inline constexpr size_t kMaxBatchLanes = microram::byteslice::kMaxBatchLanes;
inline constexpr unsigned kMaxOnlineParticipants =
    microram::byteslice::kMaxOnlineParticipants;
inline constexpr size_t kMaxCombinedBatchLanes =
    microram::byteslice::kMaxCombinedBatchLanes;
// The widest key, in bytes, of every map in this library: the hierarchy
// stores keys of 16 bytes or more as 128-bit AES outputs and reads at most
// this many input bytes, and the tree keys its position map by the same key.
inline constexpr size_t kMaxUserKeyBytes = 64;
// The largest `Options::deamortized_online_stash_entries`: 64 s with s at
// most 2^12 buckets, because level one is built directly from 2 r0 s <= 2^16
// buckets (src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp).
inline constexpr size_t kMaxOnlineStashEntries =
    microram::byteslice::kBucketCapacity << 12;
// THE WIDEST VALUE A TYPED CALL STAGES ON THE CALLER'S STACK, in bytes.  The
// typed `exchange` (for the old value, so an aliased value and output stay
// correct), callback `access` (for the callback's T) and bulk initialization
// (for one record) each need one temporary value.  Up to this width it is a
// local; above it, it is a buffer the map allocates once, at construction,
// so a call on a wide T needs no stack of that width and an access still
// allocates nothing.  `find(key, &out)` needs no temporary at any width.
inline constexpr size_t kTypedStackValueBytes = 4096;

// Unified configuration for ByteMap and Map. Options that apply only to one
// implementation are identified below; selecting an implementation is a
// compile-time choice on the map type.  Every field is a PUBLIC input: it may
// shape the memory trace (sizes, schedules, thread counts) but never depends
// on keys, values or the access sequence.  Invalid values or combinations
// are refused by the constructor and by `plan_geometry` with an exception
// naming the field: std::invalid_argument for a value outside the range its
// comment states (detail::ValidateArenaOptions checks them all before
// anything is planned).  A geometry the ranges allow but the requested
// capacity cannot use -- more owner threads than its levels, a pinned tier
// below the occupancy requirement -- is refused by the capacity ladder with
// std::length_error.
struct Options {
  // Online access limit and sizing horizon, independent of capacity. The target is
  // capacity-failure probability <= 2^-64 within this many requests; it is the
  // horizon the residual stash depths are sized and certified for
  // (src/oram/levelarena/DESIGN.md, "Online security and capacity").
  // Requests/chunks exceeding the remaining limit throw std::overflow_error
  // before mutation.  Nonzero.
  uint64_t max_accesses = uint64_t{1} << 32;
  // Lifetime AES key conversions at widths >=16, including initialization and
  // failed attempts. Unset uses actual capacity + max_accesses; zero forbids
  // conversion. This is separate from the access/capacity-failure budget.
  std::optional<uint64_t> max_key_normalizations;
  // Complete routing evaluations, counting retries, padding and worker
  // repeats. Exhaustion stops the instance, possibly during accepted work.
  // Choose a limit for the deployment's cryptographic budget; the default
  // only prevents arithmetic wrap and promises no total security target.
  uint64_t max_routing_evaluations = std::numeric_limits<uint64_t>::max();

  // The per-level arena engine's options.  The geometry, batch, seed and
  // wait-limit knobs apply to both instantiations; the thread knobs to the
  // incremental one only (see the header).
  //
  // THE THREE AXES A LADDER MAY NOT MOVE are knobs and not search variables
  // (see `PlanLevelArenaCapacity`): `deamortized_branching_factor`,
  // `deamortized_online_stash_entries` and `deamortized_dense_prefixes` are
  // choices about the WORKLOAD -- cascade length, the serial scan every
  // access pays, and how much rebuild may be outstanding -- so moving them to
  // save bytes would be retuning latency without saying so.
  // `deamortized_top_digit` and `deamortized_prefix_flushes` may be pinned for
  // a measurement sweep and are otherwise searched.

  // B, the uniform non-top fanout, in {2, 4, 8}.
  unsigned deamortized_branching_factor = kDefaultGeometry.branching_factor;
  // The fanout ladder below the top at B = 8: fanout B/2 at the lowest one to
  // three levels (as few as round the capacity) and B above them
  // (LevelArenaCapacityRequest::half_fanout_prefix).  It halves level 1's
  // rebuild work and lowers the total, for one more level and a few more
  // probe buckets.  False keeps B everywhere but a bottom fanout chosen by
  // bytes, which is what B < 8 always gets.
  bool deamortized_half_fanout_prefix = kDefaultGeometry.half_fanout_prefix;
  // BANK-FIRST: start every level's cycle in its idle odd bank (the level's
  // own region that holds its odd partial merges; an INBOX is a region of the
  // level above that receives even partials and full carries; see
  // src/oram/levelarena/DESIGN.md, "Geometry and storage bound"): the first
  // digits are built in the level's own bank rather than in an inbox of the
  // level above, which the level above may still be absorbing, so that inbox
  // is next needed later -- digit 4 at B = 8 (kNoClone, the default; B = 4 has no
  // run).  Costs one tier per level and no main storage.  kOff builds every
  // even digit in the forwarding lease, from digit 2.
  BankFirst deamortized_bank_first = BankFirst::kNoClone;
  // 64 s: the online stash's insertion unit in ENTRIES, 64 times a power of
  // two from 64 to kMaxOnlineStashEntries (262144): the stash is a whole
  // number s of 64-entry buckets, and the geometry takes s a power of two of
  // at most 2^12.
  //
  // WHAT AN ACCESS ACTUALLY SCANS ON THE DENSE SIDE IS
  // `deamortized_prefix_flushes * deamortized_online_stash_entries`, not this
  // on its own: the cascade scans the current unit, the frozen part of the
  // prefix being assembled and every complete prefix not yet replaced.  A
  // larger product means fewer, larger level-1 rebuilds but a longer serial
  // scan on every access, so cost is unimodal in that PRODUCT and largely
  // insensitive to how it is split; these two knobs are one tuning axis with
  // two spellings.
  //
  //   - a SERIAL caller is served by a moderate product, which is what 64
  //     with the ladder's own `r0` gives -- hence this default;
  //   - a BATCHING caller may prefer a somewhat larger one (for example 128
  //     here with `deamortized_prefix_flushes = 8`): the batch loads a dense
  //     bucket's key lines once per chunk and matches them from registers,
  //     so the LOADS amortise over the lanes and the optimum moves up;
  //   - a very large prefix is slow for both, because the per-lane MATCH and
  //     blend over a prefix grow with it whatever the batch amortises.
  //
  // The best value depends on the host; measure it for the deployment.
  size_t deamortized_online_stash_entries = kDefaultGeometry.online_stash_entries;
  // r0, the complete flushes that make one dense prefix, in {2, 4, 8}; 0 lets
  // the ladder choose it: the largest r0 within its byte slack (see
  // `PlanLevelArenaCapacity`).  With
  // `deamortized_online_stash_entries` it forms the ONE dense-side tuning
  // axis described there -- their product is what an access scans -- so a
  // caller that pins one and leaves the other searched has pinned half of a
  // knob.
  unsigned deamortized_prefix_flushes = 0;
  // D, the digit the top level saturates at: 1, 2, 4 or 8, at most B (only a
  // power-of-two top digit has a certified preparation); 0 lets the ladder
  // choose it alongside L, from the power-of-two digits in [B/2 + 1, B].
  // Pinning it is for a measurement sweep; it is not a way to ask for a
  // bigger table.
  unsigned deamortized_top_digit = 0;
  // q, complete dense prefixes allowed outstanding before the requester must
  // wait for level 1; at least 1.
  unsigned deamortized_dense_prefixes = kDefaultGeometry.dense_prefixes;
  // Zero sizes each level's residual tier from geometry and request
  // horizon: the requirement of the tables that level produces, so where the
  // top needs two buckets the lower levels keep one.  A positive width pins
  // one shared width, at most 8 buckets (kMaxResidualStashBuckets); a width
  // below the occupancy requirement leaves the ladder no geometry, which it
  // refuses with std::length_error.
  size_t deamortized_tier_buckets = 0;
  // HOW MANY THREADS DRIVE THE HIERARCHY.  Zero has no threads at all: the
  // REQUEST thread runs one share of the rebuild at each of its flushes
  // (`deamortized_inline_work_factor`), deterministically.  Above zero the
  // levels are divided into that many contiguous groups and each group gets a
  // thread: `deamortized_level_groups` when given, else the load
  // heuristic's division, which balances the groups' modeled rebuild demand
  // (levelarena/cpu_byteslice_level_arena_rebuild_params.hpp).
  // `deamortized_rebuild_threads` asks the heuristic to choose this count as
  // well.
  //
  // TWO IS THE DEFAULT: a small, fixed rebuild-thread budget, so that the
  // cores a default map takes do not depend on the host.  (The tree
  // hybrid's value threshold, `kHybridTreeValueThreshold` in
  // default_rule.hpp, does not depend on it.)
  //
  // A DEPLOYMENT WITH CORES TO SPARE SHOULD RAISE IT: more owner groups
  // shorten each group's rebuild queue, and what makes the threads pay more
  // than the count itself is PINNING the groups next to the caches they
  // work in, which is `deamortized_near_max_level` plus
  // `worker_thread_init`.
  //
  // It may not exceed the level count -- a thread with no level would park
  // forever and still cost a staging plan record -- so it is an input to the
  // ladder, which searches only geometries with at least this many levels,
  // and is clamped into the chosen geometry's range on the way to the engine.
  // At most 40, the most levels the ladder searches; a count above the levels
  // the requested capacity can have is refused by the ladder with
  // std::length_error.  Ignored under `deamortized_rebuild_threads`.
  unsigned deamortized_owner_threads = 2;
  // THE NEAR/FAR BOUNDARY: the largest level whose rebuild wants the request
  // thread's cache domain (small levels share the caller's last-level cache;
  // large ones stream from DRAM and can run on another domain).  0 leaves
  // the grouping as the load heuristic built it;
  // `kNearMaxLevelAuto` resolves it against THIS HOST's last-level cache,
  // which this map does once, before it plans a geometry -- the engine itself
  // never reads the host, because the boundary changes the byte bill and a
  // bill that depended on the machine would make two hosts disagree about
  // what one geometry costs.
  //
  // SETTING IT IS HALF THE JOB.  On its own it only changes which levels
  // share an owner thread, which is not consistently a gain; what pays is
  // PINNING the groups it separates, and that is the caller's, through
  // `worker_thread_init` and `deamortized_batch_thread_init` (see
  // `levelarena/cpu_byteslice_level_arena_placement.hpp` for the policy that
  // computes the assignment).
  unsigned deamortized_near_max_level = 0;

  // ---- scalar value workers (opt-in; default 0) ----
  //
  // Persistent threads that extract a SCALAR access's value bytes in
  // parallel with the requester's probe cascade
  // (levelarena/cpu_byteslice_level_arena_value_workers.hpp).  The value
  // columns of every slot are split into fixed, contiguous, public ranges,
  // one per worker; each worker reads exactly the buckets the requester's
  // own access reads, restricted to its columns, and blends under a
  // constant-time mask, so the trace stays a function of the public plan.
  // Count against the core budget.  Whether they pay off depends on the
  // host, the value width and the placement; measure before enabling.
  // At most 64 workers.  They need a dense prefix of at most 4096 buckets:
  // deamortized_prefix_flushes * deamortized_online_stash_entries / 64 <=
  // 4096 for the resolved prefix_flushes.  Construction throws
  // std::invalid_argument otherwise.
  //   value_tail         oldest probe entries the requester extracts itself
  //   value_kernel       extraction kernel (kAuto: accumulate for narrow
  //                      column ranges, permute for wide ones; kAccumulate
  //                      and kPermute pin one)
  //   value_spin_nanos   spin before a worker parks; value_pause issues PAUSE
  //                      while spinning; value_monitor_wait uses
  //                      src/core/monitor_wait.hpp where the CPU has it,
  //                      instead of parking
  //   value_demote       CLDEMOTE hint on the hand-off lines where supported
  //   value_profile      diagnostic per-thread timing (measurement only)
  //   value_thread_init  run once on each worker, index as argument, to place
  //                      it (same contract as `worker_thread_init`)
  unsigned deamortized_value_workers = 0;
  unsigned deamortized_value_tail = 2;
  ValueKernel deamortized_value_kernel = ValueKernel::kAuto;
  uint64_t deamortized_value_spin_nanos = 200000;
  bool deamortized_value_pause = true;
  bool deamortized_value_monitor_wait = false;
  bool deamortized_value_demote = false;
  bool deamortized_value_profile = false;
  std::function<void(unsigned)> deamortized_value_thread_init;

  // ---- the batch path ----
  //
  // `deamortized_batch_lanes` is the chunk width, per participant, in
  // [1, kMaxBatchLanes]: that many requests share one probe pass so their
  // DRAM misses overlap.  `deamortized_batch_participants` is the tile pool
  // this map is BUILT with, the caller included, in
  // [1, kMaxOnlineParticipants], and is a construction-time decision because
  // each participant is a preallocated tile and a persistent thread.  The
  // chunked shape refuses more than one.
  //
  //   - 16 lanes is the default: wide enough to overlap most of the misses,
  //     narrow enough that the per-lane match work stays small;
  //   - the CHUNKED shape is the default because parallel tiles pay for
  //     three phase joins per job: they help only with several participants,
  //     a job wide enough to amortise the joins, and participants PINNED
  //     beside the request thread (`deamortized_near_max_level` and
  //     `deamortized_batch_thread_init`); unpinned participants on another
  //     cache domain lose.
  //
  // Movable at run time through ByteMap::set_batch_lanes and
  // ByteMap::set_batch_participants, the latter only down to the capacity the
  // map was built with.
  unsigned deamortized_batch_lanes = 16;
  // Chunked cascade or parallel tiles; the best shape depends on the deployed
  // machine's cache topology and core placement.
  BatchExecutionShape deamortized_batch_execution = BatchExecutionShape::kChunkedCascade;
  unsigned deamortized_batch_participants = 1;
  // Opt-in whole-bucket scan of the initial dense prefix. Requires parallel
  // tiles; scalar calls keep the same canonical stash with no conversion.
  bool deamortized_batch_bucket_scan = false;
  // Diagnostic stage clocks; read engine().batch_profile(t) between calls.
  // A measurement switch only.
  bool deamortized_batch_profile = false;
  // Where a lane's probe result lands (see BatchResultLayout above):
  // kSlicedPlaceAtLane or kRows.
  BatchResultLayout deamortized_batch_result_layout =
      BatchResultLayout::kSlicedPlaceAtLane;
  // How long a participant with no phase to run spins before it sleeps.
  // Phases of one call are microseconds apart, so a participant that parked
  // between them would hold up the REQUEST thread rather than the rebuild;
  // the default is the same window the owners use and its use is counted
  // rather than silent.
  uint64_t deamortized_batch_spin_nanos =
      uint64_t{la::kLevelArenaOwnerSpinMicros} * 1000;
  // Run once on each batch participant (index >= 1; participant 0 is the
  // calling thread) before it takes any phase.  Same contract as
  // `worker_thread_init`, and the hook a caller pins the near class with.
  std::function<void(unsigned)> deamortized_batch_thread_init;

  // How long an owner with nothing to do spins before it sleeps.  Waking a
  // parked owner costs the request thread a futex wake (a system call and an
  // inter-processor interrupt), which can dominate a request's service time,
  // so the default window covers the usual gap between carries.  Zero parks
  // immediately, which is a control and what a fixture that means to catch an
  // owner asleep wants.  The requester waiting for a dense prefix slot spins
  // the same window (LevelArenaEngine::Options::owner_spin_nanos).
  uint64_t deamortized_owner_spin_nanos =
      uint64_t{la::kLevelArenaOwnerSpinMicros} * 1000;
  // How long a parked owner or requester sleeps before it looks again anyway.
  // The event protocol does not need this -- no wake is lost by construction
  // (cpu_byteslice_level_arena_event.hpp) -- so it is a safety net, and its
  // use is COUNTED (ByteMap::parks) rather than silent.  Positive.
  unsigned deamortized_park_retry_micros = 1000;
  // A REBUILD THREAD BUDGET, for the heuristic to divide
  // (levelarena/cpu_byteslice_level_arena_rebuild_params.hpp).  0 -- the
  // default -- uses `deamortized_owner_threads` owner groups as given, with
  // no helpers.  Otherwise it REPLACES that count: the map plans a geometry,
  // asks `HeuristicRebuildParams` how to spend this many threads on it --
  // owner groups while a group is the bottleneck, then helper threads and
  // lanes on the top's group -- and builds that, respecting
  // `deamortized_near_max_level`.  It may spend fewer threads than it is
  // given, when the model says another one gains nothing.  Setting it
  // together with `deamortized_top_helpers`, `deamortized_rebuild_lanes` or
  // `deamortized_level_groups` is refused: those are one answer each to the
  // question this asks the heuristic.
  unsigned deamortized_rebuild_threads = 0;
  // CACHE-DOMAIN CAPS on that budget (LevelArenaThreadBudget): with an
  // explicit `deamortized_near_max_level`, at most this many of its threads
  // may be near (on the request thread's domain), and at most this many far
  // (the other domains, the top's helpers included).  0 -- the default -- is
  // no cap.  A placement that keeps near threads on the request thread's
  // domain needs them, or a budget larger than a domain can put more threads
  // on one side than it has cores.  Read only with a budget and a boundary.
  unsigned deamortized_near_rebuild_threads = 0;
  unsigned deamortized_far_rebuild_threads = 0;
  // THE REBUILD COST MODEL the heuristic divides a budget by, and the engine
  // chooses a default division and slice rate by
  // (levelarena/cpu_byteslice_level_arena_rebuild_params.hpp).  The default
  // holds calibration constants fitted on one development machine; a
  // target's comes from the tuner (`python -m analysis.oram_bench
  // fit-rebuild`, see CONFIGURATION.md).  It changes thread division and
  // slicing only, never what is stored or which memory an access touches.
  la::LevelArenaRebuildCost deamortized_rebuild_cost;
  // AN EXPLICIT DIVISION of the levels among the owner threads, highest group
  // first, for a tuner or an A/B measurement; empty -- the default -- lets
  // the load heuristic choose.  It needs `deamortized_owner_threads` groups
  // covering the chosen geometry's levels, so a caller that sets it pins the
  // geometry too.
  std::vector<la::LevelGroupPlan> deamortized_level_groups;
  // THE REQUEST RATE THE REBUILD'S PIECES ARE SIZED FOR
  // (LevelArenaEngine::Options::slice_target_rate), in accesses per second.
  // Every owner group cuts its phases into pieces and visits its levels
  // earliest deadline first, so a level whose deadline is near waits for one
  // piece of whatever its owner was running rather than for a whole phase,
  // which at large capacities is the difference between short requester
  // stalls and stalls as long as a whole top rebuild.  0 -- the default --
  // sizes them for the rate one
  // sequential requester saturates at on the chosen geometry.  The stored
  // tables are byte-identical at any rate.
  double deamortized_slice_target_rate = 0.0;
  // A fixed piece size in bucket touches, overriding the rate; 0 uses it.
  size_t deamortized_slice_touches = 0;
  // With no owner threads, each flush's share of the rebuild as a multiple of
  // its average (LevelArenaEngine::Options::inline_work_factor), positive.
  double deamortized_inline_work_factor = la::kLevelArenaInlineWorkFactor;
  // The most lanes a level's rebuild stages run at, 1..64, and the table size
  // in buckets below which a level takes one
  // (LevelArenaEngine::Options::lanes).
  size_t deamortized_rebuild_lanes = 1;
  size_t deamortized_lane_min_buckets = size_t{1} << 15;
  // Helper threads for the owner group that holds the top level
  // (LevelArenaEngine::Options::top_helpers); they need lanes to share.  Cut
  // to the physical cores the caller, the batch participants and the owners
  // leave (HostPhysicalCores), as are the helpers a thread budget chooses:
  // the map never starts more threads than the host has cores.
  unsigned deamortized_top_helpers = 0;
  // Helper threads for the owner group that holds LEVEL 1, when it is not the
  // top's (LevelArenaEngine::Options::bottom_helpers): the same lane sharing
  // for the other expensive level.  Cut to the cores the caller, the batch
  // participants, the owners and the top's helpers leave.
  unsigned deamortized_bottom_helpers = 0;
  // Time every rebuild piece by kind and stage class; a measurement switch.
  bool deamortized_time_rebuild_stages = false;
  // Measurement controls for the level-arena microbenchmark, kept out of
  // the configuration key (configuration.hpp) on purpose: false never starts
  // a preparation before its carry is available
  // (LevelArenaEngine::Options::preroute), and a nonzero capacity keeps the
  // per-merge log of every level (merge_log_capacity).
  bool deamortized_preroute = true;
  size_t deamortized_merge_log_capacity = 0;
  // A DEADLOCK DETECTOR, not a deadline: a protocol bug reports what every
  // level was waiting for instead of hanging.  It bounds two waits of the
  // calling thread.  An access that needs a dense prefix slot waits at most
  // this long for one.  drain_rebuilds() and finish_pending_work() wait as
  // long as the owner threads keep moving (a drain waits out any rebuild in
  // flight, a speculative top preparation included, which grows with the
  // capacity) and give up after this long with no visible progress.
  // Exceeding it throws std::runtime_error before the access changes
  // anything; the map stays usable and the call may be retried.  Thread
  // start (every worker's init hook) and the batch and value pools' joins
  // cannot be abandoned: they wait at least 120 s, longer if this is
  // longer, and then end the process with std::abort().  Positive.
  unsigned deamortized_wait_limit_millis = 120 * 1000;
  // Deamortized-only. Run once ON each owner thread before it drives
  // anything, with its group index as its argument. It exists so a caller can
  // PLACE the thread -- set its affinity, name it, raise its priority -- and
  // it is the only way to do so: a std::thread inherits the affinity mask of
  // the thread that creates it, so a request thread that has pinned itself to
  // one core before constructing the map would otherwise build an owner
  // pinned to the SAME core, spinning against the very thread it serves.
  // Empty leaves placement to the OS. Owner startup is deferred until first
  // use or a nonempty initialization. Startup waits for every worker's hook;
  // a throwing hook cancels and joins the pool and propagates to that call.
  std::function<void(unsigned)> worker_thread_init;
  // Deamortized-only. The same on each rebuild helper thread: top helpers
  // have indices [0, top_helpers), followed by bottom helpers. A helper is
  // created by the thread that starts the owners and inherits its affinity
  // -- a pinned request thread's single core included -- so a caller that
  // places the owners places these too.
  std::function<void(unsigned)> deamortized_helper_thread_init;
  // The seed every tag key and dummy is derived from.  Unset by default, which
  // draws a fresh
  // one for each map as it is CONSTRUCTED: maps built from one Options, or
  // from copies of it, never share one, because a shared key would line up
  // their probe positions for equal keys.  Pin it only to make a run
  // reproduce -- a fixture, a benchmark -- and then give each map its own.
  std::optional<microram::crypto::SecretKeySeed> secret_seed;
};

namespace detail {

namespace bs = microram::byteslice;

inline void ValidateCommonArguments(size_t requested_capacity,
                                    size_t key_bytes, size_t value_bytes) {
  if (requested_capacity == 0) {
    throw std::invalid_argument("requested_capacity must be nonzero");
  }
  if (key_bytes == 0) {
    throw std::invalid_argument("key_bytes must be nonzero");
  }
  if (key_bytes > kMaxUserKeyBytes) {
    throw std::invalid_argument("key_bytes must be at most 64");
  }
  if (value_bytes == 0) {
    throw std::invalid_argument("value_bytes must be nonzero");
  }
  // The widest value whose STORED entry -- the widest stored key, the value,
  // its meta byte and the widest routing tag -- still has a bucket width that
  // size_t can hold.  Anything wider is refused here, by name, rather than
  // reaching a layout whose arithmetic would have to catch it (the engines
  // check again, and every allocation size is checked on its way there).
  constexpr size_t kStoredOverhead = bs::kMaxKeyBytes + 1 + 8;
  if (value_bytes > std::numeric_limits<size_t>::max() / bs::kBucketCapacity -
                        kStoredOverhead) {
    throw std::length_error("value_bytes is too large");
  }
}

// THE RANGES OF THE ARENA OPTIONS, each refused by name with
// std::invalid_argument before anything is planned or allocated.  One
// function for every path to an engine: the constructors and
// `plan_geometry` (through PlanArenaGeometry) and the resolver
// (configuration.hpp), which checks the Options its settings construct
// with.  `synchronous` leaves out the thread knobs that mode ignores.
// Limits that depend on the geometry the ladder chooses are the ladder's.
inline void ValidateArenaOptions(const Options& options, bool synchronous) {
  const auto require = [](bool valid, const char* message) {
    if (!valid) throw std::invalid_argument(message);
  };
  const unsigned branching = options.deamortized_branching_factor;
  require(branching == 2 || branching == 4 || branching == 8,
          "deamortized_branching_factor must be 2, 4 or 8");
  const size_t stash = options.deamortized_online_stash_entries;
  require(stash % bs::kBucketCapacity == 0 &&
              la::IsPowerOfTwo(stash / bs::kBucketCapacity) &&
              stash <= kMaxOnlineStashEntries,
          "deamortized_online_stash_entries must be 64 times a power of two, "
          "at most 262144");
  const unsigned flushes = options.deamortized_prefix_flushes;
  require(flushes == 0 || flushes == 2 || flushes == 4 || flushes == 8,
          "deamortized_prefix_flushes must be 0 (searched), 2, 4 or 8");
  const unsigned digit = options.deamortized_top_digit;
  require(digit == 0 || (la::LevelArenaGeometry::IsTopDigit(digit) &&
                         digit <= branching),
          "deamortized_top_digit must be 0 (searched) or 1, 2, 4 or 8, at "
          "most deamortized_branching_factor");
  require(options.deamortized_dense_prefixes >= 1,
          "deamortized_dense_prefixes must be at least 1");
  require(options.deamortized_tier_buckets <= bs::kMaxResidualStashBuckets,
          "deamortized_tier_buckets must be 0 (sized) or at most 8");
  require(options.deamortized_bank_first == BankFirst::kOff ||
              options.deamortized_bank_first == BankFirst::kNoClone,
          "deamortized_bank_first must be kOff or kNoClone");
  require(options.deamortized_batch_lanes >= 1 &&
              options.deamortized_batch_lanes <= kMaxBatchLanes,
          "deamortized_batch_lanes must be in [1, kMaxBatchLanes]");
  require(options.deamortized_batch_participants >= 1 &&
              options.deamortized_batch_participants <= kMaxOnlineParticipants,
          "deamortized_batch_participants must be in "
          "[1, kMaxOnlineParticipants]");
  require(options.deamortized_batch_execution ==
                  BatchExecutionShape::kChunkedCascade ||
              options.deamortized_batch_execution ==
                  BatchExecutionShape::kParallelTiles,
          "deamortized_batch_execution must be kChunkedCascade or "
          "kParallelTiles");
  require(options.deamortized_batch_execution ==
                  BatchExecutionShape::kParallelTiles ||
              (options.deamortized_batch_participants == 1 &&
               !options.deamortized_batch_bucket_scan),
          "deamortized_batch_participants above 1 and "
          "deamortized_batch_bucket_scan need kParallelTiles");
  require(options.deamortized_batch_result_layout ==
                  BatchResultLayout::kSlicedPlaceAtLane ||
              options.deamortized_batch_result_layout ==
                  BatchResultLayout::kRows,
          "deamortized_batch_result_layout must be kSlicedPlaceAtLane or "
          "kRows");
  require(options.deamortized_value_workers <= 64,
          "deamortized_value_workers must be 0..64");
  require(options.deamortized_value_kernel == ValueKernel::kAuto ||
              options.deamortized_value_kernel == ValueKernel::kAccumulate ||
              options.deamortized_value_kernel == ValueKernel::kPermute,
          "deamortized_value_kernel must be kAuto, kAccumulate or kPermute");
  require(options.deamortized_wait_limit_millis > 0,
          "deamortized_wait_limit_millis must be positive");
  if (synchronous) return;
  require(options.deamortized_rebuild_threads != 0 ||
              options.deamortized_owner_threads <=
                  la::LevelArenaCapacityRequest{}.max_levels,
          "deamortized_owner_threads must be at most 40, the most levels the "
          "ladder searches");
  require(options.deamortized_rebuild_lanes >= 1 &&
              options.deamortized_rebuild_lanes <= 64,
          "deamortized_rebuild_lanes must be 1..64");
  require(options.deamortized_park_retry_micros > 0,
          "deamortized_park_retry_micros must be positive");
  require(std::isfinite(options.deamortized_slice_target_rate) &&
              options.deamortized_slice_target_rate >= 0.0,
          "deamortized_slice_target_rate must be finite and nonnegative");
  require(std::isfinite(options.deamortized_inline_work_factor) &&
              options.deamortized_inline_work_factor > 0.0,
          "deamortized_inline_work_factor must be finite and positive");
}

// An excessive public thread count must exhaust a core budget, never wrap
// around and appear to leave room for another pool.
inline unsigned SaturatedThreadCount(uint64_t count) {
  return static_cast<unsigned>(std::min<uint64_t>(
      count, std::numeric_limits<unsigned>::max()));
}

// At most how many threads a map built from `options` starts beside its
// caller: what a tree must leave its position map before it counts payload
// workers. A budget counts as spent in full. Both storage modes may start
// batch participants and value workers; only the incremental one rebuilds
// on background threads.
template <bool Deamortize>
inline unsigned ThreadsBesideCaller(const Options& options) {
  const unsigned participants =
      options.deamortized_batch_participants > 1
          ? options.deamortized_batch_participants - 1
          : 0;
  uint64_t threads = uint64_t{participants} + options.deamortized_value_workers;
  if constexpr (Deamortize) {
    threads += options.deamortized_rebuild_threads != 0
        ? options.deamortized_rebuild_threads
        : uint64_t{options.deamortized_owner_threads} +
              options.deamortized_top_helpers +
              options.deamortized_bottom_helpers;
  }
  return SaturatedThreadCount(threads);
}

// What `deamortized_rebuild_threads` asks the heuristic for, on a chosen
// geometry: the budget, cut to the choice's cap if it has one, at the
// boundary that geometry resolved.
inline la::LevelArenaRebuildParams BudgetRebuildParams(
    const la::LevelArenaCapacityChoice& choice, const Options& options) {
  la::LevelArenaThreadBudget budget;
  budget.threads = options.deamortized_rebuild_threads;
  if (choice.rebuild_threads_cap != 0) {
    budget.threads = std::min(budget.threads, choice.rebuild_threads_cap);
  }
  budget.near_max_level =
      options.deamortized_near_max_level == 0
          ? 0
          : std::min(choice.resolved_near_max_level, choice.geometry.levels);
  budget.near_threads = options.deamortized_near_rebuild_threads;
  budget.far_threads = options.deamortized_far_rebuild_threads;
  return la::HeuristicRebuildParams(
      la::LevelArenaGeometry(choice.geometry), choice.layout, budget,
      options.deamortized_rebuild_cost,
      la::LevelResidualInputs{options.max_accesses});
}

// THE GEOMETRY THE LADDER CHOOSES for the per-level arena engine, and what it
// costs.  Pure: the same request, options and host give the same answer, which
// is what lets `ByteMap::plan_geometry` be a static function a caller can run
// before it builds anything.  `synchronous` prices the synchronous storage
// mode, which has no threads to divide.
inline la::LevelArenaCapacityChoice PlanArenaGeometry(
    size_t requested_capacity, size_t key_bytes, size_t value_bytes,
    const Options& options, bool synchronous = false) {
  ValidateCommonArguments(requested_capacity, key_bytes, value_bytes);
  if (options.max_accesses == 0) {
    throw std::invalid_argument("max_accesses must be nonzero");
  }
  // Checked here so a refusal names the public knob rather than leaving the
  // ladder without a candidate.
  ValidateArenaOptions(options, synchronous);
  la::LevelArenaCapacityRequest request;
  request.entries = requested_capacity;
  request.key_bytes = key_bytes;
  request.value_bytes = value_bytes;
  request.max_accesses = options.max_accesses;
  request.branching = options.deamortized_branching_factor;
  request.half_fanout_prefix = options.deamortized_half_fanout_prefix;
  request.bank_first = options.deamortized_bank_first;
  request.stash_buckets = options.deamortized_online_stash_entries /
                          microram::byteslice::kBucketCapacity;
  request.dense_prefixes = options.deamortized_dense_prefixes;
  request.tier_buckets = options.deamortized_tier_buckets;
  request.owner_threads = options.deamortized_owner_threads;
  request.lanes.lanes = options.deamortized_rebuild_lanes;
  request.lanes.min_buckets = options.deamortized_lane_min_buckets;
  request.top_digit = options.deamortized_top_digit;
  // A PIN IS THE CALLER'S ANSWER, so it may sit below the ladder's default
  // top-digit floor: the floor guards the unpinned search against a small
  // top, and `Options` has no knob for it, so a public pin below it lowers
  // the floor to itself rather than being refused as a contradiction the
  // caller had no way to resolve (the internal request keeps refusing an
  // explicit pin under an explicit floor).
  if (request.top_digit != 0 &&
      request.top_digit < la::LevelArenaMinTopDigit(request)) {
    request.min_top_digit = request.top_digit;
  }
  request.prefix_flushes = options.deamortized_prefix_flushes;
  request.batch_participants = options.deamortized_batch_participants;
  request.batch_bucket_scan = options.deamortized_batch_bucket_scan;
  if (synchronous) {
    request.synchronous = true;
    request.owner_threads = 0;
    request.lanes = la::LevelLaneConfig{};
    return la::PlanLevelArenaCapacity(request);
  }
  // THE BOUNDARY IS RESOLVED AGAINST A GEOMETRY, and the geometry is what the
  // ladder chooses, so a caller that asked for this host's answer gets a
  // ladder run to find a geometry, the host's answer for THAT geometry, and
  // then a second run that prices the division the engine will really be
  // built with.  Two runs of a pure search over a few dozen candidates, once,
  // at construction.
  request.near_max_level = options.deamortized_near_max_level;
  const auto plan = [&](la::LevelArenaCapacityRequest r) {
    if (options.deamortized_near_max_level != kNearMaxLevelAuto) {
      return la::PlanLevelArenaCapacity(r);
    }
    r.near_max_level = 0;
    const la::LevelArenaCapacityChoice first = la::PlanLevelArenaCapacity(r);
    r.near_max_level = la::AutoNearMaxLevel(
        la::LevelArenaGeometry(first.geometry), first.layout,
        microram::byteslice::HostLastLevelCacheBytes());
    return la::PlanLevelArenaCapacity(r);
  };
  if (options.deamortized_rebuild_threads == 0) return plan(request);
  // A THREAD BUDGET IS DIVIDED ON A GEOMETRY, and the division's group count
  // and lanes are terms of the bill the ladder chooses a geometry by.  So
  // plan, divide, and plan again with what the division costs, until the two
  // agree -- the first time, in practice, because a group count moves the
  // bill by a plan record.
  //
  // A REQUEST SEEN TWICE IS A CYCLE with no geometry that agrees with its
  // division: a plan record moves the ladder's byte budget (1% over the
  // smallest bill) across another candidate's bill (at 2^15 entries, 4 B
  // keys and 8 B values, three groups bill r0 = 4 and that geometry divides
  // into two, which bill r0 = 2, which divides into three).  The budget is
  // then cut to the cycle's fewest owners and the search goes on.  Every request of a real cycle stays within the budget
  // and one has fewer owners than it (owners alone, with no helper, means
  // the default lanes, and two such requests would be the same one), so the
  // cap falls on every cycle, and a budget of one thread is one group with
  // no helper: the search ends, and on the first agreement whenever that is
  // reached without a cycle.
  request.owner_threads = 1;
  request.lanes = la::LevelLaneConfig{};
  la::LevelArenaCapacityChoice choice;
  unsigned cap = 0;
  std::vector<la::LevelArenaCapacityRequest> seen;
  const auto same = [](const la::LevelArenaCapacityRequest& a,
                       const la::LevelArenaCapacityRequest& b) {
    return a.owner_threads == b.owner_threads &&
           a.lanes.lanes == b.lanes.lanes &&
           a.lanes.min_buckets == b.lanes.min_buckets;
  };
  for (;;) {
    choice = plan(request);
    choice.rebuild_threads_cap = cap;
    const la::LevelArenaRebuildParams params =
        BudgetRebuildParams(choice, options);
    const unsigned groups = static_cast<unsigned>(params.groups.size());
    if (groups == request.owner_threads &&
        params.lanes.lanes == request.lanes.lanes &&
        params.lanes.min_buckets == request.lanes.min_buckets) {
      break;
    }
    seen.push_back(request);
    request.owner_threads = groups;
    request.lanes = params.lanes;
    const auto first = std::find_if(
        seen.begin(), seen.end(),
        [&](const la::LevelArenaCapacityRequest& r) { return same(r, request); });
    if (first == seen.end()) continue;
    cap = std::min_element(first, seen.end(),
                           [](const la::LevelArenaCapacityRequest& a,
                              const la::LevelArenaCapacityRequest& b) {
                             return a.owner_threads < b.owner_threads;
                           })->owner_threads;
    seen.clear();
  }
  return choice;
}

// `PlanArenaGeometry` for one instantiation.
template <bool Deamortize>
la::LevelArenaCapacityChoice PlanGeometryFor(size_t requested_capacity,
                                             size_t key_bytes,
                                             size_t value_bytes,
                                             const Options& options) {
  return PlanArenaGeometry(requested_capacity, key_bytes, value_bytes,
                           options, /*synchronous=*/!Deamortize);
}

inline la::LevelArenaEngine::Options ArenaEngineOptions(
    const la::LevelArenaCapacityChoice& choice, size_t key_bytes,
    size_t value_bytes, const Options& options, bool synchronous = false) {
  la::LevelArenaEngine::Options engine;
  // The map starts the owners itself, on first use, so that `initialize` --
  // which is legal only on an untouched map and refused once an owner is
  // running -- keeps working at the default thread count.  See
  // ByteMap::EnsureRunning.
  engine.defer_owner_start = true;
  engine.geometry = choice.geometry;
  engine.key_bytes = key_bytes;
  engine.value_bytes = value_bytes;
  engine.max_accesses = options.max_accesses;
  engine.max_key_normalizations = options.max_key_normalizations;
  engine.max_routing_evaluations = options.max_routing_evaluations;
  engine.secret_seed = options.secret_seed;
  engine.wait_limit_millis = options.deamortized_wait_limit_millis;
  engine.batch_lanes = options.deamortized_batch_lanes;
  engine.batch_execution = options.deamortized_batch_execution;
  engine.batch_participants = options.deamortized_batch_participants;
  engine.batch_bucket_scan = options.deamortized_batch_bucket_scan;
  engine.batch_profile = options.deamortized_batch_profile;
  engine.batch_result_layout = options.deamortized_batch_result_layout;
  engine.value_workers = options.deamortized_value_workers;
  engine.value_tail = options.deamortized_value_tail;
  engine.value_kernel = options.deamortized_value_kernel;
  engine.value_spin_nanos = options.deamortized_value_spin_nanos;
  engine.value_pause = options.deamortized_value_pause;
  engine.value_monitor_wait = options.deamortized_value_monitor_wait;
  engine.value_demote = options.deamortized_value_demote;
  engine.value_profile = options.deamortized_value_profile;
  engine.value_thread_init = options.deamortized_value_thread_init;
  engine.batch_spin_nanos = options.deamortized_batch_spin_nanos;
  engine.batch_thread_init = options.deamortized_batch_thread_init;
  if (synchronous) {
    // The thread knobs are the incremental map's; this one runs every merge
    // on the requester (see the header).
    engine.synchronous = true;
    engine.owner_threads = 0;
    return engine;
  }
  // CLAMPED INTO THE PLANNED GEOMETRY.  The ladder searches only geometries
  // with at least `deamortized_owner_threads` levels, so this is ordinarily
  // the identity; it is written down because the engine refuses a thread with
  // no level to drive, and the clamp is what makes the refusal unreachable
  // from the public surface.
  engine.owner_threads =
      std::min<unsigned>(options.deamortized_owner_threads,
                         choice.geometry.levels);
  engine.owner_spin_nanos = options.deamortized_owner_spin_nanos;
  engine.rebuild_cost = options.deamortized_rebuild_cost;
  engine.park_retry_micros = options.deamortized_park_retry_micros;
  engine.lanes.lanes = options.deamortized_rebuild_lanes;
  engine.lanes.min_buckets = options.deamortized_lane_min_buckets;
  engine.top_helpers = options.deamortized_top_helpers;
  engine.bottom_helpers = options.deamortized_bottom_helpers;
  if (!options.deamortized_level_groups.empty()) {
    if (options.deamortized_level_groups.size() !=
        options.deamortized_owner_threads) {
      throw std::invalid_argument(
          "deamortized_level_groups must hold deamortized_owner_threads "
          "groups");
    }
    engine.groups = options.deamortized_level_groups;
  }
  if (options.deamortized_rebuild_threads != 0) {
    if (options.deamortized_top_helpers != 0 ||
        options.deamortized_bottom_helpers != 0 ||
        options.deamortized_rebuild_lanes != 1 ||
        !options.deamortized_level_groups.empty()) {
      throw std::invalid_argument(
          "deamortized_rebuild_threads chooses the helpers, lanes and "
          "division itself; leave deamortized_top_helpers, "
          "deamortized_rebuild_lanes and deamortized_level_groups unset");
    }
    la::ApplyRebuildParams(BudgetRebuildParams(choice, options), &engine);
  }
  // Explicit rate and share win over the heuristic's.
  if (options.deamortized_slice_target_rate > 0.0) {
    engine.slice_target_rate = options.deamortized_slice_target_rate;
  }
  engine.slice_touches = options.deamortized_slice_touches;
  engine.inline_work_factor = options.deamortized_inline_work_factor;
  engine.time_rebuild_stages = options.deamortized_time_rebuild_stages;
  engine.preroute = options.deamortized_preroute;
  engine.merge_log_capacity = options.deamortized_merge_log_capacity;
  engine.worker_init = options.worker_thread_init;
  engine.helper_init = options.deamortized_helper_thread_init;
  // RESOLVED HERE AND NOWHERE DEEPER.  The engine takes an explicit level,
  // because the boundary changes its byte bill; the sentinel that means "ask
  // this host" is answered once, against the geometry the ladder has just
  // chosen, so that two hosts never disagree about what one geometry costs
  // and only a caller that asked for the host's answer gets one.  The ladder
  // has already resolved `kNearMaxLevelAuto` against the geometry it chose
  // (see PlanArenaGeometry) and priced that division, so what reaches the
  // engine is always an explicit level -- clamped, because a boundary above
  // this geometry's top means "all of it is near".
  engine.near_max_level =
      options.deamortized_near_max_level == 0
          ? 0
          : std::min(choice.resolved_near_max_level, choice.geometry.levels);
  // NO MORE THREADS THAN PHYSICAL CORES (cpu_byteslice_host_cores.hpp).  The
  // caller, its batch participants, value workers and owner threads are the
  // structure the geometry was planned for, so they are kept; the top's
  // helpers only widen one group's lanes and are cut to the cores left. Explicit
  // helpers and the thread budget's alike, and after the division, so a plan
  // does not depend on the host that planned it -- a resolved configuration
  // built on a smaller host fails its agreement check instead of changing.
  // The byte bill does not depend on the helper count.
  if (engine.owner_threads > 0) {
    const uint64_t reserved = uint64_t{std::max(1u, engine.batch_participants)} +
                              engine.owner_threads + engine.value_workers;
    engine.top_helpers = microram::byteslice::HelpersThatFit(
        engine.top_helpers, SaturatedThreadCount(reserved));
    engine.bottom_helpers = microram::byteslice::HelpersThatFit(
        engine.bottom_helpers,
        SaturatedThreadCount(reserved + engine.top_helpers));
  }
  return engine;
}

// The engine, built from the geometry `PlanGeometryFor` already chose so that
// the map can keep it (`ByteMap::geometry_choice`) instead of asking a
// constructed engine what it cost.
inline std::unique_ptr<la::LevelArenaEngine> MakeArenaEngine(
    const la::LevelArenaCapacityChoice& choice, size_t key_bytes,
    size_t value_bytes, const Options& options, bool synchronous = false) {
  return std::make_unique<la::LevelArenaEngine>(
      ArenaEngineOptions(choice, key_bytes, value_bytes, options, synchronous));
}

inline void RequirePointer(const void* pointer, const char* name) {
  if (pointer == nullptr) {
    throw std::invalid_argument(name);
  }
}

// HOW MANY REQUESTS A BATCH ADAPTER STAGES AT A TIME -- the packed
// conveniences' descriptors, and the typed map's encoded keys and found flags
// beside them.  Staging a caller's whole batch would keep tens of bytes per
// request allocated after the call (tens of MiB for a million-request batch,
// outside every byte bill), while the engine only ever consumes one combined
// job at a time.  So the
// adapters stage a whole number of those jobs and hand them over in order: the
// engine cuts a batch into consecutive jobs of `combined_width` requests, so
// every job, and therefore every answer and every effect, is the one the
// unstaged call produced.  Public: a function of the job width alone.
inline constexpr size_t kBatchStagingRequests = 4096;

inline size_t BatchStagingRequests(unsigned combined_width) {
  const size_t width = combined_width == 0 ? 1 : combined_width;
  return width * std::max<size_t>(1, kBatchStagingRequests / width);
}

}  // namespace detail

// A fixed-width byte map over the per-level arena engine
// (src/oram/levelarena/DESIGN.md).  Deamortize=true, the default, overlaps
// rebuilding with accesses on owner threads; false is the engine's
// synchronous storage mode, which merges in place on the requester in about
// half the main storage.
//
// find(), insert_or_assign(), erase(), and contains() are all ORAM accesses;
// even a miss changes the internal access schedule. The pointed-to key and
// value buffers need only remain valid for the duration of the call.
//
// WHAT IS SECRET.  Keys, values, and whether a key is present are secret.
// Capacity, key and value widths, options, the operation count, which
// operation is called (find vs. erase, scalar vs. batch) and batch
// dimensions are public.  The observable trace of an access (memory
// addresses and control flow) depends on secret state only through hashed
// addresses under a secret AES key, which is what makes traces
// indistinguishable.  The bool an operation returns, and anything the
// caller does with it, are the caller's to protect.  See the repository
// DESIGN.md, "Security boundary and limitations".
//
// FAILURE.  Invalid arguments throw std::invalid_argument (null pointers,
// bad options) before any state changes; exceeding `max_accesses` or a key
// normalization budget throws std::overflow_error before mutation.  A wait
// for the owner threads that passes `deamortized_wait_limit_millis` throws
// std::runtime_error, also before mutation; failed() stays false and the
// map stays usable.  A rebuild that overflows its certified capacity -- an
// event of probability at most the certified bound -- latches the engine
// failed: the next access throws std::runtime_error and the map must be
// discarded (see failed()).
//
// THREADING.  Calls on one map must be serialized by the caller; the map's
// own threads synchronize internally.
//
// MOVING.  A moved-from map, of this class or of any adapter built on it,
// may only be destroyed or assigned to; every other member, the noexcept
// accessors included, needs the engine the move took.
template <bool Deamortize = true>
class ByteMap {
 public:
  using options_type = Options;
  static constexpr bool deamortized = Deamortize;
  // Both hierarchical engines have a bulk initializer; the hybrid map does
  // not (it may select the tree engine), and the typed adapter keys its own
  // `initialize` on this so `Map` never promises one.
  static constexpr bool supports_initialize = true;

  // TWO STEPS, because the geometry outlives the constructor.  The ladder's
  // choice is what `geometry_choice()` reports and what the engine is built
  // from, so it is planned into a member first and the engine second.
  explicit ByteMap(size_t requested_capacity, size_t key_bytes,
                   size_t value_bytes, Options options = {})
      : requested_capacity_(requested_capacity),
        key_bytes_(key_bytes),
        value_bytes_(value_bytes),
        choice_(detail::PlanGeometryFor<Deamortize>(
            requested_capacity, key_bytes, value_bytes, options)),
        engine_(detail::MakeArenaEngine(choice_, key_bytes, value_bytes,
                                        options, !Deamortize)),
        scratch_(value_bytes),
        max_accesses_(options.max_accesses) {}

#ifdef MICRORAM_BYTESLICE_BATCH_PROFILE
  // Diagnostic harness: run the public adapter over the exact same engine
  // configuration/seed as the direct arm, including experimental knobs.  The
  // geometry member stays empty -- the engine was planned outside this map,
  // so there is no ladder choice to report.
  ByteMap(size_t requested_capacity, size_t key_bytes, size_t value_bytes,
          std::unique_ptr<la::LevelArenaEngine> engine)
      : requested_capacity_(requested_capacity), key_bytes_(key_bytes),
        value_bytes_(value_bytes), engine_(std::move(engine)),
        scratch_(value_bytes) {}
#endif
  ~ByteMap() = default;
  // A moved-from map may only be destroyed or assigned to.  Assigning a map
  // to itself leaves it as it was (a memberwise self-move would empty its
  // scratch buffers); otherwise the target is destroyed, its threads joined,
  // and move-constructed from the source.
  ByteMap(ByteMap&&) noexcept = default;
  ByteMap& operator=(ByteMap&& other) noexcept {
    if (this != &other) {
      this->~ByteMap();
      ::new (static_cast<void*>(this)) ByteMap(std::move(other));
    }
    return *this;
  }
  ByteMap(const ByteMap&) = delete;
  ByteMap& operator=(const ByteMap&) = delete;

  // ONE-SHOT DIRECT INITIALIZATION.  Builds the engine's largest level from
  // `count` input records instead of writing them one access at a time: the
  // records are scattered over that level's own final region at its ordinary
  // load and routed there in place, so nothing walks the ladder and no
  // staging table is allocated.
  //
  // `first` is a SINGLE-PASS input iterator whose dereference yields an
  // `InitializationEntry` -- a `key_bytes()`-wide key and a
  // `value_bytes()`-wide value, consumed before the increment.  Only
  // dereference and pre-increment are used and the iterator is never
  // replayed, so a generated input needs storage for exactly one record.
  //
  // `count` is public and at most `capacity()`; it need not fill the table.
  // Empty input is a no-op.  Only `kDistinct` is implemented -- the caller's
  // guarantee that no key repeats.
  //
  // Legal only on an untouched map, only once, and only with exclusive
  // access.  `access_count()` still reports online accesses from zero.  An
  // iterator exception restores the logical state; its normalization
  // reservation stays spent, and a retry needs sufficient remaining budget.
  //
  // IT WORKS AT EVERY THREAD COUNT, and that costs one thing worth knowing.
  // The load drives the levels from the CALLING thread, and one thread cannot
  // establish "untouched" about storage several others are driving, so the
  // engine refuses an initialization once an owner is running.  Rather than
  // make bulk loading a property of how the map was constructed, this map
  // does not start its owner threads until it is first USED -- so the legal
  // order is construct, initialize, then access, and nothing about
  // `deamortized_owner_threads` changes.  Calling `initialize` after any
  // access, or a second time with records, is refused with an exception
  // before anything is published.
  template <class InputIterator>
  void initialize(InputIterator first, size_t count,
                  InitializationPolicy policy =
                      InitializationPolicy::kDistinct) {
    initialize_called_ = true;
    engine_->Initialize(first, count, policy);
    // An empty input is a no-op, owners included: the map is still untouched,
    // so a later initialization with records must still be legal.  The engine
    // has already refused a bad policy or a used map either way.
    if (count == 0) return;
    EnsureRunning();
  }

  // One ORAM access.  Copies the key's value (value_bytes() wide) into
  // `value_out` on a hit and writes zero bytes on a miss, so the caller's
  // buffer is written either way; returns whether the key was present.  A
  // miss still inserts a tombstone (see capacity()).
  bool find(const uint8_t* key, uint8_t* value_out) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value_out, "value_out must not be null");
    EnsureRunning();
    return engine_->Read(key, value_out);
  }

  // One ORAM access: the key now maps to `value` (value_bytes() wide).
  void insert_or_assign(const uint8_t* key, const uint8_t* value) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value, "value must not be null");
    EnsureRunning();
    engine_->Write(key, value);
  }

  // Blind upsert: no previous value or presence is requested, so no cascade
  // is needed. Older copies are resolved by the rebuild's deduplication.
  void write(const uint8_t* key, const uint8_t* value) {
    insert_or_assign(key, value);
  }

  // Alias of write(): a blind upsert that does not probe for the previous value.
  void insert_without_probe(const uint8_t* key, const uint8_t* value) {
    write(key, value);
  }

  // Call once on both hits and misses (zero value on miss), then upsert.
  // Accepts void(value[, found]) or void(key, value[, found]), using mutable
  // byte pointers. A key-changing signature always tombstones the source and
  // writes the destination, even when the callback leaves the key unchanged.
  // The callback must not reenter this map or retain its temporary buffers.
  template <class Update>
  bool access(const uint8_t* key, Update&& update) {
    detail::RequirePointer(key, "key must not be null");
    using Callback = detail::AccessCallback<Update, uint8_t*, uint8_t*>;
    EnsureRunning();
    // A key-changing callback commits a source tombstone and a destination
    // write. Check their whole public cost before invoking user code or
    // removing the source; a smaller operation can still use the remainder.
    engine_->RequireAccessBudget(Callback::changes_key ? 2 : 1);
    engine_->RequireKeyNormalizationBudget(Callback::changes_key ? 2 : 1);
    // And the prefix slots both inserts need, so that the destination write
    // cannot be refused at the wait limit after the source tombstone.
    if constexpr (Callback::changes_key) engine_->SecurePrefixSlots(2);
    // Allocate before Probe removes the source. Keep the caller's key intact.
    access_key_.resize(key_bytes_);
    access_value_.resize(value_bytes_);
    std::memcpy(access_key_.data(), key, key_bytes_);
    const auto stored_key = engine_->StoredKey(key);
    const bool found = engine_->AccessStored(
        stored_key, access_value_.data(),
        [&](uint8_t* bytes, bool present) {
          Callback::Invoke(update, access_key_.data(), bytes, present);
        }, Callback::changes_key);
    if constexpr (Callback::changes_key) {
      write(access_key_.data(), access_value_.data());
    }
    return found;
  }

  template <class Update>
  bool Access(const uint8_t* key, Update&& update) {
    return access(key, std::forward<Update>(update));
  }

  // One ORAM access: removes the key (by inserting a tombstone) and returns
  // whether it was present.
  bool erase(const uint8_t* key) {
    detail::RequirePointer(key, "key must not be null");
    EnsureRunning();
    return engine_->Erase(key);
  }

  // One ORAM access that reads and then writes.  `old_out` receives the key's
  // current value (zeros when absent); the key then holds `value` if it was
  // present or `insert` is true, and otherwise stays absent exactly as after a
  // find().  Returns whether the key was present.  find() + insert_or_assign()
  // would be two accesses; this is one.
  bool exchange(const uint8_t* key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value, "value must not be null");
    detail::RequirePointer(old_out, "old_out must not be null");
    EnsureRunning();
    return engine_->Exchange(key, value, old_out, insert);
  }

  // erase() that also returns the erased value (zeros when absent).
  bool erase(const uint8_t* key, uint8_t* old_out) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(old_out, "old_out must not be null");
    EnsureRunning();
    return engine_->Erase(key, old_out);
  }

  // One ORAM access, identical in trace to find(); returns presence only.
  bool contains(const uint8_t* key) {
    detail::RequirePointer(key, "key must not be null");
    EnsureRunning();
    return engine_->Read(key, scratch_.data());
  }

  // THE BATCH API (repository README.md, "Batched access"). Independent
  // requests, potentially from many clients, are ordered by lane. A write
  // is visible to later reads of its key, within this batch and in later
  // calls, until superseded by another write or erase. Serial program
  // equivalence is not promised: keys, inputs and request descriptors must
  // not alias or depend on another lane's outputs (including found_out);
  // when they do, the result depends on the execution shape. A write or
  // exchange may overlap its OWN value_in and value_out, even partially.
  // The deamortized engine probes `batch_lanes()` requests at a time to
  // overlap their DRAM misses. Per request: `op` and `insert` are public,
  // `key` is key_bytes() wide, `value_in` and `value_out` value_bytes() wide.
  // A non-null `value_out` receives the value BEFORE the
  // request's own operation, zeros when absent or erased; `found_out[i]`,
  // when `found_out` is non-null, is whether request i's key was present
  // before it ran, including on a write. With neither output requested,
  // kWrite skips probing; kReadThenWrite explicitly retains the probe.
  // Repeated keys are legal. Calls on
  // one instance must still be serialized by the server/caller.  The batch
  // size `n` and every request's `op`/`insert` are public; keys, values and
  // presence are secret.  An unknown op or a null required pointer throws
  // std::invalid_argument before any request runs.
  void access_batch(size_t n, const BatchRequest* requests,
                    uint8_t* found_out) {
    if (n == 0) return;
    detail::RequirePointer(requests, "requests must not be null");
    for (size_t i = 0; i < n; ++i) {
      const BatchRequest& r = requests[i];
      if (r.op != BatchOp::kRead && r.op != BatchOp::kWrite &&
          r.op != BatchOp::kErase && r.op != BatchOp::kExchange &&
          r.op != BatchOp::kReadThenWrite) {
        throw std::invalid_argument("unknown batch operation");
      }
      detail::RequirePointer(r.key, "request key must not be null");
      if (r.op == BatchOp::kWrite || r.op == BatchOp::kReadThenWrite ||
          r.op == BatchOp::kExchange) {
        detail::RequirePointer(r.value_in, "request value_in must not be null");
      }
    }
    EnsureRunning();
    engine_->AccessBatch(n, requests, found_out);
  }

  // Packed conveniences over access_batch: `keys` is n keys key_bytes() apart,
  // `values` / `values_out` n values value_bytes() apart.  Staged a bounded
  // run of whole jobs at a time (detail::BatchStagingRequests).
  void find_batch(size_t n, const uint8_t* keys, uint8_t* values_out,
                  uint8_t* found_out) {
    if (n == 0) return;
    detail::RequirePointer(keys, "keys must not be null");
    detail::RequirePointer(values_out, "values_out must not be null");
    RunStaged(n, found_out, [&](size_t i) {
      return BatchRequest{BatchOp::kRead, false, keys + i * key_bytes_,
                          nullptr, values_out + i * value_bytes_};
    });
  }
  void insert_or_assign_batch(size_t n, const uint8_t* keys,
                              const uint8_t* values) {
    if (n == 0) return;
    detail::RequirePointer(keys, "keys must not be null");
    detail::RequirePointer(values, "values must not be null");
    RunStaged(n, nullptr, [&](size_t i) {
      return BatchRequest{BatchOp::kWrite, false, keys + i * key_bytes_,
                          values + i * value_bytes_, nullptr};
    });
  }
  void erase_batch(size_t n, const uint8_t* keys, uint8_t* found_out) {
    if (n == 0) return;
    detail::RequirePointer(keys, "keys must not be null");
    RunStaged(n, found_out, [&](size_t i) {
      return BatchRequest{BatchOp::kErase, false, keys + i * key_bytes_,
                          nullptr, nullptr};
    });
  }
  // The chunk width, and how to move it at run time (in [1, kMaxBatchLanes]).
  unsigned batch_lanes() const noexcept { return engine_->batch_lanes(); }
  // Maximum requests sharing one probe snapshot. In chunked mode this equals
  // batch_lanes(), regardless of the participant count.
  unsigned max_combined_batch_lanes() const noexcept {
    return static_cast<unsigned>(engine_->MaxCombinedBatchLanes());
  }
  // Tiles running now, and tiles this map was BUILT for.  A caller may run
  // narrower than it built; it may not run wider, because a tile is
  // preallocated scratch and a persistent thread.
  unsigned batch_participants() const noexcept {
    return engine_->batch_participants();
  }
  unsigned batch_participant_capacity() const noexcept {
    return engine_->batch_participant_capacity();
  }
  void set_batch_participants(unsigned participants) {
    engine_->SetBatchParticipants(participants);
  }
  void set_batch_lanes(unsigned lanes) { engine_->SetBatchLanes(lanes); }

  // EVERY ACCEPTED PREFIX MERGED AS FAR AS IT WILL GO.  Precisely: complete
  // accepted work without waiting for a future carry merely because
  // speculative preparation exists, and retain a valid prepared job rather
  // than cancel it.
  //
  // So a drain does NOT leave the hierarchy empty and does not try to.  A
  // half-full level is waiting for carries that only future accesses can
  // produce, and a level that has speculatively routed its older half is
  // holding a PREPARED JOB and the lease it will publish into.  That job is
  // still valid -- it was planned against a coordinate and a destination that
  // have not moved -- so a drain KEEPS it, and the carry it was prepared for
  // uses it when it arrives.  Only shutdown cancels it, giving the lease back
  // explicitly rather than leaving a slot leased for the life of the process.
  //
  // What a drain therefore guarantees is a QUIESCENT hierarchy: nothing is
  // runnable, every publication the accepted work implies has happened, and
  // every retirement those publications allow has been taken.  That is what
  // makes it a measurement barrier, and what lets an inline engine and a
  // threaded one be compared after it.  The synchronous map is always
  // quiescent between calls, so there it finds nothing to do.
  //
  // A map with no access and no call to `initialize` yet has nothing to
  // drain: the call returns without starting the owner threads or any
  // rebuild, so `initialize` stays legal.  After either, it drains as above.
  // (A map whose first use failed re-raises that failure here, as every later
  // call does.)
  void drain_rebuilds() {
    if (!owners_started_ && !initialize_called_ && !engine_->Failed()) return;
    EnsureRunning();
    engine_->Drain();
  }

  // The completion barrier every map type offers (configured maps and the
  // benchmark worker call it); here it is drain_rebuilds().
  void finish_pending_work() { drain_rebuilds(); }

  // WHAT CAPACITY BOUNDS IS THE LIVE SET -- but it is worth knowing why that
  // is not obvious.  A miss and an erase each insert a TOMBSTONE -- a real
  // entry, not a dummy, because a second read of a key that left nothing
  // behind would repeat the first one's probe positions and so announce that
  // the two queries were equal (src/oram/levelarena/DESIGN.md, "Online
  // security and capacity").  A tombstone is only
  // forgotten by a carry into the TOP level, and until then it is an entry
  // like any other.  So the question is what the top holds WHILE it compacts,
  // since that is where a bucket runs out of room.
  //
  // It holds the new live set and next to nothing else.  The top's sweep
  // first clears, in its output, the older copy of every key the incoming
  // carry holds -- a tombstone's included -- and then leaves every one of the
  // carry's tombstones out of the output rather than merging it and clearing
  // it at the tail.  That is exact because the sweep's dedup has just done the
  // tombstone's shadowing job, and FIFO consumption leaves nothing older than
  // the two operands to shadow. Matching older residuals are also cleared
  // from the merge pass's private range table before a tombstone is omitted.
  // It therefore takes no merge slot even when unrelated older residuals
  // target the same bucket.  (Merging EVERY tombstone instead would let a map
  // at capacity that erased half its keys and wrote as many new ones hold
  // 1.5x capacity() at the top -- load 0.75 against a certificate at 0.5 --
  // and overflow; so would missing on, or erasing, half a capacity of absent
  // keys twice each, or writing and erasing new keys in one top window.)
  //
  // A tombstone with no older live copy at all (`kMetaUnshadowed`: its probe
  // found nothing, or found a tombstone that already carried the mark) is
  // skipped at every READ of the top's compaction, the residual scatter
  // included, not only by the sweep.  In every case the source is not
  // written and stays probeable until the top publishes, so a tombstone keeps
  // doing its position job until the top publishes.
  //
  // So neither erasing nor missing draws on capacity(), at every supported top
  // digit including an explicitly pinned D = 1, and the top level's effective
  // load is `load * |live|/capacity` -- the load its failure-probability
  // certificate is computed at -- however long such a workload runs.
  //
  // Overflow raises the declared failure -- a std::runtime_error naming a
  // rebuild bucket that did not fit -- from the next access, never a wrong
  // answer.  It is not a distinguishable exception type: a capacity overflow
  // and an unlucky load are the same physical event.
  size_t capacity() const noexcept {
    return static_cast<size_t>(engine_->Capacity());
  }
  size_t requested_capacity() const noexcept { return requested_capacity_; }
  size_t key_bytes() const noexcept { return key_bytes_; }
  size_t value_bytes() const noexcept { return value_bytes_; }
  // THE COMPLETE BILL, not the arenas: the geometry's arena bytes alone are
  // not the engine's footprint.  `arena_bytes()` is the requested total; `byte_bill()` is where the
  // breakdown by role and the allocator-rounded total live, and
  // `main_arena_bytes()` includes arenas, retained holes, masks and the tier
  // pool (the synchronous regions in synchronous mode).
  size_t arena_bytes() const { return engine_->ByteBill().requested(); }
  const LevelArenaByteBill& byte_bill() const { return engine_->ByteBill(); }
  size_t main_arena_bytes() const { return engine_->ArenaBytes(); }
  uint64_t access_count() const noexcept { return engine_->AccessCount(); }

  // Whether the engine has failed and refuses further work.  It latches a
  // failed rebuild step -- inline or on an owner thread -- or a batch that
  // threw after its probes had removed entries, and every later access, batch
  // and drain re-raises it; the map must be discarded.
  bool failed() const noexcept { return engine_->Failed(); }

  // The geometry the ladder chose, and what it cost.  Public: every number in
  // it is a function of the requested capacity and the caller's own options.
  const la::LevelArenaCapacityChoice& geometry_choice() const {
    return choice_;
  }

  // WHAT THE FAILURE-PROBABILITY ANALYSIS SAYS about this map's geometry at
  // its request horizon (la::CertifyLevelArenaGeometry): certified, above
  // the 2^-64 target, or not covered, with the conditional bound and the
  // reason.  A report, not a gate -- construction never consults it.  Both
  // instantiations run the same jobs, so they share the report.
  la::LevelArenaCertification certification() const {
    if (max_accesses_ == 0) {
      return la::LevelArenaNotCovered(
          "the engine was built outside the ladder; no planned geometry");
    }
    return la::CertifyLevelArenaGeometry(choice_.geometry, max_accesses_);
  }

  // WHAT THIS MAP WOULD CHOOSE, without building it.  A caller that has to
  // place threads needs the geometry and the resolved near/far boundary
  // BEFORE it can construct the engine -- the placement hooks are
  // construction parameters and the boundary decides the grouping they are
  // indexed by -- and building an engine at the production point merely to
  // read its geometry back is a gigabyte and a second of it.  The search is
  // pure, so this is the same answer the constructor gets.
  static la::LevelArenaCapacityChoice plan_geometry(size_t requested_capacity,
                                                    size_t key_bytes,
                                                    size_t value_bytes,
                                                    const Options& options) {
    return detail::PlanGeometryFor<Deamortize>(requested_capacity, key_bytes,
                                               value_bytes, options);
  }

  // ---- instrumentation ------------------------------------------------------
  //
  // Secret-independent by construction: cascade lengths and bucket counts are
  // functions of the published plan, and the plan is a function of public
  // counters alone.  Occupancy is NOT in here for the same reason.
  //   last_probe_tables/buckets/mains  the previous access's probe plan:
  //                                    tables and buckets probed, and how
  //                                    many were hashed mains;
  //   probe_mains, flush_count         cumulative mains probed and online
  //                                    stash flushes.
  size_t last_probe_tables() const { return engine_->LastProbeTables(); }
  size_t last_probe_buckets() const { return engine_->LastProbeBuckets(); }
  size_t last_probe_mains() const { return engine_->LastProbeMains(); }
  uint64_t probe_mains() const { return engine_->ProbeMains(); }
  uint64_t flush_count() const { return engine_->FlushCount(); }
  // Every park anybody did: the requester's backpressure waits and, with
  // owner threads, each group's.  One number, because what it answers is "did
  // this configuration run dry", and the per-actor split is on the engine for
  // a fixture that wants it.  Exact only with the hierarchy quiesced, like
  // every other cross-thread counter here.
  uint64_t parks() const {
    uint64_t total = engine_->requester_waits().parks.get();
    // `owner_groups()` is one even INLINE -- the transient scratch is sized
    // per executing thread either way -- but only a threaded engine has a
    // driver object to ask, so the loop is guarded by that and not by the
    // group count.
    if (!engine_->threaded()) return total;
    for (size_t i = 0; i < engine_->owner_groups(); ++i) {
      total += engine_->group_driver(i).waits().parks.get();
    }
    return total;
  }

  // The engine itself, for a fixture that needs a counter this adapter does
  // not re-export.  Not part of the stable surface.
  la::LevelArenaEngine& engine() noexcept { return *engine_; }
  const la::LevelArenaEngine& engine() const noexcept { return *engine_; }

 private:
  size_t requested_capacity_;
  size_t key_bytes_;
  size_t value_bytes_;
  // The ladder's choice, kept because `geometry_choice()` reports it and the
  // engine cannot be asked what it was planned at.
  la::LevelArenaCapacityChoice choice_;
  std::unique_ptr<la::LevelArenaEngine> engine_;
  std::vector<uint8_t> scratch_;
  // Lazily allocated callback buffers; no caller pointers outlive access().
  std::vector<uint8_t> access_key_;
  std::vector<uint8_t> access_value_;
  // The request horizon the engine was sized for (certification()); 0 when
  // the engine was built outside the ladder.
  uint64_t max_accesses_ = 0;
  // FIRST USE STARTS THE OWNER THREADS, and the reason is `initialize`: a
  // bulk load is refused once an owner is running, so a map that started its
  // owners in the constructor could only be loaded at
  // `deamortized_owner_threads = 0`.  Deferring the start to the first access
  // keeps the bulk loader available at every thread count and costs one
  // predictable branch, on a path that is already about to touch DRAM.  It is
  // a no-op on the synchronous engine and after the first call.
  void EnsureRunning() {
    if (!owners_started_) {
      engine_->StartOwnerThreads();
      owners_started_ = true;
    }
  }

  // One staging run after another, each a whole number of the engine's jobs,
  // with the found flags of each landing at its own offset.
  template <class Describe>
  void RunStaged(size_t n, uint8_t* found_out, Describe&& describe) {
    const size_t chunk = detail::BatchStagingRequests(max_combined_batch_lanes());
    if (requests_.size() < std::min(n, chunk)) requests_.resize(std::min(n, chunk));
    for (size_t base = 0; base < n; base += chunk) {
      const size_t m = std::min(chunk, n - base);
      for (size_t i = 0; i < m; ++i) requests_[i] = describe(base + i);
      access_batch(m, requests_.data(),
                   found_out == nullptr ? nullptr : found_out + base);
    }
  }

  bool owners_started_ = false;
  // Whether `initialize` was called, even with no records: a drain after it
  // drains (drain_rebuilds).
  bool initialize_called_ = false;
  std::vector<BatchRequest> requests_;  // the packed conveniences' requests
};

namespace detail {

// THE TYPED ADAPTER behind Map, HierarchicalMap and TreeMap: a map from Key to
// T over any byte map (ByteMap, TreeByteMap, HybridByteMap).  Keys and values
// are passed to the byte map by object representation, so every operation
// has the byte map's contract -- one ORAM access per call (callback `access`
// may take more on the tree), the same secret/public split, the same
// exceptions.  The adapter itself adds no branch on secret data, except in
// the conveniences documented as branching (optional-returning find, at).
template <typename ByteMap, typename Key, typename T>
class BasicMap {
  static_assert(std::is_trivially_copyable<Key>::value,
                "ORAM map keys must be trivially copyable");
  static_assert(std::is_trivially_copyable<T>::value,
                "ORAM map values must be trivially copyable");
  // Keys match by object representation, so a key type whose equal values
  // can differ in bytes -- padding, which a plain copy need not preserve,
  // or a floating-point member -- would miss silently.
  static_assert(std::has_unique_object_representations<Key>::value,
                "ORAM map keys are matched by their bytes: use a key type "
                "without padding bytes or floating-point members");
  static_assert(sizeof(Key) <= kMaxUserKeyBytes,
                "ORAM map keys are at most 64 bytes");

 public:
  using key_type = Key;
  using mapped_type = T;
  using size_type = size_t;
  using byte_map_type = ByteMap;
  using options_type = typename ByteMap::options_type;
  static constexpr bool deamortized = ByteMap::deamortized;
  // Whether this map's byte map has a bulk initializer.  `HierarchicalMap`
  // does; `Map` -- over the hybrid byte map, which may select the tree engine
  // -- does not, and `initialize` below is not declared for it at all rather
  // than failing somewhere inside the engine.
  static constexpr bool supports_initialize = ByteMap::supports_initialize;

  explicit BasicMap(size_t requested_capacity, options_type options = {})
      : bytes_(requested_capacity, sizeof(Key), sizeof(T),
               std::move(options)),
        wide_value_(MakeWideValue()) {}
  // Default `Map<>` with a core budget (default_rule.hpp); only byte maps
  // that take one (HybridByteMap) compile it.
  BasicMap(size_t requested_capacity, CoreBudget budget)
      : bytes_(requested_capacity, sizeof(Key), sizeof(T), budget),
        wide_value_(MakeWideValue()) {}

  // One ORAM access, hit or miss.  `*value_out` is written on BOTH outcomes
  // -- the value on a hit, all-zero bytes on a miss, which is the byte
  // interface's contract -- so this wrapper adds no branch, no store and no
  // caller-buffer address that depends on the secret result.  (Returning
  // early on a miss and copying only on a hit would put exactly such a branch
  // between the oblivious engine and the caller.)  The returned bool is the
  // one secret this interface hands back; what the caller then does with it
  // is the caller's trace.
  // The byte map writes every byte of the output on both outcomes, so it
  // writes straight into `*value_out`, whatever the width of T.
  bool find(const Key& key, T* value_out) {
    RequirePointer(value_out, "value_out must not be null");
    const KeyStorage key_bytes = EncodeKey(key);
    return bytes_.find(key_bytes.data(), reinterpret_cast<uint8_t*>(value_out));
  }

  // Conveniences that BRANCH on presence by construction -- an optional is
  // engaged or it is not, at() returns or it throws -- so their control flow
  // after the access reveals hit or miss to anything that can observe this
  // thread's instruction trace.  The engine's guarantee ends at find(key,
  // &out) above; use that where the distinction must not show.  They return
  // T by value, so they hold a T on the caller's stack: use find(key, &out)
  // for a very wide T.
  template <typename U = T,
            typename std::enable_if<
                std::is_default_constructible<U>::value, int>::type = 0>
  std::optional<T> find(const Key& key) {
    T value{};
    if (!find(key, &value)) return std::nullopt;
    return value;
  }

  template <typename U = T,
            typename std::enable_if<
                std::is_default_constructible<U>::value, int>::type = 0>
  T at(const Key& key) {
    std::optional<T> value = find(key);
    if (!value) throw std::out_of_range("key is not present in the ORAM map");
    return *value;
  }

  // ONE-SHOT DIRECT INITIALIZATION (ByteMap::initialize for the contract).
  // `first` is a SINGLE-PASS input iterator over pair-like records: `*first`
  // must have `.first` convertible to Key and `.second` to T.  The adapter
  // forwards one record at a time by object representation and buffers no
  // range, so a generated input needs storage for exactly one record.
  template <class InputIterator, class M = ByteMap,
            typename std::enable_if<M::supports_initialize, int>::type = 0>
  void initialize(InputIterator first, size_t count,
                  InitializationPolicy policy =
                      InitializationPolicy::kDistinct) {
    bytes_.initialize(TypedInput<InputIterator>(std::move(first),
                                                wide_value_.get()),
                      count, policy);
  }

  void insert_or_assign(const Key& key, const T& value) {
    const KeyStorage key_bytes = EncodeKey(key);
    bytes_.insert_or_assign(key_bytes.data(), ObjectBytes(value));
  }

  void write(const Key& key, const T& value) { insert_or_assign(key, value); }

  // Read and replace in one backend access; also supports an aliased value
  // and output. Unlike optional-returning find, this does not branch on hits.
  bool exchange(const Key& key, const T& value, T* old_out, bool insert = true) {
    RequirePointer(old_out, "old_out must not be null");
    const KeyStorage key_bytes = EncodeKey(key);
    // The old value's staging: a local up to kTypedStackValueBytes, else
    // this map's buffer.
    std::conditional_t<kWideValue, char, std::array<uint8_t, sizeof(T)>>
        local{};
    uint8_t* old_bytes = StagedBytes(local);
    const bool found = bytes_.exchange(key_bytes.data(), ObjectBytes(value),
                                       old_bytes, insert);
    std::memcpy(old_out, old_bytes, sizeof(T));
    return found;
  }

  // Mutators use T& or Key&, T&, optionally followed by a presence bool.
  // T must be default constructible to materialize a live callback object.
  // On a miss its bytes are zero; callbacks must check presence before
  // interpreting types for which all-zero bytes are not a valid value.
  template <class Update>
  bool access(const Key& key, Update&& update) {
    static_assert(std::is_default_constructible_v<T>,
                  "typed Access requires a default-constructible value type");
    using Callback = AccessCallback<Update, Key&, T&>;
    const KeyStorage key_bytes = EncodeKey(key);
    // The callback's object, value-initialized: a local up to
    // kTypedStackValueBytes, else this map's buffer.
    std::conditional_t<kWideValue, char, T> local{};
    T& value = StagedValue(local);
    if constexpr (Callback::changes_key) {
      Key updated_key = key;
      // Keys compare by representation (a typed key has no padding bytes:
      // the static_assert above), so the callback's key is the stored bytes.
      std::memcpy(std::addressof(updated_key), key_bytes.data(), sizeof(Key));
      return bytes_.access(key_bytes.data(),
          [&](uint8_t* raw_key, uint8_t* raw_value, bool found) {
            std::memcpy(std::addressof(value), raw_value, sizeof(T));
            Callback::Invoke(update, updated_key, value, found);
            std::memcpy(raw_key, ObjectBytes(updated_key), sizeof(Key));
            std::memcpy(raw_value, ObjectBytes(value), sizeof(T));
          });
    } else {
      return bytes_.access(key_bytes.data(),
          [&](uint8_t* raw_value, bool found) {
            std::memcpy(std::addressof(value), raw_value, sizeof(T));
            // No mutable key is exposed by this callback signature.
            InvokeValueCallback(update, value, found);
            std::memcpy(raw_value, ObjectBytes(value), sizeof(T));
          });
    }
  }

  template <class Update>
  bool Access(const Key& key, Update&& update) {
    return access(key, std::forward<Update>(update));
  }

  bool erase(const Key& key) {
    const KeyStorage key_bytes = EncodeKey(key);
    return bytes_.erase(key_bytes.data());
  }
  bool contains(const Key& key) {
    const KeyStorage key_bytes = EncodeKey(key);
    return bytes_.contains(key_bytes.data());
  }

  // The batch API over arrays of `n` keys and values (ByteMap::access_batch
  // for the contract).  `values_out[i]` is written for every key -- the value
  // on a hit, zero bytes on a miss -- and `found_out[i]`, when `found_out` is
  // non-null, is whether key i was present before request i ran.
  void find_batch(size_t n, const Key* keys, T* values_out, bool* found_out) {
    if (n == 0) return;
    RequirePointer(keys, "keys must not be null");
    RequirePointer(values_out, "values_out must not be null");
    RunStaged(n, keys, found_out, [&](size_t i, const uint8_t* key) {
      return BatchRequest{BatchOp::kRead, false, key, nullptr,
                          reinterpret_cast<uint8_t*>(values_out + i)};
    });
  }
  void insert_or_assign_batch(size_t n, const Key* keys, const T* values) {
    if (n == 0) return;
    RequirePointer(keys, "keys must not be null");
    RequirePointer(values, "values must not be null");
    RunStaged(n, keys, nullptr, [&](size_t i, const uint8_t* key) {
      return BatchRequest{BatchOp::kWrite, false, key, ObjectBytes(values[i]),
                          nullptr};
    });
  }
  void erase_batch(size_t n, const Key* keys, bool* found_out) {
    if (n == 0) return;
    RequirePointer(keys, "keys must not be null");
    RunStaged(n, keys, found_out, [&](size_t, const uint8_t* key) {
      return BatchRequest{BatchOp::kErase, false, key, nullptr, nullptr};
    });
  }
  unsigned batch_participants() const noexcept { return bytes_.batch_participants(); }
  unsigned batch_participant_capacity() const noexcept {
    return bytes_.batch_participant_capacity();
  }
  void set_batch_participants(unsigned participants) {
    bytes_.set_batch_participants(participants);
  }
  unsigned batch_lanes() const noexcept { return bytes_.batch_lanes(); }
  unsigned max_combined_batch_lanes() const noexcept {
    return bytes_.max_combined_batch_lanes();
  }
  void set_batch_lanes(unsigned lanes) { bytes_.set_batch_lanes(lanes); }

  void drain_rebuilds() { bytes_.drain_rebuilds(); }

  // See ByteMap::capacity(): on the deamortized engine this bounds the LIVE
  // SET -- the top level's sweep leaves a miss's or an erase's tombstone out
  // of its output once its older copies are cleared.
  size_t capacity() const noexcept { return bytes_.capacity(); }
  // Provided for std::unordered_map's shape.  There is no size(); read
  // capacity()'s comment before sizing.
  size_t max_size() const noexcept { return capacity(); }
  size_t requested_capacity() const noexcept {
    return bytes_.requested_capacity();
  }
  size_t arena_bytes() const { return bytes_.arena_bytes(); }
  void finish_pending_work() { bytes_.finish_pending_work(); }
  uint64_t access_count() const noexcept { return bytes_.access_count(); }

  ByteMap& byte_map() noexcept { return bytes_; }
  const ByteMap& byte_map() const noexcept { return bytes_; }

 private:
  template <class Update>
  static void InvokeValueCallback(Update& update, T& value, bool found) {
    // Avoid constructing or copying a Key for value-only updates.
    if constexpr (std::is_invocable_v<Update&, T&, bool>) {
      static_assert(std::is_void_v<std::invoke_result_t<Update&, T&, bool>>,
                    "Access callbacks must return void");
      std::invoke(update, value, bool(found));
    } else {
      static_assert(std::is_void_v<std::invoke_result_t<Update&, T&>>,
                    "Access callbacks must return void");
      std::invoke(update, value);
    }
  }

  // Whether a temporary T lives in `wide_value_` rather than on the stack
  // (kTypedStackValueBytes).
  static constexpr bool kWideValue = sizeof(T) > kTypedStackValueBytes;
  // One T's worth of storage, aligned for T, for the staging of a wide T.
  struct alignas(T) WideValue {
    uint8_t bytes[sizeof(T)];
  };
  static std::unique_ptr<WideValue> MakeWideValue() {
    if constexpr (kWideValue) return std::make_unique<WideValue>();
    return nullptr;
  }
  template <class Local>
  uint8_t* StagedBytes(Local& local) noexcept {
    if constexpr (kWideValue) {
      return wide_value_->bytes;
    } else {
      return local.data();
    }
  }
  template <class Local>
  T& StagedValue(Local& local) {
    if constexpr (kWideValue) {
      return *::new (static_cast<void*>(wide_value_->bytes)) T{};
    } else {
      return local;
    }
  }

  // Keep at least one full internal key block available. This is also useful
  // to optimizing compilers: the engine's runtime wide-key branch can safely
  // inspect up to 16 bytes even when Key itself is only a byte or a word.
  static constexpr size_t kKeyStorageBytes =
      sizeof(Key) < bs::kMaxKeyBytes ? bs::kMaxKeyBytes : sizeof(Key);
  using KeyStorage = std::array<uint8_t, kKeyStorageBytes>;

  // The typed -> byte adapter Initialize consumes.  It holds ONE record: the
  // key in the same padded storage EncodeKey builds and the mapped value by
  // object representation, both refilled at each dereference.  The wrapped
  // iterator is dereferenced exactly once per position and advanced only by
  // the ++ below, so a single-pass generator is enough.  A wide value is
  // held in the map's buffer (`wide`) instead of in the iterator, which is
  // passed by value.
  template <class InputIterator>
  class TypedInput {
   public:
    TypedInput(InputIterator it, WideValue* wide)
        : it_(std::move(it)), wide_(wide) {}

    InitializationEntry operator*() {
      auto&& record = *it_;
      key_ = EncodeKey(static_cast<Key>(record.first));
      if constexpr (kWideValue) {
        // Converted straight into the buffer: no T on the stack.
        ::new (static_cast<void*>(wide_->bytes))
            T(static_cast<T>(record.second));
        return InitializationEntry{key_.data(), wide_->bytes};
      } else {
        const T value = static_cast<T>(record.second);
        std::memcpy(value_.data(), ObjectBytes(value), sizeof(T));
        return InitializationEntry{key_.data(), value_.data()};
      }
    }
    TypedInput& operator++() {
      ++it_;
      return *this;
    }

   private:
    InputIterator it_;
    KeyStorage key_{};
    std::conditional_t<kWideValue, char, std::array<uint8_t, sizeof(T)>>
        value_{};
    WideValue* wide_;
  };

  static KeyStorage EncodeKey(const Key& key) noexcept {
    KeyStorage bytes{};
    std::memcpy(bytes.data(), std::addressof(key), sizeof(Key));
    return bytes;
  }

  template <typename U>
  static const uint8_t* ObjectBytes(const U& object) noexcept {
    return reinterpret_cast<const uint8_t*>(std::addressof(object));
  }

  // Encodes and submits `n` requests a staging run at a time
  // (BatchStagingRequests): each run's keys are encoded into the adapter's
  // own storage, described by `describe(i, encoded_key)`, and handed over
  // whole, so a run is a whole number of the engine's jobs.
  template <class Describe>
  void RunStaged(size_t n, const Key* keys, bool* found_out,
                 Describe&& describe) {
    const size_t chunk =
        BatchStagingRequests(bytes_.max_combined_batch_lanes());
    const size_t staged = std::min(n, chunk);
    if (batch_keys_.size() < staged) batch_keys_.resize(staged);
    if (batch_requests_.size() < staged) batch_requests_.resize(staged);
    if (found_out != nullptr && batch_found_.size() < staged) {
      batch_found_.resize(staged);
    }
    for (size_t base = 0; base < n; base += chunk) {
      const size_t m = std::min(chunk, n - base);
      for (size_t i = 0; i < m; ++i) {
        batch_keys_[i] = EncodeKey(keys[base + i]);
        batch_requests_[i] = describe(base + i, batch_keys_[i].data());
      }
      if (found_out == nullptr) {
        bytes_.access_batch(m, batch_requests_.data(), nullptr);
        continue;
      }
      bytes_.access_batch(m, batch_requests_.data(), batch_found_.data());
      for (size_t i = 0; i < m; ++i) {
        found_out[base + i] = batch_found_[i] != 0;
      }
    }
  }

  ByteMap bytes_;
  // Staging for a T wider than kTypedStackValueBytes; null otherwise.
  std::unique_ptr<WideValue> wide_value_;
  std::vector<KeyStorage> batch_keys_;
  std::vector<BatchRequest> batch_requests_;
  std::vector<uint8_t> batch_found_;
};

}  // namespace detail

}  // namespace cpu_byteslice_oram
