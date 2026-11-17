#pragma once

// THE ENGINE BUFFER MODEL AND THE CAPACITY LADDER.  DESIGN.md ("Geometry and
// storage bound") derives the main-table storage this prices.
//
// This models buffers, not total heap or resident memory; see bytes.hpp.
// Object and runtime costs vary with geometry, so byte_slack is only a
// buffer-budget policy. Two things live here, and the second uses the first.
//
// `LevelArenaEngineBytes` sums every owning component's own `Bytes(...)`
// predictor into one buffer bill: the level arenas, the dense prefix ring, one merge
// job and one range table per level, the probe-plan pool,
// the boundary rings and the request thread's scratch.  It is a pure function
// of public parameters, so it can be computed for a geometry nobody has built
// -- which is exactly what a ladder needs.
//
// `PlanLevelArenaCapacity` is that ladder.  It enumerates the supported
// `(L, r0, D <= B)` and fanout ladders below the top -- a half-fanout prefix
// of `a` levels at B = 8, a bottom fanout `b_1` otherwise
// (`half_fanout_prefix`) -- at the caller's `B` and `s`, keeps the geometries
// whose rounded entry capacity covers the request, prices each one with the
// buffer bill, and returns the smallest.  The arenas alone are not that
// price -- the geometry-only `ArenaBytes` is not the engine's bill -- and the
// difference is not decorative as a SIZE: at the production point the
// arenas are 99.5 % of the bill, but at the small capacities a position map or
// a test asks for, the plan pool, the per-level jobs and the range scratch are
// up to half of the engine, because they scale with L and with the widest
// residual pass rather than with capacity.
//
// IT CHANGES THE ANSWER.  Over the (B, s, value width, request) sweep in
// cpu_byteslice_level_arena_capacity_test.cpp, pricing by the arenas alone
// picks a different geometry on 142 of 621 requests.  The bottom fanout is
// the clearest case: b_1 trades level 1's partial bank against the DENSE
// PREFIX RING and the per-level fixed terms, and neither of those is inside
// `ArenaBytes`, so an arena-only price cannot see the side of the trade it is
// making, and per-level range scratch and the residual routing's DFS
// workspaces are likewise outside it.  The fixture pins the count EXACTLY, so that a future term which
// reordered more candidates is noticed rather than silently changing every
// geometry this library hands out.
//
// WHAT IS SEARCHED AND WHAT IS NOT.  `L`, `r0`, `D` and the ladder's own
// axis -- the prefix length `a`, or the BOTTOM FANOUT `b_1` -- are searched,
// because they trade size against each other at one capacity.  Which ladder
// is searched is a stated rule, not a price (`half_fanout_prefix`).  `B`, `s` and
// `q` are the caller's: each is a choice about the WORKLOAD rather than about
// the size -- `B` sets the cascade length and the routing work per entry, `s`
// is the insertion unit and therefore the serial scan every access pays, `q`
// is how much rebuild may be outstanding -- and a ladder that moved them to
// save bytes would be silently retuning latency.  Tuning those three is a
// measurement on the target workload, and belongs to a caller that has run
// it.
//
// AND `r0` IS NOT MINIMISED BY BYTES, which is the one place this ladder
// departs from "smallest bill wins".  `r0` is the prefix length: the dense
// prefix ring -- `(q+1) r0 s` buckets -- is SCANNED IN FULL by every access,
// and level 1's prefix dedup is `s^2 r0 (r0-1) / 2` bucket pairs, but level
// 1's carry is `2 r0 s` buckets, and at a fixed capacity and L a four times
// longer prefix pays for two more fanout-B/2 levels, which rewrite each
// record fewer times per bit of capacity.  None of that is in a byte bill,
// whose own preference between two `r0` is in the fifth decimal place.  So
// the selection admits every candidate within `byte_slack` of the smallest
// bill and takes the LARGEST `r0` among them: in throughput sweeps at equal
// bytes, dense scan included, the longer prefix's cheaper rebuild outweighed
// its longer scan, most clearly on write-heavy workloads.  The
// failure bound does not decide it: from 2^20 to 2^28 entries every
// candidate this ladder prices meets the 2^-64 target conditionally
// (analysis/bound_certification/CONFIGURATION_SPACE.md), and the public
// plan reports the bound of the configuration it chose.  Taking the largest
// `r0` costs at most about 0.33 % of the bytes from 2^12 to 2^30 entries
// (the capacity test prints the worst spend), inside the default slack.
//
// WHICH BYTE FIGURE IS MINIMISED: the REQUESTED total, not the reserved one.
// Reserved bytes carry AllocateAligned64's huge-page rounding, which is a
// property of the process -- it moves with `MICRORAM_HUGE_PAGES` and with
// whether the kernel has THP at all -- and a ladder that minimised it would
// hand two processes on one host different geometries for one request.  The
// requested total is the design's own number and is the same everywhere.  Both
// are reported.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_batch.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_boundary.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_bytes.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_dense.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_placement.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_stash.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_synchronous.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_probe_addresses.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"
#include "src/oram/table/cpu_byteslice_stored_key.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// ---------------------------------------------------------------------------
// The shape an engine is built at
// ---------------------------------------------------------------------------

// THE STORED LAYOUT: the user key at the width a bucket holds it in, the value
// with the meta line folded in as its last byte, and a routing tag sized for
// the WIDEST index any digit-bearing table routes on -- log2(U_L), the
// largest non-top block (digit B at level L-1 is U_L buckets) -- plus, above
// it, the digit wherever some table has an odd part above one: a non-top
// fanout above 2.  The top is binary and routes K + log2 D raw bits under no
// digit at all; PlanRoutingTag is told so, and widens
// the tag only where no digit byte already makes the room -- which is B = 2,
// where it also stops reserving a digit byte nothing writes.
//
// The engine derives its layout from this and from nothing else, so the bill
// and the ladder price the bytes the engine will actually allocate.
inline Layout LevelArenaStoredLayout(size_t key_bytes, size_t value_bytes,
                                     const LevelArenaGeometry& geometry) {
  Layout layout;
  layout.key_bytes = StoredKeyBytes(key_bytes);
  // + the meta line.  Checked, as the whole width is below: a value width
  // near SIZE_MAX would otherwise wrap into a small layout whose request
  // scratch is then filled with the caller's width.
  layout.value_bytes = CheckedSizeAdd(value_bytes, 1, "value width");
  const unsigned index_bits =
      Log2Checked(geometry.CarryBuckets(geometry.Levels()), "U_L");
  const RoutingTagPlan tag = PlanRoutingTag(
      index_bits, geometry.AnyFanoutAboveTwo(), index_bits + geometry.TopPower());
  layout.tag_bytes = tag.tag_bytes;
  layout.digit_bits = tag.digit_bits;
  ValidateLayoutWidths(layout);
  return layout;
}

// Every physical buffer in the hierarchy.  It is both the bound on live hashed
// tables -- one per occupied slot -- and half of the plan-record bound, which
// is why it has one spelling.
inline size_t TotalArenaSlots(const LevelArenaGeometry& geometry) {
  size_t slots = 0;
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    slots += geometry.storage().At(l).slots.size();
  }
  return slots;
}

// How many hashed tables can be live at once: one per arena slot, or one per
// level in the synchronous mode, whose levels each hold one region.
inline size_t LiveTableSlots(const LevelArenaGeometry& geometry,
                             bool synchronous) {
  return synchronous ? SynchronousLevels::TableSlots(geometry)
                     : TotalArenaSlots(geometry);
}

// The publisher's sizing, from the geometry and the number of threads that
// publish.  One staging record per PUBLISHING thread, which is the group
// count and not the level count: a group runs one level at a time and so holds
// one staging record at a time.
inline LevelArenaPublisher::Config LevelArenaPublisherConfig(
    const LevelArenaGeometry& geometry, size_t owner_groups,
    bool synchronous = false) {
  LevelArenaPublisher::Config config;
  // The reserved dense half of every plan: the current unit, the frozen part
  // of the prefix being assembled, and at most q complete prefixes.  It has to
  // agree with DensePrefixRing::plan_prefix_slots(), which is where the
  // request thread's half of a plan is actually written.
  config.prefix_slots = geometry.DensePrefixes() + 2;
  config.arena_slots = LiveTableSlots(geometry, synchronous);
  config.dense_slots = geometry.DensePrefixes() + 1;
  config.owner_threads = owner_groups;
  return config;
}

// ---------------------------------------------------------------------------
// The buffer bill (not total allocation; see bytes.hpp)
// ---------------------------------------------------------------------------

// The request thread's own storage: the candidate-address scratch, sized for
// the longest cascade this hierarchy can present, and the six value buffers
// the access path blends through.  Mirrors LevelArenaEngine::AllocateScratch.
inline LevelArenaByteBill RequestScratchBytes(
    const LevelArenaGeometry& geometry, const Layout& layout,
    size_t owner_groups, bool synchronous = false) {
  const LevelArenaPublisher::Config config =
      LevelArenaPublisherConfig(geometry, owner_groups, synchronous);
  LevelArenaByteBill bill;
  bill.AddPlain(ByteRole::kRequestScratch,
                ProbeScratch::Bytes(LevelArenaPublisher::MaxTablesFor(config),
                                    config.arena_slots));
  // Three buffers at the STORED value width (its last byte is the meta line)
  // and three at the user's.
  bill.AddAligned64(ByteRole::kRequestScratch, layout.value_bytes, 3);
  bill.AddAligned64(ByteRole::kRequestScratch, layout.value_bytes - 1, 3);
  return bill;
}

// ONE BATCH TILE PER PARTICIPANT.  It is a fixed cost of a constructed
// engine, whether or not its caller ever batches, because a batch may not
// reach the allocator on the request path; `participants` is the pool the
// engine was BUILT for, which a caller may then run narrower.
//
// Tiles are included in the buffer model even when the caller never batches.
// Object storage and runtime overhead are outside that model; see bytes.hpp.
inline LevelArenaByteBill BatchScratchBytes(const LevelArenaGeometry& geometry,
                                            const Layout& layout,
                                            size_t owner_groups,
                                            unsigned participants,
                                            bool synchronous = false) {
  const LevelArenaPublisher::Config config =
      LevelArenaPublisherConfig(geometry, owner_groups, synchronous);
  LevelArenaByteBill bill;
  for (unsigned p = 0; p < participants; ++p) {
    bill.Add(LevelArenaBatchTile::Bytes(
        LevelArenaPublisher::MaxTablesFor(config), config.arena_slots, layout,
        layout.value_bytes - 1, geometry.StashBuckets()));
  }
  return bill;
}

// `groups` is how many EXECUTING THREADS publish -- one for the inline
// executor, one per owner thread otherwise.  It is a real term of the bill
// and not a rounding: it sizes the plan pool's staging records and the
// request and batch scratch.  Which levels each group holds is not: the
// transient scratch is per level.
//
// `synchronous` prices the synchronous mode instead: its regions and jobs
// (SynchronousLevels::Bytes) replace the arenas, jobs and boundaries.
inline LevelArenaByteBill LevelArenaEngineBytes(
    const LevelArenaGeometry& geometry, const Layout& layout,
    const LevelArenaStashSizing& sizing, size_t groups,
    unsigned batch_participants, bool batch_bucket_scan = false,
    const LevelLaneConfig& lanes = {}, bool synchronous = false) {
  if (groups == 0) {
    throw std::invalid_argument(
        "level arena: a byte bill needs at least one executing thread");
  }
  LevelArenaByteBill bill;
  if (synchronous) bill.Add(SynchronousLevels::Bytes(geometry, sizing, layout));
  else bill.Add(LevelArenaSet::Bytes(geometry, layout));
  for (unsigned l = 1; l <= geometry.Levels() && !synchronous; ++l) {
    const LevelPlan& plan = geometry.storage().At(l);
    bill.Add(LevelMergeJob::StorageBytes(geometry, sizing, layout, l,
                                         LevelLaneCount(geometry, l, lanes)));
    // One boundary per RECEIVING level; level 1 has no inbox and no boundary.
    bill.Add(LevelBoundary::Bytes(plan.inbox_count()));
  }
  bill.Add(DensePrefixRing::Bytes(geometry, layout));
  bill.Add(LevelArenaPublisher::Bytes(
      LevelArenaPublisherConfig(geometry, groups, synchronous)));
  // THE TRANSIENT HALF OF THE RESIDUAL ACCOUNTING: one range table PER LEVEL,
  // sized from that level's widest pass.  Not one per executing thread: a
  // phase may stop between two pieces with its range table attached while
  // its thread runs another level, and a shared table would be clobbered by
  // that level's pass.  The tables are small -- a few times a level's stash
  // depth, not its size -- so the sum over levels costs little more than
  // the widest one alone.
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    bill.Add(LevelMergeScratch::Bytes(
        layout, MaxLevelMergeRangeBuckets(geometry, sizing, l),
        MaxLevelDfsAllocation(geometry, sizing, l)));
  }
  bill.Add(RequestScratchBytes(geometry, layout, groups, synchronous));
  bill.Add(BatchScratchBytes(geometry, layout, groups, batch_participants,
                             synchronous));
  if (batch_bucket_scan)
    bill.Add(LevelArenaBucketBatch::Bytes(batch_participants, layout.value_bytes - 1));
  bill.Validate("this engine");
  return bill;
}

// ---------------------------------------------------------------------------
// The capacity ladder
// ---------------------------------------------------------------------------

// What a caller asks for.  The searched axes -- L, r0, D and a or b_1 -- appear
// only as optional pins below (L only as a search bound); the rest are the
// caller's own and are passed through to the geometry unchanged.
struct LevelArenaCapacityRequest {
  uint64_t entries = 0;  // the capacity to cover; the contract is below

  size_t key_bytes = 8;     // the USER key width
  size_t value_bytes = 16;  // the USER value width
  uint64_t max_accesses = uint64_t{1} << 32;  // the stash certificate's horizon

  unsigned branching = 8;       // B; {2, 4, 8}
  // Build each cycle's first digits in the idle odd bank (Params::bank_first).
  BankFirst bank_first = BankFirst::kNoClone;
  size_t stash_buckets = 1;     // s; the online stash holds 64 s entries
  unsigned dense_prefixes = 2;  // q
  size_t tier_buckets = 0;  // automatic: each level's own tier width

  // How many threads will drive the hierarchy: 0 for the inline executor,
  // otherwise the owner-thread count.  It changes the bill, so it is an input
  // to the ladder and not something applied afterwards.
  unsigned owner_threads = 0;
  // Price the synchronous storage mode (LevelArenaEngine::Options::
  // synchronous) instead of the arenas.  The search, its rules and the
  // geometries it can return are the same; only the bill differs.  Takes no
  // owner threads or lanes.
  bool synchronous = false;
  // How many BATCH participants the engine will be built for (the caller
  // included).  One tile each, and a tile is a fixed cost of a constructed
  // engine, so it is an input to the ladder for the same reason
  // `owner_threads` is.
  unsigned batch_participants = 1;
  bool batch_bucket_scan = false;
  // The near/far boundary the engine will be BUILT with, or 0 for
  // none.  It changes which levels share a group but not the bill, which
  // counts groups; the choice reports it CLAMPED into the chosen geometry's
  // level range, because `L` is what this search varies and a boundary above
  // a candidate's top simply means "all of it is near" there.
  unsigned near_max_level = 0;
  // The lanes the engine will be built with (LevelLaneConfig): a lane is a
  // stash array per level that takes them, so it is part of the bill.
  LevelLaneConfig lanes;

  // THE FANOUT LADDER BELOW THE TOP.  With `half_fanout_prefix` (the default)
  // the lowest `a` levels have fanout B/2 and every level above them B, with
  // `a` in [1, log2 B] searched like any other axis: a B/2 level holds one
  // bit less than a B level, so those `a` reach every residue of the
  // capacity's exponent, which is all that rounding needs.  A fanout-b level
  // rewrites each record (b + 1)/2 times for log2 b bits of capacity -- 1.25
  // a bit at b = 4 against 1.5 at b = 8 -- and level 1's finish offers its
  // pool to every main bucket, so its cost scales with its table, b_1 U_1.
  // A B/2 level 1 therefore halves level 1's work and lowers the total
  // rebuild work despite the extra level, at the price of a few more probe
  // buckets and slightly more bytes.  The byte objective never chooses it,
  // so it is a stated rule and not a price.  It applies where B/2 is at least 4, so at
  // B = 8: at B = 4 a fanout-2 level costs 1.5 rewrites a bit against 1.25,
  // and B < 8 keeps the bottom-fanout search below whatever this says.  And
  // it steps aside where the bottom-fanout ladder rounds the request to a
  // smaller capacity or reaches it at a shorter prefix -- small maps, whose
  // floor geometry the prefix doubles (PlanLevelArenaCapacity).
  bool half_fanout_prefix = true;

  // Pin a searched axis, or leave it zero to search it.  Pinning is what a
  // measurement sweep does; it is not a way to ask for a bigger table.
  unsigned top_digit = 0;       // D in {1, 2, 4, 8}, at most B
  unsigned prefix_flushes = 0;  // r0 in {2, 4, 8}
  // `a`, the number of B/2 levels under the half-fanout prefix; 0 searches
  // [1, log2 B].  Refused where the prefix does not apply.
  unsigned half_prefix_levels = 0;
  // THE BOTTOM-FANOUT SEARCH, where the prefix does not apply: b_1, the
  // fanout of the SMALLEST level; 0 searches {2, 4, ..., B}.  Every level
  // above it keeps B.  One dimension is enough: `U_L = 2 r0 s prod(b)`
  // already reaches every power of two at or above `4s`, so a wider ladder
  // adds spellings rather than geometries -- what `b_1` adds is the ability
  // to reach one of them without raising `r0`.  Refused under the prefix.
  unsigned bottom_fanout = 0;

  // THE MEMORY-OVERHEAD FLOOR on an unpinned `D`, and 0 for the default,
  // `B/2 + 1` (`LevelArenaMinTopDigit`).  The search runs over the binary
  // digits (LevelArenaGeometry::IsTopDigit) from here to `B`: only a binary
  // top has a certified preparation, and the geometry refuses a top wider
  // than the fanout, so the ceiling is `B` itself and
  // the default floor leaves `D = B` alone.  Main buckets per unit of top is
  // `2 + (3B-1)/((B-1) D)` -- `2 + 3.29/D` at `B = 8` -- so the whole spread
  // is on the small-`D` side, and minimising bytes at a fixed capacity IS
  // minimising `U_L`, which IS maximising `D`: every `D <= B/2` has a
  // `2D <= B` twin at half the `U_L`.  Below the smallest `D = B`
  // geometry's capacity, `64 s r0 B` entries, `U_L` is at its own floor and a smaller top is the only way to stop
  // overshooting, so a caller that wants a tiny map (a position map, a
  // fixture) lowers this to 1 and is told, by this field, that it did.
  // Pinning `top_digit` below it is a contradiction and is refused rather
  // than silently resolved either way.
  unsigned min_top_digit = 0;

  // HOW MANY BYTES THE SELECTION MAY SPEND TO RAISE `r0`, as a fraction of
  // the smallest buffer bill.  See the header: a longer prefix buys a larger
  // level-1 carry and more fanout-B/2 levels, neither of which is a byte, and
  // the bill's own preference between two `r0` values is in the fifth
  // decimal place.  0 restores a pure byte objective, which is what a fixture
  // comparing against an enumeration of bills wants.
  double byte_slack = 0.01;

  // A bound on the search, not on the engine.  L is a count of hashed levels;
  // the arithmetic overflows long before this at any real entry width.
  unsigned max_levels = 40;
};

// The chosen geometry, everything derived from it, and what it costs.
struct LevelArenaCapacityChoice {
  LevelArenaGeometry::Params geometry;
  Layout layout;
  // The ROUNDED capacity, 32T entries: what the engine will actually hold,
  // which is at least the request and usually more.
  uint64_t capacity = 0;
  LevelArenaByteBill bill;
  // How many feasible geometries were compared, for a caller that wants to
  // know the search was not empty by accident.
  size_t candidates = 0;
  // The near/far boundary of the request, clamped into the chosen geometry's
  // level range.  0 when there is none.  It is what the engine should
  // be built with; it does not change the bill, which counts groups.
  unsigned resolved_near_max_level = 0;
  // A cap on the rebuild thread budget that divides this geometry, 0 for
  // none.  The ladder never sets it: the public map's budget path does, where
  // no geometry agreed with the whole budget's division (PlanArenaGeometry).
  unsigned rebuild_threads_cap = 0;
  // The ROUNDED capacity over the request.  1.0 is an exact fit and anything
  // above it is overshoot the caller is paying for -- which is how a request
  // below the `min_top_digit` floor's reach announces itself, since there the
  // floor cannot be met without a bigger top (see `min_top_digit`).
  double capacity_ratio = 0.0;
  // Whether the geometry is the half-fanout prefix's, or the bottom-fanout
  // search's (below B = 8, with the prefix off, or where it stepped aside).
  bool half_fanout_prefix = false;
};

// The floor the ladder searches `D` from: the request's own, or `B/2 + 1` when
// it left the field 0.  One spelling, because the ladder and the public map's
// pin handling both need it.
inline unsigned LevelArenaMinTopDigit(const LevelArenaCapacityRequest& request) {
  return request.min_top_digit != 0 ? request.min_top_digit
                                    : request.branching / 2 + 1;
}

// Whether the ladder below the top is the half-fanout prefix (see
// `half_fanout_prefix`): asked for, and B/2 at least 4.
inline bool UsesHalfFanoutPrefix(const LevelArenaCapacityRequest& request) {
  return request.half_fanout_prefix && request.branching >= 8;
}

// The fanouts of levels 1..L-1 of one candidate: `half_levels` levels of
// B/2 under B, or B everywhere but a bottom fanout of `bottom`.  One
// spelling, so that the ladder and a fixture enumerating its candidates
// state the same ladders.
inline std::vector<unsigned> HalfPrefixFanouts(unsigned branching,
                                               unsigned levels,
                                               unsigned half_levels) {
  std::vector<unsigned> fanouts(levels - 1, branching);
  for (unsigned l = 0; l < half_levels && l < fanouts.size(); ++l) {
    fanouts[l] = branching / 2;
  }
  return fanouts;
}

inline std::vector<unsigned> BottomFanouts(unsigned branching, unsigned levels,
                                           unsigned bottom) {
  std::vector<unsigned> fanouts(levels - 1, branching);
  fanouts[0] = bottom;
  return fanouts;
}

// Entry capacity of a geometry: 32T, the top's T buckets at the load-0.5
// occupancy of 32 entries per 64-entry bucket.  A free function because the
// ladder needs it for candidates it has not built.
//
// THIS OVERLOAD IS THE UNIFORM-FANOUT SPECIAL CASE and is kept for callers
// that state a geometry as four scalars (the fixtures' independent
// enumeration, the model script's comparisons).  The `Params` overload below
// is the general one and is what the ladder itself calls; a per-level ladder
// passed through here as its maximum `B` would be priced at a capacity it
// does not have.
inline uint64_t LevelArenaCapacityOf(unsigned branching, unsigned levels,
                                     unsigned top_digit,
                                     unsigned prefix_flushes,
                                     size_t stash_buckets) {
  // 32 T = 32 D U_L = 32 D Z B^(L-1) and Z = 2 r0 s, so this is
  // (64 s) r0 D B^(L-1): the insertion unit times everything above it.
  const uint64_t unit = CheckedMul(kBucketCapacity, stash_buckets, "64 s");
  return CheckedMul(
      CheckedMul(CheckedMul(unit, prefix_flushes, "64 s r0"), top_digit,
                 "64 s r0 D"),
      CheckedPow(branching, levels - 1, "B^(L-1)"), "capacity");
}

// The general form: 32 D Z prod(b_l), over whatever fanout ladder `params`
// states.  An empty `level_fanouts` is the uniform ladder, exactly as the
// geometry reads it.
inline uint64_t LevelArenaCapacityOf(const LevelArenaGeometry::Params& params) {
  const uint64_t unit = CheckedMul(kBucketCapacity, params.stash_buckets,
                                   "64 s");
  uint64_t product = 1;
  for (unsigned l = 1; l < params.levels; ++l) {
    const unsigned fanout = params.level_fanouts.empty()
                                ? params.branching
                                : params.level_fanouts[l - 1];
    product = CheckedMul(product, fanout, "fanout product");
  }
  return CheckedMul(
      CheckedMul(CheckedMul(unit, params.prefix_flushes, "64 s r0"),
                 params.top_digit, "64 s r0 D"),
      product, "capacity");
}

// The bottom fanout of a candidate, with the empty ladder read as uniform B --
// one spelling, because the ladder, the tie break and the reporting all need
// it and three readings of an optional vector is three places to disagree.
inline unsigned BottomFanoutOf(const LevelArenaGeometry::Params& params) {
  return params.level_fanouts.empty() ? params.branching
                                      : params.level_fanouts.front();
}

// The tie break, in one place so that it is a rule rather than the order the
// loops happen to run in: among candidates the selection has already found
// equal, prefer the smaller L -- a shorter cascade for the same storage --
// then the smaller r0, then the smaller D, then the fanout ladder that is
// smaller level by level from the bottom (the smaller b_1, or the longer B/2
// prefix).  No two candidates agree on all of these, because (L, r0, D, the
// ladder) is what a candidate IS.
//
// `r0` sits here as well as in the selection below, and that is not a
// duplicate: the selection decides `r0` against a byte budget, and this
// decides it when two candidates are otherwise indistinguishable.
inline bool PrefersCapacityCandidate(const LevelArenaGeometry::Params& a,
                                     const LevelArenaGeometry::Params& b) {
  if (a.levels != b.levels) return a.levels < b.levels;
  if (a.prefix_flushes != b.prefix_flushes) {
    return a.prefix_flushes < b.prefix_flushes;
  }
  if (a.top_digit != b.top_digit) return a.top_digit < b.top_digit;
  for (unsigned l = 1; l < a.levels; ++l) {
    const unsigned fa =
        a.level_fanouts.empty() ? a.branching : a.level_fanouts[l - 1];
    const unsigned fb =
        b.level_fanouts.empty() ? b.branching : b.level_fanouts[l - 1];
    if (fa != fb) return fa < fb;
  }
  return false;
}

// The rule the selection applies WITHIN the byte budget: the largest `r0`
// (the header says why), then the smallest bill, then the tie break.  Split
// out of the ladder so that a fixture enumerating candidates for itself can
// apply the same rule rather than reimplementing it and agreeing by luck.
inline bool PrefersLadderCandidate(const LevelArenaCapacityChoice& a,
                                   const LevelArenaCapacityChoice& b) {
  if (a.geometry.prefix_flushes != b.geometry.prefix_flushes) {
    return a.geometry.prefix_flushes > b.geometry.prefix_flushes;
  }
  if (a.bill.requested() != b.bill.requested()) {
    return a.bill.requested() < b.bill.requested();
  }
  return PrefersCapacityCandidate(a.geometry, b.geometry);
}

// The byte budget: the smallest bill plus `byte_slack` of it, saturating
// rather than wrapping, because `min_bytes * slack` is a product of a size
// and a caller's double and a negative or enormous slack must not become a
// budget that admits everything.  Above 2^53 bytes the double rounding can
// put it below `min_bytes`; the selection refuses that case.
inline size_t LevelArenaByteBudget(size_t min_bytes, double slack) {
  if (!(slack > 0.0)) return min_bytes;  // also catches NaN
  const double budget = static_cast<double>(min_bytes) * (1.0 + slack);
  if (budget >= static_cast<double>(std::numeric_limits<size_t>::max())) {
    return std::numeric_limits<size_t>::max();
  }
  return static_cast<size_t>(budget);
}

// THE LADDER.  Enumerates (L, r0, D, a or b_1) at the caller's B and s, keeps what
// covers the request, prices each one with the buffer bill and selects by
// the two stages above.
//
// THE CAPACITY CONTRACT counts the LIVE key set, and is worth stating because
// a miss and an erase each insert a TOMBSTONE -- a real entry, since a second
// read of a key that left nothing behind would repeat the first one's probe
// positions.  Neither adds a term at the top: a tombstone for a held key is
// deduplicated against it by the carry that consumes both, and one whose probe
// found no older copy is marked unshadowed and omitted by the top sweep before
// it occupies an output slot (DESIGN.md, "Online security and capacity").
// Overflow surfaces as a declared failure from a rebuild bucket that did not
// fit, never as a wrong answer.
//
// SELECTION, in two stages because the two things being minimised are in
// different units.  Bytes first: `byte_slack` of the smallest buffer bill
// is the whole budget, and at `byte_slack = 0` this is exactly "the smallest
// bill wins".  Then, within that budget, the largest `r0` -- the header says
// why -- then the smallest bill, then the stated tie break.  Every stage is
// deterministic rather than merely stable, and the tie break is total, so two
// runs on two hosts return the same geometry.
inline LevelArenaCapacityChoice PlanLevelArenaCapacity(
    const LevelArenaCapacityRequest& request) {
  if (request.entries == 0) {
    throw std::invalid_argument("level arena: a capacity of zero");
  }
  if (request.synchronous &&
      (request.owner_threads != 0 || request.lanes.lanes > 1)) {
    throw std::invalid_argument(
        "level arena: the synchronous mode takes no owner threads or lanes");
  }
  // D <= B and a binary D are the geometry's rules; they are checked here as
  // well so that a pin or a floor that breaks one is refused by name rather
  // than leaving no candidate.
  const unsigned max_top_digit =
      std::min(request.branching, LevelArenaGeometry::kMaxTopDigit);
  if (request.top_digit > max_top_digit ||
      (request.top_digit != 0 &&
       !LevelArenaGeometry::IsTopDigit(request.top_digit))) {
    throw std::invalid_argument(
        "level arena: D must be 0 (search it) or 1, 2, 4 or 8, at most B -- "
        "only a binary top has a certified preparation");
  }
  const unsigned min_top_digit = LevelArenaMinTopDigit(request);
  if (min_top_digit > max_top_digit) {
    throw std::invalid_argument("level arena: min_top_digit must be in [1, B]");
  }
  if (request.top_digit != 0 && request.top_digit < min_top_digit) {
    throw std::invalid_argument(
        "level arena: pinned top digit is below min_top_digit");
  }
  const unsigned digit_lo =
      request.top_digit != 0 ? request.top_digit : min_top_digit;
  const unsigned digit_hi =
      request.top_digit != 0 ? request.top_digit : max_top_digit;
  const unsigned flush_candidates[] = {2u, 4u, 8u};
  if (request.bottom_fanout != 0 &&
      (request.bottom_fanout < 2 || request.bottom_fanout > request.branching ||
       !IsPowerOfTwo(request.bottom_fanout))) {
    throw std::invalid_argument(
        "level arena: bottom_fanout must be a power of two in [2, B]");
  }
  // The two ladders are alternatives, so each one's pin is refused under the
  // other rather than silently ignored.
  const bool half_prefix = UsesHalfFanoutPrefix(request);
  const unsigned max_half_levels =
      half_prefix ? Log2Exact(request.branching) : 0;
  if (half_prefix && request.bottom_fanout != 0) {
    throw std::invalid_argument(
        "level arena: bottom_fanout pins the bottom-fanout ladder; clear "
        "half_fanout_prefix to use it");
  }
  if (request.half_prefix_levels != 0 &&
      (!half_prefix || request.half_prefix_levels > max_half_levels)) {
    throw std::invalid_argument(
        "level arena: half_prefix_levels must be in [1, log2 B], under the "
        "half-fanout prefix (B = 8)");
  }
  // One candidate ladder per value of the searched ladder axis: `a` under the
  // prefix, `b_1` otherwise.
  std::vector<unsigned> ladder_axis;
  if (half_prefix) {
    for (unsigned a = 1; a <= max_half_levels; ++a) {
      if (request.half_prefix_levels == 0 || a == request.half_prefix_levels) {
        ladder_axis.push_back(a);
      }
    }
  } else {
    for (unsigned bottom = 2; bottom <= request.branching; bottom *= 2) {
      if (request.bottom_fanout == 0 || bottom == request.bottom_fanout) {
        ladder_axis.push_back(bottom);
      }
    }
  }

  // A THREAD WITH NO LEVEL WOULD PARK FOREVER, so a hierarchy shorter than
  // the owner-thread count is not a candidate.  Stated here rather than left
  // to the engine's refusal, because "this request needs at least
  // as many levels as it has threads" is a property of the search and not an
  // accident of which candidate happened to throw first.
  const unsigned lowest_levels = std::max(2u, request.owner_threads);
  // Every feasible candidate, priced.  Collected rather than folded, because
  // the selection below needs the global byte minimum before it can say which
  // candidates are inside the budget, and a fold cannot know that yet.  The
  // count is at most a few hundred and this runs once, at construction.
  std::vector<LevelArenaCapacityChoice> feasible;
  for (unsigned levels = lowest_levels; levels <= request.max_levels;
       ++levels) {
    for (unsigned flushes : flush_candidates) {
      if (request.prefix_flushes != 0 && flushes != request.prefix_flushes) {
        continue;
      }
      for (unsigned digit = digit_lo; digit <= digit_hi; ++digit) {
        if (!LevelArenaGeometry::IsTopDigit(digit)) continue;
        for (unsigned axis : ladder_axis) {
          // A prefix of `a` B/2 levels needs `a` levels below the top.
          if (half_prefix && axis > levels - 1) continue;
          LevelArenaGeometry::Params params;
          params.branching = request.branching;
          params.bank_first = request.bank_first;
          params.levels = levels;
          params.top_digit = digit;
          params.prefix_flushes = flushes;
          params.stash_buckets = request.stash_buckets;
          params.dense_prefixes = request.dense_prefixes;
          params.tier_buckets = request.tier_buckets;
          params.level_fanouts =
              half_prefix ? HalfPrefixFanouts(request.branching, levels, axis)
                          : BottomFanouts(request.branching, levels, axis);

          // EVERY REJECTION BELOW IS A THROW, and that is the checked
          // arithmetic doing its job rather than a shape this loop failed to
          // anticipate: the geometry, the stash certificate, the layout and
          // the bill each refuse what they cannot represent, and past some L
          // every one of them overflows.  A candidate that cannot be built is
          // simply not a candidate, so the loop moves on; what it must not do
          // is stop, because a taller L that overflows says nothing about a
          // shorter one that does not.
          uint64_t capacity = 0;
          try {
            capacity = LevelArenaCapacityOf(params);
          } catch (const std::exception&) {
            continue;
          }
          if (capacity < request.entries) continue;
          LevelArenaCapacityChoice candidate;
          candidate.geometry = params;
          candidate.capacity = capacity;
          candidate.capacity_ratio = static_cast<double>(capacity) /
                                     static_cast<double>(request.entries);
          candidate.resolved_near_max_level =
              request.near_max_level == 0
                  ? 0u
                  : std::min(request.near_max_level, params.levels);
          try {
            params = ResolveLevelArenaTierGeometry(params, request.max_accesses);
            candidate.geometry = params;
            const LevelArenaGeometry geometry(params);
            candidate.layout = LevelArenaStoredLayout(
                request.key_bytes, request.value_bytes, geometry);
            if (!RoutingDigitFits(candidate.layout)) continue;
            const LevelArenaStashSizing sizing(geometry, request.max_accesses);
            candidate.bill = LevelArenaEngineBytes(
                geometry, candidate.layout, sizing,
                std::max(1u, request.owner_threads),
                request.batch_participants, request.batch_bucket_scan,
                request.lanes, request.synchronous);
          } catch (const std::exception&) {
            continue;
          }
          feasible.push_back(std::move(candidate));
        }
      }
    }
  }
  if (feasible.empty()) {
    // The request's own constraints that can leave no candidate, named so
    // the refusal does not read as a capacity problem alone.
    std::string constraints;
    if (lowest_levels > 2) {
      constraints += ", with at least " + std::to_string(lowest_levels) +
                     " levels (one per owner thread)";
    }
    if (request.tier_buckets != 0) {
      constraints += ", with tier_buckets pinned at " +
                     std::to_string(request.tier_buckets) +
                     " (a pin below a geometry's lifetime occupancy "
                     "requirement rules that geometry out)";
    }
    throw std::length_error(
        "level arena: no supported geometry holds " +
        std::to_string(request.entries) + " entries at B = " +
        std::to_string(request.branching) + ", s = " +
        std::to_string(request.stash_buckets) + constraints);
  }
  // STAGE 1: the byte budget, from the global minimum.
  size_t min_bytes = std::numeric_limits<size_t>::max();
  for (const LevelArenaCapacityChoice& c : feasible) {
    min_bytes = std::min(min_bytes, c.bill.requested());
  }
  const size_t budget = LevelArenaByteBudget(min_bytes, request.byte_slack);
  // STAGE 2: within it, the largest r0, then the smallest bill, then the
  // stated tie break.
  const LevelArenaCapacityChoice* winner = nullptr;
  for (const LevelArenaCapacityChoice& c : feasible) {
    if (c.bill.requested() > budget) continue;
    if (winner == nullptr || PrefersLadderCandidate(c, *winner)) winner = &c;
  }
  // The cheapest candidate passes unless the budget rounded below it: a bill
  // above 2^53 bytes converts to double inexactly, and a tiny positive
  // `byte_slack` adds nothing to it.
  if (winner == nullptr) {
    throw std::length_error(
        "level arena: the byte budget rounds below the smallest bill (" +
        std::to_string(min_bytes) + " bytes), so no candidate fits it");
  }
  LevelArenaCapacityChoice best = *winner;
  const size_t candidates = feasible.size();
  best.candidates = candidates;
  best.half_fanout_prefix = half_prefix;
  // THE PREFIX NEVER COSTS CAPACITY.  Its smallest geometry has twice the
  // bottom-fanout ladder's U_L, so a small map would round up to twice the
  // capacity; where the bottom-fanout ladder rounds to a smaller capacity it
  // is used instead.  Nothing else moves the choice between the two ladders:
  // `r0` is chosen within the prefix's own candidates, by the same largest-r0
  // rule, so the prefix is the ladder wherever it fits.  A pinned prefix
  // length is the caller's answer and is kept.
  if (half_prefix && request.half_prefix_levels == 0) {
    LevelArenaCapacityRequest bottom_request = request;
    bottom_request.half_fanout_prefix = false;
    const LevelArenaCapacityChoice bottom =
        PlanLevelArenaCapacity(bottom_request);
    if (bottom.capacity < best.capacity) return bottom;
  }
  return best;
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
