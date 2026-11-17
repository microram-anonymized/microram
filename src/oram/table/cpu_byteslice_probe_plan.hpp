#pragma once

// The probe plan: the immutable list of tables one access probes, and the
// invariants that make probing it safe.
//
// An access snapshots exactly one plan and probes exactly that one.  A
// published plan is never mutated, and old plans are never merged into new
// ones.  In the level-arena engine a rebuild is a merge job whose publication
// removes its sources (the older partial A and the incoming carry B, or at
// level one the consumed dense prefix) and adds its output in the SAME swap
// (src/oram/levelarena/cpu_byteslice_level_arena_publication.hpp; carries,
// partials and inboxes are defined in src/oram/levelarena/DESIGN.md).  A
// retired plan, and the slabs it named, are freed only after the reader epoch
// that could have snapshotted them has passed.  All of that exists because a
// background worker deletes the assumption a synchronous rebuild could make --
// that publication happens between accesses and is therefore instantaneous.
//
// WINDOWS, NOT LEVELS, ORDER THE CASCADE.  Every live table owns a half-open
// window of the insertion timeline; the live windows form a laminar family; the
// probe order is window_end descending, then tier ascending.  Neither level
// number nor table size can stand in for the window: at fanout B > 2 a level's
// partial P_j owns the union of the j carries it has absorbed, two tables of one
// size can be live at one level (an adopted first carry and the next carry
// waiting in the level's other inbox), and the dense prefixes, the carries
// waiting in inboxes and the partials they will join are not ordered by level.
// The window is assigned at every publication, and window order alone makes
// "the first table that has the key holds its freshest copy" true.
//
// DENSE VS HASHED.  A dense table -- the current online stash, and the frozen
// stashes waiting to be consumed -- is scanned in full on every access.  Its
// address is fixed, so it needs no routing nonce, issues no dummy probe, and
// leaks nothing positional.  A hashed table is probed at one key-derived
// bucket, or at an independent dummy one below the level where the key was
// found.
//
// THE FAMILY IS THE SECURITY BOUNDARY, not the table id.  One nonce family can
// span several successively published tables that share a hash, and the
// invariant that must hold is "at most one real probe per (nonce_family_id,
// key)" over the family's lifetime.  So the plan asserts at most one member per family, and
// the audit keys on (family, key) and keeps a family's state until its LAST
// member retires.

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"
#include "src/oram/table/cpu_byteslice_probe_addresses.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"

namespace microram {
namespace byteslice {

// One live, probeable table.  Immutable once published.
//
// `window_begin`/`window_end` are access-counter bounds of the half-open window
// of insertions this table owns.  The live tables' windows form a LAMINAR
// family over [0, next flush boundary) -- any two nested or disjoint, never
// crossing -- which is
// the invariant CheckWindowLaminar asserts and the reason the probe order needs
// no case analysis.
//
// `nonce_family_id` is the SECURITY BOUNDARY, not `table_id`.  One nonce can
// carry several table ids over time -- a carry and the table it becomes when
// a level adopts or installs it keep one hash (CanonicalFamily in
// src/oram/levelarena/cpu_byteslice_level_arena_family.hpp) -- and both
// nonce-reuse failures are invisible to
// anything keyed per table: two family members live at once are real-probed at
// congruent positions in one access with each table's own audit set still
// fresh, and a key real-probed once under one id and once under its successor
// repeats no table-local key.  So the plan asserts at most one member per family (the
// runtime check that no two live tables share a hash function) and the audit
// keys on (nonce_family_id, key) and keeps a family's state until its LAST
// member retires (the runtime check that no key is really probed twice under
// one hash function).
//
// The entry is in two layers.  TableShape is the PUBLIC, STORAGE-FREE part --
// window, identity, geometry -- and is what a reader may keep after the reader
// epoch it read under has closed: there is nothing in it to dereference.  It
// is the element type of ProbePlanSnapshot.  TableEntry adds the storage the
// cascade probes and the packed nonce words, and lives only inside a plan.
struct TableShape {
  uint64_t window_begin = 0;
  uint64_t window_end = 0;  // primary sort key, DESCENDING
  uint32_t tier = 0;        // 0 = main, 1 = second-tier residual; tiebreak
  TableKind kind = TableKind::kHashed;
  // Removal survives only in the current online stash.  Every other
  // table -- including a frozen stash, which is a rebuild source -- is
  // read-only under probing.
  bool removable = false;
  uint64_t table_id = 0;         // unique over the run; never reused
  uint64_t nonce_family_id = 0;  // 0 for a dense table, which has no nonce
  size_t num_buckets = 0;
  // The mixed-radix index.  A table of
  // m * 2^index_bits buckets with m = radix * 2^e folds the e into index_bits,
  // so `radix` is the ODD part alone and the bucket of a tag is
  //   (tag & LowMask(index_bits)) + (mod(tag >> index_bits, radix) << index_bits)
  // -- radix blocks of 2^index_bits buckets each.  radix == 1 is a
  // power-of-two table and ModSmallOdd(v, 1) == 0 makes that expression
  // bit-for-bit the plain power-of-two mask.  That is every table whose digit
  // j is a power of two -- every table of a fanout-2 level and every full
  // carry -- because every U_l is a power of two
  // (src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp).
  unsigned index_bits = 0;  // log2 of one block; 0 for a dense table
  unsigned radix = 1;       // odd part of the digit; 1 = power-of-two table
  // The raw REAL nonce.  The probe path reads only the packed words in
  // TableEntry; this pair is here for the nonce-structure assertions the
  // tests make (allocated-not-sampled, level field, seed reproducibility).
  // The raw dummy pair is not kept: it has no such reader, and would add 16
  // bytes per entry copied and sorted at every publication.
  uint64_t nonce_lo = 0, nonce_hi = 0;
};

// A table as the cascade probes it: its shape plus the storage it names.  The
// two pointers are live exactly as long as the plan holding the entry is
// reachable from a reader epoch, which is why they are NOT part of the shape:
// a copy that outlives its epoch (LevelArenaEngine::PlanSnapshot, a
// ProbePlanSnapshot) is made of shapes.
struct TableEntry : TableShape {
  uint8_t* data = nullptr;
  uint64_t* masks = nullptr;
  // PackAesCtrHighWord of the two nonces, so the probe path never repacks.
  uint64_t real_high = 0;
  uint64_t dummy_high = 0;
};

// Buckets of one cascade step BEYOND the first: zero for every hashed table
// (a hashed probe is one key-derived bucket by construction) and for every
// one-bucket dense table.  Wider insertion units, merged frozen runs and
// multi-bucket tiers are the run scan, selected by public geometry.
//
// SHARED BY BOTH ENGINES, and it has to be: the run scan's contract -- the
// buckets of a run are ordered oldest to newest, so the entry's answer is the
// LAST match in it -- is a property of how the plan was built, and two
// spellings of "how long is this run" are two chances to disagree with it.
inline size_t DenseExtraBuckets(const TableEntry& t) {
  return t.kind == TableKind::kDense && t.num_buckets > 1 ? t.num_buckets - 1
                                                          : 0;
}

// The tombstone flags of the entry a cascade step just extracted -- the
// tombstone bit and its unshadowed qualifier, both as they sit in the meta
// byte -- latched under the same gate the value blend uses.  The meta byte
// rides at the end of the value scratch (`value_bytes` is the USER width, so
// the meta byte is one past it), and the extract's miss contract is
// UNSPECIFIED bytes rather than zeros -- which is why this is gated on `take`
// and never read otherwise.
inline void TakeTombstoneFlags(const uint8_t* scratch, size_t value_bytes,
                               uint64_t take, uint64_t* taken_flags) {
  const uint64_t flags_here = static_cast<uint64_t>(
      scratch[value_bytes] & (kMetaErased | kMetaUnshadowed));
  core::CMOV8(take != 0, *taken_flags, flags_here);
}

// The probe plan: IMMUTABLE, published by a single atomic pointer store.
// Sorted by window_end DESCENDING, tier ASCENDING: windows form a laminar
// family and a window's tiers are an ordered list, main before residual.
// `hashed` and `dense` list the indices of tables[] by kind so the
// address-resolution pass can batch the AES without a branch per table; both
// are public functions of the schedule.
//
// `addressing` is PUBLICATION-TIME ADDRESSING, filled by
// BuildProbePlanAddressing and read by the per-access pass alone.  Every field
// is a public function of the plan; none of it depends on a key.  It is the
// shared ProbeAddressing both hierarchies resolve their candidates from
// (cpu_byteslice_probe_addresses.hpp).
struct ProbePlan {
  // `tables` is ONE array with two owners.  The first `prefix_slots` entries
  // are reserved for the DENSE PREFIX -- the current online stash and the
  // frozen stashes (completed dense prefixes) level one has not consumed yet
  // -- and are written by the REQUEST
  // thread, inside its reader epoch, from ring state only it changes; every
  // entry from `prefix_slots` on is the worker's, written before publication
  // and immutable after.  The two never touch each other's half.
  //
  // Why the split: a flush changes nothing but the prefix.  Every hashed table
  // and tier is older than every unconsumed frozen stash (the prefix ring
  // holds exactly the records level one has not consumed, and the merge
  // output that consumes a prefix replaces it in the same publication), so
  // the sorted plan is always [current][frozen, newest
  // first][hashed tables and tiers] and the suffix is byte-identical before
  // and after a flush.  The request thread therefore rewrites its few prefix
  // entries at the next access instead of rebuilding, sorting, validating and
  // publishing a whole plan under the publication lock at every flush.
  //
  // The prefix is filled from the back: entries [first_live, prefix_slots) are
  // live and the cascade starts at `first_live`; entries below it are
  // placeholders (dense, zero buckets) no reader dereferences.  How many are
  // live follows from the access counter and `heads_consumed`, the number of
  // frozen stashes whose level-one merge output has been published -- the
  // plan that adds that output also raises `heads_consumed` past its stash,
  // which is what keeps "a merge output replaces its frozen stash in one
  // swap" true with two writers.
  std::vector<TableEntry> tables;
  // Indices into `tables` by kind, the worker's half only (absolute positions,
  // so the address pass and the cascade index one array).
  std::vector<uint32_t> hashed;
  std::vector<uint32_t> dense;
  size_t prefix_slots = 0;
  uint64_t heads_consumed = 0;
  // Request-thread-owned, set by FillDensePrefix: where the live prefix
  // starts and how many buckets it probes.
  size_t first_live = 0;
  size_t prefix_buckets = 0;
  // How many of `dense` are SMALL LEVEL tables: a level, or a carry temporary
  // of one, published as a dense run rather than as a hashed table.  The
  // level arena publishes no such tables, so it sets this to zero; the field
  // stays in the shared plan format.  The rest of `dense` is the stash ring
  // and the second tiers.  Counted at publication because afterwards nothing
  // can tell the three apart -- a small level, a frozen stash and a tier are
  // all fixed-address, nonce-free, fully scanned tables, which is exactly the
  // property that makes a dense prefix cost nothing positional.
  size_t small_dense = 0;
  uint64_t epoch = 0;

  ProbeAddressing addressing;
  size_t probe_buckets = 0;

  void ClearAddressing() {
    addressing.Clear();
    probe_buckets = 0;
  }
};

// A DENSE TABLE'S CANDIDATE PAIR IS THE TABLE ITSELF, fixed for the life of
// the publication, so it is written once per plan epoch rather than once per
// access.  `cached_epoch` is the caller's memo of which plan it last wrote;
// the probe scratch has one owner, so none of this is atomic.
//
// The dense PREFIX is deliberately not in `plan.dense`: its entries move with
// every flush and the request thread writes them itself.
//
// The epoch is unique per publication and a recycled plan object still gets a
// new one, which is what makes the memo safe against a pool that hands the
// same address back.
inline void ResolveDenseProbeAddresses(const ProbePlan& plan,
                                       uint64_t* cached_epoch,
                                       ProbeScratch& out) {
  if (*cached_epoch == plan.epoch) return;
  for (uint32_t i : plan.dense) {
    const TableEntry& t = plan.tables[i];
    out.bucket[2 * i] = t.data;
    out.bucket[2 * i + 1] = t.data;
    out.mask[2 * i] = t.masks;
    out.mask[2 * i + 1] = t.masks;
  }
  *cached_epoch = plan.epoch;
}

// Which tables a PlanSnapshot counts.  A dense table is a few buckets; a
// hashed table is every mask word of a level -- megabytes at the production
// point -- all read inside the reader epoch, holding up reclamation meanwhile.
enum class OccupancyScope { kDense, kAll };

// What a reader outside the cascade gets to keep: the probed list as shapes,
// a live-entry count per table, and the plan's public totals.  No storage
// pointer anywhere in it, by type rather than by comment -- a ProbePlan copy
// with its pointers still in it left every caller to remember that they died
// with the epoch, and one did not.  Built by SnapshotOf from a live plan: the prefix
// placeholders are dropped, the index lists rebuilt over the trimmed list, and
// the request thread's prefix counts folded into the totals.
struct ProbePlanSnapshot {
  // `occupancy[i]` when tables[i] was outside the requested scope.
  static constexpr size_t kNotCounted = ~size_t{0};
  std::vector<TableShape> tables;  // probe order: newest window first
  // Live entries in tables[i] -- the popcount of its mask words -- taken
  // while the reader epoch still held the table's storage live.  A function
  // of the secret keys, so instrumentation for benchmarks and tests, never an
  // input to the schedule.
  std::vector<size_t> occupancy;
  std::vector<uint32_t> hashed;  // indices into `tables` by kind
  std::vector<uint32_t> dense;
  size_t small_dense = 0;
  uint64_t epoch = 0;
  uint64_t heads_consumed = 0;
  size_t probe_buckets = 0;
};

// THE SNAPSHOT: a live plan's probed half as shapes, with no storage pointer
// in it, so it stays valid after the reader epoch closes.  The prefix
// placeholders are dropped, the index lists rebuilt over the trimmed list and
// the plan's public totals folded in.
//
// `scope` is not a convenience.  Counting a hashed table's occupancy reads
// every mask word of a level -- megabytes at the production point -- and it
// happens INSIDE the reader epoch, holding up every retirement meanwhile.
// kDense leaves those entries at kNotCounted instead.  The caller supplies
// the request thread's own prefix counts, which are not in the plan.
inline ProbePlanSnapshot SnapshotOf(const ProbePlan& p, OccupancyScope scope) {
  ProbePlanSnapshot out;
  const size_t n = p.tables.size() - p.first_live;
  out.tables.reserve(n);
  out.occupancy.reserve(n);
  for (size_t i = p.first_live; i < p.tables.size(); ++i) {
    const TableEntry& t = p.tables[i];
    // The shape alone: the push slices the entry to its base, which is the
    // whole point of the split -- nothing past this line can be dereferenced.
    out.tables.push_back(t);
    (t.kind == TableKind::kHashed ? out.hashed : out.dense)
        .push_back(static_cast<uint32_t>(out.tables.size() - 1));
    size_t live = ProbePlanSnapshot::kNotCounted;
    if (t.kind != TableKind::kHashed || scope == OccupancyScope::kAll) {
      live = 0;
      for (size_t b = 0; b < t.num_buckets; ++b) live += Popcount64(t.masks[b]);
    }
    out.occupancy.push_back(live);
  }
  out.small_dense = p.small_dense;
  out.epoch = p.epoch;
  out.heads_consumed = p.heads_consumed;
  out.probe_buckets = p.probe_buckets + p.prefix_buckets;
  return out;
}

// Fills the publication-time addressing block from `tables` and `hashed`.
// Call after `hashed`/`dense` are final and before the plan is published.
//
// The dummy counter of hashed table i is `dummy_base + i` --
// the cascade re-derives it from the table's own cascade position, so the
// offset handed to AddHashed is that position.
inline void BuildProbePlanAddressing(ProbePlan& plan) {
  plan.ClearAddressing();
  for (const TableEntry& t : plan.tables) {
    if (t.kind == TableKind::kDense) {
      plan.probe_buckets += t.num_buckets;
    } else {
      ++plan.probe_buckets;
    }
  }
  plan.addressing.Begin(plan.hashed.size());
  for (const uint32_t i : plan.hashed) {
    const TableEntry& t = plan.tables[i];
    plan.addressing.AddHashed(i, t.data, t.masks, t.index_bits, t.radix,
                              t.real_high, t.dummy_high, i);
  }
}

// The laminarity of the live windows, as a predicate on a plan alone, so a test
// can exhibit a violating plan without having to provoke one.
//
// In probe order (window_end descending, tier ascending), tiers of one window
// must be consecutive, and every pair of distinct windows must be NESTED or
// DISJOINT.  Checking adjacent windows alone misses a crossing hidden behind
// a smaller nested window.  A pair that OVERLAPS without nesting -- one window
// starting inside another but not covering it -- is what
// makes the freshness argument fail: there is then no order in which "the first
// table that has the key has the freshest copy" is true.
//
// Where the live windows happen to tile the timeline the condition holds
// trivially; it is the weaker property the freshness argument needs.
//
// `first` is where the checked range starts: 0 for a hand-built or trimmed
// plan, `prefix_slots` when the worker validates the half it wrote before
// publication, `first_live` when the request thread checks the composed view.
// An empty range behind a reserved prefix is legal (no hashed table yet); an
// empty plan is not.
//
// Over either plan type: the live ProbePlan (the worker checks the half it
// wrote before publication, the request thread the composed view) or a
// ProbePlanSnapshot (the tests, on a copy).  Both are shapes to this.
template <class Plan>
bool PlanWindowsLaminar(const Plan& plan, size_t first = 0) {
  const size_t n = plan.tables.size();
  if (first > n) return false;
  if (first == n) return first > 0;
  if (plan.tables[first].tier != 0) return false;
  if (plan.tables.back().window_begin != 0) return false;
  for (size_t i = first; i < n; ++i) {
    const TableShape& older = plan.tables[i];
    if (older.window_end <= older.window_begin) return false;
    if (i == first) continue;
    const TableShape& newer = plan.tables[i - 1];
    if (newer.window_end == older.window_end) {
      // Two tiers of one window: same interval, main first.
      if (newer.window_begin != older.window_begin) return false;
      if (newer.tier >= older.tier) return false;
      continue;
    }
    if (newer.window_end < older.window_end) return false;
    // Every window group starts with its main table.  A tier here means its
    // main is missing, whether the window is nested or disjoint; the found
    // gate relies on probing that main first (see MakeTierEntry).
    if (older.tier != 0) return false;
  }

  // Sweep from newer ends to older ends.  The active windows are nested, so
  // their starts are nondecreasing.  Pop windows wholly to the right of the
  // next one; the innermost remaining window must contain it.  Each distinct
  // window is pushed and popped once, and tiers need no additional work.
  uint64_t starts[2 * 64];
  size_t depth = 0;
  for (size_t i = first; i < n; ++i) {
    const TableShape& older = plan.tables[i];
    if (older.tier != 0) continue;
    while (depth != 0 && starts[depth - 1] >= older.window_end) --depth;
    if (depth != 0 && starts[depth - 1] > older.window_begin) return false;
    if (depth == sizeof(starts) / sizeof(starts[0])) {
      // Keep publication allocation-free without imposing a depth limit on
      // hand-built plans: unusually deep nesting uses the exhaustive check.
      for (size_t a = first; a < n; ++a) {
        const TableShape& right = plan.tables[a];
        if (right.tier != 0) continue;
        for (size_t b = a + 1; b < n; ++b) {
          const TableShape& left = plan.tables[b];
          if (left.tier != 0) continue;
          if (right.window_begin > left.window_begin &&
              right.window_begin < left.window_end) return false;
        }
      }
      return true;
    }
    starts[depth++] = older.window_begin;
  }
  return true;
}

// The pair loop skips a table with no family, so it walks only the hashed
// ones -- half the plan at load 0.5, where every hashed table carries a dense
// second tier.  Collecting them first makes that skip free rather than a
// quadratic number of loads on the request thread's publication path.
template <class Plan>
bool PlanHasAtMostOneMemberPerFamily(const Plan& plan) {
  uint64_t families[2 * 64];
  size_t n = 0;
  for (const TableShape& t : plan.tables) {
    if (t.nonce_family_id == 0) continue;  // dense tables carry no nonce
    // More live families than any supported geometry can produce: fall back
    // to the direct O(n^2) walk rather than silently checking a prefix.
    if (n == sizeof(families) / sizeof(families[0])) {
      for (size_t i = 0; i < plan.tables.size(); ++i) {
        const uint64_t f = plan.tables[i].nonce_family_id;
        if (f == 0) continue;
        for (size_t j = 0; j < i; ++j) {
          if (plan.tables[j].nonce_family_id == f) return false;
        }
      }
      return true;
    }
    for (size_t j = 0; j < n; ++j) {
      if (families[j] == t.nonce_family_id) return false;
    }
    families[n++] = t.nonce_family_id;
  }
  return true;
}

}  // namespace byteslice
}  // namespace microram
