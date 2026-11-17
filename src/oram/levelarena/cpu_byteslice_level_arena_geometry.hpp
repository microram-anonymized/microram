#pragma once

// The geometry of the per-level arena hierarchy: what the levels are, how big
// every physical buffer is, and which buffer a given carry is written into.
// The design is src/oram/levelarena/DESIGN.md ("Geometry and storage bound",
// "Carries and preparation"); analysis/level_arena_model.py checks the
// storage closed forms against slot enumeration.
//
// THE SHAPE.  Every hashed level below the top has a fanout b_l and builds,
// over b_l incoming carries, a table that grows 1, 2, ... b_l times the
// incoming carry size U_l.  The first b_l-1 of those PARTIAL tables live in
// the odd bank and the outgoing inbox; the b_l-th -- the FULL table, which is
// exactly the next level's incoming carry size -- is built directly into a
// slot leased from the next level up.  That is the whole idea: a producer
// never needs a full-size buffer of its own, because its output is born
// inside the arena of the level that will consume it.
//
// THE FANOUT IS PER LEVEL and `B` is its MAXIMUM.  `Params::level_fanouts`
// states the ladder; an empty one means "B everywhere", the uniform
// geometry.  The capacity ladder varies only the
// SMALLEST level's fanout, because U_L = 2 r0 s prod(b_l) already reaches
// every power of two at or above 4s -- what a smaller b_1 adds is a way to
// reach one WITHOUT lengthening the dense prefix, which every access scans in
// full (see the capacity header).  What the ladder must be is powers of two:
// U_l is the block width of every butterfly in the engine, so every b_l is a
// power of two and every U_l is one.  A TABLE, j U_l, need not be and
// routinely is not.
//
// WHY ONE BANK AND NOT TWO.  A merge reads the previous partial P_(j-1) and
// writes P_j, so the two cannot share storage, and alternating by the PARITY
// of the digit is enough to keep consecutive digits apart.  But only ONE of
// the two parities needs a bank of the level's own: the ODD partials live in
// the odd bank, (b_l-1)U_l, and the EVEN partials P_2, P_4, ..., P_(b_l-2)
// are built in the slot the level will forward INTO -- an inbox of the level
// above, leased at digit 2 rather than at digit b_l and held through digit
// b_l.  That slot is idle for digits 1..b_l-1 and every even partial fits it
// ((b_l-2)U_l < b_l U_l), so the even bank is not a buffer the design needs;
// a non-top level costs (3b_l-1)U_l counting its two inbox slots above rather
// than the (4b_l-3)U_l a second bank would make it.  There is still no
// allocator, no placement search and no fragmentation: every destination is a
// fixed slot named by the digit alone.
//
// WHAT IT COSTS is the slack the level above has to consume a carry, since
// the outstanding slot is next needed at digit 2 of the following cycle
// rather than at digit b_l, so the level above must hand the inbox back
// within b_l + 2 producer periods instead of 2 b_l; the bank-first run below
// widens that window again.  The
// lifetime of a partial inside a lease is BoundaryProducer's (PinUntil); this
// header only says where the digit goes.
//
// Fanout two uses the same odd-bank allocation. Its first carry is installed
// through the ordinary partial job, releasing the source inbox after
// publication and reader retirement.
//
// Every receiving level owns two U_l-bucket inboxes. Higher fanouts still
// adopt digit 1 in place and release that inbox when digit 2 replaces it.
//
// THE BANK-FIRST RUN (Params::bank_first).  At the start
// of a cycle the odd bank is idle -- its last occupant P_(b-1) left when the
// full table published -- while the inbox the next even digit needs may still
// hold the previous full table the level above is absorbing.  The run builds
// digits 2..r in the bank instead, so the forwarding lease is first needed at
// digit r + 1 rather than 2.  Two consecutive partials must coexist in the
// bank (P_j is written while P_(j-1) is still live), so they alternate
// between its top and its base, and they fit only while (2r-1)U <= (b-1)U,
// r <= b/2.  What ends the run is a PARITY question and nothing else:
//
// an ODD last digit is followed by an even one, which goes to the lease as
// usual, while an even last digit would be followed by an odd one that has
// to live in the bank beside it, and the two do not fit.  So the run
// (BankFirst::kNoClone, the default) stops at the largest odd digit <= b/2:
// none at b = 2 and 4, digits 2..3 at b = 8.  It runs the same merges on the
// same bytes, only in the bank, so it widens the window at no cost.  The odd
// bank's even partials need their own lifecycle and tier while its odd ones
// are live, so a level with a run has a SECOND slot over
// the same buckets (SlotKind::kRunBank).
//
// WHAT THIS HEADER IS NOT.  It is pure arithmetic over PUBLIC counters: level
// sizes, digit positions, bucket offsets.  Nothing here reads occupancy, keys,
// matches or tombstone counts, and nothing here allocates.  The allocation and
// the slot lifetimes are cpu_byteslice_level_arena_slots.hpp; the nonce
// coordinates are cpu_byteslice_level_arena_family.hpp.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_bytes.hpp"
#include "src/oram/rebuild/cpu_byteslice_residual_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

static_assert(sizeof(size_t) == 8,
              "the level-arena engine is 64-bit only (so is AVX-512)");

// ---------------------------------------------------------------------------
// Checked arithmetic
// ---------------------------------------------------------------------------
//
// Entry capacities, byte sizes, access windows and nonce coordinates are all
// products of user-supplied geometry, and a silently wrapped one would be a
// correctness failure that no test can see.  Every such product goes through
// these, which REFUSE rather than wrap.  They are not on any hot path: the
// geometry is computed once at construction.

inline uint64_t CheckedAdd(uint64_t a, uint64_t b, const char* what) {
  if (a > ~uint64_t{0} - b) {
    throw std::overflow_error(std::string("level arena: ") + what +
                              " overflows a 64-bit count");
  }
  return a + b;
}

inline uint64_t CheckedMul(uint64_t a, uint64_t b, const char* what) {
  if (a != 0 && b > ~uint64_t{0} / a) {
    throw std::overflow_error(std::string("level arena: ") + what +
                              " overflows a 64-bit count");
  }
  return a * b;
}

// base^exponent, refusing rather than wrapping.
inline uint64_t CheckedPow(uint64_t base, unsigned exponent,
                           const char* what) {
  uint64_t result = 1;
  for (unsigned i = 0; i < exponent; ++i) result = CheckedMul(result, base, what);
  return result;
}

inline bool IsPowerOfTwo(uint64_t v) { return v != 0 && (v & (v - 1)) == 0; }

// Log2Exact (cpu_byteslice_layout.hpp) rounds UP for a non-power-of-two, which
// is silently wrong for an index-bit count.  Every caller here states the
// precondition instead of assuming it.
inline unsigned Log2Checked(uint64_t v, const char* what) {
  if (!IsPowerOfTwo(v)) {
    throw std::invalid_argument(std::string("level arena: ") + what +
                                " must be a power of two");
  }
  unsigned bits = 0;
  while ((uint64_t{1} << bits) < v) ++bits;
  return bits;
}

// ---------------------------------------------------------------------------
// Physical slots
// ---------------------------------------------------------------------------

// Which fixed buffer of a level's arena a slot is.  The design has no
// variable-size allocator and no size classes, so a slot's identity IS its
// role.
enum class SlotKind : uint8_t {
  // Partial destinations P_1, P_3, ..., P_(b_l-1); (b_l-1)U_l buckets.  The
  // level's ONLY bank: the even partials are built in an inbox of the level
  // above, under the forwarding lease (see the header).
  kOddBank,
  // A receiver-owned carry destination, U_l buckets.  Two per level 2..L: the
  // producer at l-1 leases one, builds its full table in it, publishes and
  // hands it over.  See the two-inbox argument at the top of this file.
  kInbox,
  // The top's two T-bucket banks, A (published) and C (next compaction
  // destination).  Only level L has these.
  kTopBank,
  // The odd bank's buckets under a SECOND lifecycle, with a tier of its own:
  // the even partials of a bank-first run, each written
  // while the odd partial beside it in the same bank is still live.  It
  // allocates no main (SlotSpec::shares_main), and exists only at a level
  // whose run is not empty.
  kRunBank,
};

inline const char* SlotKindName(SlotKind kind) {
  switch (kind) {
    case SlotKind::kOddBank: return "odd-bank";
    case SlotKind::kInbox: return "inbox";
    case SlotKind::kTopBank: return "top-bank";
    case SlotKind::kRunBank: return "run-bank";
  }
  return "?";
}

// One physical buffer: where it is in its level's arena and how big it is.
// `main_*` is the table, `tier_*` its dedicated second-tier companion.  The
// tier is part of the SLOT, not a separately recycled resource, so an old tier
// can never be reused while its main is still pinned by a reader -- which is
// why a credit may only be returned when the whole slot is free.
struct SlotSpec {
  unsigned level = 0;
  SlotKind kind = SlotKind::kOddBank;
  // 0 or 1 for inboxes and top banks (top bank 0 is A at construction, but the
  // A/C roles alternate, so this is an identity and not a role).  0 otherwise.
  unsigned index = 0;
  size_t main_buckets = 0;
  size_t main_offset = 0;  // bucket offset within the level's arena
  size_t tier_buckets = 0;
  size_t tier_offset = 0;  // bucket offset within the level's arena
  // The main is ANOTHER slot's buckets (the run bank's is the odd bank's), so
  // it is not allocated or billed twice.  Which of the two lifecycles may
  // write which part of the buckets is the carry plan's placement, checked at
  // construction (ExpectBanksCoverEveryPartial) and at every lease
  // (LevelState::AcquireDestination).
  bool shares_main = false;
};

// Every physical buffer of one level, plus the lookups the owner loop needs.
// Slot indices are positions in `slots`; kNoSlot means the level does not have
// that buffer (no odd bank at the top, no inbox at level 1, top banks only at
// level L).
struct LevelPlan {
  static constexpr unsigned kNoSlot = ~0u;

  unsigned level = 0;
  std::vector<SlotSpec> slots;
  size_t arena_buckets = 0;  // mains + tiers of this level

  unsigned odd_bank = kNoSlot;
  // The odd bank's second lifecycle, for a bank-first run's even partials.
  unsigned run_bank = kNoSlot;
  unsigned inbox[2] = {kNoSlot, kNoSlot};
  unsigned top_bank[2] = {kNoSlot, kNoSlot};

  const SlotSpec& At(unsigned slot) const { return slots.at(slot); }

  // How many inbox slots this level owns: two at every receiving level, none
  // at level 1.  It is the size of both rings of the level's boundary, which
  // is what makes a ring sized for the slot count provably big enough
  // (cpu_byteslice_level_arena_boundary.hpp), so the boundary and the byte
  // bill ask the plan rather than each counting for themselves.
  size_t inbox_count() const {
    size_t inboxes = 0;
    for (unsigned i = 0; i < 2; ++i) {
      if (inbox[i] != kNoSlot) ++inboxes;
    }
    return inboxes;
  }
};

// ONE level's arena is ONE buffer holding the mains and the tiers of every
// slot (SlotSpec: a tier is part of the slot, not a separately recycled
// resource).  Splitting its requested bytes by role is exact, because the
// slot specs say which buckets are which; the allocator's rounding is the
// whole buffer's and belongs to neither half, which is why both go into the
// bill in one call.
inline void AddLevelArenaBytes(LevelArenaByteBill* bill, const LevelPlan& plan,
                               const Layout& layout) {
  size_t mains = 0;
  size_t tiers = 0;
  for (const SlotSpec& slot : plan.slots) {
    if (!slot.shares_main) mains += slot.main_buckets;
    tiers += slot.tier_buckets;
  }
  if (mains + tiers != plan.arena_buckets) {
    throw std::logic_error(
        "level arena: a level's slots do not span its arena");
  }
  bill->AddAligned64Split(
      {RoleShare{ByteRole::kMains,
                 CheckedTableBytes(mains, layout)},
       RoleShare{ByteRole::kTiers,
                 CheckedTableBytes(tiers, layout)}});
}

// The storage bill of the whole hierarchy, in buckets.  `main_buckets` is the
// quantity DESIGN.md ("Geometry and storage bound") gives a closed form for; it
// deliberately excludes tiers, masks, the dense prefix ring and every kind of
// scratch, because those are functions of the Layout and the stash planners
// rather than of the level shape.  ArenaBytes() is the thing to quote as a
// memory figure; main/T is the thing to compare against the plan.
struct StoragePlan {
  std::vector<LevelPlan> levels;  // index 0 unused; 1..L are the hashed levels
  size_t partial_bank_buckets = 0;
  size_t inbox_buckets = 0;
  size_t top_bank_buckets = 0;  // 2T
  size_t main_buckets = 0;      // the three above
  size_t tier_buckets = 0;
  size_t arena_buckets = 0;     // main_buckets + tier_buckets

  // Index 0 is a placeholder so that `levels[l]` is level l.  Returning it
  // would be an empty plan rather than an error, so ask for it and you get a
  // refusal.
  const LevelPlan& At(unsigned level) const {
    if (level < 1 || level >= levels.size()) {
      throw std::out_of_range("level arena: no such level");
    }
    return levels[level];
  }
};

// ---------------------------------------------------------------------------
// What happens to an incoming carry
// ---------------------------------------------------------------------------

enum class CarryOutcome : uint8_t {
  // Level >= 2, digit 1, when adoption is enabled: the inbox BECOMES P_1 with
  // no copy, no kernel and no probe-plan swap.  The only outcome that performs
  // no work at all.
  kAdopt,
  // Non-adopted digits below B (including default binary digit 1): merge into
  // this level's odd bank if the digit is odd or in a bank-first run, and
  // otherwise into the level above's inbox, under the forwarding lease (see
  // the header).
  kPartial,
  // Digit B below the top: merge into a slot leased from level+1's inbox.  The
  // output is exactly U_(l+1) buckets, so it fits the receiver's slot exactly.
  kForward,
  // The top: compaction of bank A plus the carry into bank C.  The top has no
  // digit odometer; it is always T buckets.
  kCompact,
};

// Where the output of one accepted carry goes, and how big it is.  A pure
// function of public counters -- the level and the carry ordinal -- which is
// what keeps slot choice and table size off the secret-dependent list.
struct CarryPlan {
  CarryOutcome outcome = CarryOutcome::kPartial;
  unsigned level = 0;              // the level accepting the carry
  uint64_t ordinal = 0;            // its one-based incoming carry count
  unsigned digit = 0;              // 1..B below the top; the top reports D
  unsigned destination_level = 0;  // `level`, or level+1 when forwarding
  SlotKind destination_kind = SlotKind::kOddBank;
  // Where the output starts inside its slot's main, in buckets.  Zero except
  // for a bank table a bank-first run puts at the bank's top.
  size_t destination_offset = 0;
  size_t output_buckets = 0;
};

// How a level's cycle uses its idle odd bank (the rule is at the top of this
// file).
enum class BankFirst : uint8_t {
  // Every even digit is built in the forwarding lease, from digit 2.
  kOff,
  // Digits 2..r in the bank, r the largest ODD digit <= b/2; no copy.
  kNoClone,
};

inline const char* BankFirstName(BankFirst mode) {
  switch (mode) {
    case BankFirst::kOff: return "off";
    case BankFirst::kNoClone: return "no-clone";
  }
  return "?";
}

// Whether a merge at `digit` has an OLDER operand: every digit above 1 absorbs
// P_(j-1), and the top always compacts A.  Digit 1 has none, whether it adopts,
// builds the dense carry or installs a binary carry into the odd bank.  One
// spelling, because the level's scheduling and the job's binding check must
// agree on it.
inline bool MergeHasOlderHalf(bool top, unsigned digit) {
  return top || digit > 1;
}

// A partial table whose destination is an inbox of the level above -- every
// EVEN digit below b_l: this level's table, written and published under the
// forwarding lease, never announced, and retired by this level through
// BoundaryProducer::PinUntil rather than through its own arena.
inline bool PartialInInbox(const CarryPlan& carry) {
  return carry.outcome == CarryOutcome::kPartial &&
         carry.destination_kind == SlotKind::kInbox;
}

// Whether a carry's destination is reached through the producer's lease on
// the level above's inbox: digit b_l, and every even digit below it.
// Everything else is a slot of the level's own arena.
inline bool UsesForwardingLease(const CarryPlan& carry) {
  return carry.outcome == CarryOutcome::kForward || PartialInInbox(carry);
}

// ---------------------------------------------------------------------------
// LevelArenaGeometry
// ---------------------------------------------------------------------------

class LevelArenaGeometry {
 public:
  // The public geometry.  Symbols in the comments are the plan's.
  struct Params {
    unsigned branching = 8;       // B, maximum non-top fanout; {2, 4, 8}
    unsigned levels = 4;          // L, hashed levels INCLUDING the top; >= 2
    unsigned top_digit = 4;       // D, the top's fixed digit; {1,2,4,8}, <= B
    unsigned prefix_flushes = 8;  // r0, online-stash flushes per prefix; {2,4,8}
    size_t stash_buckets = 1;     // s; the online stash holds 64s entries
    unsigned dense_prefixes = 2;  // q, complete prefixes allowed outstanding
    // Optional per-level fanouts, indexed 1..L-1. Empty means uniform B.
    std::vector<unsigned> level_fanouts;
    // Concrete shared tier width for raw geometry. Engine/capacity options
    // default to zero (automatic) and resolve it before constructing geometry.
    // A ResidualStash's inline occupancy array limits the resolved width.
    // With a per-level profile it is the profile's widest entry.
    size_t tier_buckets = 1;
    // THE PER-LEVEL TIER PROFILE, indexed 1..L; empty is the shared width.
    // Entry l is the width of the tables LEVEL l PRODUCES, so it is where
    // level l's banks and top banks hold their tiers and where level l+1's
    // inboxes hold theirs: a tier's width is its producer's, whichever level
    // stores or reads it (TierBucketsOf).  Automatic sizing (tier_buckets =
    // 0) resolves it from the stash sizing (ResolveLevelArenaTierGeometry).
    std::vector<size_t> level_tier_buckets;
    // Build each cycle's first digits in the idle odd bank.  Costs one tier
    // per level that has a run and no main storage.
    // kNoClone by default: it runs the same merges on the same bytes, only
    // in the bank, and widens every producer's window.
    BankFirst bank_first = BankFirst::kNoClone;
  };

  // 8, not kMaxRadix: a top whose digit is a power of two routes A with
  // binary butterfly levels and no radix pass, so D = 8 needs no radix-8
  // kernel.  8 is the ceiling
  // because the sweep packs an entry's way into the digit's three bits.
  static constexpr unsigned kMaxTopDigit = 8;

  // THE TOP IS BINARY: D is a power of two, routed as one (K + log2 D)-level
  // butterfly over all of T under a kRaw map (the low K + log2 D tag bits
  // name the final bucket directly).  Its preparation and a direct
  // initialization distribute through the one-page DFS, whose final-range
  // event is certified for a binary top's population map only
  // (analysis/bound_certification/README.md); a radix-D top has no certified
  // preparation, so no geometry has one.
  static bool IsTopDigit(unsigned top_digit) {
    return top_digit >= 1 && top_digit <= kMaxTopDigit &&
           (top_digit & (top_digit - 1)) == 0;
  }
  // e = log2 D, for a digit IsTopDigit accepts.
  static unsigned TopPower(unsigned top_digit) {
    return static_cast<unsigned>(__builtin_ctz(top_digit));
  }

  explicit LevelArenaGeometry(const Params& params) : p_(params) {
    Validate();
    // Z = 2 r0 s is a prefix at half load; level 1 routes it into U_1 = Z.
    const size_t z =
        CheckedMul(2 * uint64_t{p_.prefix_flushes}, p_.stash_buckets, "Z");
    dense_prefix_buckets_ = z / 2;
    routed_prefix_buckets_ = z;
    dense_ring_buckets_ = static_cast<size_t>(
        CheckedMul(CheckedAdd(p_.dense_prefixes, 1, "q + 1"),
                   dense_prefix_buckets_, "dense prefix ring"));
    carry_buckets_.assign(p_.levels + 1, 0);
    fanout_.assign(p_.levels + 1, p_.branching);
    prefix_product_.assign(p_.levels + 1, 1);
    for (unsigned l = 1; l < p_.levels; ++l) {
      fanout_[l] = p_.level_fanouts.empty() ? p_.branching
                                            : p_.level_fanouts[l - 1];
      prefix_product_[l + 1] =
          CheckedMul(prefix_product_[l], fanout_[l], "fanout prefix product");
    }
    for (unsigned l = 1; l <= p_.levels; ++l) {
      carry_buckets_[l] =
          l == 1 ? routed_prefix_buckets_
                 : CheckedMul(z, prefix_product_[l], "U_l");
    }
    top_buckets_ = CheckedMul(p_.top_digit, carry_buckets_[p_.levels], "T");
    capacity_entries_ = CheckedMul(32, top_buckets_, "capacity");
    prefix_positions_ =
        CheckedMul(CheckedMul(kBucketCapacity, p_.stash_buckets, "64s"),
                   p_.prefix_flushes, "64 s r0");
    BuildStorage();
    ExpectBanksCoverEveryPartial();
  }

  // ---- public geometry ----------------------------------------------------

  unsigned Branching() const { return p_.branching; }      // maximum B
  unsigned Fanout(unsigned level) const {
    if (level < 1 || level >= p_.levels) {
      throw std::out_of_range(
          "level arena: fanout is only defined below the top");
    }
    return fanout_[level];
  }
  uint64_t PrefixProduct(unsigned level) const {
    if (level < 1 || level > p_.levels) {
      throw std::out_of_range("level arena: prefix product outside hierarchy");
    }
    return prefix_product_[level];
  }
  bool AnyFanoutAboveTwo() const {
    for (unsigned l = 1; l < p_.levels; ++l) {
      if (fanout_[l] > 2) return true;
    }
    return false;
  }
  unsigned Levels() const { return p_.levels; }            // L
  unsigned TopLevel() const { return p_.levels; }          // L
  unsigned TopDigit() const { return p_.top_digit; }       // D
  unsigned TopPower() const { return TopPower(p_.top_digit); }  // e at the top
  // The top's merge block, 2^(K + e): all of T.  What the stash certificate
  // and the job's storage size from.
  size_t TopBlockBuckets() const {
    return carry_buckets_[p_.levels] << TopPower();
  }
  unsigned PrefixFlushes() const { return p_.prefix_flushes; }  // r0
  size_t StashBuckets() const { return p_.stash_buckets; }      // s
  unsigned DensePrefixes() const { return p_.dense_prefixes; }  // q
  // The widest tier: the shared width, or the profile's maximum.
  size_t TierBuckets() const { return p_.tier_buckets; }
  bool HasTierProfile() const { return !p_.level_tier_buckets.empty(); }
  // The tier width of the tables `level` PRODUCES (see
  // Params::level_tier_buckets): its banks' and the next level's inboxes'.
  size_t TierBucketsOf(unsigned level) const {
    if (level < 1 || level > p_.levels) {
      throw std::out_of_range("level arena: no such level");
    }
    return p_.level_tier_buckets.empty() ? p_.tier_buckets
                                         : p_.level_tier_buckets[level - 1];
  }
  // The tier a slot of `level` of this kind holds: an inbox holds tables the
  // level below produced.
  size_t SlotTierBuckets(unsigned level, SlotKind kind) const {
    return kind == SlotKind::kInbox ? TierBucketsOf(level - 1)
                                    : TierBucketsOf(level);
  }
  // The tier of the carry a merge at `level` absorbs: the level below's,
  // in this level's inbox.  Level 1's carry is the dense prefix and has none.
  size_t CarryTierBuckets(unsigned level) const {
    return level == 1 ? 0 : TierBucketsOf(level - 1);
  }
  // The tier of the older operand a merge of `digit` at `level` reads: a
  // table this level built -- in its bank, the run bank, or the next level's
  // inbox under the forwarding lease -- except an adopted first carry, which
  // stays in this level's inbox with the level below's tier.  The top's
  // older operand is its own A.
  size_t OlderTierBuckets(unsigned level, unsigned digit) const {
    if (level < p_.levels && digit == 2 &&
        PlanCarry(level, 1).outcome == CarryOutcome::kAdopt) {
      return TierBucketsOf(level - 1);
    }
    return TierBucketsOf(level);
  }
  const Params& params() const { return p_; }

  // 64s: the entries one online-stash flush publishes.
  size_t OnlineStashEntries() const { return kBucketCapacity * p_.stash_buckets; }
  // U_1: the HASHED buckets one routed prefix occupies -- Z = 2 r0 s.
  size_t RoutedPrefixBuckets() const { return routed_prefix_buckets_; }
  // Z/2 = r0 s: the DENSE buckets one prefix occupies before it is routed.
  // Half of Z because a hashed table runs at logical load 0.5 and a dense one
  // is full.
  size_t DensePrefixBuckets() const { return dense_prefix_buckets_; }
  // (q+1) prefix slots: q complete ones outstanding plus the one being
  // assembled (which contains the current online stash as its newest unit).
  //
  // Computed and CHECKED at construction, not here.  `q + 1` in unsigned
  // arithmetic wraps to zero at UINT_MAX -- which would report a ring of no
  // buckets for a geometry that constructed successfully -- and the product
  // with the prefix size is a second place to wrap.  A count that sizes a
  // buffer may not be allowed to do either.
  size_t DenseRingBuckets() const { return dense_ring_buckets_; }
  // 64 s r0: access POSITIONS in one complete prefix.  Windows are half-open
  // ranges in this unit, as ProbePlan's are.
  uint64_t PrefixPositions() const { return prefix_positions_; }

  // U_l = Z B^(l-1), the incoming carry size at hashed level l, for l in
  // [1, L].  There is deliberately no U_(L+1): the top never forwards, so the
  // largest thing anything asks for is level L's own carry, and computing one
  // more term would only add a geometry that overflows where the real ladder
  // does not.
  size_t CarryBuckets(unsigned level) const {
    if (level < 1 || level > p_.levels) {
      throw std::out_of_range("level arena: level outside the hierarchy");
    }
    return carry_buckets_[level];
  }

  size_t TopBuckets() const { return top_buckets_; }        // T = D U_L
  uint64_t CapacityEntries() const { return capacity_entries_; }  // 32T

  // The largest table a level OWNS: its full partial at digit B-1, or the top
  // at T.  This is what its own arena has to hold.
  size_t MaxResidentBuckets(unsigned level) const {
    if (level == p_.levels) return top_buckets_;
    return CheckedMul(Fanout(level) - 1, CarryBuckets(level), "max partial");
  }

  // The largest table a level's owner WRITES, which is a different and larger
  // number: at digit B it writes B U_l = U_(l+1) buckets into the receiver's
  // inbox.  Stash and range scratch are sized from THIS -- the biggest
  // operation the owner performs -- not from what it keeps.
  size_t MaxOutputBuckets(unsigned level) const {
    if (level == p_.levels) return top_buckets_;
    return CarryBuckets(level + 1);
  }

  // ---- the digit odometer -------------------------------------------------

  // The digit an incoming carry with one-based ordinal `ordinal` installs at
  // `level`: 1 + ((v-1) mod b_l), so digit b_l is the one that forwards and
  // resets.  The level is an argument rather than implied, because the fanout
  // is per level and a digit computed under another level's would odometer
  // this one into a partial its bank cannot hold.  Ordinals are never reset
  // between cycles, which is what keeps the nonce families of successive
  // cycles distinct.
  unsigned CarryDigit(unsigned level, uint64_t ordinal) const {
    if (ordinal == 0) {
      throw std::invalid_argument("level arena: carry ordinals are one-based");
    }
    return 1 + static_cast<unsigned>((ordinal - 1) % Fanout(level));
  }

  // ---- the bank-first run ------------------------------------------------

  // THE LAST DIGIT OF `level`'s RUN: digits 2..r of every cycle are built in
  // the level's own odd bank (and digit 1 too, where it is built at all).  1
  // means no run.  It stops at the largest odd digit up to b/2 (the most two
  // consecutive partials can share a (b-1)U bank), so that the digit after
  // the run is even and goes to the lease without a copy.  The top has none.
  unsigned BankRunEnd(unsigned level) const {
    if (level < 1 || level >= p_.levels) return 1;
    const unsigned half = Fanout(level) / 2;
    switch (p_.bank_first) {
      case BankFirst::kOff: return 1;
      case BankFirst::kNoClone: return half % 2 == 1 ? half : half - 1;
    }
    return 1;
  }

  // THE FIRST DIGIT OF A CYCLE AT WHICH `level` NEEDS AN INBOX OF THE LEVEL
  // ABOVE: 2 without a run (P_2, or the full table at fanout two), and r + 1
  // after one -- an even digit built in the lease.  The level above has from the arrival of one full table until
  // this digit of the NEXT cycle but one to hand that table's inbox back,
  // which is the window the run widens.  CHECKED against the odometer at
  // construction (ExpectBanksCoverEveryPartial).
  unsigned ForwardingLeaseDigit(unsigned level) const {
    if (level < 1 || level >= p_.levels) {
      throw std::out_of_range(
          "level arena: the top forwards nothing, so it leases no inbox");
    }
    return BankRunEnd(level) + 1;
  }

  // Where a bank table at `digit` starts, in buckets of the bank.  Outside a
  // run every table sits at the bank's base.  Inside one the run's last
  // partial sits at the TOP and those before it alternate top, base, top, ...
  // walking down, so consecutive digits never overlap: P_j and P_(j-1) take
  // (2j-1)U <= (2r-1)U <= (b-1)U.
  size_t BankOffset(unsigned level, unsigned digit) const {
    const unsigned end = BankRunEnd(level);
    const bool in_run = digit <= end && (end - digit) % 2 == 0;
    if (end < 2 || !in_run) return 0;
    return static_cast<size_t>(
        CheckedMul(Fanout(level) - 1 - digit, CarryBuckets(level),
                   "bank offset"));
  }

  // The complete disposition of one accepted carry.  See CarryOutcome.
  CarryPlan PlanCarry(unsigned level, uint64_t ordinal) const {
    if (level < 1 || level > p_.levels) {
      throw std::out_of_range("level arena: level outside the hierarchy");
    }
    CarryPlan plan;
    plan.level = level;
    plan.ordinal = ordinal;
    if (level == p_.levels) {
      // The top has no odometer: it is always T buckets and every carry is a
      // compaction of A plus the carry into C.
      if (ordinal == 0) {
        throw std::invalid_argument("level arena: carry ordinals are one-based");
      }
      plan.outcome = CarryOutcome::kCompact;
      plan.digit = p_.top_digit;
      plan.destination_level = level;
      plan.destination_kind = SlotKind::kTopBank;
      plan.output_buckets = top_buckets_;
      return plan;
    }
    const unsigned fanout = Fanout(level);
    const unsigned digit = CarryDigit(level, ordinal);
    plan.digit = digit;
    if (digit == fanout) {
      plan.outcome = CarryOutcome::kForward;
      plan.destination_level = level + 1;
      plan.destination_kind = SlotKind::kInbox;
      plan.output_buckets = CarryBuckets(level + 1);
      return plan;
    }
    plan.destination_level = level;
    plan.output_buckets =
        CheckedMul(digit, CarryBuckets(level), "partial table");
    if (digit == 1 && AdoptsFirstCarry(level)) {
      // Zero-copy adoption: P_1 stays where the producer built it.
      plan.outcome = CarryOutcome::kAdopt;
      plan.destination_kind = SlotKind::kInbox;
      return plan;
    }
    plan.outcome = CarryOutcome::kPartial;
    if (digit % 2 == 0 && digit > BankRunEnd(level)) {
      // An even partial past the run is built in the receiver's inbox slot
      // under the forwarding lease, which is taken at ForwardingLeaseDigit
      // and held to digit b_l.  `digit < fanout` here, so this is never the
      // full table.
      plan.destination_level = level + 1;
      plan.destination_kind = SlotKind::kInbox;
      return plan;
    }
    // The level's own bank: every odd partial, whose P_(j-1) is either even
    // and in the lease or a run partial beside it in the bank, and the run's
    // even partials, under the bank's second lifecycle.  Parity alone picks
    // the occupancy, because consecutive digits must not share one.
    plan.destination_kind =
        digit % 2 == 0 ? SlotKind::kRunBank : SlotKind::kOddBank;
    plan.destination_offset = BankOffset(level, digit);
    return plan;
  }

  // ---- storage ------------------------------------------------------------

  const StoragePlan& storage() const { return storage_; }

  // Buckets of MAIN table storage, the quantity the plan's closed form covers.
  size_t MainBuckets() const { return storage_.main_buckets; }
  // Every bucket this engine's level arenas hold, tiers included.  Still not
  // the whole byte bill: the dense ring, the level-1 private log, the
  // preparation sheds and the transient range scratch are separate.
  size_t ArenaBuckets() const { return storage_.arena_buckets; }

  // Bytes of one level's arena: its buckets plus one occupancy word each.
  //
  // This is the REQUESTED size.  AllocateAligned64 rounds a request of 2 MiB
  // or more up to a whole huge page, so the resident figure for a large level
  // is a little higher; that rounding is an allocator property and is reported
  // where allocation happens, not derived here.
  size_t LevelArenaBytes(unsigned level, const Layout& layout) const {
    const size_t buckets = storage_.At(level).arena_buckets;
    return static_cast<size_t>(
        CheckedAdd(CheckedMul(buckets, layout.BucketBytes(), "level bucket bytes"),
                   CheckedMul(buckets, sizeof(uint64_t), "level mask bytes"),
                   "level bytes"));
  }

  // The same over every level.
  size_t ArenaBytes(const Layout& layout) const {
    uint64_t total = 0;
    for (unsigned l = 1; l <= p_.levels; ++l) {
      total = CheckedAdd(total, LevelArenaBytes(l, layout), "arena bytes");
    }
    return static_cast<size_t>(total);
  }

 private:
  void Validate() const {
    if (p_.branching != 2 && p_.branching != 4 && p_.branching != 8) {
      throw std::invalid_argument("level arena: B must be 2, 4 or 8");
    }
    if (p_.levels < 2) {
      throw std::invalid_argument("level arena: L must be at least 2");
    }
    // A sanity bound, far below the nonce's 15-bit level field: L is a count
    // of hashed levels, and even 32 of them is a capacity no machine holds.
    // The nonce field itself is checked where it is packed (FamilyId).
    if (p_.levels > 1024) {
      throw std::invalid_argument("level arena: L is implausibly large");
    }
    if (!IsTopDigit(p_.top_digit)) {
      throw std::invalid_argument(
          "level arena: D must be 1, 2, 4 or 8 -- only a binary top has a "
          "certified preparation");
    }
    // THE TOP IS NO WIDER THAN THE FANOUT.  Per access the top moves
    // 2D/(B+1) times what a fanout-B level does, so D <= B keeps that under
    // 2x; a wider top would make the top dominate the rebuild work.
    // The cap is the configured B, the maximum fanout, and not b_(L-1): the
    // ladder only ever lowers b_1, so the two differ only for an L = 2
    // geometry, which only a tiny map has.
    if (p_.top_digit > p_.branching) {
      throw std::invalid_argument("level arena: D must not exceed B");
    }
    if (p_.prefix_flushes != 2 && p_.prefix_flushes != 4 &&
        p_.prefix_flushes != 8) {
      throw std::invalid_argument("level arena: r0 must be 2, 4 or 8");
    }
    if (!IsPowerOfTwo(p_.stash_buckets)) {
      throw std::invalid_argument(
          "level arena: s must be a positive power of two");
    }
    if (p_.dense_prefixes < 1) {
      throw std::invalid_argument("level arena: q must be at least 1");
    }
    if (p_.tier_buckets == 0) {
      throw std::invalid_argument("level arena: a slot needs a tier bucket");
    }
    // A tier is drained into as a ResidualStash, whose occupancy is an INLINE
    // array of kMaxResidualStashBuckets words.  Past that width the stash's
    // own Count()/Reset() read off the end of themselves, so the ladder
    // refuses the geometry rather than the allocation succeeding and the
    // overrun waiting for a shed.
    if (p_.tier_buckets > kMaxResidualStashBuckets) {
      throw std::invalid_argument(
          "level arena: a tier is wider than a residual stash's occupancy "
          "array");
    }
    if (!p_.level_tier_buckets.empty()) {
      if (p_.level_tier_buckets.size() != p_.levels) {
        throw std::invalid_argument(
            "level arena: a tier profile holds one width per level");
      }
      size_t widest = 0;
      for (size_t width : p_.level_tier_buckets) {
        if (width == 0 || width > kMaxResidualStashBuckets) {
          throw std::invalid_argument(
              "level arena: every profile width must be a nonzero residual "
              "stash width");
        }
        widest = std::max(widest, width);
      }
      if (widest != p_.tier_buckets) {
        throw std::invalid_argument(
            "level arena: a tier profile's widest entry is its tier_buckets");
      }
      // Non-decreasing below the top, so a binary level's digit-1 install,
      // which moves its carry's tier (the level below's) unchanged into its
      // own output tier, always has the room (LevelTierProfile).
      for (unsigned l = 2; l < p_.levels; ++l) {
        if (p_.level_tier_buckets[l - 1] < p_.level_tier_buckets[l - 2]) {
          throw std::invalid_argument(
              "level arena: a tier profile narrows below the top");
        }
      }
    }
    if (!p_.level_fanouts.empty() &&
        p_.level_fanouts.size() != p_.levels - 1) {
      throw std::invalid_argument(
          "level arena: level_fanouts must contain one entry per non-top level");
    }
    for (unsigned fanout : p_.level_fanouts) {
      if (fanout < 2 || fanout > p_.branching || !IsPowerOfTwo(fanout)) {
        throw std::invalid_argument(
            "level arena: every level fanout must be a power of two in [2, B]");
      }
    }
    if (p_.bank_first != BankFirst::kOff &&
        p_.bank_first != BankFirst::kNoClone) {
      throw std::invalid_argument("level arena: unknown bank_first mode");
    }
    // The direct build caches each prefix lane's B home in at most two byte
    // lines: U_1 = 2 r0 s <= 2^16.
    if (p_.stash_buckets > (size_t{1} << 12)) {
      throw std::invalid_argument(
          "level arena: a directly built level one needs U_1 <= 2^16");
    }
  }

  // Appends one slot to `level`, placing its main and its tier at the arena
  // cursor.  Mains and tiers interleave per slot rather than living in two
  // regions: a slot is one lifetime, and keeping its two pieces adjacent is
  // what makes "the whole slot is free" a single range.
  unsigned AddSlot(LevelPlan& plan, SlotKind kind, unsigned index,
                   size_t main_buckets) {
    const size_t tier = SlotTierBuckets(plan.level, kind);
    SlotSpec spec;
    spec.level = plan.level;
    spec.kind = kind;
    spec.index = index;
    spec.main_buckets = main_buckets;
    spec.main_offset = plan.arena_buckets;
    spec.tier_buckets = tier;
    spec.tier_offset = plan.arena_buckets + main_buckets;
    plan.arena_buckets = static_cast<size_t>(
        CheckedAdd(plan.arena_buckets,
                   CheckedAdd(main_buckets, tier, "slot buckets"),
                   "level arena"));
    const unsigned slot = static_cast<unsigned>(plan.slots.size());
    plan.slots.push_back(spec);
    storage_.tier_buckets = static_cast<size_t>(
        CheckedAdd(storage_.tier_buckets, tier, "tier storage"));
    storage_.main_buckets =
        static_cast<size_t>(CheckedAdd(storage_.main_buckets, main_buckets,
                                       "main storage"));
    return slot;
  }

  // A second slot over slot `of`'s MAIN, with a tier of its own at the arena
  // cursor.  The run bank is the only one: its lifecycle is separate because
  // its tables coexist with the odd bank's, and nothing else about it is.
  unsigned AddSharedSlot(LevelPlan& plan, SlotKind kind, unsigned of) {
    SlotSpec spec = plan.At(of);
    spec.kind = kind;
    spec.index = 0;
    spec.shares_main = true;
    const size_t tier = SlotTierBuckets(plan.level, kind);
    spec.tier_buckets = tier;
    spec.tier_offset = plan.arena_buckets;
    plan.arena_buckets = static_cast<size_t>(
        CheckedAdd(plan.arena_buckets, tier, "level arena"));
    const unsigned slot = static_cast<unsigned>(plan.slots.size());
    plan.slots.push_back(spec);
    storage_.tier_buckets = static_cast<size_t>(
        CheckedAdd(storage_.tier_buckets, tier, "tier storage"));
    return slot;
  }

  // Whether digit 1 at a level below the top ADOPTS the ready inbox table as
  // its P_1 instead of installing it as a partial.  Never at level 1,
  // whose carry is built from the dense prefix, and never at a binary level,
  // which installs P_1 into its odd bank so that both inboxes stay available
  // (DESIGN.md, "Geometry and storage bound").
  bool AdoptsFirstCarry(unsigned level) const {
    return level >= 2 && Fanout(level) > 2;
  }

  // THE ARGUMENT ABOVE, CHECKED rather than trusted, once at construction.
  // Walking every level's whole odometer is `sum(b_l) <= 8L` calls, and what
  // it rules out is the failure the bank rule could cause: a carry whose
  // destination is a bank the plan did not allocate, which a lease would then
  // take for kNoSlot and index an arena with.
  //
  // With a bank-first run it also checks the PAIR RULE the placement exists
  // for: P_j is written while P_(j-1) is live, so two consecutive tables in
  // the bank use different occupancies (and so different tiers) and disjoint
  // buckets.  And that ForwardingLeaseDigit is the first digit that really does need the lease.
  void ExpectBanksCoverEveryPartial() const {
    const auto in_bank = [](const CarryPlan& c) {
      return c.outcome == CarryOutcome::kPartial &&
             (c.destination_kind == SlotKind::kOddBank ||
              c.destination_kind == SlotKind::kRunBank);
    };
    for (unsigned l = 1; l < p_.levels; ++l) {
      const LevelPlan& plan = storage_.levels[l];
      const auto fail = [&](const std::string& what) {
        throw std::logic_error("level arena: level " + std::to_string(l) +
                               " " + what);
      };
      unsigned first_lease = 0;
      bool uses_run_bank = false;
      for (unsigned digit = 1; digit <= fanout_[l]; ++digit) {
        const CarryPlan carry = PlanCarry(l, digit);
        if (first_lease == 0 && UsesForwardingLease(carry)) {
          first_lease = digit;
        }
        if (digit >= 2) {
          const CarryPlan prev = PlanCarry(l, digit - 1);
          if (in_bank(prev) && in_bank(carry)) {
            if (prev.destination_kind == carry.destination_kind) {
              fail("builds two consecutive partials in one bank occupancy");
            }
            // The odd bank and the run bank share buckets.
            if (prev.destination_offset <
                    carry.destination_offset + carry.output_buckets &&
                carry.destination_offset <
                    prev.destination_offset + prev.output_buckets) {
              fail("overlaps two consecutive partials in its bank");
            }
          }
        }
        if (carry.outcome != CarryOutcome::kPartial) continue;
        if (carry.destination_kind == SlotKind::kInbox) {
          if (carry.destination_offset != 0) {
            fail("places a partial inside an inbox at an offset");
          }
          // An even partial: it is written into an inbox of the level above,
          // which must exist and hold it.
          const LevelPlan& up = storage_.levels[l + 1];
          for (unsigned i = 0; i < 2; ++i) {
            if (up.inbox[i] == LevelPlan::kNoSlot) {
              throw std::logic_error(
                  std::string("level arena: level ") + std::to_string(l) +
                  " plans an even partial in an inbox the level above does "
                  "not have");
            }
            if (up.At(up.inbox[i]).main_buckets < carry.output_buckets) {
              throw std::logic_error(
                  std::string("level arena: level ") + std::to_string(l) +
                  "'s even partial does not fit the inbox above it");
            }
          }
          continue;
        }
        const bool run = carry.destination_kind == SlotKind::kRunBank;
        uses_run_bank |= run;
        const unsigned slot = run ? plan.run_bank : plan.odd_bank;
        if (slot == LevelPlan::kNoSlot) {
          fail(std::string("plans a partial table in a ") +
               SlotKindName(carry.destination_kind) + " it was not given");
        }
        const size_t bank = plan.At(slot).main_buckets;
        if (carry.destination_offset > bank ||
            carry.output_buckets > bank - carry.destination_offset) {
          fail(std::string("has a ") + SlotKindName(carry.destination_kind) +
               " too small for a partial where the run places it");
        }
      }
      if (uses_run_bank != (plan.run_bank != LevelPlan::kNoSlot)) {
        fail("allocates a run bank its odometer does not use, or the reverse");
      }
      if (first_lease != ForwardingLeaseDigit(l)) {
        fail("first needs the forwarding lease at another digit than "
             "ForwardingLeaseDigit says");
      }
    }
  }

  void BuildStorage() {
    storage_.levels.resize(p_.levels + 1);
    for (unsigned l = 1; l <= p_.levels; ++l) {
      LevelPlan& plan = storage_.levels[l];
      plan.level = l;
      const size_t u = carry_buckets_[l];
      if (l < p_.levels) {
        const unsigned fanout = Fanout(l);
        // The common layout reserves (b_l-1)U_l at every non-top level.
        const size_t odd = CheckedMul(fanout - 1, u, "odd bank");
        plan.odd_bank = AddSlot(plan, SlotKind::kOddBank, 0, odd);
        storage_.partial_bank_buckets += odd;
        if (BankRunEnd(l) >= 2) {
          plan.run_bank =
              AddSharedSlot(plan, SlotKind::kRunBank, plan.odd_bank);
        }
      }
      if (l >= 2) {
        for (unsigned i = 0; i < 2; ++i) {
          plan.inbox[i] = AddSlot(plan, SlotKind::kInbox, i, u);
          storage_.inbox_buckets += u;
        }
      }
      if (l == p_.levels) {
        for (unsigned i = 0; i < 2; ++i) {
          plan.top_bank[i] = AddSlot(plan, SlotKind::kTopBank, i, top_buckets_);
          storage_.top_bank_buckets += top_buckets_;
        }
      }
      storage_.arena_buckets = static_cast<size_t>(
          CheckedAdd(storage_.arena_buckets, plan.arena_buckets, "arena"));
    }
  }

  Params p_;
  size_t dense_prefix_buckets_ = 0;
  size_t routed_prefix_buckets_ = 0;
  size_t dense_ring_buckets_ = 0;
  std::vector<size_t> carry_buckets_;
  std::vector<unsigned> fanout_;
  std::vector<uint64_t> prefix_product_;
  size_t top_buckets_ = 0;
  uint64_t capacity_entries_ = 0;
  uint64_t prefix_positions_ = 0;
  StoragePlan storage_;
};

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
