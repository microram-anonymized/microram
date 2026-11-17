#pragma once

// Nonce families as PUBLIC COORDINATES: which tables share a hash function,
// what window they all end at, and how that pair is encoded in the AES nonce,
// plus the counters a direct initialization seeds.  DESIGN.md ("Carries and
// preparation", "Direct initialization") gives the design.
//
// WHY A FAMILY IS NOT A TABLE.  A table's routing nonce is what turns a key
// into a bucket, so two live tables under the SAME nonce are probed at
// congruent positions in one access -- which is the nonce reuse this whole
// scheme forbids.  But a carry that is handed up the hierarchy is the same
// bytes in the same order under the same nonce, published two or three times
// under different table identities.  The security boundary is therefore the
// FAMILY, not the table: at most one member of a family may be live at a time,
// and the probe audit keys on (family, key) and holds a family's history until
// its LAST member retires.  ProbePlan already states both rules; this header is
// what assigns the families so that they hold.
//
// THE COORDINATE.  A family is named by the TERMINAL publication it is heading
// for -- the first place its bytes stop being forwarded.  A carry accepted at
// level l with ordinal v forwards when v is a multiple of THAT LEVEL'S fanout
// b_l, becoming ordinal v/b_l at level l+1, and so on; the loop below runs
// that forwarding to its end.  The fanout is read per level because it varies
// per level (cpu_byteslice_level_arena_geometry.hpp).
// Naming the destination rather than the origin is what makes a producer and
// its consumer agree on the nonce WITHOUT talking to each other: both compute
// the same pure function of public counters, before either starts work.
//
// WHY NOT A PER-OWNER ALLOCATOR.  NonceAllocator hands out family ids from a
// local counter.  One instance per owner thread would hand two levels the same
// id, and one shared instance would put a mutex on the path this design exists
// to keep lock-free.  The canonical coordinate needs neither: it is already
// unique, already agreed, and already monotone in the window it ends at.

#include <cstdint>
#include <stdexcept>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_geometry.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// A family coordinate: the level and one-based carry ordinal of the terminal
// publication.  Every member of the family -- the producer's full table, the
// consumer's adoption of it, and any further full table it is folded into
// without being re-tagged -- carries this same pair.
struct Family {
  unsigned level = 0;
  uint64_t ordinal = 0;

  friend bool operator==(const Family& a, const Family& b) {
    return a.level == b.level && a.ordinal == b.ordinal;
  }
  friend bool operator!=(const Family& a, const Family& b) { return !(a == b); }
};

// The ordinal field is the nonce's 48-bit rebuild-epoch field and the level
// field its 15-bit level field, so these are the exhaustion bounds.
inline constexpr uint64_t kMaxFamilyOrdinal = crypto::kAesCtrCounterMask;
inline constexpr uint64_t kMaxFamilyLevel = crypto::kAesCtrLevelMask;

// The canonical terminal publication of the family a carry belongs to.
// Runs the forwarding chain to its
// end: while this carry would be forwarded, follow it.
//
// Digit-1 adoption is terminal AT THAT LEVEL -- v % b_l == 1 stops the loop
// on the first test -- and inherits this identity without allocating
// anything.

// THE WALK ITSELF, once.  `fanout_at(level)` is the fanout of the level a
// carry is currently at; the three entry points below differ only in where
// they read it from, and writing the loop three times is how a producer and
// its consumer would eventually disagree about a nonce.
template <typename FanoutAt>
inline Family ForwardToTerminal(unsigned levels, unsigned level,
                                uint64_t ordinal, FanoutAt&& fanout_at) {
  if (level < 1 || level > levels || ordinal < 1) {
    throw std::invalid_argument("level arena: invalid family coordinate");
  }
  while (level < levels) {
    const unsigned fanout = fanout_at(level);
    if (fanout < 2) {
      // B = 1 is a hierarchy in which every ordinal forwards and no level
      // below the top can ever hold a table; B = 0 makes this a division by
      // zero.  The geometry admits {2, 4, 8}; this rejects only what has no
      // meaning at all, so a test may still walk shapes the ladder itself
      // does not build.
      throw std::invalid_argument("level arena: B must be at least 2");
    }
    if (ordinal % fanout != 0) break;
    ordinal /= fanout;
    ++level;
  }
  return Family{level, ordinal};
}

inline Family CanonicalFamily(const std::vector<unsigned>& fanouts,
                              unsigned levels, unsigned level,
                              uint64_t ordinal) {
  if (fanouts.size() + 1 != levels) {
    throw std::invalid_argument("level arena: fanout ladder has wrong length");
  }
  return ForwardToTerminal(levels, level, ordinal,
                           [&](unsigned l) { return fanouts[l - 1]; });
}

// The uniform ladder as four scalars, for a caller that has no geometry.
inline Family CanonicalFamily(unsigned branching, unsigned levels,
                              unsigned level, uint64_t ordinal) {
  return ForwardToTerminal(levels, level, ordinal,
                           [&](unsigned) { return branching; });
}

inline Family CanonicalFamily(const LevelArenaGeometry& g, unsigned level,
                              uint64_t ordinal) {
  return ForwardToTerminal(g.Levels(), level, ordinal,
                           [&](unsigned l) { return g.Fanout(l); });
}

// family_id = (ordinal << 15) | level, which is ALSO the packed AES high word
// of the real nonce (PackAesCtrHighWord puts the level in the low 15 bits, the
// counter above it and the domain bit at 63).  Zero is reserved for dense
// tables, and no legal coordinate produces it: levels are one-based.
inline uint64_t FamilyId(const Family& family) {
  if (family.level < 1 || family.level > kMaxFamilyLevel) {
    throw std::invalid_argument("level arena: family level does not fit the "
                                "nonce's level field");
  }
  if (family.ordinal < 1 || family.ordinal > kMaxFamilyOrdinal) {
    throw std::runtime_error("level arena: nonce ordinal exhausted; refusing "
                             "to reuse a nonce family");
  }
  return (family.ordinal << crypto::kAesCtrLevelBits) | family.level;
}

// The packing itself, shared by the two constructors below so they cannot
// drift: the level goes in the nonce's level field, the ordinal in its epoch
// field, and the real/dummy pair differ only in the domain bit.  Note that
// `epoch` is the ORDINAL here, not a global rebuild counter: the coordinate IS
// the epoch, which is what lets two owners agree without sharing an allocator.
inline RebuildNonce PackFamilyNonce(unsigned level, uint64_t ordinal,
                                    uint64_t family_id) {
  RebuildNonce n;
  n.family_id = family_id;
  n.epoch = ordinal;
  n.target_level = level;
  n.real_lo = level;
  n.real_hi = ordinal;
  n.dummy_lo = uint64_t{level} | crypto::kAesCtrDomainBit;
  n.dummy_hi = ordinal;
  n.real_high = crypto::PackAesCtrHighWord(n.real_lo, n.real_hi);
  n.dummy_high = crypto::PackAesCtrHighWord(n.dummy_lo, n.dummy_hi);
  return n;
}

// The real and dummy nonces of a family, packed the way the probe path wants
// them.
inline RebuildNonce FamilyNonce(const Family& family) {
  return PackFamilyNonce(family.level, family.ordinal, FamilyId(family));
}

// THE EMPTY TOP.  A fresh engine publishes an empty top at epoch 0 and target
// level L, so its family id is just L -- below 1 << 15, and therefore disjoint
// from every regular family, all of which have ordinal >= 1.  It goes through
// its own constructor rather than through FamilyId, which rejects ordinal 0 on
// purpose: an ordinary family with a zero ordinal would be a counter bug, and
// the one legitimate exception should not weaken the check for the rest.
inline uint64_t EmptyTopFamilyId(unsigned levels) {
  if (levels < 1 || levels > kMaxFamilyLevel) {
    throw std::invalid_argument("level arena: L does not fit the nonce's "
                                "level field");
  }
  return levels;
}

inline RebuildNonce EmptyTopNonce(unsigned levels) {
  return PackFamilyNonce(levels, /*ordinal=*/0, EmptyTopFamilyId(levels));
}

// ---------------------------------------------------------------------------
// Windows
// ---------------------------------------------------------------------------
//
// Every member of a family ends at the SAME window end, which is what lets a
// full table and its adoption occupy one another's place in the probe cascade
// without reordering it.  In PREFIX units that end is v * prod(b_j, j < l),
// and the expression is invariant under CanonicalFamily's loop TERM BY TERM:
// dividing v by b_l and raising l by one moves exactly that factor from one
// side of the product to the other.  It is why a per-level ladder needs no
// new window argument, only the per-level product.

inline uint64_t FamilyPrefixWindowEnd(const std::vector<unsigned>& fanouts,
                                      const Family& family) {
  // Levels are one-based.  Without this, level 0 makes `level - 1` wrap and
  // the failure surfaces as an overflow inside a product, which says nothing
  // about the coordinate that was actually wrong.
  if (family.level < 1 || family.ordinal < 1) {
    throw std::invalid_argument("level arena: invalid family coordinate");
  }
  if (family.level > fanouts.size() + 1) {
    throw std::invalid_argument(
        "level arena: family level exceeds the fanout ladder");
  }
  uint64_t product = 1;
  for (unsigned l = 1; l < family.level; ++l) {
    product = CheckedMul(product, fanouts[l - 1], "window end");
  }
  return CheckedMul(family.ordinal, product, "window end");
}

// The uniform ladder as a scalar, for a caller that has no geometry.
inline uint64_t FamilyPrefixWindowEnd(unsigned branching,
                                      const Family& family) {
  if (branching < 2 || family.level < 1 || family.ordinal < 1) {
    throw std::invalid_argument("level arena: invalid family coordinate");
  }
  return CheckedMul(family.ordinal,
                    CheckedPow(branching, family.level - 1, "window end"),
                    "window end");
}

// The same boundary in ACCESS POSITIONS, which is the unit ProbePlan's
// half-open windows are stated in.  One prefix is 64 s r0 positions.
inline uint64_t FamilyWindowEnd(const LevelArenaGeometry& g,
                                const Family& family) {
  if (family.level < 1 || family.level > g.Levels() || family.ordinal < 1) {
    throw std::invalid_argument("level arena: invalid family coordinate");
  }
  // prod(b_j, j < level) is the geometry's own PrefixProduct, computed and
  // checked once at construction.  Recomputing it here would be a second
  // spelling of the number a producer and its consumer have to agree on.
  return CheckedMul(
      CheckedMul(family.ordinal, g.PrefixProduct(family.level), "window end"),
      g.PrefixPositions(), "window end");
}

// ---------------------------------------------------------------------------
// Direct initialization
// ---------------------------------------------------------------------------
//
// Building an engine from a batch of records publishes a FULL top and nothing
// else, then continues as if the hierarchy had reached that state by ordinary
// insertion.  The counters that state implies are all derived from one number:
// H, the count of synthetic completed prefixes the initial top stands for.
//
// The three counters below are in three DIFFERENT units -- prefixes, stash
// flushes, access positions -- and the reason they are named and returned
// together is that mixing them is the mistake this struct exists to prevent.
struct InitialSeed {
  uint64_t prefixes = 0;  // H = D B^(L-1): synthetic completed prefixes
  // Accepted incoming carries per level, ONE-BASED: index 0 is an unused
  // placeholder so that `level_carries[l]` is level l, not a level.  Level l
  // holds
  // H / B^(l-1), which is a multiple of B below the top -- so every non-top
  // digit is zero, i.e. no level holds a partial table.  The top holds D.
  std::vector<uint64_t> level_carries;
  uint64_t stash_flushes = 0;  // r0 H
  uint64_t access_offset = 0;  // 64 s r0 H, which is also 32T
  Family top_family;           // (L, D)
};

inline InitialSeed DirectInitializationSeed(const LevelArenaGeometry& g) {
  InitialSeed seed;
  seed.prefixes = CheckedMul(g.TopDigit(), g.PrefixProduct(g.Levels()), "H");
  seed.level_carries.assign(g.Levels() + 1, 0);
  for (unsigned l = 1; l <= g.Levels(); ++l) {
    seed.level_carries[l] = seed.prefixes / g.PrefixProduct(l);
  }
  seed.stash_flushes = CheckedMul(g.PrefixFlushes(), seed.prefixes, "r0 H");
  seed.access_offset =
      CheckedMul(seed.prefixes, g.PrefixPositions(), "access offset");
  seed.top_family = Family{g.Levels(), g.TopDigit()};
  return seed;
}

// Check the entire declared lifetime before allocating engine storage. Reserve
// direct initialization's synthetic positions even for an empty start, so a
// later Initialize call cannot invalidate the bound. Accepted carries at level
// l are at most floor(positions / carry_positions); preparation may run once
// ahead. Forwarding preserves ordinal * carry_positions and only decreases
// the ordinal, so checking the unforwarded coordinate covers every family.
inline void RequireLifetimeFits(const LevelArenaGeometry& g,
                                uint64_t max_accesses) {
  const uint64_t positions = CheckedAdd(
      DirectInitializationSeed(g).access_offset, max_accesses,
      "initialized lifetime positions");
  for (unsigned level = 1; level <= g.Levels(); ++level) {
    const uint64_t span = CheckedMul(g.PrefixProduct(level),
                                     g.PrefixPositions(), "carry positions");
    const uint64_t next = CheckedAdd(positions / span, 1,
                                     "speculative carry ordinal");
    if (next > kMaxFamilyOrdinal) {
      throw std::overflow_error(
          "level arena: lifetime exceeds the nonce ordinal field");
    }
    // Include the whole window even if the last carry never arrives.
    (void)CheckedMul(next, span, "speculative carry window");
  }

  // Level 1 also covers dense arithmetic without another limit. Write its
  // span as r*u (r = PrefixFlushes <= 8, u = OnlineStashEntries), and its
  // next ordinal as q. Then f = floor(positions/u) < r*q < 2^51, so shifting
  // any flush/prefix counter by eight bits cannot reach the dense ID's bit 63.
  // The padded current-unit end (f+1)*u <= q*r*u fits the checked window,
  // including the next empty unit exposed by draining the final full unit.
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
