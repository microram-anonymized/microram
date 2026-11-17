#pragma once

// The byte-sliced bucket layout, and the types every kernel in this directory
// is phrased in.
//
// A bucket holds 64 entries and is stored TRANSPOSED: byte b of all 64 entries
// sits contiguously in one 64-byte cache line ("byte line" b), so an entry of
// E bytes occupies one byte in each of E lines rather than E bytes in one
// place.  The point is that a byte line is exactly one AVX-512 register, so
// permuting all 64 entries of a bucket by an arbitrary permutation costs one
// instruction per line instead of 64 scalar moves.  Every rebuild kernel here
// is a loop over byte lines applying the same register-resident index vector.
//
// An entry is laid out key | value | tag:
//   - key    key_bytes lines.  The caller's key verbatim up to 15 bytes, 16
//            for the AES-128 rehash of a wider one (see StoredKeyBytes).
//   - value  value_bytes lines, opaque to everything here.
//   - tag    tag_bytes lines of routing tag, pure rebuild scratch.  Probes
//            never read it and every rebuild recomputes it wholesale.
//
// Tag bytes are stored MOST SIGNIFICANT FIRST, which looks backwards and is
// load bearing.  Butterfly level l routes on tag bit l and the bucket index
// carries that bit from then on, so tag byte l/8 is dead once level 8(l/8)+7
// has run.  Under the reversed order the dead bytes are the LAST lines of the
// entry, so "which lines are still live" is a shrinking prefix -- a smaller
// loop bound -- rather than a hole in the middle that every kernel would have
// to branch around.
//
// Occupancy is a uint64 mask per bucket, bit e set iff slot e holds a real
// entry.  Dummies are never materialized; they are unset bits over don't-care
// bytes.  Nothing ever needs to write a dummy, which is why a rebuild moves
// only real data.

#include <immintrin.h>

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <memory>
#include <new>
#include <stdexcept>
#include <string>

#if defined(__linux__)
#include <sys/mman.h>
#endif

#include "src/core/mov_intrinsics.hpp"

namespace microram {
namespace byteslice {

inline constexpr size_t kBucketCapacity = 64;  // one AVX-512 register of bytes

// How a live table is probed, which is a property of the table and not of the
// engine that built it -- so it lives here, beside the layout, rather than in
// either hierarchy's configuration.
//
// A dense table is scanned in full on every access (the current insertion unit,
// and the frozen ones waiting for their carry): its address is fixed, so it
// needs no routing nonce, issues no dummy probe, and leaks nothing positional.
// A hashed table is probed at one key-derived bucket, or at an independent
// dummy one.
enum class TableKind : uint8_t { kDense, kHashed };

// ---------------------------------------------------------------------------
// Stored keys
// ---------------------------------------------------------------------------
//
// A STORED key is what occupies an entry's leading key_bytes byte lines.  Up to
// 15 bytes it is the caller's key verbatim, so a key of 9..15 bytes costs no
// more lines than it has bytes; from 16 bytes it is the AES-128 rehash of the
// caller's key (crypto::AesHashKey128), which is one whole block -- so 16 is
// the widest stored key that exists and everything here is sized for it.
// StoredKeyBytes() is the map from a user key width to the stored one; the
// ORAMs apply it, the kernels below only ever see the result.
inline constexpr size_t kMaxKeyBytes = 16;

inline size_t StoredKeyBytes(size_t user_key_bytes) {
  return user_key_bytes < kMaxKeyBytes ? user_key_bytes : kMaxKeyBytes;
}

// A stored key in the two words the kernels want it in: w0 holds key byte
// lines 0..7 (line l = byte l, little-endian) and w1 lines 8..15.  Implicitly
// constructible from a uint64, so every call site that predates 16-byte keys
// reads and compiles exactly as it did.
struct KeyWords {
  uint64_t w0 = 0;
  uint64_t w1 = 0;

  constexpr KeyWords() = default;
  constexpr KeyWords(uint64_t low) : w0(low) {}  // NOLINT: intentional
  constexpr KeyWords(uint64_t low, uint64_t high) : w0(low), w1(high) {}

  friend bool operator==(const KeyWords& a, const KeyWords& b) {
    return a.w0 == b.w0 && a.w1 == b.w1;
  }
  friend bool operator!=(const KeyWords& a, const KeyWords& b) {
    return !(a == b);
  }
  friend bool operator<(const KeyWords& a, const KeyWords& b) {
    return a.w1 != b.w1 ? a.w1 < b.w1 : a.w0 < b.w0;
  }
};

// Entry field widths in bytes. Adjustable at runtime; the byte-sliced layout
// needs no padding or alignment per field. key_bytes is capped at 16 (one AES
// block, see kMaxKeyBytes) and tag_bytes at 8 (the tag must fit a uint64).
//
// Tag byte order is REVERSED (most significant tag byte first): tag byte tb --
// the one holding butterfly bits [8tb, 8tb+8) -- is stored at byte line
// TagOffset() + tag_bytes-1-tb, not TagOffset()+tb.  That is what makes tag
// pruning free: level l consumes bit l, after which the bucket index already
// determines bits [0, l], so tag byte tb is dead once level 8tb+7 has run.
// The dead bytes are the LOW ones, and under the reversed order they occupy
// the END of the entry, so "the lines still worth routing" is a prefix
// (RoutedLines) and pruning is just a smaller loop bound -- no branch, no
// second range in the hot loop.  The radix digit byte is the most significant
// tag byte, hence line TagOffset(): it is never pruned, which is exactly what
// the post-butterfly radix pass needs.
struct Layout {
  size_t key_bytes = 8;
  size_t value_bytes = 16;
  size_t tag_bytes = 4;
  // Where the radix digit sits WITHIN the digit byte line, in bits.  0 is the
  // reserved-byte layout, in which the digit owns a whole tag byte and the
  // radix kernels can compare that byte to `q` directly.
  //
  // The digit is at most kMaxRadix = 7, i.e. three bits, and the top index
  // byte usually has three or more bits to spare, so a reserved byte is a
  // whole 64-byte line per bucket -- moved at every butterfly level, every
  // copy and every re-tag, and the one tag line pruning can never retire --
  // bought for three bits.  Setting this to `index_bits % 8` packs the digit
  // into the top index byte instead and drops tag_bytes by one whenever
  // `index_bits % 8` is 1 to 5.  Above 5 the digit would straddle a byte
  // boundary and the reserved byte is kept, which is also the case where
  // packing would save nothing.
  //
  // The ORAM derives this from its own geometry
  // (RoutingDigitBits) and overwrites whatever the caller passed; a kernel
  // test that builds a Layout by hand gets 0 and the original behaviour.
  size_t digit_bits = 0;

  // Two layouts are the same layout iff all four fields are: every offset
  // below is a function of them.  Views of one table held by different
  // phases have to compare equal, or the same bytes are read at different
  // line offsets.
  friend bool operator==(const Layout& a, const Layout& b) {
    return a.key_bytes == b.key_bytes && a.value_bytes == b.value_bytes &&
           a.tag_bytes == b.tag_bytes && a.digit_bits == b.digit_bits;
  }
  friend bool operator!=(const Layout& a, const Layout& b) { return !(a == b); }

  size_t EntryBytes() const { return key_bytes + value_bytes + tag_bytes; }
  size_t TagOffset() const { return key_bytes + value_bytes; }
  size_t BucketBytes() const { return EntryBytes() * kBucketCapacity; }

  // Byte line holding butterfly bit `bit` (i.e. tag byte bit/8).
  size_t TagLine(unsigned bit) const {
    return TagOffset() + tag_bytes - 1 - (bit >> 3);
  }
  // Byte line holding the radix digit (the most significant tag byte, where
  // the kRadixDigit map puts it).  The digit occupies the three bits above
  // `digit_bits`, which is what lets one byte carry both it and the top index
  // bits; the kernels recover it with NormalizeDigitLine (shift down by
  // digit_bits, mask to 3 bits), and that is the only spelling of the rule.
  size_t DigitLine() const { return TagOffset(); }
  // Lines that still carry live data once butterfly bits [0, bit] have been
  // routed: the payload plus every tag byte no level has consumed yet.  A
  // MergeSplit on `bit` must WRITE this many lines; it separately READS
  // TagLine(bit), which for bit = 7 mod 8 is the byte it just retired and so
  // may already sit past the prefix.
  size_t RoutedLines(unsigned bit) const {
    return EntryBytes() - ((bit + 1) >> 3);
  }
  // Payload only (key | value, plus the caller's meta lines folded into
  // value): what a phase that will never route on a tag again has to move --
  // the fixed-level fold, the 0.25 -> 0.5 contraction, the radix pass, the
  // stash merges and the dense scatters, all of which are followed by a fresh
  // ComputeRoutingTags before any tag is read again.
  size_t PayloadLines() const { return TagOffset(); }
  // The 1-byte entry metadata folded into the payload: the LAST payload line.
  // Its top bit is the erasure tombstone (kMetaErased, see the meta-byte
  // helpers in cpu_byteslice_meta.hpp); bit 5 qualifies it (kMetaUnshadowed)
  // and bit 6 is the merged residual offer's class mark inside a range table
  // (kMetaResidualClass).
  // StashLayout::MetaOffset() is the same line, reached from the other side.
  size_t MetaLine() const { return TagOffset() - 1; }
};

// SIZE ARITHMETIC THAT REFUSES RATHER THAN WRAPS.  A width or a count here is
// public input -- a caller's value width, a geometry's bucket count -- and a
// wrapped product is not an error anybody sees: it is a small allocation that
// the code then writes a large amount into.  So the few places that turn
// widths into byte counts before allocating go through these, and none of
// them is on a hot path.
inline size_t CheckedSizeAdd(size_t a, size_t b, const char* what) {
  if (a > std::numeric_limits<size_t>::max() - b) {
    throw std::length_error(std::string(what) + " overflows size_t");
  }
  return a + b;
}

inline size_t CheckedSizeMul(size_t a, size_t b, const char* what) {
  if (a != 0 && b > std::numeric_limits<size_t>::max() / a) {
    throw std::length_error(std::string(what) + " overflows size_t");
  }
  return a * b;
}

// Refuses a layout whose entry or bucket width is not representable, so that
// EntryBytes() and BucketBytes() -- plain arithmetic, because the kernels
// call them per bucket -- are exact for every layout an engine was built
// with.  Engines call it once, where they derive their layout.
inline void ValidateLayoutWidths(const Layout& layout) {
  const size_t entry = CheckedSizeAdd(
      CheckedSizeAdd(layout.key_bytes, layout.value_bytes, "entry width"),
      layout.tag_bytes, "entry width");
  (void)CheckedSizeMul(entry, kBucketCapacity, "bucket width");
}

// Construction and storage prediction must check the bucket COUNT as well
// as the width. Checking a tally after this multiplication is too late.
inline size_t CheckedTableBytes(size_t buckets, const Layout& layout) {
  ValidateLayoutWidths(layout);
  return CheckedSizeMul(buckets, layout.BucketBytes(), "table bytes");
}

// ---------------------------------------------------------------------------
// Huge pages for the big allocations
// ---------------------------------------------------------------------------
//
// The engines keep their big arenas in few large allocations
// -- the level arena's per-level buffers, the tree's `buckets` -- and every
// access walks them at random bucket granularity, so at 2^24 the working set is gigabytes touched through 4 KiB
// PTEs and the dTLB reach (1.5-3k entries, i.e. 6-12 MiB on a Zen core) covers
// a fraction of a percent of it.  A 2 MiB-aligned mapping under MADV_HUGEPAGE
// covers the same arena in 512x fewer entries.
//
// Only allocations at or above `kHugePageBytes` take the wide alignment:
// below it the rounding waste would dwarf the allocation, and the thousands
// of per-value scratch buffers this header also serves are all tiny.  A
// request that is honoured is 2 MiB-ALIGNED as well as advised, because
// MADV_HUGEPAGE on a misaligned range can only back the aligned interior.
//
// The policy is process-global and explicit rather than a knob on each
// engine's Options: it is an allocator property, both engines share the
// allocator, and an A/B wants to move it for a whole process.  It is read
// from `MICRORAM_HUGE_PAGES` (0 turns it off) once, so a sweep script can
// move it without a rebuild, and `SetHugePagePolicy` overrides that.
//
// **On by default**: it lowers dTLB misses on the hierarchical engine's
// random bucket accesses; the tree's path walk keeps a much smaller TLB
// working set, so it gains little there.  It costs at most one 2 MiB
// rounding per large allocation (a negligible fraction of a multi-GiB arena)
// and is inert wherever transparent huge pages (THP) are unavailable.
enum class HugePagePolicy { kOff, kOn };

inline constexpr size_t kHugePageBytes = size_t{2} << 20;

// THE POLICY IS A PLAIN PROCESS GLOBAL, read without synchronization by
// every allocating thread (AllocateAligned64 reads it twice per allocation).
// Set it only while no other thread allocates through this header: before
// the first map is built, or between maps with every map's threads quiesced.
// An engine allocates on its owner, helper and worker threads too.
inline HugePagePolicy& MutableHugePagePolicy() {
  static HugePagePolicy policy = [] {
    const char* env = std::getenv("MICRORAM_HUGE_PAGES");
    if (env == nullptr) return HugePagePolicy::kOn;
    return env[0] == '0' ? HugePagePolicy::kOff : HugePagePolicy::kOn;
  }();
  return policy;
}
inline HugePagePolicy CurrentHugePagePolicy() { return MutableHugePagePolicy(); }
inline void SetHugePagePolicy(HugePagePolicy p) { MutableHugePagePolicy() = p; }

// Whether THIS allocation took the huge-page path: the policy is on, the
// request is big enough to be worth 2 MiB of alignment, and the platform has
// madvise at all.  A pointer's deleter has to agree with its allocation, so
// the decision is one function both sides call.
inline bool UseHugePages(size_t bytes) {
#if defined(__linux__) && defined(MADV_HUGEPAGE)
  return bytes >= kHugePageBytes &&
         CurrentHugePagePolicy() == HugePagePolicy::kOn;
#else
  (void)bytes;
  return false;
#endif
}

// The alignment is carried IN the deleter rather than recomputed from the
// size, because the policy may move between an allocation and its release
// (a benchmark that sweeps it) and `operator delete[]` must be handed the
// same alignment `operator new[]` was.
struct Aligned64Deleter {
  size_t align = 64;
  void operator()(uint8_t* p) const {
    ::operator delete[](p, std::align_val_t{align});
  }
};
using Aligned64Ptr = std::unique_ptr<uint8_t[], Aligned64Deleter>;

// A std::vector allocator whose storage starts on a 128-byte boundary and is
// padded to whole 128-byte pairs: scratch one thread writes while another
// thread is on its critical path must not share a line, or the pair the L2
// spatial prefetcher fetches, with anything else on the heap.
template <class T>
struct LineAllocator {
  using value_type = T;
  static constexpr size_t kAlign = 128;
  LineAllocator() = default;
  template <class U>
  LineAllocator(const LineAllocator<U>&) noexcept {}
  static size_t Bytes(size_t n) {
    // Check the product and its padding together before either can wrap.
    // This is also used by the byte bill, outside std::vector's size checks.
    if (n > (std::numeric_limits<size_t>::max() - (kAlign - 1)) / sizeof(T)) {
      throw std::bad_array_new_length();
    }
    return (n * sizeof(T) + kAlign - 1) / kAlign * kAlign;
  }
  T* allocate(size_t n) {
    return static_cast<T*>(::operator new(Bytes(n), std::align_val_t{kAlign}));
  }
  void deallocate(T* p, size_t n) noexcept {
    ::operator delete(p, Bytes(n), std::align_val_t{kAlign});
  }
  template <class U>
  bool operator==(const LineAllocator<U>&) const noexcept { return true; }
  template <class U>
  bool operator!=(const LineAllocator<U>&) const noexcept { return false; }
};

// The ALIGNMENT this allocation is made at, which is also the granularity its
// length is rounded to.  One function so that the request, the release and the
// byte bill cannot disagree about which of the two paths an allocation took.
inline size_t Aligned64Alignment(size_t bytes) {
  return UseHugePages(bytes) ? kHugePageBytes : size_t{64};
}

// What AllocateAligned64 asks the allocator to reserve for a request of
// `bytes`: the request rounded up to that alignment.  It is a LOWER bound on
// the resident cost -- what a general-purpose allocator does inside its own
// size classes is not visible from here -- and it is the only rounding this
// code performs itself, which is why a report that separates requested from
// reserved bytes separates exactly these two numbers.
inline size_t Aligned64AllocationBytes(size_t bytes) {
  const size_t align = Aligned64Alignment(bytes);
  // A request within one alignment of SIZE_MAX would round to zero.
  if (bytes > std::numeric_limits<size_t>::max() - (align - 1)) {
    throw std::bad_array_new_length();
  }
  return (bytes + align - 1) & ~(align - 1);
}

// No object can be larger than PTRDIFF_MAX, so a request that large is
// refused before the round-up rather than handed to operator new.  The bound
// leaves room for the huge-page rounding, which then cannot pass it either.
// It also gives the compiler the proof it needs: without it, GCC's range
// analysis cannot bound a size built from checked arithmetic and warns
// (-Walloc-size-larger-than) wherever such a size is inlined into here.
inline constexpr size_t kMaxAligned64Request =
    static_cast<size_t>(std::numeric_limits<std::ptrdiff_t>::max()) -
    kHugePageBytes;

inline Aligned64Ptr AllocateAligned64(size_t bytes) {
  if (bytes > kMaxAligned64Request) throw std::bad_array_new_length();
  if (!UseHugePages(bytes)) {
    return Aligned64Ptr(
        static_cast<uint8_t*>(::operator new[](bytes, std::align_val_t{64})),
        Aligned64Deleter{64});
  }
  // Round the LENGTH up too: madvise takes whole pages, and an arena whose
  // last partial page is not advised leaves its tail on 4 KiB entries.
  const size_t rounded = Aligned64AllocationBytes(bytes);
  uint8_t* p = static_cast<uint8_t*>(
      ::operator new[](rounded, std::align_val_t{kHugePageBytes}));
#if defined(__linux__) && defined(MADV_HUGEPAGE)
  // Advisory: a kernel with THP off, or one that cannot find the contiguous
  // frames, refuses and the mapping stays on 4 KiB pages.  That is a
  // performance outcome, not an error, so the return value is deliberately
  // unchecked -- `AnonHugePages` in /proc/self/smaps is what says whether it
  // took, and the benchmark reports it.
  (void)::madvise(p, rounded, MADV_HUGEPAGE);
#endif
  return Aligned64Ptr(p, Aligned64Deleter{kHugePageBytes});
}

// ---------------------------------------------------------------------------
// AllocationTally
// ---------------------------------------------------------------------------
//
// A running total over allocation REQUESTS: how many there were, how many
// bytes they asked for, and how many the allocator was asked to reserve once
// this file's own rounding is applied.
//
// The two numbers are kept apart on purpose.  A byte bill built out of
// `requested` is a statement about the design -- it is what the geometry and
// the layout say the engine needs -- while `reserved` is a statement about
// this process, and moves when the huge-page policy does.  Reporting one as
// the other is how a 2 MiB rounding per large buffer disappears from a
// memory figure, or appears in a storage bound it was never part of.
//
// It tallies requests; it does not allocate, and nothing here has to be the
// thing that later frees them.
struct AllocationTally {
  size_t allocations = 0;
  size_t requested = 0;
  size_t reserved = 0;

  // `count` buffers of `bytes` each, from AllocateAligned64.
  void AddAligned64(size_t bytes, size_t count = 1) {
    if (bytes == 0 || count == 0) return;
    allocations = CheckedSizeAdd(allocations, count, "allocation count");
    requested = CheckedSizeAdd(
        requested, CheckedSizeMul(count, bytes, "requested bytes"),
        "requested bytes");
    reserved = CheckedSizeAdd(
        reserved,
        CheckedSizeMul(count, Aligned64AllocationBytes(bytes),
                       "reserved bytes"),
        "reserved bytes");
  }

  // `count` buffers of `bytes` each from the ordinary allocator -- `new[]`,
  // or a vector's reservation.  No rounding is modelled: what such an
  // allocator rounds to is its own affair and not visible here.
  void AddPlain(size_t bytes, size_t count = 1) {
    if (bytes == 0 || count == 0) return;
    const size_t total = CheckedSizeMul(count, bytes, "requested bytes");
    allocations = CheckedSizeAdd(allocations, count, "allocation count");
    requested = CheckedSizeAdd(requested, total, "requested bytes");
    reserved = CheckedSizeAdd(reserved, total, "reserved bytes");
  }

  void Add(const AllocationTally& other) {
    allocations =
        CheckedSizeAdd(allocations, other.allocations, "allocation count");
    requested = CheckedSizeAdd(requested, other.requested, "requested bytes");
    reserved = CheckedSizeAdd(reserved, other.reserved, "reserved bytes");
  }

  // Equality is what lets a constructor CHECK the static predictor a byte
  // bill quotes it by, instead of the two agreeing today and drifting at the
  // next allocation somebody adds.
  friend bool operator==(const AllocationTally& a, const AllocationTally& b) {
    return a.allocations == b.allocations && a.requested == b.requested &&
           a.reserved == b.reserved;
  }
  friend bool operator!=(const AllocationTally& a, const AllocationTally& b) {
    return !(a == b);
  }

  std::string Describe() const {
    return std::to_string(allocations) + " allocations, " +
           std::to_string(requested) + " B requested, " +
           std::to_string(reserved) + " B reserved";
  }
};

// num_buckets byte-sliced buckets plus one occupancy mask per bucket.
//
// A table a butterfly routes end to end is a power of two, but that is a
// property of the CALLER, not of this allocation: at a level of fanout B > 2 a
// mixed-radix table is r * 2^k buckets with r odd (3, 5 or 7), and both the
// radix kernels and their tests allocate one.  So the shape rule
// lives at the kernels that need it -- ButterflyRouteStash* assert
// route_levels <= log2(num_buckets), the radix passes assert
// num_buckets == r << block_bits -- and this only insists on a nonempty table.
struct Table {
  Layout layout;
  size_t num_buckets = 0;
  Aligned64Ptr data;
  std::unique_ptr<uint64_t[]> masks;

  static Table Create(size_t num_buckets, Layout layout) {
    assert(layout.key_bytes >= 1 && layout.key_bytes <= kMaxKeyBytes);
    assert(layout.tag_bytes >= 1 && layout.tag_bytes <= 8);
    assert(num_buckets > 0);
    Table t;
    t.layout = layout;
    t.num_buckets = num_buckets;
    t.data = AllocateAligned64(CheckedTableBytes(num_buckets, layout));
    // make_unique<T[]> value-initializes scalar elements, so masks are already
    // zero and need no second full-array memset.
    t.masks = std::make_unique<uint64_t[]>(num_buckets);
    return t;
  }

  uint8_t* Bucket(size_t b) { return data.get() + b * layout.BucketBytes(); }
  const uint8_t* Bucket(size_t b) const {
    return data.get() + b * layout.BucketBytes();
  }
};

// Non-owning view used when a table occupies a region of a larger arena.  The
// level-arena engine preallocates its banks and inboxes once and hands every
// merge views of regions inside them (src/oram/levelarena/DESIGN.md).
struct TableView {
  Layout layout;
  size_t num_buckets = 0;
  uint8_t* data = nullptr;
  uint64_t* masks = nullptr;

  uint8_t* Bucket(size_t b) { return data + b * layout.BucketBytes(); }
  const uint8_t* Bucket(size_t b) const {
    return data + b * layout.BucketBytes();
  }
};

inline TableView View(Table& t) {
  return TableView{t.layout, t.num_buckets, t.data.get(), t.masks.get()};
}

// Scalar accessors for tests and input generation (not perf-critical): entry
// byte b of slot e lives at bucket[b * 64 + e].
inline void WriteEntry(uint8_t* bucket, size_t slot, const uint8_t* entry,
                       size_t entry_bytes) {
  for (size_t b = 0; b < entry_bytes; ++b) {
    bucket[b * kBucketCapacity + slot] = entry[b];
  }
}

inline void ReadEntry(const uint8_t* bucket, size_t slot, uint8_t* entry,
                      size_t entry_bytes) {
  for (size_t b = 0; b < entry_bytes; ++b) {
    entry[b] = bucket[b * kBucketCapacity + slot];
  }
}

inline unsigned Popcount64(uint64_t v) {
  return static_cast<unsigned>(_mm_popcnt_u64(v));
}

// The low `count` bits set.  PRECONDITION: count <= 64 (every caller passes a
// popcount, a minimum of popcounts, a lane count or a width that is).  BZHI
// reads only bits 7:0 of `count`, so it saturates to all ones for 64..255 and
// wraps from 256: LowMask64(256) is 0, LowMask64(257) is 1.  It avoids a
// secret-count branch when this helper is used by final dummy
// filtering/contraction.
inline uint64_t LowMask64(unsigned count) {
  return _bzhi_u64(~uint64_t{0}, count);
}

// ---------------------------------------------------------------------------
// Stored key helpers (scalar; the vector paths are further down)
// ---------------------------------------------------------------------------

// Drops every bit above key_bytes, so a stored key has one canonical
// representation whatever the caller handed in.
inline KeyWords MaskKey(KeyWords key, size_t key_bytes) {
  if (key_bytes >= kMaxKeyBytes) return key;
  if (key_bytes >= 8) {
    key.w1 &= LowMask64(static_cast<unsigned>(8 * (key_bytes - 8)));
    return key;
  }
  return KeyWords{key.w0 & LowMask64(static_cast<unsigned>(8 * key_bytes)), 0};
}

// take_b ? b : a, with no branch on `take_b` (it is derived from `found` on the
// probe path, which is secret).
inline KeyWords ObliSelectKey(KeyWords a, KeyWords b, bool take_b) {
  return KeyWords{core::obliSelectU64(a.w0, b.w0, take_b),
                  core::obliSelectU64(a.w1, b.w1, take_b)};
}

// Writes / reads the key of one slot of a byte-sliced bucket.  Same fixed
// address sequence for every key value, so these are safe on secret keys.
inline void WriteSlotKey(uint8_t* bucket, size_t slot, size_t key_bytes,
                         KeyWords key) {
  const size_t low = key_bytes < 8 ? key_bytes : 8;
  for (size_t kb = 0; kb < low; ++kb) {
    bucket[kb * kBucketCapacity + slot] =
        static_cast<uint8_t>(key.w0 >> (8 * kb));
  }
  for (size_t kb = 8; kb < key_bytes; ++kb) {
    bucket[kb * kBucketCapacity + slot] =
        static_cast<uint8_t>(key.w1 >> (8 * (kb - 8)));
  }
}

inline KeyWords ReadSlotKey(const uint8_t* bucket, size_t slot,
                            size_t key_bytes) {
  KeyWords key;
  const size_t low = key_bytes < 8 ? key_bytes : 8;
  for (size_t kb = 0; kb < low; ++kb) {
    key.w0 |= uint64_t{bucket[kb * kBucketCapacity + slot]} << (8 * kb);
  }
  for (size_t kb = 8; kb < key_bytes; ++kb) {
    key.w1 |= uint64_t{bucket[kb * kBucketCapacity + slot]} << (8 * (kb - 8));
  }
  return key;
}
// Ceiling log2, with zero mapped to zero for the existing geometry helpers.
// Shifting the input down also handles values above the largest power of two
// without shifting a 1 beyond size_t's width.
inline unsigned CeilLog2(size_t value) {
  size_t remaining = value == 0 ? 0 : value - 1;
  unsigned bits = 0;
  while (remaining != 0) {
    remaining >>= 1;
    ++bits;
  }
  return bits;
}

// An alias of CeilLog2 kept under this name for existing call sites: exact
// for powers of two, rounds other inputs upward.
inline unsigned Log2Exact(size_t value) {
  return CeilLog2(value);
}

}  // namespace byteslice
}  // namespace microram

namespace std {
// So a stored key can key an unordered_map the way a uint64 did.  A stored key
// is either a caller's raw key or a PRF output; the usual 64-bit finalizer over
// the two words is enough for a hash table either way.
template <>
struct hash<microram::byteslice::KeyWords> {
  size_t operator()(const microram::byteslice::KeyWords& key) const noexcept {
    uint64_t z = key.w0 ^ (key.w1 * 0xD6E8FEB86659FD93ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return static_cast<size_t>(z ^ (z >> 31));
  }
};
}  // namespace std
