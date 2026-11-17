// The TOP's compaction (src/oram/levelarena/DESIGN.md, "Top compaction and
// residuals"): a full level A and an inbox carry B merged into the other bank
// C, over real arena slots, through the same LevelMergeJob every other level
// uses.  The top is where every live entry eventually lands, so a lost,
// duplicated or misplaced key here is a wrong answer for every later access.
//
// WHAT IS DIFFERENT ABOUT THE TOP, and therefore what this file is for:
//
//   - its digit is FIXED at D, a power of two (the geometry refuses any
//     other: only a binary top has a certified preparation), and its route
//     is one binary butterfly over all of T with no radix pass, so even
//     D = 8 needs no radix-eight kernel; its older operand is
//     the whole of A rather than a partial at digit j-1;
//   - it runs TWO residual passes, both fused.  The pass that ends A's route
//     -- its last butterfly level -- finishes C's route, so A's sheds are
//     offered back right then through the one-page DFS distributor, and what
//     will not fit is RETAINED; the merge's class-marked pass then rides the
//     sweep, carrying that retained carry (A's class, a one-page DFS leaf)
//     against B's tier (the fresher class, offered directly), with the
//     sweep's own shed drain-only;
//   - its carry is never installed.  The sweep reads B in the inbox, and the
//     block digit saying which of C's D blocks each of B's entries belongs to
//     is RECOMPUTED from the key, because B was published under another map;
//   - and it is the ONE rebuild allowed to forget a tombstone.  It does so at
//     two moments: every tombstone that reaches C is dropped LAST, over C and
//     over the tier beside it, and one that shadows nothing
//     (`kMetaUnshadowed`) is dropped EARLIER still, as the sweep reads the
//     source holding it, so it never takes a slot in C to begin with.  The
//     `unshadowed` cases are what says those two agree.
//
// THE CLAIM EVERY CASE MAKES.  Over C's main plus its tier, every key whose
// newest copy is live appears exactly once and with that copy's value; every
// key whose newest copy is a tombstone is GONE; every entry sits in the bucket
// its key selects; and neither A nor B -- main, tier or mask -- has a byte
// changed, because both are published storage a request may be probing.
//
// FIVE OF THESE CASES GUARD THE OFFER'S CLASS ORDERING, not a
// demonstration.  The merge's pass rides its own sweep, so the sweep's
// shed is drain-only and the only thing that can resolve it afterwards is
// ResidualLeftoverDedupRange -- which reaches a range LEFTOVER and nothing
// else.  What keeps the A-class copy of a shed key a leftover is that the
// offer allocates A's class out of the lanes that were free BEFORE B's tier
// cleared any (PlanResidualOfferMerge), so a bucket that was full when the
// sweep shed into it absorbs nothing of A's.  Allocate the two classes
// together instead, without resolving first, and D = 1, 4, the default-key
// case and `poisoned, D=1` each publish one key twice -- the staler copy in
// C's main, the fresher in its tier.
//
// AND TWO ORACLES FOR THE RE-TAG, which is the one thing here with no model:
// the digits this merge computes in a register are compared against the bytes
// a real CopyAndRetagRange would have written into a copy of the bucket, and
// then a whole sweep under the recomputed digits is compared, byte for byte,
// against the same sweep over a privately re-tagged carry -- the existing
// fixed-merge path used as a test oracle, and the reason production needs no
// copy of the carry at all.

#include <immintrin.h>

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_slots.hpp"
#include "src/oram/rebuild/cpu_byteslice_dedup_network.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
namespace ts = microram::byteslice::test_support;

int failures = 0;

// Counts rather than exits, so one broken case does not hide the rest.
void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

template <class Fn>
bool Throws(Fn&& fn) {
  try {
    fn();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

bs::SubtaskBudget WholeBudget() {
  return bs::SubtaskBudget{~size_t{0}, ~size_t{0}, ~size_t{0},
                           ~size_t{0}, ~size_t{0}, ~size_t{0}};
}
bs::SubtaskBudget SlicedBudget() {
  return bs::SubtaskBudget{3, 2, 2, 24, 5, 3};
}

// ---------------------------------------------------------------------------
// The top's flat destination index
// ---------------------------------------------------------------------------
//
// The merge re-tags under a map whose digit sits where the LAYOUT keeps it;
// the flat form is the same map with the digit packed straight above the index
// bits, so that map(tag) IS the bucket number in C.  A fixture needs the flat
// one twice: to pick keys that land on a chosen bucket, and to say where every
// surviving entry should have ended up.
bs::RoutingIndexMap FlatTopMap(const la::MergeShape& shape) {
  bs::RoutingIndexMap map;
  if (!shape.has_radix_pass()) return map;  // D = 1 is kRaw
  map.kind = bs::TagMapKind::kRadixDigit;
  map.low_bits = shape.block_bits;
  map.modulus = shape.odd_part;
  map.digit_shift = shape.block_bits;
  return map;
}

// How many tag bits the flat index occupies: the index bits, plus the three a
// digit is reserved in wherever a digit exists at all.
unsigned FlatTopBits(const la::MergeShape& shape) {
  return shape.block_bits +
         (shape.has_radix_pass() ? bs::kRoutingDigitBits : 0u);
}

// The low `bits` bits of each key's tag under `map`, which for the flat map is
// where the key belongs and for a kRaw one is which bucket of a power-of-two
// table holds it.
std::vector<size_t> TagIndices(const bs::Layout& layout,
                               const bs::RebuildNonce& nonce,
                               const bs::RoutingIndexMap& map, unsigned bits,
                               const bs::AesTagKeys& aes_keys,
                               const std::vector<bs::KeyWords>& keys) {
  std::vector<size_t> indices;
  indices.reserve(keys.size());
  bs::Table probe = ts::ZeroedTable(1, layout);
  for (size_t i = 0; i < keys.size(); i += bs::kBucketCapacity) {
    const size_t n = std::min(bs::kBucketCapacity, keys.size() - i);
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      ts::PlantEntry(layout, probe.Bucket(0), slot,
                     keys[i + std::min(slot, n - 1)], 0);
    }
    bs::TableView v = bs::View(probe);
    bs::ComputeRoutingTags(v, nonce.real_lo, nonce.real_hi, map, bits,
                           aes_keys);
    for (size_t slot = 0; slot < n; ++slot) {
      indices.push_back(static_cast<size_t>(
          ts::SlotTagBitsOf(layout, probe.Bucket(0), slot, bits)));
    }
  }
  return indices;
}

// ---------------------------------------------------------------------------
// One case
// ---------------------------------------------------------------------------

struct Case {
  const char* name = "";
  unsigned branching = 4;
  unsigned levels = 2;
  unsigned top_digit = 4;  // D
  unsigned prefix_flushes = 2;
  size_t stash_buckets = 1;
  // Eight buckets rather than the default one, and the reason is the FIXTURE
  // rather than the design.  Forcing a shed means aiming many keys at ONE
  // destination index, and everything that then fails to be placed -- the
  // preparation's retained carry and the sweep's shed alike -- carries that
  // same index into the merge pass's range table, where one index gets one
  // pile.  The table's width comes from the POOL's width (PlanResidualRange),
  // so a wider tier is what buys the pile room.  In a real hierarchy the
  // residuals of one pass are spread by their hashes and this does not arise;
  // here it is the difference between a fixture that tests the wiring and one
  // that reports a certified-rare overflow as a defect.
  size_t tier_buckets = 8;
  size_t key_bytes = 8;
  size_t value_bytes = 8;
  size_t tag_bytes = 4;
  // The PACKED tag layout: the radix digit shares the top index byte instead
  // of getting a reserved one of its own (Layout::digit_bits).
  size_t digit_bits = 0;
  // Tombstones on two different key residues, one per operand, so that one
  // case covers all three shapes: a key deleted by A and rewritten by B (it
  // survives with B's value), a key live in A and deleted by B (it vanishes),
  // and a key deleted in both.
  bool tombstones = false;
  // Qualify the tombstones that shadow nothing with `kMetaUnshadowed`, which
  // moves WHEN they are forgotten: not at the finish's trailing kDropErased
  // over C, but as each source is read into it -- the sweep ANDs them out of
  // its own copy of the carry's occupancy word, so they never take a slot in
  // the output at all.  The claim this makes is that the two are the SAME
  // forgetting: a case with the flag is checked against the same model as one
  // without, because bit 5 changes nothing about which keys are live.  It is
  // the only bit in this file the engine acts on early, and the only one a
  // fixture can set wrongly and get a false failure from -- see `meta_of`.
  bool unshadowed = false;
  // A holds nothing: the first compaction of a hierarchy's life, and the one
  // shape in which the preparation routes an empty table.
  bool empty_top = false;
  // Scribble over every stored tag byte of the carry -- its digit line
  // included -- after it is published.  The merge must not notice, which is
  // what says the per-bucket re-tag really is the whole of what it reads.
  bool poison_carry_tags = false;
  // Keys aimed at ONE final bucket of C.  `forced_older` overloads it during
  // the preparation's route, so A sheds and its retained carry is nonempty;
  // `forced_fresh` then gives B entries for that same, now full, bucket, so
  // the sweep sheds too.  Both classes of the merge's pass are then loaded.
  //
  // A MARGIN, not a threshold: how many keys it takes depends on where the
  // rest of the load fell, which depends on the instance key.  RunAndReport's
  // two "nothing shed" guards are what catch a case that slid below the line
  // -- and the range-table pile above is what stops the counts from simply
  // being raised until nothing can be in doubt.
  size_t forced_older = 0;
  size_t forced_fresh = 0;
  // B carries a (shadowing) tombstone for every `forced_older` key it has room
  // for.  Those keys overload one bucket of C, so some of their only A copies
  // are in the RETAINED carry rather than in C -- the one place the sweep's
  // dedup cannot reach -- and it is the merge pass's staler class that has to
  // be cleared by the tombstone before the sweep omits it.
  bool erase_retained = false;
  // B's TIER carries a tombstone for the first kTierErasures `forced_older`
  // keys, while `forced_fresh` live keys in B's main target the same full
  // bucket of C: REPORT.tex's local counterexample at native capacity.  A
  // schedule that merged B's main before its tier's tombstones cleared C's
  // copies sheds every forced live key; the resolved reference keeps them.
  bool erase_in_tier = false;
  bool sliced = false;
  // The instance's AES key, as a seed.  0 is the fixed public schedule the
  // standalone kernels use, which one case keeps so the plumbing is exercised
  // both ways.
  uint64_t key_seed = 0x70FDEAD70Full;
};

bs::Layout LayoutOf(const Case& c) {
  bs::Layout layout;
  layout.key_bytes = c.key_bytes;
  layout.value_bytes = c.value_bytes;
  layout.tag_bytes = c.tag_bytes;
  layout.digit_bits = c.digit_bits;
  return layout;
}

// The Case's usual B = 4 for a digit it admits, else 8: the geometry refuses a
// top wider than its fanout.
unsigned WidestUsualFanoutFor(unsigned digit) { return digit <= 4 ? 4 : 8; }

la::LevelArenaGeometry::Params ParamsOf(const Case& c) {
  la::LevelArenaGeometry::Params p;
  p.branching = c.branching;
  p.levels = c.levels;
  p.top_digit = c.top_digit;
  p.prefix_flushes = c.prefix_flushes;
  p.stash_buckets = c.stash_buckets;
  p.tier_buckets = c.tier_buckets;
  return p;
}

using Model = std::map<bs::KeyWords, ts::LiveEntry>;

std::string Describe(const Case& c) {
  return std::string(c.name) + " (B=" + std::to_string(c.branching) +
         " D=" + std::to_string(c.top_digit) + ")";
}

// Overwrite every stored tag byte of a table.  A carry's tags are SCRATCH
// (its bucket positions are valid, its stored tag bytes may be stale) and this merge recomputes the one thing it reads out of them, so a
// poisoned carry has to produce the identical output.
void PoisonTags(const bs::Layout& layout, uint8_t* bucket) {
  std::memset(bucket + layout.TagOffset() * bs::kBucketCapacity, 0xE7,
              layout.tag_bytes * bs::kBucketCapacity);
}

struct CaseResult {
  Model live;                // C's main plus its tier
  bool unique = true;
  uint64_t out_digest = 0;   // C's bytes and its tier's, for split-vs-unsplit
  size_t retained = 0;       // what the preparation's pass could not place
  size_t tier_entries = 0;   // what the merge's pass could not place
  // Retained entries whose key B deletes: the range-table dedup must act.
  size_t retained_erased = 0;
  // The resolved reference's complete-home excess, sum_v (X_v - 64)+ over the
  // live winners' final homes: what the tier must hold exactly.
  size_t reference_excess = 0;
};

// Stages that ran in more than one lane, over every laned run, and lanes the
// helper threads ran.
uint64_t g_laned_stages = 0;
// Resumed runs whose residual charges were checked against the estimate.
uint64_t g_residual_charge_checks = 0;
uint64_t g_dfs_preparations = 0;  // top preparations that distributed
uint64_t g_dfs_finishes = 0;      // top finishes that distributed
// Of those, offer stages whose lanes cleared private range masks.
uint64_t g_private_mask_stages = 0;
std::atomic<uint64_t> g_helper_lanes{0};

// Threads that run lanes of one job's shared phases until stopped: the test's
// stand-in for an owner group's helpers.
class HelperThreads {
 public:
  HelperThreads(la::LevelMergeJob* job, unsigned count,
                const bs::SubtaskBudget& budget) {
    if (count == 0) return;
    job->AttachHelpers(&event_, &owner_, budget);
    for (unsigned i = 0; i < count; ++i) {
      threads_.emplace_back([this, job] {
        while (!stop_.load(std::memory_order_acquire)) {
          if (job->HelpOnce()) {
            g_helper_lanes.fetch_add(1, std::memory_order_relaxed);
          } else {
            std::this_thread::yield();
          }
        }
      });
    }
  }
  ~HelperThreads() { Stop(); }
  void Stop() {
    stop_.store(true, std::memory_order_release);
    for (std::thread& t : threads_) {
      if (t.joinable()) t.join();
    }
    threads_.clear();
  }

 private:
  la::OwnerEvent event_, owner_;
  std::atomic<bool> stop_{false};
  std::vector<std::thread> threads_;
};

// Stages a helper opened, over every interleaved run.
uint64_t g_helper_opened_stages = 0;

// A HELPER'S TURNS TAKEN ON THE FIXTURE'S OWN THREAD, between the owner's
// pieces (the job test's InterleavedHelper says why).  A helper that opens a stage must signal the owner, which may be
// parked on kHelpersBusy waiting for it; the owner must never signal itself.
class InterleavedHelper {
 public:
  InterleavedHelper(la::LevelMergeJob* job, bool on,
                    const bs::SubtaskBudget& budget, std::string name)
      : job_(on ? job : nullptr), name_(std::move(name)) {
    if (on) job->AttachHelpers(&helpers_, &owner_, budget);
  }

  template <class Fn>
  bool Owner(Fn&& fn) {
    const uint64_t own = owner_.Generation();
    const bool done = fn();
    if (job_ != nullptr && job_->shared()) {
      Expect(!owner_.ChangedSince(own),
             name_ + ": the owner signalled its own event");
    }
    return done;
  }

  void Turn() {
    if (job_ == nullptr) return;
    const uint64_t own = owner_.Generation();
    const uint64_t help = helpers_.Generation();
    if (!job_->HelpOnce()) return;
    // A helper's lane never stops, so the helpers' event moved only if this
    // lane was its stage's last and a next stage opened.
    if (helpers_.ChangedSince(help)) {
      ++g_helper_opened_stages;
      Expect(owner_.ChangedSince(own),
             name_ + ": a helper opened a stage and did not tell the owner, "
                     "which may be parked waiting for it");
    }
  }

 private:
  la::LevelMergeJob* job_;
  std::string name_;
  la::OwnerEvent helpers_, owner_;
};

// `resumed` drives every phase through the job's cursor at the sliced budget,
// stopping after EVERY piece and resuming (a phase must be resumable at any
// piece boundary with byte-identical output), and `lanes` divides every stage
// that may be divided into up to that many lanes.
//
// `helpers` more threads run lanes of the job's phases alongside this one
// (LevelMergeJob::HelpOnce: m = 1 against m > 1 helpers at one lane count
// must be the same bytes).  `interleaved` takes a helper's
// turn on this thread after each of the owner's stops instead
// (InterleavedHelper); it needs `resumed` and no helper threads.
CaseResult RunCase(const Case& c, bool split, bool resumed = false,
                   size_t lanes = 1, unsigned helpers = 0,
                   bool interleaved = false) {
  if (interleaved && (!resumed || helpers != 0)) {
    throw std::logic_error("an interleaved run stops after every piece and "
                           "has no helper threads");
  }
  const bs::Layout layout = LayoutOf(c);
  // Derived, not stored: the keys chosen to force a shed, the carry's own
  // placement, the job, and the check that recomputes where each key belongs
  // all read this one object, and a job that ignored it would misroute
  // against all three.
  const std::unique_ptr<bs::AesTagKeys> instance_keys =
      c.key_seed == 0 ? nullptr
                      : bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
                            microram::crypto::SecretKeySeed::Fixed(c.key_seed)));
  const bs::AesTagKeys& keys =
      instance_keys == nullptr ? bs::DefaultAesTagKeys() : *instance_keys;
  const la::LevelArenaGeometry geometry(ParamsOf(c));
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  la::LevelArenaSet arenas(geometry, layout);
  const unsigned top = geometry.TopLevel();
  const size_t carry_buckets = geometry.CarryBuckets(top);  // U_L
  const unsigned carry_bits = bs::Log2Exact(carry_buckets);
  const la::MergeShape shape =
      la::MakeTopMergeShape(carry_buckets, geometry.TopDigit());
  const bs::RoutingIndexMap flat = FlatTopMap(shape);
  const unsigned flat_bits = FlatTopBits(shape);

  // The compaction's ordinal.  A carry reaches the top as ordinal v after its
  // producer forwarded ordinal v*B, and CanonicalFamily gives both (L, v):
  // the fixture takes the coordinate the way the two owners would.
  const uint64_t ordinal = 3;
  const la::Family family = la::CanonicalFamily(geometry, top, ordinal);
  Expect(family == la::CanonicalFamily(geometry, top - 1,
                                       ordinal * geometry.Branching()),
         Describe(c) + ": the producer and the top do not agree on the family "
                       "of one carry");
  const bs::RebuildNonce nonce = la::FamilyNonce(family);
  const la::CarryPlan plan = geometry.PlanCarry(top, ordinal);
  Expect(plan.outcome == la::CarryOutcome::kCompact &&
             plan.output_buckets == shape.out_buckets,
         Describe(c) + ": the geometry does not call this a top compaction");

  Model model;
  uint64_t next_key = 1;
  std::mt19937_64 rng(0xA55E + 31 * c.top_digit + c.branching);
  // Declared before `meta_of` because the UNSHADOWED mark is a claim about
  // this vector: see below.
  std::vector<bs::KeyWords> older_keys;
  size_t unshadowed_planted = 0;
  // Keys B holds only as a tombstone (`erase_retained`), whatever their residue.
  std::set<bs::KeyWords> erased_by_carry;
  // THE UNSHADOWED QUALIFIER IS NOT THE FIXTURE'S TO HAND OUT FREELY.  Bit 5
  // means "no OLDER copy of this key exists anywhere", and the engine's merge
  // believes it: a tombstone carrying it is skipped as the sweep reads its
  // source, so an older copy left behind would resurrect.  Marking one wrongly
  // here would report a sound engine as broken.  Two facts make the rule below
  // exact within this fixture:
  //
  //   - A is the OLDEST table there is here, and A's main and tier are
  //     disjoint by construction, so nothing is older than an A entry;
  //   - every duplicate in this fixture is made one way -- B draws a third of
  //     its main keys, and all of its tier keys, out of `older_keys` -- so a
  //     B key absent from that vector has no copy in A either.
  //
  // Hence: mark every A tombstone, and a B tombstone only when its key is new.
  // The shadowing tombstones (B's, over A's copies) stay unmarked, which is
  // what keeps both classes in every case that sets the flag.
  const auto meta_of = [&](bs::KeyWords key, uint8_t source) -> uint8_t {
    if (source == 2 && erased_by_carry.count(key) != 0) return bs::kMetaErased;
    if (!c.tombstones) return 0;
    if (key.w0 % (source == 1 ? 3 : 5) != 0) return 0;
    if (!c.unshadowed) return bs::kMetaErased;
    if (source == 2 && std::find(older_keys.begin(), older_keys.end(), key) !=
                           older_keys.end()) {
      return bs::kMetaErased;
    }
    ++unshadowed_planted;
    return bs::kMetaErased | bs::kMetaUnshadowed;
  };

  la::LevelArena& arena = arenas.At(top);

  // ---- A, the published bank ---------------------------------------------
  //
  // Its arrangement is arbitrary: the preparation copies, re-tags and routes
  // the whole of it from scratch, so nothing about where the fixture planted
  // an entry survives into C.
  const std::vector<bs::KeyWords> forced_older =
      (c.forced_older == 0 || c.empty_top)
          ? std::vector<bs::KeyWords>()
          : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, flat,
                               flat_bits, flat_bits, /*target=*/0,
                               c.forced_older, &next_key, keys);
  const ts::PublishedSource older = ts::PublishSlot(
      &arena, arena.plan().top_bank[0], shape.older_buckets, layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        if (c.empty_top) return;
        size_t taken = 0;
        const size_t per_bucket = 12;
        for (size_t b = 0; b < main.num_buckets; ++b) {
          for (size_t slot = 0; slot < per_bucket; ++slot) {
            const bs::KeyWords key =
                taken < forced_older.size()
                    ? forced_older[taken++]
                    : ts::FixtureKey(next_key++, layout.key_bytes);
            // Once, not once per use: `meta_of` counts the marks it hands out.
            const uint8_t meta = meta_of(key, 1);
            ts::PlantEntry(layout, main.Bucket(b), slot, key, 1, meta);
            model[key] = {1, meta};
            older_keys.push_back(key);
          }
          main.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
        }
        // A NONEMPTY TIER, disjoint from the main: A and its tier are one
        // internally unique source, and the preparation's pass takes both.
        std::vector<bs::KeyWords> tier_keys;
        for (int i = 0; i < 12; ++i) {
          tier_keys.push_back(ts::FixtureKey(next_key++, layout.key_bytes));
          older_keys.push_back(tier_keys.back());
        }
        ts::PlantTierPerKey(layout, tier, tier_keys, 1,
                            [&](bs::KeyWords k) { return meta_of(k, 1); },
                            &model);
      });

  // ---- B, the inbox carry -------------------------------------------------
  //
  // A published hashed table is exactly "every entry in the bucket its hash
  // selects", so the fixture places each key there directly rather than
  // routing one: a carry that shed while being built would be an incomplete
  // published table, which is a broken fixture and not a result.
  const std::vector<bs::KeyWords> forced_fresh =
      c.forced_fresh == 0
          ? std::vector<bs::KeyWords>()
          : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, flat,
                               flat_bits, flat_bits, /*target=*/0,
                               c.forced_fresh, &next_key, keys);
  // A third of the carry's keys shadow A, so the merge has real duplicates to
  // resolve across main, tier and sheds.
  std::vector<bs::KeyWords> fresh_keys = forced_fresh;
  if (c.erase_retained) {
    // Newest-planted first: B's bucket has room for 64 of the 72, and the
    // preparation's sheds come from the end of A's forced run, so this order
    // is the one that deletes the retained ones.  RunAndReport checks that it
    // did (`retained_erased`) rather than trusting the order.
    for (auto it = forced_older.rbegin(); it != forced_older.rend(); ++it) {
      fresh_keys.push_back(*it);
      erased_by_carry.insert(*it);
    }
  }
  for (size_t i = 0; i < carry_buckets * 10; ++i) {
    if (!older_keys.empty() && rng() % 3 == 0) {
      const bs::KeyWords candidate = older_keys[rng() % older_keys.size()];
      if (std::find(fresh_keys.begin(), fresh_keys.end(), candidate) ==
          fresh_keys.end()) {
        fresh_keys.push_back(candidate);
        continue;
      }
    }
    fresh_keys.push_back(ts::FixtureKey(next_key++, layout.key_bytes));
  }
  // Where each one goes under the carry's OWN map: kRaw over its K bits,
  // which is what a full table forwarded from level L-1 is published as.
  const std::vector<size_t> fresh_home =
      TagIndices(layout, nonce, bs::RoutingIndexMap{}, carry_bits, keys,
                 fresh_keys);

  const ts::PublishedSource carry = ts::PublishSlot(
      &arena, arena.plan().inbox[0], carry_buckets, layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        std::vector<unsigned> fill(main.num_buckets, 0);
        for (size_t i = 0; i < fresh_keys.size(); ++i) {
          const size_t b = fresh_home[i];
          if (fill[b] >= bs::kBucketCapacity) continue;  // the fixture's cap
          const bs::KeyWords key = fresh_keys[i];
          const uint8_t meta = meta_of(key, 2);
          ts::PlantEntry(layout, main.Bucket(b), fill[b], key, 2, meta);
          main.masks[b] |= uint64_t{1} << fill[b];
          ++fill[b];
          model[key] = {2, meta};
        }
        // Its stored tags, under the family nonce and its own kRaw map: this
        // is what makes it a table a real producer could have published, and
        // what the top's re-tag then has to redo WITHOUT re-routing.
        bs::ComputeRoutingTags(main, nonce.real_lo, nonce.real_hi,
                               bs::RoutingIndexMap{}, carry_bits, keys);
        // A NONEMPTY TIER holding keys A also has: the pass's fresher class
        // must beat the older copy of each.  Disjoint from the carry's OWN
        // main, because a table and its tier are one logical source and the
        // merge is only defined for sources that hold each key once -- a
        // fixture that broke that would be handing the engine an input no
        // engine produces and reading the two survivors as a defect.
        std::vector<bs::KeyWords> tier_keys;
        if (c.erase_in_tier) {
          // 32, not all 72: every one of them names the same destination
          // index, and with the retained keys they share one bucket of the
          // merge pass's range table (see `tier_buckets`).
          constexpr size_t kTierErasures = 32;
          for (const bs::KeyWords& key : forced_older) {
            if (tier_keys.size() == kTierErasures) break;
            if (std::find(fresh_keys.begin(), fresh_keys.end(), key) !=
                fresh_keys.end()) {
              continue;
            }
            tier_keys.push_back(key);
            erased_by_carry.insert(key);
          }
        }
        const size_t erased_in_tier = tier_keys.size();
        for (size_t i = 0;
             i < older_keys.size() && tier_keys.size() < erased_in_tier + 10;
             ++i) {
          const bs::KeyWords key = older_keys[(i * 7 + 3) % older_keys.size()];
          if (std::find(fresh_keys.begin(), fresh_keys.end(), key) !=
              fresh_keys.end()) {
            continue;
          }
          if (std::find(tier_keys.begin(), tier_keys.end(), key) ==
              tier_keys.end()) {
            tier_keys.push_back(key);
          }
        }
        ts::PlantTierPerKey(layout, tier, tier_keys, 2,
                            [&](bs::KeyWords k) { return meta_of(k, 2); },
                            &model);
        if (c.poison_carry_tags) {
          for (size_t b = 0; b < main.num_buckets; ++b) {
            PoisonTags(layout, main.Bucket(b));
          }
          for (size_t b = 0; b < tier->num_buckets; ++b) {
            PoisonTags(layout, tier->Bucket(b));
          }
        }
      });

  // ---- C, the destination -------------------------------------------------

  la::SlotLease dest;
  if (!arena.TryLeaseOwn(arena.plan().top_bank[1], &dest)) {
    throw std::logic_error("the fixture could not lease the top's other bank");
  }

  la::LevelMergeJob job(geometry, sizing, layout, top, keys, lanes);
  HelperThreads helper_threads(&job, helpers,
                               c.sliced || resumed ? SlicedBudget()
                                                   : WholeBudget());
  InterleavedHelper interleave(&job, interleaved, SlicedBudget(), Describe(c));
  la::LevelMergeScratch scratch(
      layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, top),
      la::MaxLevelDfsAllocation(geometry, sizing, top));
  // Timed, so that which range builder each pass ran can be checked below.
  job.EnableStageTiming(true);

  la::LevelMergeBinding binding;
  binding.ordinal = ordinal;
  binding.out = arena.WritableMain(dest, shape.out_buckets);
  binding.out_tier = arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  binding.older_main = older.Main();
  binding.older_tier = older.Tier();
  // A previous occupancy's bytes are still in the bank, and a merge that only
  // wrote part of its output would otherwise read as correct because the rest
  // happened to be zero.
  std::memset(binding.out.data, 0xA5, shape.out_buckets * layout.BucketBytes());
  for (size_t b = 0; b < shape.out_buckets; ++b) binding.out.masks[b] = 0;
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * layout.BucketBytes());

  la::LevelCarry incoming;
  incoming.ordinal = ordinal;
  incoming.family = family;
  incoming.main = carry.Main();
  incoming.tier = carry.Tier();

  const bs::SubtaskBudget budget =
      c.sliced || resumed ? SlicedBudget() : WholeBudget();
  // Resumed, every piece asks to stop, and every stop is resumed at once.
  size_t stops = 0;
  // What the owner's pieces were charged for residual work.
  uint64_t residual_charged = 0;
  const auto stop = [&stops, &residual_charged,
                     resumed](const bs::Subtask& piece) {
    ++stops;
    residual_charged += ts::ResidualCharge(piece);
    return resumed;
  };
  job.Begin(binding);
  Expect(job.top() && job.digit() == geometry.TopDigit() &&
             job.family() == family &&
             job.nonce().real_hi == nonce.real_hi &&
             job.nonce().real_lo == nonce.real_lo,
         Describe(c) + ": the job derived a different coordinate than the "
                       "fixture placed its carry under");
  if (split) {
    if (resumed || helpers > 0) {
      while (!interleave.Owner(
          [&] { return job.ContinuePrepare(budget, &scratch, stop); })) {
        interleave.Turn();
      }
    } else {
      job.PrepareOlder(budget, &scratch);
    }
    // A PAUSE between the preparation and the carry: the sources are exactly
    // where they were, and the retained carry is all the phase leaves behind.
    Expect(older.Unchanged(layout), Describe(c) + ": the preparation wrote A");
    Expect(carry.Unchanged(layout),
           Describe(c) + ": the preparation touched a carry it has not taken");
  }
  if (resumed || helpers > 0) {
    while (!interleave.Owner([&] {
      return job.ContinueInstall(incoming, budget, &scratch, stop);
    })) {
      interleave.Turn();
    }
  } else {
    job.InstallCarry(incoming, budget, &scratch);
  }

  CaseResult result;
  // What the preparation's pass could not place, counted HERE: the merge's
  // pass sweeps it and then resets it, so after the finish it is gone.  Shed
  // counts are secret and nothing in the engine may branch on them; a checked
  // fixture is the only place such a check belongs.
  //
  // The retained carry is the slot past the merge's, which is past the radix
  // pass's, which is past the route's -- the same arithmetic the job uses.
  const bs::ResidualStash& retained_carry =
      job.older_sheds()[shape.block_bits + la::kLevelMergePrepCarryStashOffset];
  result.retained = retained_carry.Count();
  {
    Model retained_live;
    bool retained_unique = true;
    size_t retained_damaged = 0;
    ts::CollectLiveStashes(layout, &retained_carry, 1, &retained_live,
                           &retained_unique, &retained_damaged);
    for (const auto& entry : retained_live) {
      const auto it = model.find(entry.first);
      if (it != model.end() && it->second.source == 2 &&
          (it->second.meta & bs::kMetaErased) != 0) {
        ++result.retained_erased;
      }
    }
  }
  // AND EVERY SLOT THE TWO POOLS DO NOT COVER MUST BE EMPTY.  A route
  // `n` bits deep owns [0, n); the preparation's pass offers those back and
  // the radix slot with them, the merge's sheds into its own.  The quad's
  // one-past slot is the only slack, and an entry that landed in it would be
  // in no pool, never offered back or drained, and reset away without a word.
  Expect(job.older_sheds()[shape.block_bits].Count() == 0,
         Describe(c) + ": the slot past the route is outside every pool and "
                       "is not empty");
  if (resumed || helpers > 0) {
    while (!interleave.Owner(
        [&] { return job.ContinueFinish(&scratch, budget, stop); })) {
      interleave.Turn();
    }
  }
  if (resumed && helpers == 0) {
    // Interleaved, the helper's turns run most pieces, so few are stops.
    Expect(interleaved || stops > 100,
           Describe(c) + ": the resumed run stopped only " +
               std::to_string(stops) + " times, so the cursor was not "
               "exercised");
    // THE INLINE SHARE'S ESTIMATE IS WHAT THE PIECES ARE CHARGED: both of
    // the top's passes and their offers.
    if (!interleaved) {
      const double estimate = la::LevelMergeResidualTouches(
          geometry, layout, sizing, top, geometry.TopDigit());
      Expect(double(residual_charged) == estimate,
             Describe(c) + ": the pieces were charged " +
                 std::to_string(residual_charged) +
                 " residual touches, LevelMergeResidualTouches counts " +
                 std::to_string(estimate));
      ++g_residual_charge_checks;
    }
  } else if (helpers == 0) {
    job.FinishMerge(&scratch, budget);
  }
  helper_threads.Stop();
  Expect(!job.bound(), Describe(c) + ": the job stayed bound after finishing");
  g_laned_stages += job.laned_stages();
  g_private_mask_stages += job.private_mask_stages();

  // ---- what the compaction produced --------------------------------------

  size_t damaged = 0;
  ts::CollectLive(binding.out, &result.live, &result.unique, &damaged);
  const size_t main_live = result.live.size();
  ts::CollectLiveStashes(layout, binding.out_tier, 1, &result.live,
                         &result.unique, &damaged);
  result.tier_entries = result.live.size() - main_live;
  Expect(damaged == 0,
         Describe(c) + ": " + std::to_string(damaged) +
             " entries carry a payload their key and source do not agree "
             "with");
  result.out_digest = ts::DigestTable(binding.out) * 0x100000001b3ull ^
                      ts::DigestStash(layout, *binding.out_tier);
  Expect(result.unique,
         Describe(c) + ": a key survives twice across C and its tier");

  // THE TOMBSTONE DROP.  This is the one rebuild allowed to forget one, so
  // what C must hold is the newest copy of every key MINUS every key whose
  // newest copy is a tombstone -- including the ones a carry tombstone
  // deleted over a live copy in A.
  Model expected;
  size_t forgotten = 0;
  for (const auto& entry : model) {
    if ((entry.second.meta & bs::kMetaErased) != 0) {
      ++forgotten;
      continue;
    }
    expected.emplace(entry.first, entry.second);
  }
  Expect(!c.tombstones || forgotten > 0,
         Describe(c) + ": no tombstone was planted, so the drop is untested");
  // The same guard one level up: a case can ask for unshadowed tombstones and
  // get none -- the residues that select them are the tombstone residues, and
  // a shape where every B tombstone happened to land on an A key would leave
  // the early skip untested.
  Expect(!c.unshadowed || unshadowed_planted > 0,
         Describe(c) + ": no tombstone was marked unshadowed, so the early "
                       "skip is untested");
  if (result.live != expected) {
    size_t missing = 0, extra = 0, wrong = 0;
    bs::KeyWords first_missing, first_wrong, first_extra;
    for (const auto& want : expected) {
      const auto it = result.live.find(want.first);
      if (it == result.live.end()) {
        if (missing++ == 0) first_missing = want.first;
      } else if (it->second != want.second) {
        if (wrong++ == 0) first_wrong = want.first;
      }
    }
    for (const auto& got : result.live) {
      if (expected.find(got.first) == expected.end()) {
        if (extra++ == 0) first_extra = got.first;
      }
    }
    Expect(false,
           Describe(c) + ": C is not exactly the live newest copy of every "
                         "key (" +
               std::to_string(missing) + " missing e.g. " +
               std::to_string(first_missing.w0) + ", " +
               std::to_string(extra) + " unexpected e.g. " +
               std::to_string(first_extra.w0) + " (a kept tombstone?), " +
               std::to_string(wrong) + " at the wrong value e.g. " +
               std::to_string(first_wrong.w0) + "; model " +
               std::to_string(expected.size()) + ", output " +
               std::to_string(result.live.size()) + ")");
  }

  // Every entry of C's main is in the bucket its KEY selects -- recomputed
  // from the key and not from the stored tag, because a second chance moves
  // PAYLOAD LINES only and an entry it put back carries whatever tag bytes
  // were in that slot.  The tier is exempt by construction: it is what did
  // not fit into any bucket.
  std::vector<bs::KeyWords> out_keys;
  std::vector<size_t> out_buckets;
  for (size_t b = 0; b < binding.out.num_buckets; ++b) {
    uint64_t mask = binding.out.masks[b];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      out_keys.push_back(
          ts::SlotKeyWordsOf(layout, binding.out.Bucket(b), slot));
      out_buckets.push_back(b);
    }
  }
  size_t misrouted = 0;
  if (!out_keys.empty()) {
    const std::vector<size_t> want =
        TagIndices(layout, nonce, flat, flat_bits, keys, out_keys);
    for (size_t i = 0; i < out_keys.size(); ++i) {
      if (want[i] != out_buckets[i]) ++misrouted;
    }
  }
  Expect(misrouted == 0,
         Describe(c) + ": " + std::to_string(misrouted) + " of " +
             std::to_string(out_keys.size()) +
             " entries are not in the bucket their key selects");

  // THE RESOLVED REFERENCE'S CAPACITY (REPORT.tex, Lemma
  // "resolved-compression"): with X_v live winners at final home v, C holds
  // min(X_v, 64) there and the tier exactly sum_v (X_v - 64)+.  The finish
  // resolves every version and tombstone before it tests capacity, so no
  // later deletion frees a slot a shed could have used; the old order (merge
  // B's main, then let B's tier delete) emitted more.
  {
    std::vector<bs::KeyWords> winners;
    for (const auto& entry : expected) winners.push_back(entry.first);
    std::vector<size_t> home_count(binding.out.num_buckets, 0);
    if (!winners.empty()) {
      for (size_t home :
           TagIndices(layout, nonce, flat, flat_bits, keys, winners)) {
        ++home_count[home];
      }
    }
    size_t wrong_homes = 0;
    for (size_t v = 0; v < binding.out.num_buckets; ++v) {
      const size_t x = home_count[v];
      result.reference_excess += x > 64 ? x - 64 : 0;
      if (bs::Popcount64(binding.out.masks[v]) != std::min<size_t>(x, 64)) {
        ++wrong_homes;
      }
    }
    Expect(wrong_homes == 0 && result.tier_entries == result.reference_excess,
           Describe(c) + ": the finish's capacity is not the resolved "
                         "reference's (" +
               std::to_string(wrong_homes) + " homes not min(X_v, 64); tier " +
               std::to_string(result.tier_entries) + " against excess " +
               std::to_string(result.reference_excess) + ")");
  }

  // Both operands are published storage and this merge only reads them.
  Expect(older.Unchanged(layout), Describe(c) + ": the merge wrote A");
  Expect(carry.Unchanged(layout),
         Describe(c) + ": the merge wrote the carry it consumed");
  // THE CERTIFIED RANGE BUILDERS: both passes distribute through the
  // one-page DFS wherever their pools' plans route at all -- the finish its
  // retained carry alone, with B's tier offered directly, as every separated
  // finish does.
  {
    const la::LevelMergePoolShape prepare = la::TopPreparePoolShapeOf(
        shape, sizing.Buckets(top), geometry.OlderTierBuckets(top, 0));
    const la::LevelMergePoolShape merge = la::TopMergePoolShapeOf(
        shape, sizing.Buckets(top), geometry.CarryTierBuckets(top));
    const bool prepare_dfs =
        bs::DfsResidualRangeApplies(prepare.swept_buckets, prepare.main_levels);
    const bool merge_dfs = bs::DfsResidualRangeApplies(
        merge.swept_buckets - merge.direct_buckets, merge.main_levels);
    Expect(merge.direct_buckets == geometry.CarryTierBuckets(top),
           Describe(c) + ": the top finish does not offer B's tier directly");
    Expect((scratch.dfs() != nullptr) == (prepare_dfs || merge_dfs) &&
               (scratch.dfs() == nullptr || scratch.dfs()->pages() == 1),
           Describe(c) + ": the top's DFS workspace is not the one page its "
                         "pools need");
    Expect((job.kind_nanos(bs::Subtask::kResidualDfsPartition) > 0) ==
               (prepare_dfs || merge_dfs),
           Describe(c) + ": the top did not distribute through the DFS "
                         "exactly where its pools route");
    g_dfs_preparations += prepare_dfs;
    g_dfs_finishes += merge_dfs;
  }
  return result;
}

void RunAndReport(const Case& c) {
  const CaseResult split = RunCase(c, /*split=*/true);
  // The unsplit path is the same prepare/finish helpers in sequence, so on the same
  // inputs it has to produce the same table -- not merely an equivalent one.
  const CaseResult unsplit = RunCase(c, /*split=*/false);
  Expect(split.live == unsplit.live,
         Describe(c) + ": pausing between preparation and the carry changed "
                       "the result");
  // Byte identity is only meaningful once every byte the merge reads is
  // defined, so this run is the control: two identical runs must agree BEFORE
  // "pausing changed nothing" is worth asserting.
  const CaseResult control = RunCase(c, /*split=*/true);
  Expect(control.out_digest == split.out_digest,
         Describe(c) + ": two identical runs produced different bytes");
  Expect(split.out_digest == unsplit.out_digest,
         Describe(c) + ": pausing changed the output's bytes");
  // STOPPING AFTER EVERY PIECE CHANGES NOTHING: the
  // same compaction through the job's cursor at a tight budget, stopped and
  // resumed between every two pieces, against the one issued whole.
  const CaseResult resumed = RunCase(c, /*split=*/true, /*resumed=*/true);
  Expect(resumed.out_digest == split.out_digest,
         Describe(c) + ": stopping and resuming the phases changed the "
                       "output's bytes");
  // LANES CHANGE NOTHING EITHER, whole and stopped
  // after every piece; see the job test for why the bytes must match.
  for (bool stop : {false, true}) {
    const CaseResult laned =
        RunCase(c, /*split=*/true, /*resumed=*/stop, /*lanes=*/3);
    Expect(laned.out_digest == split.out_digest,
           Describe(c) + ": running the stages in lanes changed the output's "
                         "bytes" + (stop ? " (stopping after every piece)" : ""));
  }
  // AND WHICH THREAD RUNS A LANE CHANGES NOTHING: the same three
  // lanes with two helper threads claiming them against this one, whole and
  // stopping after every piece.
  for (bool stop : {false, true}) {
    const CaseResult helped = RunCase(c, /*split=*/true, /*resumed=*/stop,
                                      /*lanes=*/3, /*helpers=*/2);
    Expect(helped.out_digest == split.out_digest,
           Describe(c) + ": running the lanes on helper threads changed the "
                         "output's bytes" +
               (stop ? " (stopping after every piece)" : ""));
  }
  // The same with the helper's turns taken between the owner's pieces, which
  // is where who is told of each stage opening gets checked.
  {
    const CaseResult interleaved =
        RunCase(c, /*split=*/true, /*resumed=*/true, /*lanes=*/3,
                /*helpers=*/0, /*interleaved=*/true);
    Expect(interleaved.out_digest == split.out_digest,
           Describe(c) + ": interleaving a helper's lanes with the owner's "
                         "pieces changed the output's bytes");
  }
  // EARLY DROP == TAIL DROP, compared rather than argued.  The same case with
  // the qualifier removed plants the same keys, in the same places, with the
  // same liveness -- bit 5 decides only WHEN a tombstone is forgotten, never
  // whether -- so the two runs must publish the same live set.  Their BYTES
  // need not agree and do not: a tombstone the sweep never placed leaves a
  // lane the offer fills with something else, which is the whole point of
  // skipping it and is why this compares `live` and not `out_digest`.
  if (c.unshadowed) {
    Case tail_only = c;
    tail_only.unshadowed = false;
    const CaseResult tail = RunCase(tail_only, /*split=*/true);
    Expect(tail.live == split.live,
           Describe(c) + ": forgetting an unshadowed tombstone as the sweep "
                         "reads it and forgetting it at the trailing drop "
                         "publish different live sets");
  }
  if (c.forced_older != 0) {
    Expect(split.retained > 0,
           Describe(c) + ": the preparation retained nothing, so the merge's "
                         "older class was empty");
  }
  if (c.erase_retained) {
    Expect(split.retained_erased > 0,
           Describe(c) + ": the carry deleted no retained key, so the residual dedup "
                         "before the early tombstone drop resolved nothing");
    Expect(split.tier_entries == 0,
           Describe(c) + ": deletion tombstones still consumed residual capacity");
  }
  if (c.erase_in_tier) {
    // RunCase checked the tier against the resolved excess; this says the
    // case had the margin to tell the orders apart: merging B's main into
    // the full bucket first sheds all `forced_fresh` live keys.
    Expect(split.reference_excess < c.forced_fresh,
           Describe(c) + ": the resolved excess " +
               std::to_string(split.reference_excess) +
               " leaves no margin against the " +
               std::to_string(c.forced_fresh) + " keys the old order sheds");
  }
  if (!c.erase_retained && !c.erase_in_tier &&
      (c.forced_older != 0 || c.forced_fresh != 0)) {
    Expect(split.tier_entries > 0,
           Describe(c) + ": nothing reached the published tier, so the "
                         "merge's residual wiring was not loaded");
  }
  std::printf("  %-42s %zu keys, %zu retained, %zu in tier (excess %zu)%s%s\n",
              Describe(c).c_str(), split.live.size(), split.retained,
              split.tier_entries, split.reference_excess,
              c.sliced ? ", sliced" : "",
              c.erase_retained
                  ? (", " + std::to_string(split.retained_erased) +
                     " retained keys deleted by the carry")
                        .c_str()
                  : "");
}

// ---------------------------------------------------------------------------
// The two oracles for the re-tag
// ---------------------------------------------------------------------------

// ORACLE 1, at the byte: the digit line this merge computes in a register is
// the one a real re-tag would have STORED.
//
// The straightforward re-tag is a copy of each source bucket into a private
// scratch view; what runs is ComputeBucketDigitLine, which produces the same
// digits and copies nothing.  That is only sound if the two agree byte for
// byte, so this builds that copy and compares it.
void TestRecomputedDigitsMatchAStoredRetag() {
  struct Shape {
    size_t tag_bytes;
    size_t digit_bits;
    size_t key_bytes;
    unsigned carry_bits;
    unsigned radix;
    // A BINARY top: the merge's own map is kRaw and
    // its way is the raw tag's bits just above the carry's.  The reference
    // is then the copy re-tagged under the WHOLE-DIGIT map with the same
    // modulus, whose stored digit is (T >> K) mod 2^e -- the same bits.
    bool binary;
  };
  const Shape shapes[] = {
      {4, 0, 8, 4, 4, false},   // the reserved digit byte
      {1, 4, 8, 4, 3, false},   // packed into the top index byte
      {5, 0, 16, 9, 7, false},  // wide keys, and an index across a byte boundary
      {2, 1, 8, 9, 5, false},   // packed, with index bits above eight
      {4, 0, 8, 4, 8, true},    // the binary top at D = 8, reserved byte
      {1, 4, 8, 4, 4, true},    // D = 4, packed: the way IS the digit's bits
      {2, 1, 8, 9, 2, true},    // D = 2, packed, index bits above eight
      {5, 0, 16, 9, 8, true},   // D = 8, wide keys
  };
  const std::unique_ptr<bs::AesTagKeys> instance = bs::MakeAesTagKeys(
      microram::crypto::DeriveAesRoundKeys(
          microram::crypto::SecretKeySeed::Fixed(0xD1617u)));
  for (const Shape& shape : shapes) {
    const std::string at = " at tag_bytes " + std::to_string(shape.tag_bytes) +
                           ", digit_bits " + std::to_string(shape.digit_bits) +
                           (shape.binary ? ", binary top" : "");
    bs::Layout layout;
    layout.key_bytes = shape.key_bytes;
    layout.value_bytes = 8;
    layout.tag_bytes = shape.tag_bytes;
    layout.digit_bits = shape.digit_bits;
    // The whole-digit map: the merge's own for a whole-digit top, and the
    // REFERENCE for a binary one.
    bs::RoutingIndexMap map;
    map.kind = bs::TagMapKind::kRadixDigit;
    map.low_bits = shape.carry_bits;
    map.modulus = shape.radix;
    map.digit_shift = bs::RoutingDigitShift(layout);
    const bs::RoutingIndexMap raw;  // a binary top's own map
    const bs::RoutingIndexMap& merge_map = shape.binary ? raw : map;
    Expect(bs::RoutingDigitFits(layout),
           "the oracle's own layout cannot hold a radix digit" + at);

    bs::Table source = ts::ZeroedTable(1, layout);
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      ts::PlantEntry(layout, source.Bucket(0), slot,
                     ts::FixtureKey(slot + 1, layout.key_bytes), 1);
    }
    source.masks[0] = ~uint64_t{0};

    // The scratch copy, written by the fused copy-and-re-tag kernel.
    bs::Table copy = ts::ZeroedTable(1, layout);
    bs::CopyAndRetagRange(bs::View(copy), bs::View(source), 0, 1, 0,
                          /*nonce_lo=*/7, /*nonce_hi=*/11, map,
                          shape.carry_bits, *instance);
    const __m512i stored = bs::NormalizeDigitLine(
        _mm512_load_si512(reinterpret_cast<const void*>(
            copy.Bucket(0) + layout.DigitLine() * bs::kBucketCapacity)),
        layout.digit_bits);

    const bs::FixedMergeRetag retag = bs::MakeFixedMergeRetag(
        merge_map, /*nonce_lo=*/7, /*nonce_hi=*/11, *instance,
        shape.carry_bits, shape.radix);
    const __m512i computed = bs::FixedMergeSourceDigits(
        source.Bucket(0), layout, shape.radix, &retag);

    alignas(64) uint8_t want[bs::kBucketCapacity];
    alignas(64) uint8_t got[bs::kBucketCapacity];
    _mm512_store_si512(reinterpret_cast<void*>(want), stored);
    _mm512_store_si512(reinterpret_cast<void*>(got), computed);
    size_t differ = 0, nonzero = 0;
    for (size_t i = 0; i < bs::kBucketCapacity; ++i) {
      if (want[i] != got[i]) ++differ;
      if (want[i] != 0) ++nonzero;
    }
    Expect(differ == 0,
           "the recomputed digit line differs from the stored one in " +
               std::to_string(differ) + " of 64 lanes" + at);
    // The control: an all-zero digit line would match trivially, and a
    // comparison that can pass without a single nonzero digit is not one.
    Expect(nonzero > 0, "every digit came out zero" + at);
  }
  std::printf("  re-tag: the register IS the stored digit line, 4 layouts, "
              "and a binary top's way IS the whole-digit map's digit, 4 "
              "more\n");
}

// ORACLE 2, at the sweep: a whole fixed merge whose source digits are
// recomputed produces the same table, byte for byte, as the SAME kernel over a
// privately re-tagged copy of the carry -- the merge every non-top level
// runs, and the copy production at the top does not allocate.
void TestSweepMatchesARetaggedCarry() {
  struct Ways {
    unsigned radix;  // the sweep's fan-in, D
    bool binary;     // the merge's own map is kRaw (a binary top)
  };
  const Ways all[] = {{1, false}, {2, false}, {3, false}, {4, false},
                      {5, false}, {6, false}, {7, false},
                      {2, true},  {4, true},  {8, true}};
  for (const Ways& w : all) {
    const unsigned radix = w.radix;
    const std::string at = " at radix " + std::to_string(radix) +
                           (w.binary ? " (binary top)" : "");
    bs::Layout layout;
    layout.key_bytes = 8;
    layout.value_bytes = 8;
    layout.tag_bytes = 4;
    const unsigned carry_bits = 4;
    const size_t block = size_t{1} << carry_bits;
    // The whole-digit map: the merge's own, or -- at a binary top -- the
    // ORACLE's, under which the stored digit is the binary top's way.
    bs::RoutingIndexMap map;
    if (radix > 1) {
      map.kind = bs::TagMapKind::kRadixDigit;
      map.low_bits = carry_bits;
      map.modulus = radix;
      map.digit_shift = bs::RoutingDigitShift(layout);
    }
    const bs::RoutingIndexMap raw;
    const bs::RoutingIndexMap& merge_map = w.binary ? raw : map;
    const std::unique_ptr<bs::AesTagKeys> instance = bs::MakeAesTagKeys(
        microram::crypto::DeriveAesRoundKeys(
            microram::crypto::SecretKeySeed::Fixed(0xACE00 + radix)));

    // C, twice and identical; and B, published under ANOTHER map -- kRaw over
    // its own index bits -- which is the position the top's inbox carry is in.
    bs::Table c1 = ts::ZeroedTable(block * radix, layout);
    bs::Table c2 = ts::ZeroedTable(block * radix, layout);
    bs::Table b = ts::ZeroedTable(block, layout);
    uint64_t next_key = 1;
    for (size_t i = 0; i < c1.num_buckets; ++i) {
      for (size_t slot = 0; slot < 20; ++slot) {
        const bs::KeyWords key = ts::FixtureKey(next_key++, layout.key_bytes);
        ts::PlantEntry(layout, c1.Bucket(i), slot, key, 1);
        ts::PlantEntry(layout, c2.Bucket(i), slot, key, 1);
      }
      c1.masks[i] = c2.masks[i] = bs::LowMask64(20);
    }
    for (size_t i = 0; i < b.num_buckets; ++i) {
      for (size_t slot = 0; slot < 24; ++slot) {
        ts::PlantEntry(layout, b.Bucket(i), slot,
                       ts::FixtureKey(next_key++, layout.key_bytes), 2);
      }
      b.masks[i] = bs::LowMask64(24);
    }
    bs::TableView bv = bs::View(b);
    bs::ComputeRoutingTags(bv, /*nonce_lo=*/5, /*nonce_hi=*/9,
                           bs::RoutingIndexMap{}, carry_bits, *instance);

    // The ORACLE's private copy: the whole carry re-tagged under the merge's
    // map, which is what a per-bucket scratch view would hold one bucket at a
    // time.  Its masks are the carry's -- a re-tag moves nothing.
    bs::Table retagged = ts::ZeroedTable(block, layout);
    bs::CopyAndRetagRange(bs::View(retagged), bv, 0, block, 0, 5, 9, map,
                          carry_bits, *instance);
    for (size_t i = 0; i < block; ++i) retagged.masks[i] = b.masks[i];

    // The two sheds.  AllocateAligned64 rather than a vector: the stash
    // kernels load their lines with _mm512_load_si512.
    const size_t stash_buckets = 4;
    const size_t stash_bytes = stash_buckets * layout.BucketBytes();
    bs::Aligned64Ptr store1 = bs::AllocateAligned64(stash_bytes);
    bs::Aligned64Ptr store2 = bs::AllocateAligned64(stash_bytes);
    std::memset(store1.get(), 0, stash_bytes);
    std::memset(store2.get(), 0, stash_bytes);
    bs::ResidualStash stash1, stash2;
    stash1.data = store1.get();
    stash2.data = store2.get();
    stash1.num_buckets = stash2.num_buckets = stash_buckets;
    stash1.entry_bytes = stash2.entry_bytes = layout.EntryBytes();

    const bs::FixedMergeRetag retag = bs::MakeFixedMergeRetag(
        merge_map, /*nonce_lo=*/5, /*nonce_hi=*/9, *instance, carry_bits,
        radix);
    Expect(bs::MergeRadixLevelSourcesRange</*CheckOverflow=*/true>(
               bs::View(c1), bv, radix, stash1, 0, block,
               bs::FixedMergeTombstones::kMerge, &retag),
           "the recomputed-digit sweep overflowed its stash" + at);
    Expect(bs::MergeRadixLevelSourcesRange</*CheckOverflow=*/true>(
               bs::View(c2), bs::View(retagged), radix, stash2, 0, block),
           "the oracle sweep overflowed its stash" + at);

    Expect(ts::DigestTable(bs::View(c1)) == ts::DigestTable(bs::View(c2)),
           "a sweep under recomputed digits produced other bytes than the "
           "same sweep over a privately re-tagged carry" + at);
    Expect(ts::DigestStash(layout, stash1) == ts::DigestStash(layout, stash2),
           "the two sweeps shed differently" + at);
    // The control: comparing two tables nothing was merged into would pass by
    // itself, so the sweep has to have moved something.
    size_t merged = 0;
    for (size_t i = 0; i < c1.num_buckets; ++i) {
      merged += static_cast<size_t>(bs::Popcount64(c1.masks[i]));
    }
    Expect(merged > 20 * c1.num_buckets,
           "the sweep merged nothing, so the comparison proves nothing" + at);
  }
  std::printf("  re-tag: a whole sweep equals one over a re-tagged carry, "
              "D = 1..7, and at the binary tops 2, 4, 8\n");
}

// ---------------------------------------------------------------------------
// Tombstones sharing a destination with unrelated older residuals must not
// become merge sheds: otherwise two retained entries can keep 66 tombstones
// alive and overflow the D=1 merge stash of 64 entries.
void TestTombstonesBesideRetainedEntries() {
  la::LevelArenaGeometry::Params params;
  params.branching = 8;
  params.levels = 4;
  params.top_digit = 1;
  params.prefix_flushes = 2;
  const la::LevelArenaGeometry geometry(params);
  const la::LevelArenaStashSizing sizing(geometry, uint64_t{1} << 32);
  const bs::Layout layout{8, 2, 2};
  const size_t n = geometry.TopBuckets();
  const unsigned bits = la::Log2Checked(n, "top");
  const size_t depth = sizing.Buckets(geometry.TopLevel());
  Expect(depth == 1, "the tombstone overflow fixture needs a 64-entry stash");
  uint64_t next = 1;
  std::vector<bs::KeyWords> keys[2];
  for (size_t i = 0; i < 2; ++i) {
    keys[i] = ts::KeysAtTagIndex(layout, 123, 456, {}, bits, bits, i,
                                 98, &next);
  }
  // Per-bucket ranges, a shared range, and two direct offer groups. The last
  // two exercise multiple destinations sharing mutable range masks.
  for (unsigned shape : {0u, 1u, 2u}) {
    for (bool erase_retained : {false, true}) {
      for (auto rule : {bs::ResidualDedupRule::kTableWins,
                        bs::ResidualDedupRule::kClassMark}) {
        auto c = ts::ZeroedTable(n, layout);
        auto b = ts::ZeroedTable(n, layout);
        const size_t groups = shape == 2 ? 2 : 1;
        auto range = ts::ZeroedTable(shape == 0 ? n : groups, layout);
        auto storage = bs::AllocateAligned64(depth * layout.BucketBytes());
        bs::ResidualStash stash;
        stash.data = storage.get();
        stash.num_buckets = depth;
        stash.entry_bytes = layout.EntryBytes();
        for (size_t i = 0; i < 2; ++i) {
          for (size_t s = 0; s < 64; ++s) {
            ts::PlantEntry(layout, c.Bucket(i), s, keys[i][s], 1);
          }
          c.masks[i] = ~uint64_t{0};
          const size_t rb = shape == 0 ? i : i % groups;
          ts::PlantEntry(layout, range.Bucket(rb), i, keys[i][64], 1);
          range.masks[rb] |= uint64_t{1} << i;
          for (size_t s = 0; s < 33; ++s) {
            ts::PlantEntry(layout, b.Bucket(i), s, keys[i][65 + s], 2,
                            bs::kMetaErased);
          }
          if (erase_retained) {
            ts::PlantEntry(layout, b.Bucket(i), 33, keys[i][64], 2,
                            bs::kMetaErased);
          }
          b.masks[i] = bs::LowMask64(erase_retained ? 34 : 33);
        }
        bs::ComputeRoutingTags(bs::View(range), 123, 456, {}, bits);
        const uint64_t before = ts::DigestBytes(b.data.get(), n * layout.BucketBytes());
        bs::ResidualOfferSet offer;
        offer.range = bs::View(range);
        offer.plan.range_buckets = range.num_buckets;
        offer.plan.range_bits = shape == 0 ? bits : 0;
        offer.plan.index_bits = shape == 0 ? 0 : bits;
        offer.plan.groups = groups;
        offer.rule = rule;
        offer.lines = layout.PayloadLines();
        Expect(bs::MergeFixedLevelSourcesOffersRange<true>(
                   bs::View(c), bs::View(b), 1, stash, &offer, 1, 0, n,
                   bs::FixedMergeTombstones::kAll),
               "unrelated tombstones beside retained entries overflowed");
        Expect(stash.Count() == 0, "a tombstone occupied the merge stash");
        size_t retained = 0;
        for (size_t i = 0; i < range.num_buckets; ++i) {
          retained += bs::Popcount64(range.masks[i]);
        }
        Expect(retained == (erase_retained ? 0 : 2),
               "older residual deletion did not respect key equality");
        for (size_t i = 0; i < 2; ++i) {
          Expect(c.masks[i] == ~uint64_t{0}, "an unrelated live key was cleared");
          Expect(b.masks[i] == bs::LowMask64(erase_retained ? 34 : 33),
                 "the published carry mask was changed");
        }
        Expect(before == ts::DigestBytes(b.data.get(), n * layout.BucketBytes()),
               "the published carry bytes were changed");
      }
    }
  }
  std::printf("  tombstones beside retained entries: no merge capacity used\n");
}

// Refusals and sizing
// ---------------------------------------------------------------------------

void TestTopRefusals() {
  Case c;
  c.name = "refusals";
  const bs::Layout layout = LayoutOf(c);
  const la::LevelArenaGeometry geometry(ParamsOf(c));
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  la::LevelArenaSet arenas(geometry, layout);
  const unsigned top = geometry.TopLevel();
  la::LevelArena& arena = arenas.At(top);
  const size_t carry_buckets = geometry.CarryBuckets(top);
  const size_t out_buckets = geometry.TopBuckets();

  la::SlotLease dest, a_lease, b_lease;
  Expect(arena.TryLeaseOwn(arena.plan().top_bank[1], &dest), "leased C");
  Expect(arena.TryLeaseOwn(arena.plan().top_bank[0], &a_lease), "leased A");
  Expect(arena.TryLeaseOwn(arena.plan().inbox[0], &b_lease), "leased B");

  la::LevelMergeBinding good;
  good.ordinal = 3;
  good.out = arena.WritableMain(dest, out_buckets);
  good.out_tier = arena.WritableTier(dest);
  good.destination_generation = dest.generation;
  good.older_main = arena.WritableMain(a_lease, out_buckets);
  good.older_tier = arena.WritableTier(a_lease);

  const auto refuses = [&](la::LevelMergeBinding bad, const char* what) {
    Expect(Throws([&] {
             la::LevelMergeJob other(geometry, sizing, layout, top,
                                     bs::DefaultAesTagKeys());
             other.Begin(bad);
           }),
           what);
  };
  // The one that matters most here: A is a FULL level, not a partial at digit
  // D-1.  A binding that supplied (D-1)*U_L would read nothing out of bounds
  // and would route the wrong extent into C.
  la::LevelMergeBinding partial = good;
  partial.older_main = arena.WritableMain(a_lease, out_buckets - carry_buckets);
  refuses(partial, "an older operand that is not the whole of A was accepted "
                   "at the top");
  la::LevelMergeBinding unleased = good;
  unleased.destination_generation = 0;
  refuses(unleased, "a destination that was never leased was accepted");
  la::LevelMergeBinding zero = good;
  zero.ordinal = 0;
  refuses(zero, "a zero ordinal was accepted");
  la::LevelMergeBinding wide = good;
  wide.out.layout.value_bytes += 8;
  refuses(wide, "a destination view in another entry layout was accepted");

  la::LevelMergeJob job(geometry, sizing, layout, top,
                        bs::DefaultAesTagKeys());
  job.Begin(good);
  la::LevelMergeScratch scratch(
      layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, top),
      la::MaxLevelDfsAllocation(geometry, sizing, top));
  // The top's preparation ENDS IN A PASS, so it needs the executing thread's
  // range table -- and says so, rather than building a pass with no range.
  Expect(Throws([&] { job.PrepareOlder(WholeBudget()); }),
         "the top's preparation ran without range scratch");
  job.PrepareOlder(WholeBudget(), &scratch);
  Expect(Throws([&] { job.PrepareOlder(WholeBudget(), &scratch); }),
         "a second preparation of one job was accepted");

  la::LevelCarry wrong;
  wrong.ordinal = good.ordinal + 1;
  wrong.family = job.family();
  wrong.main = arena.WritableMain(b_lease, carry_buckets);
  wrong.tier = arena.WritableTier(b_lease);
  Expect(Throws([&] { job.Finish(wrong, &scratch, WholeBudget()); }),
         "a carry out of order was accepted at a prepared top");
  la::LevelCarry foreign = wrong;
  foreign.ordinal = good.ordinal;
  foreign.family = la::Family{job.family().level, job.family().ordinal + 1};
  Expect(Throws([&] { job.Finish(foreign, &scratch, WholeBudget()); }),
         "a carry from another nonce family was accepted at the top");
  la::LevelCarry short_carry = foreign;
  short_carry.family = job.family();
  short_carry.main = arena.WritableMain(b_lease, carry_buckets - 1);
  Expect(Throws([&] { job.Finish(short_carry, &scratch, WholeBudget()); }),
         "a carry that is not U_L buckets was accepted at the top");
  std::printf("  refusals: A's extent, the family, the ordinal, the scratch\n");
}

// The scratch sizing covers BOTH of the top's passes.  They are built by two
// pieces of code and sized by two more, so a disagreement would otherwise be
// found only by whichever pass happened to run into it first.
void TestScratchCoversBothTopPasses() {
  for (unsigned digit : {1u, 2u, 4u, 8u}) {
    const std::string at = " at D = " + std::to_string(digit);
    Case c;
    c.top_digit = digit;
    c.branching = WidestUsualFanoutFor(digit);
    const la::LevelArenaGeometry geometry(ParamsOf(c));
    const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
    const unsigned top = geometry.TopLevel();
    const size_t needed = la::MaxLevelMergeRangeBuckets(geometry, sizing, top);
    const la::MergeShape shape =
        la::MakeTopMergeShape(geometry.CarryBuckets(top), digit);
    const la::LevelMergePoolShape prepare = la::TopPreparePoolShapeOf(
        shape, sizing.Buckets(top), geometry.TierBuckets());
    const la::LevelMergePoolShape merge = la::TopMergePoolShapeOf(
        shape, sizing.Buckets(top), geometry.TierBuckets());
    Expect(prepare.swept_buckets > 0 && merge.swept_buckets > 0,
           "a top pass sweeps nothing" + at);
    Expect(needed >= la::TopPrepareRangePlan(prepare).range_buckets,
           "the top's scratch does not cover its preparation's pass" + at);
    Expect(needed >= la::LevelFinishRangePlan(merge).range_buckets +
                         merge.direct_buckets,
           "the top's scratch does not cover its merge's pass" + at);
    Expect(merge.direct_buckets == geometry.TierBuckets(),
           "the top's merge does not offer B's tier directly" + at);
  }
  // ONLY A BINARY TOP: the others have no certified preparation, so no
  // geometry and no top shape takes one.
  for (unsigned digit : {3u, 5u, 6u, 7u}) {
    Case c;
    c.top_digit = digit;
    c.branching = 8;
    Expect(Throws([&] { la::LevelArenaGeometry geometry(ParamsOf(c)); }),
           "a geometry accepted the nonbinary top D = " + std::to_string(digit));
    Expect(Throws([&] { la::MakeTopMergeShape(16, digit); }),
           "a top shape accepted the nonbinary D = " + std::to_string(digit));
  }
  std::printf("  scratch: both top passes fit, D = 1, 2, 4, 8; nonbinary "
              "tops refused\n");
}

}  // namespace

int main() {
  TestTombstonesBesideRetainedEntries();
  std::printf("level arena, the top's compaction\n");
  TestRecomputedDigitsMatchAStoredRetag();
  TestSweepMatchesARetaggedCarry();
  TestScratchCoversBothTopPasses();
  TestTopRefusals();

  // THE ONE-PAGE DFS PREPARATION at B = 8, where its pool routes: forced
  // sheds, poisoned carry tags and an empty A, with pauses, lanes and helper
  // threads, and the pieces' charges against the estimate.
  for (unsigned digit : {1u, 2u, 4u, 8u}) {
    Case c;
    c.name = "DFS top preparation";
    c.branching = 8;
    c.top_digit = digit;
    c.forced_older = 72;
    c.forced_fresh = 24;
    c.poison_carry_tags = true;
    RunAndReport(c);
    c.empty_top = true;
    c.forced_older = 0;
    c.forced_fresh = 0;
    RunAndReport(c);
  }

  // EVERY TOP DIGIT.  1 is the binary fixed merge with no digit at all; 2, 4
  // and 8 route one butterfly over all of T and split the sweep on raw tag
  // bits.  A digit above 4 runs at B = 8, since the top
  // is no wider than B.
  for (unsigned digit : {1u, 2u, 4u, 8u}) {
    Case c;
    c.name = "digit";
    c.top_digit = digit;
    c.branching = WidestUsualFanoutFor(digit);
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // An EMPTY top, which is the first compaction of a hierarchy's life: the
  // preparation routes a table with nothing in it, and C is exactly the carry.
  {
    Case c;
    c.name = "empty top";
    c.top_digit = 2;
    c.empty_top = true;
    RunAndReport(c);
  }

  // TOMBSTONES, which only this rebuild may forget -- in A, in B and in both
  // tiers, on keys the other operand also holds.
  {
    Case c;
    c.name = "tombstones";
    c.top_digit = 4;
    c.tombstones = true;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // THE SAME TOMBSTONES, QUALIFIED as shadowing nothing, so the top forgets
  // them as it READS its sources rather than at the trailing drop over C.
  // Each of these cases runs ITSELF twice, once with the qualifier and once
  // without, and compares the two live sets (RunAndReport): the claim is that
  // the two ways of forgetting produce the same table, not merely that the
  // early one produces something the model tolerates.
  {
    Case c;
    c.name = "unshadowed tombstones";
    c.top_digit = 4;
    c.tombstones = true;
    c.unshadowed = true;
    // A MARGIN WITH TWO EDGES, which its pair above does not have.  A third
    // of the forced keys are tombstones, and the skip takes them out of A
    // before the preparation's route can pile them on the target bucket, so
    // its 72 stops overloading anything and the retained carry comes back
    // empty (nothing is retained at 72, 80 or 88).  But the comparison
    // run below forgets those same tombstones only at the END, so it carries
    // every forced key into one index of the merge pass's range table -- and
    // at 112 that pile no longer fits, which is a fixture limit and not a
    // result (`tier_buckets` buys the room and is already at the widest a
    // ResidualStash's inline occupancy array can describe).  The window is
    // 96..104; 100 sits in it with both guards satisfied on both runs.
    c.forced_older = 100;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // And at the NARROWEST top there is, which is the geometry the early skip
  // exists for: D = 1's sweep is one digit block wide, so it is the merge with
  // the least room to carry a tombstone it is going to drop anyway, and the
  // first to run out of it without the skip.
  {
    Case c;
    c.name = "unshadowed, D=1";
    c.top_digit = 1;
    c.tombstones = true;
    c.unshadowed = true;
    c.forced_older = 100;  // the same window, for the same reason
    RunAndReport(c);
  }

  // EARLY TOMBSTONE DROP. Some deleted keys exist only
  // in the preparation's retained carry. The sweep must clear those range
  // candidates before omitting the carry tombstones, or they resurrect.
  // Exercise D=1 and two binary tops whose ways are recomputed.
  for (unsigned digit : {1u, 4u, 2u}) {
    Case c;
    c.name = "carry erases retained keys";
    c.top_digit = digit;
    c.branching = WidestUsualFanoutFor(digit);
    c.forced_older = 72;
    c.erase_retained = true;
    RunAndReport(c);
  }

  // TIER TOMBSTONES AT A FULL HOME (REPORT.tex's local counterexample, at
  // native capacity): A fills one bucket of C, B's tier deletes those keys,
  // and B's main adds live keys for the same bucket.  Resolving first, the
  // live keys fit and nothing sheds; merging B's main before the tier's
  // deletions shed them.  D = 1 and every binary top, with tombstones
  // elsewhere too in one of them.
  for (unsigned digit : {1u, 2u, 4u, 8u}) {
    Case c;
    c.name = "tier erases a full home";
    c.top_digit = digit;
    c.branching = WidestUsualFanoutFor(digit);
    c.forced_older = 72;
    c.forced_fresh = 24;
    c.erase_in_tier = true;
    c.tombstones = digit == 4;
    RunAndReport(c);
  }

  // POISONED CARRY TAGS: every stored tag byte of B, the digit line included,
  // scribbled over before it is published.  The merge recomputes the one thing
  // it reads out of them, so the result must be unchanged -- and this is what
  // says so, rather than the argument that it should be.
  {
    Case c;
    c.name = "poisoned tags";
    c.branching = 8;
    c.top_digit = 8;
    c.poison_carry_tags = true;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }
  {
    Case c;
    c.name = "poisoned, D=1";
    c.top_digit = 1;
    c.poison_carry_tags = true;
    c.forced_older = 72;
    RunAndReport(c);
  }

  // The PACKED tag layout: U_L is 16 buckets, so the four index bits leave
  // room for the lower levels' digit in the same byte and PlanRoutingTag
  // drops the reserved one.  The top's raw route, its recomputed ways and the
  // residual retag read index bits above bit 4 of that same byte, and the
  // compaction is only correct if every one of them follows the layout.
  {
    Case c;
    c.name = "packed digit";
    c.top_digit = 2;
    c.tag_bytes = 1;
    c.digit_bits = 4;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // Wide keys at their stored width, and a tag wide enough to carry them.
  {
    Case c;
    c.name = "wide keys";
    c.branching = 8;
    c.top_digit = 8;
    c.key_bytes = 16;
    c.value_bytes = 24;
    c.tag_bytes = 5;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // B = 8 under a small top, so U_L is 32 buckets rather than 16 at a digit
  // the B = 4 cases also run: the carry is a different size at the same D.
  {
    Case c;
    c.name = "B=8";
    c.branching = 8;
    c.top_digit = 4;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // The fixed default key, which is what every standalone kernel and benchmark
  // uses: the job takes the key it is given, and that includes this one.
  {
    Case c;
    c.name = "default key";
    c.top_digit = 4;
    c.key_seed = 0;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  // The same compaction issued under a tight subtask budget, which slices
  // every phase into many small tasks: the plan is the same work either way,
  // and a phase that depended on being issued whole would show up here.
  {
    Case c;
    c.name = "sliced";
    c.top_digit = 2;
    c.sliced = true;
    c.forced_older = 72;
    c.forced_fresh = 24;
    RunAndReport(c);
  }

  Expect(g_dfs_preparations > 0,
         "no top preparation distributed through the DFS, so its gate "
         "compared nothing");
  Expect(g_dfs_finishes > 0,
         "no top finish distributed through the DFS, so its gate compared "
         "nothing");
  Expect(g_residual_charge_checks > 0,
         "no resumed run checked its residual charges against the estimate");
  std::printf("  residual charges matched LevelMergeResidualTouches in %llu "
              "resumed runs\n",
              (unsigned long long)g_residual_charge_checks);
  Expect(g_laned_stages > 0,
         "no compaction ran a stage in more than one lane, so the lane gate "
         "compared nothing");
  Expect(g_helper_lanes.load() > 0,
         "no helper thread ran a lane, so the helper gate compared nothing");
  std::printf("  helpers: %llu lanes run by helper threads\n",
              (unsigned long long)g_helper_lanes.load());
  Expect(g_helper_opened_stages > 0,
         "no interleaved helper opened a stage, so who is told of one was "
         "never checked");
  std::printf("  helpers: %llu stages opened by an interleaved helper\n",
              (unsigned long long)g_helper_opened_stages);
  std::printf("  lanes: %llu stages ran divided\n",
              (unsigned long long)g_laned_stages);
  // The offer stages are the ones private masks let lanes divide at all at
  // these sizes, whose range words span the whole stage.
  Expect(g_private_mask_stages > 0,
         "no offer stage ran its lanes on private range masks, so the lane "
         "gates never compared the AND against the one-lane masks");
  std::printf("  lanes: %llu offer stages ran on private range masks\n",
              (unsigned long long)g_private_mask_stages);
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena top checks failed\n", failures);
    return 1;
  }
  std::printf("level arena top compaction: OK\n");
  return 0;
}
