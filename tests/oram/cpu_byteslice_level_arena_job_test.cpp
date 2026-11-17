// The owning merge job of the level-arena engine (LevelMergeJob,
// src/oram/levelarena/cpu_byteslice_level_arena_job.hpp): a whole non-top
// merge over REAL ARENA SLOTS, including the residual passes.  A merge at
// digit d of level l combines the level's older table (operand A) with the
// fresher CARRY from the level below (B: a published table, or at level one
// the dense prefix of flushed stash buckets) into the output the level
// publishes next; the vocabulary is defined in src/oram/levelarena/DESIGN.md.
//
// cpu_byteslice_level_arena_merge_test.cpp drives the three phase planners over
// hand-built tables with no residual pass active.  That establishes the
// subtask stream and nothing about what a merge DOES with what it sheds, which
// is where this design's own decisions live:
//
//   - both input tiers have PRIVATE MASKS before any pass runs, so a pool dedup or a
//     reset can never write storage a request may be probing;
//   - the fresher class and the older class enter the finish's one pass as two
//     RANKS, with the ridden pass's shed as the drain-only prefix;
//   - level one's fresher class is B's direct-build tier, offered directly;
//   - at level one digit one the build writes the output and its tier itself.
//
// THE CLAIM EVERY CASE MAKES.  Over the output's main PLUS its tier, every key
// appears exactly once and with its newest value -- the carry's where both
// sources hold it, the older operand's where only it does -- and tombstones
// survive, because only the top may forget one.  Nothing is compared against
// another run of the same code: a model is built alongside the fixture and the
// merge is compared to that.
//
// AND WHAT IT MAY NOT TOUCH.  Every source is published storage.  Its bytes
// and its occupancy words are digested before the merge and again after, and
// a merge that wrote one of them fails here rather than racing a reader later.
//
// The cases sweep the merge shapes.  Every digit of B = 4 at level 1 (the
// dense builder, including its digit-1 shape) and at level 2 (the sparse
// install); B = 8's 5, 6, 7 and 8, which is where the odd parts B = 4 cannot
// reach live and where digit 6 is the one shape in the ladder running cross
// levels AND a radix pass; B = 2, which has no radix pass anywhere and whose
// digit-1 carry is level 1's real forward rather than a planted table.  Then
// forced sheds in both routing phases, nonempty tiers on both inputs with keys
// that conflict across main and tier, tombstones, wide keys, three tag layouts
// including the packed digit, Z >= 256 so that routing bits cross a tag byte
// boundary, a tight subtask budget -- and, for each, two identical runs
// compared to each other before a paused preparation is compared with an
// uninterrupted one.
//
// AND WHO IS TOLD WHEN A STAGE OPENS.  A helper that finishes a stage's last lane opens the next one, and the owner
// may be parked waiting for exactly that, so it has to be signalled; an owner
// that opens a stage itself must not signal its own event, which would stop
// the phase it is in.  InterleavedHelper takes the helper's turns on the
// fixture's thread, between the owner's pieces, so that every such opening is
// one the fixture can attribute rather than one a race decided.
//
// What is NOT swept: B = 8's digits 2, 3 and 4, whose (r, e) shapes B = 4
// already covers, and any level above 2, whose operands are megabytes while
// these fixtures plant entries one slot at a time.

#include <immintrin.h>

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <functional>
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
#include "src/oram/rebuild/cpu_byteslice_rebuild.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace la = microram::byteslice::levelarena;
namespace ts = microram::byteslice::test_support;

int failures = 0;
size_t g_dfs_finishes = 0;  // finishes that ran the DFS distributor
// Directly built level-one finishes that reached the SHED-KEY TRAP: a B-main
// key in the merge stash while an older copy of it waits in A's residual
// pool, which only the epilogue may resolve.
size_t g_direct_trap_witnesses = 0;

// Counts rather than exits, so one broken case does not hide the rest -- and
// so that a failure inside a case still runs that case's remaining checks,
// which is usually what says WHICH thing broke.
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

// The request horizon every case is certified for.  Large enough that the
// stash depth is not the trivial one, small enough to build quickly.
constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

bs::SubtaskBudget WholeBudget() {
  return bs::SubtaskBudget{~size_t{0}, ~size_t{0}, ~size_t{0},
                           ~size_t{0}, ~size_t{0}, ~size_t{0}};
}
bs::SubtaskBudget SlicedBudget() {
  return bs::SubtaskBudget{3, 2, 2, 24, 5, 3};
}

// ---------------------------------------------------------------------------
// One case
// ---------------------------------------------------------------------------

struct Case {
  const char* name = "";
  unsigned branching = 4;
  unsigned levels = 3;
  unsigned prefix_flushes = 2;
  size_t stash_buckets = 1;
  unsigned level = 2;
  unsigned digit = 2;
  size_t key_bytes = 8;
  size_t value_bytes = 8;
  size_t tag_bytes = 4;
  // The PACKED tag layout: the radix digit shares the top index byte instead
  // of getting a reserved one of its own, which moves it and every routing bit
  // above it (Layout::digit_bits).  0 is the unpacked form every hand-built
  // Layout gets.
  size_t digit_bits = 0;
  bool tombstones = false;
  // Keys forced onto one destination index, so a routing phase overloads a
  // bucket and has to shed.  0 leaves the fixture at its natural load, where
  // nothing sheds and the residual wiring is exercised but never loaded.
  //
  // A MARGIN, not a threshold.  How many forced keys it takes to overflow a
  // bucket depends on where the rest of the load fell, which depends on the
  // instance key: 50 sheds under one key and not under another, and three
  // cases sitting on that line stopped loading the residual wiring the moment
  // the fixture got a key of its own.  RunAndReport's "nothing shed" guard is
  // what catches that, which is why these counts sit well above the line
  // rather than at the smallest value that once worked.
  size_t forced_older = 0;
  size_t forced_fresh = 0;
  // Sparse digit 1 only: the carry is PRODUCED, not planted.  The level
  // below's forwarding merge runs first, in the same arenas and under the two
  // forced counts above, and this case consumes what it published.  A planted
  // tier can aim an entry at any bucket; a produced one holds only what a real
  // residual pass could not place, which is why the digit-1 pass may drain
  // it without offering it.
  size_t tier_buckets = 1;
  bool produced_carry = false;
  bool split = true;   // prepare, pause, then install and finish
  bool sliced = false; // issue the phases under a tight subtask budget
  // THE INSTANCE'S AES KEY, as a seed to derive it from.  The tag PRF's key
  // is the per-ORAM secret and the nonce is public, so a job that used
  // the fixed default key would put every entry it routes at a position
  // anyone can recompute -- and a fixture that planted, routed and checked
  // under that same default would agree with it perfectly.  Every case here
  // therefore runs under a key of its own; 0 means the default one, which is
  // what keeps the plumbing tested in both directions.
  uint64_t key_seed = 0x5EED0C0DEull;
  // The bank-first run: where the geometry puts this digit and the one
  // before it.
  la::BankFirst bank_first = la::BankFirst::kOff;
};

bs::Layout LayoutOf(const Case& c) {
  bs::Layout layout;
  layout.key_bytes = c.key_bytes;
  layout.value_bytes = c.value_bytes;
  layout.tag_bytes = c.tag_bytes;
  layout.digit_bits = c.digit_bits;
  return layout;
}

la::LevelArenaGeometry::Params ParamsOf(const Case& c) {
  la::LevelArenaGeometry::Params p;
  p.tier_buckets = c.tier_buckets;
  p.branching = c.branching;
  p.levels = c.levels;
  p.top_digit = 2;
  p.prefix_flushes = c.prefix_flushes;
  p.stash_buckets = c.stash_buckets;
  p.bank_first = c.bank_first;
  return p;
}

// What the merge should produce, accumulated as the fixture plants entries.
// `value` tells the two sources apart (1 older, 2 fresher) and `meta` carries
// the tombstone bit, which a non-top merge may not drop.
using Model = std::map<bs::KeyWords, ts::LiveEntry>;

// Where each of `keys` belongs in the output, recomputed FROM THE KEY.
//
// Not from the stored tag, and the difference is the whole point: a residual
// second chance moves PAYLOAD LINES only (rp.lines == PayloadLines()), so an
// entry the sweep put back carries whatever tag bytes were in that slot
// before.  Reading those back would call every re-placed entry mis-routed.
// What must hold for every live entry, however it got there, is that a
// request looking for its key probes the bucket it is in -- which is this.
//
// The flat destination is ApplyRadixIndexMap with digit_shift == low_bits:
// the low index bits, and the radix digit as the block number.  Asking
// ComputeRoutingTags for that map gives it directly, since the raw AES tag
// does not depend on which map is applied to it.
std::vector<size_t> DestinationBuckets(const bs::Layout& layout,
                                       const bs::RebuildNonce& nonce,
                                       const la::MergeShape& shape,
                                       const bs::AesTagKeys& aes_keys,
                                       const std::vector<bs::KeyWords>& keys) {
  bs::RoutingIndexMap flat;
  if (shape.has_radix_pass()) {
    flat.kind = bs::TagMapKind::kRadixDigit;
    flat.low_bits = shape.block_bits;
    flat.modulus = shape.odd_part;
    flat.digit_shift = shape.block_bits;  // the FLAT form
  }
  const unsigned bits = shape.block_bits + (shape.has_radix_pass() ? 3 : 0);
  std::vector<size_t> buckets;
  buckets.reserve(keys.size());
  bs::Table probe = ts::ZeroedTable(1, layout);
  for (size_t i = 0; i < keys.size(); i += bs::kBucketCapacity) {
    const size_t n = std::min(bs::kBucketCapacity, keys.size() - i);
    for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
      ts::PlantEntry(layout, probe.Bucket(0), slot,
                     keys[i + std::min(slot, n - 1)], 0);
    }
    bs::TableView v = bs::View(probe);
    bs::ComputeRoutingTags(v, nonce.real_lo, nonce.real_hi, flat, bits,
                           aes_keys);
    for (size_t slot = 0; slot < n; ++slot) {
      buckets.push_back(static_cast<size_t>(
          ts::SlotTagBitsOf(layout, probe.Bucket(0), slot, bits)));
    }
  }
  return buckets;
}

std::string Describe(const Case& c) {
  return std::string(c.name) + " (B=" + std::to_string(c.branching) +
         " level=" + std::to_string(c.level) +
         " digit=" + std::to_string(c.digit) +
         (c.bank_first == la::BankFirst::kOff
              ? std::string()
              : std::string(" bank-first ") + la::BankFirstName(c.bank_first)) +
         ")";
}

// ---------------------------------------------------------------------------
// The fixture
// ---------------------------------------------------------------------------

// Stages that ran in more than one lane, over every laned run, and lanes the
// helper threads ran: a gate that saw none tested nothing.
uint64_t g_laned_stages = 0;
// Runs whose residual charges were checked against LevelMergeResidualTouches.
uint64_t g_residual_charge_checks = 0;
// Offer stages whose lanes cleared private range masks.
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

// Stages a helper opened, over every interleaved run: a gate that saw none
// tested nothing.
uint64_t g_helper_opened_stages = 0;

// A HELPER'S TURNS TAKEN ON THE FIXTURE'S OWN THREAD.  The owner stops after
// every piece and puts its lane back; a turn takes that lane, or the next
// unclaimed one, and runs it to its end, as LevelHelpers would.  Whoever runs
// a stage's last lane opens the next stage, so here both the owner and the
// helper open stages, each at a point the fixture knows, and the signals
// either sends can be checked against who sent them.  Off, both calls are
// pass-throughs and nothing is attached.
class InterleavedHelper {
 public:
  InterleavedHelper(la::LevelMergeJob* job, bool on,
                    const bs::SubtaskBudget& budget, std::string name)
      : job_(on ? job : nullptr), name_(std::move(name)) {
    if (on) job->AttachHelpers(&helpers_, &owner_, budget);
  }

  // One of the owner's calls, which must leave the owner's event alone: in
  // an owner thread a signal to its own event stops the phase it runs.
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

struct CaseResult {
  std::vector<uint8_t> occupied_output;
  Model live;               // output main + tier
  bool unique = true;
  uint64_t out_digest = 0;  // the output main's bytes, for split-vs-unsplit
  size_t carry_tier = 0;    // a produced carry's leftovers, for the report
};

// `into`, when given, is the arena set of the case that consumes this one's
// output as its carry: the merge runs there and its destination is published
// at the end, the way an owner hands a forwarded table to the level above.
// `resumed` drives every phase through the job's cursor at the sliced budget,
// stopping after EVERY piece and resuming (preemptibility), and `lanes`
// divides every stage that may be divided into up to that many lanes.
//
// `helpers` more threads run lanes of the job's phases alongside this one
// (LevelMergeJob::HelpOnce: one thread against several at one lane count
// must be the same bytes).  `interleaved` takes a helper's turn on
// this thread after each of the owner's stops instead (InterleavedHelper);
// it needs `resumed` and no helper threads.
CaseResult RunCase(const Case& c, bool split, size_t* shed_out,
                   la::LevelArenaSet* into = nullptr, bool resumed = false,
                   size_t lanes = 1, unsigned helpers = 0,
                   bool interleaved = false) {
  if (interleaved && (!resumed || helpers != 0)) {
    throw std::logic_error("an interleaved run stops after every piece and "
                           "has no helper threads");
  }
  const bs::Layout layout = LayoutOf(c);
  // Derived, not stored, so a case is still one line: everything downstream
  // -- the keys chosen to force a shed, the carry's own route, the job, and
  // the check that recomputes where each key belongs -- reads this one
  // object, and a job that ignored it would misroute against all three.
  const std::unique_ptr<bs::AesTagKeys> instance_keys =
      c.key_seed == 0 ? nullptr
                      : bs::MakeAesTagKeys(microram::crypto::DeriveAesRoundKeys(
                            microram::crypto::SecretKeySeed::Fixed(c.key_seed)));
  const bs::AesTagKeys& keys =
      instance_keys == nullptr ? bs::DefaultAesTagKeys() : *instance_keys;
  const la::LevelArenaGeometry geometry(ParamsOf(c));
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  std::unique_ptr<la::LevelArenaSet> own_arenas;
  if (into == nullptr) {
    own_arenas = std::make_unique<la::LevelArenaSet>(geometry, layout);
  }
  la::LevelArenaSet& arenas = into != nullptr ? *into : *own_arenas;
  const bool dense = c.level == 1;
  const size_t carry_buckets = geometry.CarryBuckets(c.level);
  const unsigned carry_bits = bs::Log2Exact(carry_buckets);

  // The ordinal whose digit is the one under test: v = digit works, since
  // the digit is 1 + (v - 1) mod B.
  const uint64_t ordinal = c.digit;
  const la::Family family =
      la::CanonicalFamily(geometry, c.level, ordinal);
  const bs::RebuildNonce nonce = la::FamilyNonce(family);
  const la::CarryPlan carry_plan = geometry.PlanCarry(c.level, ordinal);
  if (carry_plan.outcome == la::CarryOutcome::kAdopt) {
    throw std::logic_error("this digit adopts and runs no merge");
  }

  const unsigned radix = c.digit >> static_cast<unsigned>(_tzcnt_u32(c.digit));
  const la::MergeShape shape =
      la::MakeMergeShape(carry_buckets, c.digit, radix);
  bs::RoutingIndexMap map;
  if (radix > 1) {
    map.kind = bs::TagMapKind::kRadixDigit;
    map.low_bits = shape.block_bits;
    map.modulus = radix;
    map.digit_shift = bs::RoutingDigitShift(layout);
  }

  Model model;
  uint64_t next_key = 1;
  std::mt19937_64 rng(0xA55E + 97 * c.level + 7 * c.digit + c.branching);
  const uint8_t tomb = c.tombstones ? bs::kMetaErased : 0;

  // ---- the older operand -------------------------------------------------
  //
  // P_(digit-1), read where the previous ordinal's merge left it, so it is
  // PlanCarry of that ordinal that says where:
  //
  //   - ADOPTED (digit 2 at a fanout-4 or -8 level above level 1, and at a
  //     binary one only in the compact layout): the inbox P_1 arrived in.  The
  //     carry takes inbox[0] here, so P_1 is in inbox[1];
  //   - an ODD partial: this level's own odd bank.  In the default layout that
  //     includes a binary level's P_1, which digit 1 installs there
  //     (NeedsOddBank) instead of adopting it;
  //   - an EVEN partial: the level above's inbox[0], built there under the
  //     forwarding lease;
  //   - a bank-first run's even partial: the run bank, at the offset the
  //     run places it at.
  la::LevelArena& arena = arenas.At(c.level);
  std::vector<bs::KeyWords> older_keys;
  ts::PublishedSource older;
  const size_t older_buckets = shape.older_buckets;
  if (c.digit > 1) {
    const la::CarryPlan older_plan = geometry.PlanCarry(c.level, ordinal - 1);
    la::LevelArena& older_arena = arenas.At(older_plan.destination_level);
    unsigned older_slot = older_arena.plan().inbox[0];
    if (older_plan.outcome == la::CarryOutcome::kAdopt) {
      older_slot = older_arena.plan().inbox[1];
    } else if (older_plan.destination_kind == la::SlotKind::kOddBank) {
      older_slot = older_arena.plan().odd_bank;
    } else if (older_plan.destination_kind == la::SlotKind::kRunBank) {
      older_slot = older_arena.plan().run_bank;
    }
    // Keys aimed at one destination index, so a preparation butterfly
    // overloads a bucket and sheds; the rest are spread.
    std::vector<bs::KeyWords> forced =
        c.forced_older == 0
            ? std::vector<bs::KeyWords>()
            : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, map,
                                 shape.block_bits, shape.block_bits,
                                 /*target=*/0, c.forced_older, &next_key,
                                 keys);
    older = ts::PublishSlot(
        &older_arena, older_slot, older_buckets, layout,
        [&](bs::TableView main, bs::ResidualStash* tier) {
          size_t taken = 0;
          const size_t per_bucket = 16;
          for (size_t b = 0; b < main.num_buckets; ++b) {
            for (size_t slot = 0; slot < per_bucket; ++slot) {
              const bs::KeyWords key =
                  taken < forced.size()
                      ? forced[taken++]
                      : ts::FixtureKey(next_key++, layout.key_bytes);
              ts::PlantEntry(layout, main.Bucket(b), slot, key, 1, tomb);
              model[key] = {1, tomb};
              older_keys.push_back(key);
            }
            for (size_t slot = per_bucket; slot < bs::kBucketCapacity; ++slot) {
              bs::WriteSlotKey(main.Bucket(b), slot, layout.key_bytes,
                               ts::FixtureKey(rng() % next_key,
                                              layout.key_bytes));
            }
            main.masks[b] = bs::LowMask64(static_cast<unsigned>(per_bucket));
          }
          // A NONEMPTY OLDER TIER, disjoint from the main: the two are one
          // internally unique source, and the pass's older class is both.
          std::vector<bs::KeyWords> tier_keys;
          for (int i = 0; i < 12; ++i) {
            tier_keys.push_back(ts::FixtureKey(next_key++, layout.key_bytes));
            older_keys.push_back(tier_keys.back());
          }
          ts::PlantTier(layout, tier, tier_keys, 1, tomb, &model);
        },
        older_plan.destination_offset);
  }

  // ---- the fresher operand -----------------------------------------------
  //
  // Sparse: a published table of U buckets, routed under the family nonce --
  // the same nonce this merge uses, which is what lets the install re-tag
  // without re-routing.  Dense: the complete frozen prefix.
  ts::PublishedSource carry;
  size_t carry_tier_entries = 0;
  bs::Table prefix;
  uint64_t prefix_digest = 0;
  const size_t fresh_keys_wanted = dense ? 0 : carry_buckets * 16;
  // A produced carry's forced counts are its producer's, under its nonce.
  const std::vector<bs::KeyWords> forced_fresh =
      c.forced_fresh == 0 || c.produced_carry
          ? std::vector<bs::KeyWords>()
          : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, map,
                               shape.block_bits,
                               dense ? bs::Log2Exact(
                                           geometry.RoutedPrefixBuckets())
                                     : shape.block_bits,
                               /*target=*/0, c.forced_fresh, &next_key, keys);

  // A third of the fresher keys shadow the older operand, so the merge has
  // real duplicates to resolve across main, tier and sheds.
  const auto fresher_key = [&](size_t i, std::vector<bs::KeyWords>* used) {
    if (i < forced_fresh.size()) return forced_fresh[i];
    if (!older_keys.empty() && rng() % 3 == 0) {
      const bs::KeyWords candidate = older_keys[rng() % older_keys.size()];
      if (std::find(used->begin(), used->end(), candidate) == used->end()) {
        return candidate;
      }
    }
    return ts::FixtureKey(next_key++, layout.key_bytes);
  };

  if (dense) {
    const size_t log_buckets = geometry.DensePrefixBuckets();
    const size_t unit = geometry.StashBuckets();
    prefix = ts::ZeroedTable(log_buckets, layout);
    // r0 units of s FULL buckets, which is what an online-stash flush is.  A
    // key may repeat across units -- the builder keeps the newest -- but never
    // within one, which is internally unique by construction.
    for (unsigned u = 0; u < geometry.PrefixFlushes(); ++u) {
      std::vector<bs::KeyWords> in_unit;
      for (size_t sb = 0; sb < unit; ++sb) {
        const size_t b = u * unit + sb;
        for (size_t slot = 0; slot < bs::kBucketCapacity; ++slot) {
          const size_t i = (u * unit + sb) * bs::kBucketCapacity + slot;
          const bs::KeyWords key = fresher_key(i, &in_unit);
          in_unit.push_back(key);
          ts::PlantEntry(layout, prefix.Bucket(b), slot, key, 2, tomb);
          model[key] = {2, tomb};  // units are planted oldest first
        }
        prefix.masks[b] = ~uint64_t{0};
      }
    }
    prefix_digest = ts::DigestTable(bs::View(prefix));
  } else if (c.produced_carry) {
    // The level below forwards into this level's inbox[0] under this digit's
    // own family (a forward shares its receiver's nonce), so running
    // that merge first, here, leaves exactly the table an engine hands this
    // job.  Its RunCase checks it like any other output before it is handed
    // on, so its live set is this case's model.
    Case producer = c;
    producer.level = c.level - 1;
    producer.digit = geometry.Fanout(producer.level);
    producer.produced_carry = false;
    const la::CarryPlan forward =
        geometry.PlanCarry(producer.level, producer.digit);
    if (c.digit != 1 || forward.outcome != la::CarryOutcome::kForward ||
        forward.destination_level != c.level ||
        la::CanonicalFamily(geometry, producer.level, producer.digit) !=
            family) {
      throw std::logic_error(
          "a produced carry is a digit-1 carry forwarded from the level "
          "below under its own family");
    }
    size_t producer_shed = 0;
    model = RunCase(producer, split, &producer_shed, &arenas).live;
    carry.arena = &arena;
    carry.slot = arena.plan().inbox[0];
    carry.buckets = carry_buckets;
    carry.Digest(layout);

    // 7(a)'S PREMISE, on a carry an engine can publish: every tier entry is
    // aimed at a FULL bucket.  A leftover exists only because its bucket
    // ended full, and nothing lowers a non-top main's occupancy after its
    // offer.  The target is recomputed from the key, under this job's own
    // map, because that is the bucket an offer would have used.
    const bs::TableView carry_main = carry.Main();
    const bs::ResidualStash& carry_tier = *carry.Tier();
    std::vector<bs::KeyWords> tier_keys;
    for (size_t b = 0; b < carry_tier.num_buckets; ++b) {
      uint64_t mask = carry_tier.masks[b];
      while (mask != 0) {
        const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
        mask &= mask - 1;
        tier_keys.push_back(
            ts::SlotKeyWordsOf(layout, carry_tier.Bucket(b), slot));
      }
    }
    carry_tier_entries = tier_keys.size();
    // Without leftovers the pass has nothing to offer, and the checks below
    // would pass for any pass at all.
    Expect(!tier_keys.empty(),
           Describe(c) + ": the producer left nothing in its tier, so the "
                         "digit-1 pass is not loaded");
    size_t open = 0;
    for (size_t target :
         DestinationBuckets(layout, nonce, shape, keys, tier_keys)) {
      if (carry_main.masks[target] != ~uint64_t{0}) ++open;
    }
    Expect(open == 0,
           Describe(c) + ": " + std::to_string(open) + " of " +
               std::to_string(tier_keys.size()) +
               " carry-tier entries are aimed at a bucket with a free lane");
  } else {
    const unsigned inbox = arena.plan().inbox[0];
    carry = ts::PublishSlot(
        &arena, inbox, carry_buckets, layout,
        [&](bs::TableView main, bs::ResidualStash* tier) {
          std::vector<bs::KeyWords> used;
          const size_t per_bucket = 16;
          for (size_t i = 0; i < fresh_keys_wanted; ++i) {
            used.push_back(fresher_key(i, &used));
          }
          for (size_t b = 0; b < main.num_buckets; ++b) {
            const size_t count = b * per_bucket < used.size()
                ? std::min(per_bucket, used.size() - b * per_bucket) : 0;
            for (size_t slot = 0; slot < count; ++slot) {
              const bs::KeyWords key = used[b * per_bucket + slot];
              ts::PlantEntry(layout, main.Bucket(b), slot, key, 2, tomb);
              model[key] = {2, tomb};
            }
            for (size_t slot = count; slot < bs::kBucketCapacity; ++slot) {
              bs::WriteSlotKey(main.Bucket(b), slot, layout.key_bytes,
                               ts::FixtureKey(rng() % next_key,
                                              layout.key_bytes));
            }
            main.masks[b] = bs::LowMask64(static_cast<unsigned>(count));
          }
          // Published as its own power-of-two table: kRaw over its K bits,
          // under the FAMILY nonce.  The merge re-tags these same entries
          // under the same nonce and a wider map, which changes their higher
          // bits and their radix digit and leaves the low K alone.
          bs::ComputeRoutingTags(main, nonce.real_lo, nonce.real_hi,
                                 bs::RoutingIndexMap{}, carry_bits, keys);
          // The fixture's own route, at the same certified depth the engine
          // would give it: a carry that shed here would be an incomplete
          // published table, which is a broken fixture and not a result.
          const size_t route_depth = sizing.Buckets(c.level);
          const size_t route_bytes =
              carry_bits * route_depth * layout.BucketBytes();
          // AllocateAligned64, not a vector: the routing kernels load stash
          // lines with _mm512_load_si512, which faults on anything less.
          bs::Aligned64Ptr route_store = bs::AllocateAligned64(route_bytes);
          std::memset(route_store.get(), 0, route_bytes);
          std::vector<bs::ResidualStash> route(carry_bits);
          for (unsigned b = 0; b < carry_bits; ++b) {
            route[b].data =
                route_store.get() + b * route_depth * layout.BucketBytes();
            route[b].num_buckets = route_depth;
            route[b].entry_bytes = layout.EntryBytes();
          }
          if (!bs::ButterflyRouteStashCacheOblivious<true>(main, carry_bits,
                                                           route.data())) {
            throw std::logic_error("the fixture's carry route overflowed");
          }
          for (unsigned b = 0; b < carry_bits; ++b) {
            if (route[b].Count() != 0) {
              throw std::logic_error("the fixture's carry shed while routing");
            }
          }
          // A NONEMPTY FRESHER TIER, holding keys the older operand also has:
          // the pass's fresher class must beat the older copy of each.
          std::vector<bs::KeyWords> tier_keys;
          for (size_t i = 0; i < older_keys.size() && tier_keys.size() < 12; ++i) {
            const auto key = older_keys[(i + 3) % older_keys.size()];
            if (std::find(used.begin(), used.end(), key) == used.end())
              tier_keys.push_back(key);
          }
          ts::PlantTier(layout, tier, tier_keys, 2, tomb, &model);
        });
  }

  if (!dense) {
    Model union_b;
    bool unique_b = true;
    size_t damage_b = 0;
    ts::CollectLive(carry.Main(), &union_b, &unique_b, &damage_b);
    ts::CollectLiveStashes(layout, carry.Tier(), 1, &union_b, &unique_b, &damage_b);
    Expect(unique_b && damage_b == 0, Describe(c) + ": B main/tier contract");
  }

  // ---- the destination ----------------------------------------------------

  la::LevelArena& dest_arena = arenas.At(carry_plan.destination_level);
  unsigned dest_slot = la::kNoSlot;
  switch (carry_plan.destination_kind) {
    case la::SlotKind::kInbox:
      dest_slot = dest_arena.plan().inbox[0];
      break;
    case la::SlotKind::kOddBank:
      dest_slot = dest_arena.plan().odd_bank;
      break;
    case la::SlotKind::kRunBank:
      dest_slot = dest_arena.plan().run_bank;
      break;
    default:
      throw std::logic_error("a non-top merge does not publish to a top bank");
  }
  la::SlotLease dest;
  if (!dest_arena.TryLeaseOwn(dest_slot, &dest)) {
    throw std::logic_error("the fixture could not lease the destination");
  }

  // ---- the job ------------------------------------------------------------

  la::LevelMergeJob job(geometry, sizing, layout, c.level, keys, lanes);
  HelperThreads helper_threads(&job, helpers,
                               c.sliced || resumed ? SlicedBudget()
                                                   : WholeBudget());
  InterleavedHelper interleave(&job, interleaved, SlicedBudget(), Describe(c));
  std::unique_ptr<la::LevelMergeScratch> scratch_store =
      std::make_unique<la::LevelMergeScratch>(
          layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, c.level),
          la::MaxLevelDfsAllocation(geometry, sizing, c.level));
  la::LevelMergeScratch* const scratch = scratch_store.get();

  const bs::SubtaskBudget budget =
      c.sliced || resumed ? SlicedBudget() : WholeBudget();
  // Called after the finish's last offer, before its epilogue (single
  // threaded runs only, where the pieces are the owner's).
  std::function<void()> before_epilogue;
  const bool fused_offers = c.digit > 1;
  const auto last_offer = [&](const bs::Subtask& piece) {
    if (piece.kind == bs::Subtask::kFixedMergeOffers)
      return piece.end == shape.carry_buckets;
    if (piece.kind == bs::Subtask::kCrossLevelOffers)
      return piece.end == size_t{1} << (shape.block_bits - 1);
    if (piece.kind == bs::Subtask::kRadixPassOffers)
      return piece.end == size_t{1} << shape.block_bits;
    return false;
  };
  // Whether the DFS range builder actually ran.
  size_t dfs_pieces = 0;
  size_t cross_pieces = 0, insertion_pieces = 0;
  // What the owner's pieces were charged for residual work (ResidualCharge).
  uint64_t residual_charged = 0;
  // Resumed, every piece asks to stop, and every stop is resumed at once.
  size_t stops = 0;
  const auto stop = [&](const bs::Subtask& piece) {
    ++stops;
    cross_pieces += piece.kind == bs::Subtask::kCrossLevelRange ||
                    piece.kind == bs::Subtask::kCrossLevelOffers ||
                    piece.kind == bs::Subtask::kRadixPassRange ||
                    piece.kind == bs::Subtask::kRadixPassOffers;
    insertion_pieces += piece.kind == bs::Subtask::kFixedMergeOffers;
    residual_charged += ts::ResidualCharge(piece);
    dfs_pieces += piece.kind == bs::Subtask::kResidualDfsPartition;
    if (before_epilogue && fused_offers && helpers == 0 && !interleaved &&
        last_offer(piece)) {
      before_epilogue();
    }
    return resumed;
  };

  la::LevelMergeBinding binding;
  binding.ordinal = ordinal;
  binding.out = dest_arena.WritableMain(dest, carry_plan.destination_offset,
                                        shape.out_buckets);
  binding.out_tier = dest_arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  const bs::TableView published = binding.out;
  uint8_t* const assigned_tier = binding.out_tier->data;
  uint64_t* const assigned_tier_masks = binding.out_tier->masks;
  if (c.digit > 1) {
    binding.older_main = older.Main();
    binding.older_tier = older.Tier();
  }
  // The output's bytes are a leased slot's; a previous occupancy's are still
  // in them, and a merge that only wrote part of its output would otherwise
  // read as correct because the rest happened to be zero.
  const size_t poisoned = shape.out_buckets;
  std::memset(binding.out.data, 0xA5, poisoned * layout.BucketBytes());
  for (size_t b = 0; b < poisoned; ++b) binding.out.masks[b] = 0;
  // The tier is part of the published table and so part of the byte-identity
  // claim; its slack lanes come from the same uncleared arena.
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * layout.BucketBytes());

  la::LevelCarry incoming;
  incoming.ordinal = ordinal;
  if (dense) {
    incoming.dense_prefix = bs::View(prefix);
  } else {
    incoming.family = family;
    incoming.main = carry.Main();
    incoming.tier = carry.Tier();
  }

  job.Begin(binding);
  Expect(job.digit() == c.digit && job.family() == family &&
             job.nonce().real_hi == nonce.real_hi &&
             job.nonce().real_lo == nonce.real_lo,
         Describe(c) + ": the job derived a different coordinate than the "
                       "fixture placed its carry under");
  if (resumed || helpers > 0) {
    if (split) {
      while (!interleave.Owner(
          [&] { return job.ContinuePrepare(budget, scratch, stop); })) {
        interleave.Turn();
      }
    }
    while (!interleave.Owner([&] {
      return job.ContinueInstall(incoming, budget, scratch, stop);
    })) {
      interleave.Turn();
    }
  } else {
    if (split) job.PrepareOlder(budget);
    job.InstallCarry(incoming, budget);
  }
  // The main as the install left it: a copy of the carry's, so the full
  // buckets checked above are the ones the tier's entries target.  A digit-1
  // finish is its one pass and nothing else.
  std::vector<uint64_t> installed_masks;
  // And the thread's range scratch, poisoned: a drain-only pass builds no
  // range table, so the finish must leave every byte of it alone.
  uint64_t range_digest = 0;
  if (c.produced_carry) {
    installed_masks.assign(binding.out.masks,
                           binding.out.masks + binding.out.num_buckets);
    const bs::TableView carry_main = carry.Main();
    Expect(std::equal(installed_masks.begin(), installed_masks.end(),
                      carry_main.masks),
           Describe(c) + ": the install did not copy the carry's occupancy");
    const bs::TableView range = scratch->Range(scratch->range_buckets());
    std::memset(range.data, 0x3C, range.num_buckets * layout.BucketBytes());
    std::fill_n(range.masks, range.num_buckets, uint64_t{0x3C3C});
    range_digest = ts::DigestTable(range);
  }
  // Counted HERE, between the install and the finish: the finish's pass ends
  // in a kResidualReset that empties every owned slot, so after it the sheds
  // are gone whether they were resolved or drained.  A count of shed entries
  // is secret and nothing in the engine may branch on it; a checked fixture
  // is the only place for such a check.
  size_t shed = 0;
  for (size_t s = 0; s < job.older_shed_slots(); ++s) {
    shed += job.older_sheds()[s].Count();
  }
  // A direct build's leftovers: B's tier, or the output tier at digit 1.
  if (job.dense()) {
    shed += c.digit > 1 ? job.dense_tier()->Count()
                        : binding.out_tier->Count();
  }
  *shed_out = shed;
  // THE SLOTS THE POOL DOES NOT COVER MUST BE EMPTY.  A route `n` bits deep
  // owns stash slots [0, n), and the finish's pool offers exactly those back
  // -- plus the radix pass's own slot, which is the drain-only prefix when it
  // runs.  Everything above is slack: the quad's one-past index, and the fixed
  // merge's slot, which no non-top merge has.  An entry that landed in one of
  // them would be in no pool, would never be offered back or drained, and
  // would be reset away at the end of the pass without a word.
  for (size_t s = shape.block_bits; s < job.older_shed_slots(); ++s) {
    if (s == shape.block_bits + 1 && shape.has_radix_pass()) continue;
    Expect(job.older_sheds()[s].Count() == 0,
           Describe(c) + ": slot " + std::to_string(s) +
               " of the older sheds is outside every pool and is not empty");
  }
  // THE SHED-KEY TRAP, seen after the last offer and before the epilogue:
  // the merge stash (B-main sheds, drain-only) against A's swept route and
  // radix stashes.  A shared key there is an older A copy that must stay a
  // leftover for the leftover dedup to remove; the model check below is what
  // says it did.
  if (job.dense() && c.digit > 1) {
    const std::function<void()> previous = before_epilogue;
    before_epilogue = [&, previous] {
      if (previous) previous();
      Model shed, pool;
      bool unique = true;
      size_t damage = 0;
      ts::CollectLiveStashes(
          layout,
          job.older_sheds() + shape.block_bits + la::kLevelMergeMergeStashOffset,
          1, &shed, &unique, &damage);
      ts::CollectLiveStashes(layout, job.older_sheds(), shape.block_bits,
                             &pool, &unique, &damage);
      if (shape.has_radix_pass()) {
        ts::CollectLiveStashes(
            layout,
            job.older_sheds() + shape.block_bits + la::kLevelMergeRadixStashOffset,
            1, &pool, &unique, &damage);
      }
      for (const auto& kv : shed) g_direct_trap_witnesses += pool.count(kv.first);
    };
  }
  if (resumed || helpers > 0) {
    while (!interleave.Owner(
        [&] { return job.ContinueFinish(scratch, budget, stop); })) {
      interleave.Turn();
    }
  } else {
    // Whole, but through the resumable form, so the witness sees the finish
    // between its last offer and its epilogue.
    if (!job.ContinueFinish(scratch, budget, stop)) {
      throw std::logic_error("a whole finish stopped");
    }
  }
  helper_threads.Stop();
  if (la::SeparatedSources(geometry, c.level, c.digit) && helpers == 0 &&
      !interleaved) {
    Expect(cross_pieces == 0 && insertion_pieces > 0,
           Describe(c) + ": separated route ran cross-source stages");
  }
  // Every distributing finish below the top is DFS (the certified routing);
  // only a pool whose plan is direct routes nothing at all.
  if (helpers == 0 && !interleaved) {
    const auto pool = la::FinishPoolShapeAt(geometry, sizing.Buckets(c.level),
                                            c.level, shape);
    const bool dfs_applies =
        la::FinishRunsPass(geometry, c.level, c.digit) &&
        bs::DfsResidualRangeApplies(pool.swept_buckets - pool.direct_buckets,
                                    pool.main_levels);
    Expect((dfs_pieces > 0) == dfs_applies,
           Describe(c) + ": the finish did not run the DFS distributor exactly "
                         "where its pool distributes");
    g_dfs_finishes += dfs_pieces > 0;
  }
  // THE INLINE SHARE'S ESTIMATE IS WHAT THE PIECES ARE CHARGED.  Every piece
  // the owner ran passed its yield -- all of them without helpers, and below
  // the top even a whole run, whose residual passes are all in the finish.
  if (helpers == 0 && !interleaved &&
      (resumed || c.level < geometry.Levels())) {
    const double estimate = la::LevelMergeResidualTouches(
        geometry, layout, sizing, c.level, c.digit);
    Expect(double(residual_charged) == estimate,
           Describe(c) + ": the pieces were charged " +
               std::to_string(residual_charged) +
               " residual touches, LevelMergeResidualTouches counts " +
               std::to_string(estimate));
    ++g_residual_charge_checks;
  }
  if (resumed && helpers == 0) {
    // Interleaved, the helper's turns run most pieces, so few are stops.
    Expect(interleaved || stops >= 2,
           Describe(c) + ": the resumed run stopped only " +
               std::to_string(stops) + " times, so the cursor was not "
               "exercised");
  }
  Expect(!job.bound(), Describe(c) + ": the job stayed bound after finishing");
  g_laned_stages += job.laned_stages();
  g_private_mask_stages += job.private_mask_stages();
  if (c.produced_carry) {
    // 7(a) ITSELF: the pass offered nothing, so no main mask moved, no range
    // table was built, and all of the carry's tier drained into the output's.
    Expect(ts::DigestTable(scratch->Range(scratch->range_buckets())) ==
               range_digest,
           Describe(c) + ": the digit-1 pass wrote the range scratch");
    size_t changed = 0;
    for (size_t b = 0; b < binding.out.num_buckets; ++b) {
      if (binding.out.masks[b] != installed_masks[b]) ++changed;
    }
    Expect(changed == 0,
           Describe(c) + ": the digit-1 pass changed " +
               std::to_string(changed) + " main masks");
    Expect(binding.out_tier->Count() == carry_tier_entries,
           Describe(c) + ": the output tier holds " +
               std::to_string(binding.out_tier->Count()) + " entries, not "
               "the carry tier's " + std::to_string(carry_tier_entries));
  }

  // ---- what the merge produced -------------------------------------------

  CaseResult result;
  size_t damaged = 0;
  ts::CollectLive(published, &result.live, &result.unique, &damaged);
  ts::CollectLiveStashes(layout, binding.out_tier, 1, &result.live,
                         &result.unique, &damaged);
  Expect(damaged == 0,
         Describe(c) + ": " + std::to_string(damaged) +
             " entries carry a payload their key and source do not agree "
             "with");
  // The tier's bytes are part of the published table, so they are part of the
  // byte-identity claim too.
  // Compare exact occupied positions/payloads against the expanded-tree
  // reference. Dummy bytes and tier tags are not part of published content.
  for (const auto view : {published, bs::TableView{layout,
          binding.out_tier->num_buckets, binding.out_tier->data,
          binding.out_tier->masks}}) {
    for (size_t b = 0; b < view.num_buckets; ++b) {
      for (unsigned byte = 0; byte < 8; ++byte)
        result.occupied_output.push_back(uint8_t(view.masks[b] >> (byte * 8)));
      for (size_t lane = 0; lane < 64; ++lane) if ((view.masks[b] >> lane) & 1)
        for (size_t line = 0; line < layout.PayloadLines(); ++line)
          result.occupied_output.push_back(view.Bucket(b)[line * 64 + lane]);
    }
  }
  result.out_digest = ts::DigestTable(published) * 0x100000001b3ull ^
                      ts::DigestStash(layout, *binding.out_tier);
  Expect(result.unique,
         Describe(c) + ": a key survives twice across the output and its tier");
  if (result.live != model) {
    size_t missing = 0, extra = 0, wrong = 0;
    bs::KeyWords first_missing, first_wrong;
    for (const auto& want : model) {
      const auto it = result.live.find(want.first);
      if (it == result.live.end()) {
        if (missing++ == 0) first_missing = want.first;
      } else if (it->second != want.second) {
        if (wrong++ == 0) first_wrong = want.first;
      }
    }
    for (const auto& got : result.live) {
      if (model.find(got.first) == model.end()) ++extra;
    }
    Expect(false,
           Describe(c) + ": the output is not exactly the newest copy of "
                         "every key (" +
               std::to_string(missing) + " missing e.g. " +
               std::to_string(first_missing.w0) + "/" +
               std::to_string(first_missing.w1) + ", " +
               std::to_string(extra) + " unexpected, " +
               std::to_string(wrong) + " at the wrong value e.g. " +
               std::to_string(first_wrong.w0) + "/" +
               std::to_string(first_wrong.w1) +
               "; model " + std::to_string(model.size()) + ", output " +
               std::to_string(result.live.size()) + ")");
  }

  // Every entry of the OUTPUT MAIN is in the bucket its KEY selects, which is
  // the bucket a request will probe for it.  The tier is exempt by
  // construction: it is what did not fit into any bucket.
  std::vector<bs::KeyWords> out_keys;
  std::vector<size_t> out_buckets;
  for (size_t b = 0; b < published.num_buckets; ++b) {
    uint64_t mask = published.masks[b];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      out_keys.push_back(
          ts::SlotKeyWordsOf(layout, published.Bucket(b), slot));
      out_buckets.push_back(b);
    }
  }
  size_t misrouted = 0;
  if (!out_keys.empty()) {
    const std::vector<size_t> want =
        DestinationBuckets(layout, nonce, shape, keys, out_keys);
    for (size_t i = 0; i < out_keys.size(); ++i) {
      if (want[i] != out_buckets[i]) ++misrouted;
    }
  }
  Expect(misrouted == 0,
         Describe(c) + ": " + std::to_string(misrouted) + " of " +
             std::to_string(out_keys.size()) +
             " entries are not in the bucket their key selects");

  // The completed non-top input contract is stronger than merely
  // a_i <= x_i: every tier key homes at a full bucket, hence a_i=min(x_i,64).
  // Check the result of every digit/offer shape, including paused and helper
  // executions, not only the produced carry used by the digit-1 cases above.
  std::vector<bs::KeyWords> residual_keys;
  for (size_t b = 0; b < binding.out_tier->num_buckets; ++b) {
    uint64_t mask = binding.out_tier->masks[b];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      residual_keys.push_back(ts::SlotKeyWordsOf(
          layout, binding.out_tier->Bucket(b), slot));
    }
  }
  size_t open_residual_homes = 0;
  for (size_t target :
       DestinationBuckets(layout, nonce, shape, keys, residual_keys)) {
    if (published.masks[target] != ~uint64_t{0}) {
      ++open_residual_homes;
    }
  }
  Expect(open_residual_homes == 0,
         Describe(c) + ": " + std::to_string(open_residual_homes) +
             " output tier records target a nonfull main bucket");
  // The sources are published storage and this merge only reads them.
  if (c.digit > 1) {
    Expect(older.Unchanged(layout),
           Describe(c) + ": the merge wrote the older operand");
  }
  if (dense) {
    Expect(ts::DigestTable(bs::View(prefix)) == prefix_digest,
           Describe(c) + ": the builder wrote the published prefix");
  } else {
    Expect(carry.Unchanged(layout),
           Describe(c) + ": the merge wrote the carry it consumed");
  }

  Expect(binding.out_tier == dest_arena.WritableTier(dest) &&
             binding.out_tier->data == assigned_tier &&
             binding.out_tier->masks == assigned_tier_masks,
         Describe(c) + ": rebuild moved its assigned residual slice or masks");
  result.carry_tier = carry_tier_entries;
  if (into != nullptr &&
      !(dest_arena.Publish(dest) &&
        dest_arena.TryAccept(dest_slot, dest.generation))) {
    throw std::logic_error("the fixture could not publish a produced carry");
  }
  if (into != nullptr) {
    const auto tier_view = dest_arena.PublishedTierTable(dest_slot);
    Expect(tier_view.data == assigned_tier && tier_view.masks == assigned_tier_masks,
           Describe(c) + ": publication copied the residual destination");
  }
  return result;
}

// ---------------------------------------------------------------------------
// Cases
// ---------------------------------------------------------------------------

// The battery every case runs: split and unsplit, a control, stopped after
// every piece, in lanes, on helper threads and interleaved -- one set of
// published bytes for all of them.  RunCase checks each run against the
// model: the newest copy of every key, tombstones included.
void RunAndReport(const Case& c) {
  size_t split_shed = 0, unsplit_shed = 0;
  const CaseResult split = RunCase(c, /*split=*/true, &split_shed);
  // The unsplit path is the same three helpers in sequence, so on the
  // same inputs it has to produce the same table -- not merely an equivalent
  // one.  A prepared job that re-planned anything on arrival shows up here.
  const CaseResult unsplit = RunCase(c, /*split=*/false, &unsplit_shed);
  Expect(split.live == unsplit.live,
         Describe(c) + ": pausing between preparation and the carry changed "
                       "the result");
  // Byte identity is only meaningful once every byte the merge reads is
  // defined, so this run is the control: two identical runs must agree
  // BEFORE "pausing changed nothing" is worth asserting.  It also catches a
  // fixture that leaves dummy lanes uninitialized, which would make the
  // comparison below fail for a reason that has nothing to do with pausing.
  size_t control_shed = 0;
  const CaseResult control = RunCase(c, /*split=*/true, &control_shed);
  Expect(control.out_digest == split.out_digest,
         Describe(c) + ": two identical runs produced different bytes");
  Expect(split.out_digest == unsplit.out_digest,
         Describe(c) + ": pausing changed the output's bytes");
  // STOPPING AFTER EVERY PIECE CHANGES NOTHING: the
  // same merge through the job's cursor at a tight budget, stopped and
  // resumed between every two pieces, against the one issued whole.
  size_t resumed_shed = 0;
  const CaseResult resumed =
      RunCase(c, /*split=*/true, &resumed_shed, nullptr, /*resumed=*/true);
  Expect(resumed.out_digest == split.out_digest,
         Describe(c) + ": stopping and resuming the phases changed the "
                       "output's bytes");
  // LANES CHANGE NOTHING EITHER: every divisible stage
  // cut into up to three lanes -- an odd count, so the cuts are uneven --
  // each shedding into stashes of its own that fold back in lane order, and
  // stopped after every piece.  The stashes append, so the fold rebuilds the
  // one-lane stash exactly and the published bytes must match.
  for (bool stop : {false, true}) {
    size_t laned_shed = 0;
    const CaseResult laned = RunCase(c, /*split=*/true, &laned_shed, nullptr,
                                     /*resumed=*/stop, /*lanes=*/3);
    Expect(laned.out_digest == split.out_digest,
           Describe(c) + ": running the stages in lanes changed the output's "
                         "bytes" + (stop ? " (stopping after every piece)" : ""));
  }
  // AND WHICH THREAD RUNS A LANE CHANGES NOTHING.
  for (bool stop : {false, true}) {
    size_t helped_shed = 0;
    const CaseResult helped =
        RunCase(c, /*split=*/true, &helped_shed, nullptr, /*resumed=*/stop,
                /*lanes=*/3, /*helpers=*/2);
    Expect(helped.out_digest == split.out_digest,
           Describe(c) + ": running the lanes on helper threads changed the "
                         "output's bytes" +
               (stop ? " (stopping after every piece)" : ""));
  }
  // The same with the helper's turns taken between the owner's pieces, which
  // is where who is told of each stage opening gets checked (InterleavedHelper).
  {
    size_t interleaved_shed = 0;
    const CaseResult interleaved =
        RunCase(c, /*split=*/true, &interleaved_shed, nullptr,
                /*resumed=*/true, /*lanes=*/3, /*helpers=*/0,
                /*interleaved=*/true);
    Expect(interleaved.out_digest == split.out_digest,
           Describe(c) + ": interleaving a helper's lanes with the owner's "
                         "pieces changed the output's bytes");
  }
  if ((c.forced_older != 0 || c.forced_fresh != 0) &&
      !(c.level > 1 && c.digit == 1)) {
    Expect(split_shed > 0,
           Describe(c) + ": nothing shed, so the residual wiring was not "
                         "loaded");
  }
  const std::string carry_tier =
      c.produced_carry
          ? ", " + std::to_string(split.carry_tier) + " in the carry's tier"
          : "";
  std::printf("  %-46s %zu keys, %zu shed%s%s\n", Describe(c).c_str(),
              split.live.size(), split_shed, carry_tier.c_str(),
              c.sliced ? ", sliced" : "");
}

// A DIRECT BUILD'S OWN CAPACITY EVENT (level one's direct B build,
// src/oram/rebuild/cpu_byteslice_dense_select.hpp): B's leftovers go to ONE bucket above digit 1 and to the output
// tier at digit 1, and more than that is a declared failure of the install --
// named, so that it cannot be mistaken for a route's -- even where the final
// split would have fit.  200 distinct keys at B home 0 leave at least 136.
void TestDirectProducerOverflow() {
  for (unsigned digit : {1u, 2u}) {
    Case c;
    c.name = "direct overflow";
    c.branching = 4;
    c.level = 1;
    c.digit = digit;
    c.prefix_flushes = 4;
    c.forced_fresh = 200;

    size_t shed = 0;
    std::string what;
    try {
      RunCase(c, /*split=*/true, &shed);
    } catch (const std::runtime_error& e) {
      what = e.what();
    }
    Expect(what.find("dense-drain") != std::string::npos,
           Describe(c) + ": an overfull B producer did not fail at its drain"
                         " (got \"" + what + "\")");
  }
}

// The refusals that keep a job from running a merge it was not prepared for.
// Each one guards an operand that is another level's arena, or a nonce the
// already-routed older half cannot be re-planned under.
void TestJobRefusals() {
  Case c;
  c.name = "refusals";
  const bs::Layout layout = LayoutOf(c);
  const la::LevelArenaGeometry geometry(ParamsOf(c));
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  la::LevelArenaSet arenas(geometry, layout);
  la::LevelArena& arena = arenas.At(2);
  // A digit-2 destination is an inbox of the level ABOVE, written under the
  // forwarding lease, so that is where the fixture leases it from.
  la::LevelArena& above = arenas.At(3);
  const size_t carry_buckets = geometry.CarryBuckets(2);

  la::SlotLease dest, older_lease, carry_lease;
  Expect(above.TryLeaseOwn(above.plan().inbox[0], &dest), "leased dest");
  Expect(arena.TryLeaseOwn(arena.plan().inbox[1], &older_lease), "leased older");
  Expect(arena.TryLeaseOwn(arena.plan().inbox[0], &carry_lease), "leased carry");

  const uint64_t ordinal = 2;
  la::LevelMergeBinding good;
  good.ordinal = ordinal;
  good.out = above.WritableMain(dest, 2 * carry_buckets);
  good.out_tier = above.WritableTier(dest);
  good.destination_generation = dest.generation;
  good.older_main = arena.WritableMain(older_lease, carry_buckets);
  good.older_tier = arena.WritableTier(older_lease);

  la::LevelMergeJob job(geometry, sizing, layout, 2,
                        bs::DefaultAesTagKeys());
  // The digit, the family and the nonce come from the ordinal, so an ordinal
  // whose digit does not match the storage the caller supplied is refused --
  // there is no second field for the two to disagree in.
  Expect(Throws([&] {
           la::LevelMergeBinding bad = good;
           bad.ordinal = 3;  // digit 3, but the views are a digit-2 merge's
           la::LevelMergeJob other(geometry, sizing, layout, 2,
                                   bs::DefaultAesTagKeys());
           other.Begin(bad);
         }),
         "an ordinal whose digit does not fit its destination was accepted");
  Expect(Throws([&] {
           la::LevelMergeBinding bad = good;
           bad.ordinal = 0;
           la::LevelMergeJob other(geometry, sizing, layout, 2,
                                   bs::DefaultAesTagKeys());
           other.Begin(bad);
         }),
         "a zero ordinal was accepted");
  Expect(Throws([&] {
           la::LevelMergeBinding bad = good;
           bad.older_main.num_buckets -= 1;
           la::LevelMergeJob other(geometry, sizing, layout, 2,
                                   bs::DefaultAesTagKeys());
           other.Begin(bad);
         }),
         "an older operand that is not (j-1)*U buckets was accepted");
  Expect(Throws([&] {
           la::LevelMergeBinding bad = good;
           bad.ordinal = 1;  // digit 1: level 2 adopts and runs no merge
           la::LevelMergeJob other(geometry, sizing, layout, 2,
                                   bs::DefaultAesTagKeys());
           other.Begin(bad);
         }),
         "a digit-1 merge above level 1 was accepted");
  Expect(Throws([&] {
           la::LevelMergeBinding bad = good;
           bad.destination_generation = 0;
           la::LevelMergeJob other(geometry, sizing, layout, 2,
                                   bs::DefaultAesTagKeys());
           other.Begin(bad);
         }),
         "a destination that was never leased was accepted");
  // The top IS one of these jobs -- same storage, same state machine,
  // a different shape -- so what is refused here is only a level the
  // hierarchy does not have.  The top's own gate is
  // cpu_byteslice_level_arena_top_test.cpp.
  Expect(!Throws([&] {
           la::LevelMergeJob top(geometry, sizing, layout, geometry.Levels(),
                                 bs::DefaultAesTagKeys());
         }),
         "the top was refused as a job");
  Expect(Throws([&] {
           la::LevelMergeJob beyond(geometry, sizing, layout,
                                    geometry.Levels() + 1,
                                    bs::DefaultAesTagKeys());
         }),
         "a job above the top was accepted");

  // AND A TAG THAT CANNOT HOLD THE WHOLE RADIX DIGIT, refused at the BINDING
  // rather than at whichever phase runs first: U_2 is 16 buckets, so the four
  // index bits fit below a digit at bit 7, and the digit's three reserved
  // bits do not.  A digit truncated to one bit sends every entry of block 2
  // into block 0 and loses it.
  //
  // The layout arithmetic is cpu_byteslice_level_arena_merge_test.cpp's; what
  // this adds is that a job never reaches a phase with one -- and the control,
  // digit_bits = 4, which is the packed layout PlanRoutingTag really does
  // produce for a 4-bit index and which must still bind.
  // A VIEW IN ANOTHER ENTRY LAYOUT.  A `TableView` carries its own layout and
  // the job derives its map, its stash widths and every line offset from the
  // one it was CONSTRUCTED with; nothing downstream compares the two, so the
  // same bytes would simply be read at different offsets.  The per-phase
  // check in ExpectLevelMergeContexts cannot catch this -- all three phases
  // copy the same wrong view and agree perfectly -- and neither can the digit
  // check, which a binary digit does not reach at all.
  {
    auto refuses_layout = [&](la::LevelMergeBinding bad, const char* what) {
      Expect(Throws([&] {
               la::LevelMergeJob other(geometry, sizing, layout, 2,
                                       bs::DefaultAesTagKeys());
               other.Begin(bad);
             }),
             what);
    };
    la::LevelMergeBinding wide_out = good;
    wide_out.out.layout.value_bytes += 8;
    refuses_layout(wide_out, "a destination view in another entry layout was "
                             "accepted");
    la::LevelMergeBinding wide_older = good;
    wide_older.older_main.layout.tag_bytes += 1;
    refuses_layout(wide_older, "an older operand in another entry layout was "
                               "accepted");
    // The digit's position is part of the layout, and a merge that re-tagged
    // under one and swept under the other would misplace exactly the entries
    // whose digit is nonzero.
    la::LevelMergeBinding packed = good;
    packed.out.layout.digit_bits = 4;
    refuses_layout(packed, "a destination whose digit sits elsewhere was "
                           "accepted");
    bs::ResidualStash foreign_tier = *good.out_tier;
    foreign_tier.entry_bytes += 1;
    la::LevelMergeBinding wide_tier = good;
    wide_tier.out_tier = &foreign_tier;
    refuses_layout(wide_tier, "a destination tier in another entry layout was "
                              "accepted");
  }

  {
    auto binds = [&](size_t digit_bits) {
      bs::Layout narrow = layout;
      narrow.tag_bytes = 1;
      narrow.digit_bits = digit_bits;
      la::LevelArenaSet narrow_arenas(geometry, narrow);
      la::LevelArena& narrow_level = narrow_arenas.At(2);
      // Digit 3: the destination is this level's odd bank and the older half
      // is P_2, which lives in the level above's inbox.
      la::LevelArena& narrow_above = narrow_arenas.At(3);
      la::SlotLease narrow_dest, narrow_older;
      Expect(narrow_level.TryLeaseOwn(narrow_level.plan().odd_bank,
                                      &narrow_dest) &&
                 narrow_above.TryLeaseOwn(narrow_above.plan().inbox[0],
                                          &narrow_older),
             "the fixture could not lease the narrow-tag operands");
      la::LevelMergeBinding narrow_binding;
      narrow_binding.ordinal = 3;  // digit 3: a radix pass, and so a digit
      narrow_binding.out =
          narrow_level.WritableMain(narrow_dest, 3 * carry_buckets);
      narrow_binding.out_tier = narrow_level.WritableTier(narrow_dest);
      narrow_binding.destination_generation = narrow_dest.generation;
      narrow_binding.older_main =
          narrow_above.WritableMain(narrow_older, 2 * carry_buckets);
      narrow_binding.older_tier = narrow_above.WritableTier(narrow_older);
      la::LevelMergeJob narrow_job(geometry, sizing, narrow, 2,
                                   bs::DefaultAesTagKeys());
      narrow_job.Begin(narrow_binding);
      return narrow_job.digit() == 3;
    };
    Expect(binds(4), "the packed layout a 4-bit index plans was refused");
    Expect(Throws([&] { binds(7); }),
           "a layout whose tag cuts the radix digit off was accepted");
  }

  job.Begin(good);
  Expect(job.destination_generation() == dest.generation,
         "the job did not record the occupancy it was bound to");
  Expect(job.ordinal() == ordinal && job.digit() == 2 &&
             job.family() == la::CanonicalFamily(geometry, 2, ordinal),
         "the job did not derive the coordinate of its own ordinal");
  Expect(Throws([&] { job.Begin(good); }),
         "a second pending job at one level was accepted");

  la::LevelMergeScratch scratch(
      layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, 2));
  la::LevelCarry wrong;
  wrong.ordinal = ordinal + 1;
  wrong.family = job.family();
  wrong.main = arena.WritableMain(carry_lease, carry_buckets);
  wrong.tier = arena.WritableTier(carry_lease);
  Expect(Throws([&] {
           job.Finish(wrong, &scratch, WholeBudget());
         }),
         "a carry out of order was accepted at a prepared job");
  la::LevelCarry foreign = wrong;
  foreign.ordinal = ordinal;
  foreign.family = la::Family{job.family().level, job.family().ordinal + 1};
  Expect(Throws([&] {
           job.Finish(foreign, &scratch, WholeBudget());
         }),
         "a carry from another nonce family was accepted");
  // Arrival validates the carry's LAYOUT too, for the same reason the binding
  // does: the install re-tags it in place at this job's line offsets.
  la::LevelCarry wide = wrong;
  wide.ordinal = ordinal;
  wide.main.layout.tag_bytes += 1;
  Expect(Throws([&] { job.Finish(wide, &scratch, WholeBudget()); }),
         "a carry in another entry layout was accepted");
  std::printf("  refusals: family, extents, ordinal, digit and level\n");
}

// THE JOB ROUTES UNDER THE KEY IT WAS GIVEN.
//
// The nonce is public and the key is the instance's secret, so "the tags are
// self-consistent" is not the property that matters: a job that used the
// fixed default key would produce a table that passes every check in RunCase
// -- planted, routed and read back under one hash -- while every entry in it
// sat at a position anyone can recompute.  What distinguishes the two is
// only visible ACROSS keys, so that is what is asserted here: the same case
// under two instance keys places its entries differently, and each run is
// exactly right under its own.  (RunCase does the second half; a run that
// mixed two keys would lose or misroute records rather than merely move
// them.)
void TestTheInstanceKeyRoutes() {
  Case c;
  c.name = "instance key";
  c.level = 2;
  c.digit = 3;
  c.branching = 4;
  c.forced_older = 70;
  size_t shed = 0;
  Case other = c;
  other.key_seed = c.key_seed ^ 0x9E3779B97F4A7C15ull;
  const CaseResult a = RunCase(c, /*split=*/true, &shed);
  const CaseResult b = RunCase(other, /*split=*/true, &shed);
  Expect(a.out_digest != b.out_digest,
         "two instance keys placed one merge's entries identically, so the "
         "key the job was handed is not the one it routed under");
  // The same entries, in different places: a key changes where a record goes,
  // never which records survive.
  Expect(a.live.size() == b.live.size(),
         "two instance keys did not merge the same records");
  std::printf("  instance key: two keys, two placements, one live set\n");
}

// The range scratch is the executing thread's, and is checked rather than
// clamped: a pass given a narrower range table than it was planned for sweeps
// the wrong extent and silently drops what it meant to offer back.
void TestScratchIsChecked() {
  const bs::Layout layout = LayoutOf(Case{});
  const la::LevelArenaGeometry geometry(ParamsOf(Case{}));
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  const size_t needed = la::MaxLevelMergeRangeBuckets(geometry, sizing, 2);
  Expect(needed > 0, "a merge needs a range table");
  la::LevelMergeScratch scratch(layout, needed);
  Expect(scratch.Range(needed).num_buckets == needed,
         "the thread's scratch does not cover the widest merge");
  Expect(Throws([&] { scratch.Range(needed + 1); }),
         "a range table wider than the scratch was handed out");
  Expect(Throws([&] { scratch.Range(0); }), "an empty range table was handed out");
  Expect(Throws([&] { la::LevelMergeScratch none(layout, 0); }),
         "scratch with no capacity was accepted");
  // THE CERTIFIED ROUTING's workspaces: every ordinary level distributes its
  // A leaf on one page per coarse range (its
  // widest range table is that leaf table plus B's direct tier), and the top
  // its preparation on one.
  {
    Case bc;
    bc.branching = 8;
    bc.levels = 4;
    bc.prefix_flushes = 8;
    const la::LevelArenaGeometry wide(ParamsOf(bc));
    const la::LevelArenaStashSizing wide_sizing(wide, kMaxAccesses);
    const auto level1 = la::MaxLevelDfsAllocation(wide, wide_sizing, 1);
    Expect(level1.any() && level1.pages == la::kSeparatedDfsPages,
           "level 1's DFS workspace is not one page");
    for (unsigned l = 2; l < wide.Levels(); ++l) {
      const auto alloc = la::MaxLevelDfsAllocation(wide, wide_sizing, l);
      Expect(alloc.any() && alloc.pages == la::kSeparatedDfsPages,
             "a separated level's DFS workspace is not one page");
      size_t widest = 0;
      for (unsigned d = 2; d <= wide.Fanout(l); ++d) {
        const auto pool = la::LevelMergePoolShapeOf(
            la::LevelMergeShapeOf(wide, l, d), wide_sizing.Buckets(l),
            wide.OlderTierBuckets(l, d), wide.CarryTierBuckets(l));
        Expect(pool.direct_buckets == wide.CarryTierBuckets(l),
               "a separated pool does not offer B's tier directly");
        widest = std::max(widest, la::LevelFinishRangePlan(pool).range_buckets +
                                      pool.direct_buckets);
      }
      Expect(la::MaxLevelMergeRangeBuckets(wide, wide_sizing, l) == widest,
             "a separated level's scratch is not its widest leaf table plus "
             "B's tier");
    }
    const auto top = la::MaxLevelDfsAllocation(wide, wide_sizing, wide.Levels());
    Expect(top.any() && top.pages == la::kTopPrepareDfsPages,
           "the top's preparation workspace is not one page");
  }
  // One workspace per level, at one page count: a binary level's digit-1
  // finish (which does not adopt its carry) only drains the carry's tier, so
  // its separated digits' one A page is the level's only count.
  {
    Case bc;
    bc.branching = 2;
    bc.levels = 5;
    bc.prefix_flushes = 4;
    const la::LevelArenaGeometry binary(ParamsOf(bc));
    const la::LevelArenaStashSizing binary_sizing(binary, kMaxAccesses);
    for (unsigned l = 2; l < binary.Levels(); ++l) {
      const auto pool = la::LevelMergePoolShapeOf(
          la::LevelMergeShapeOf(binary, l, 1), binary_sizing.Buckets(l),
          binary.OlderTierBuckets(l, 1), binary.CarryTierBuckets(l));
      const auto alloc = la::MaxLevelDfsAllocation(binary, binary_sizing, l);
      Expect(pool.swept_buckets == 0 && alloc.any() && alloc.pages == 1,
             "a separated binary level's DFS workspace is not one page");
    }
    Expect(la::MaxLevelDfsAllocation(binary, binary_sizing, 1).pages ==
               la::kSeparatedDfsPages,
           "level 1 lost its own DFS page count beside separated levels");
  }
  std::printf("  scratch: sized for the widest digit, refused beyond it; the "
              "certified routing's workspaces\n");
}

// The certified depths, and the geometry the table cannot cover.
void TestStashSizing() {
  la::LevelArenaGeometry::Params p = ParamsOf(Case{});
  p.branching = 8;
  p.levels = 4;
  p.prefix_flushes = 8;
  const la::LevelArenaGeometry geometry(p);
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  Expect(sizing.At(4).rebuilds == 16385.0,
         "2^32 accesses plus initialization require 16385 top executions");
  for (unsigned l = 1; l <= geometry.Levels(); ++l) {
    const la::LevelStashPlan& plan = sizing.At(l);
    Expect(plan.buckets >= 1 && plan.buckets <= bs::kMaxResidualStashBuckets,
           "a certified depth is outside the stash type's range");
    Expect(plan.target_log2 <= -64.0,
           "a level's failure budget is looser than 2^-64");
    // A level higher up rebuilds less often and so may need no more than the
    // one below it at the same width; what actually grows is the width.
    Expect(plan.route_buckets == geometry.MaxOutputBuckets(l),
           "the depth was bought for the wrong operation width");
  }
  Expect(sizing.DeepestBuckets() >= sizing.Buckets(1),
         "the deepest is not the maximum");
  // The accepted 2^27-record counterexample needs two tier buckets. This
  // planning check allocates no table and includes initialization in R_L.
  auto large_params = p;
  large_params.levels = 6;
  large_params.top_digit = 8;
  large_params.tier_buckets = 0;
  const auto resolved = la::ResolveLevelArenaTierGeometry(large_params,
                                                         kMaxAccesses);
  Expect(resolved.tier_buckets == 2,
         "automatic sizing retained the insufficient one-bucket large tier");
  large_params.tier_buckets = 1;
  Expect(Throws([&] {
    la::ResolveLevelArenaTierGeometry(large_params, kMaxAccesses);
  }), "an undersized explicit tier bypassed lifetime sizing");
  large_params.tier_buckets = 3;
  Expect(la::ResolveLevelArenaTierGeometry(large_params, kMaxAccesses)
             .tier_buckets == 3,
         "automatic sizing shrank an adequate explicit tier");
  // The top alone is not sufficient: the penultimate level has the same
  // width but executes more often, crossing a tier-width boundary.
  large_params.prefix_flushes = 2;
  large_params.top_digit = 1;
  const la::LevelArenaStashSizing non_top(
      la::LevelArenaGeometry(large_params), kMaxAccesses);
  Expect(non_top.At(6).tier_buckets == 1 &&
             non_top.At(5).tier_buckets == 2 &&
             non_top.DeepestTierBuckets() == 2,
         "tier sizing checked only the top's execution count");
  Expect(bs::ResidualTierBuckets(std::numeric_limits<uint64_t>::max(), 100)
             == 0,
         "unrepresentable tier requirement wrapped into a supported depth");
  Expect(Throws([&] { la::LevelArenaStashSizing bad(geometry, 0); }),
         "a stash depth without a request horizon was accepted");
  Expect(Throws([&] { sizing.At(0); }), "there is no level 0");
  // Count actual event opportunities at both sides of period boundaries,
  // including a direct initialization followed by a full online horizon.
  // Mixed fanouts make the period at each level different.
  p.level_fanouts = {2, 4, 8};
  const la::LevelArenaGeometry mixed(p);
  const uint64_t prefix =
      mixed.OnlineStashEntries() * mixed.PrefixFlushes();
  for (const uint64_t horizon : {uint64_t{1}, prefix - 1, prefix,
                                  prefix + 1, prefix * 64,
                                  prefix * 64 + 1, kMaxAccesses}) {
    const la::LevelArenaStashSizing counted(mixed, horizon);
    uint64_t period = prefix;
    for (unsigned l = 1; l <= mixed.Levels(); ++l) {
      const uint64_t online = horizon / period + (horizon % period != 0);
      const uint64_t expected = online + (l == mixed.Levels() ? 1 : 0);
      Expect(counted.At(l).rebuilds == static_cast<double>(expected),
             "stash budget omitted a partial period or initialization");
      using Wide = unsigned __int128;
      const auto& plan = counted.At(l);
      const unsigned bits = static_cast<unsigned>(-plan.target_log2) - 66;
      const Wide events = (Wide{mixed.Levels()} + 1) * expected * plan.stages;
      Expect((Wide{1} << bits) >= events &&
                 (bits == 0 || (Wide{1} << (bits - 1)) < events),
             "stage exponent does not exactly cover the event product");
      Expect(plan.target_log2 == -static_cast<double>(66 + bits),
             "stage budget used a fractional floating exponent");
      if (l < mixed.Levels()) period *= mixed.Fanout(l);
    }
  }
  // Conversion to the floating-point lookup must not lose an event at the
  // largest request horizon. Long double can represent this integer here.
  const uint64_t largest = std::numeric_limits<uint64_t>::max();
  const la::LevelArenaStashSizing large(mixed, largest);
  const uint64_t first_events = largest / prefix + (largest % prefix != 0);
  Expect(static_cast<long double>(large.At(1).rebuilds) >=
             static_cast<long double>(first_events),
         "large request horizon rounded its event count down");
  using Wide = unsigned __int128;
  const Wide large_events =
      (Wide{mixed.Levels()} + 1) * first_events * large.At(1).stages;
  const unsigned large_bits =
      static_cast<unsigned>(-large.At(1).target_log2) - 66;
  Expect((Wide{1} << large_bits) >= large_events &&
             (Wide{1} << (large_bits - 1)) < large_events,
         "stage budget lost precision on the large event product");
  // (L+1)*stages = 32 and R = 2^47+1. A double log sum rounds the
  // requested exponent down to 118, while the exact ceiling is 119.
  auto edge_params = p;
  edge_params.levels = 3;
  edge_params.branching = 2;
  edge_params.level_fanouts.clear();
  edge_params.prefix_flushes = 2;
  edge_params.stash_buckets = 1;
  edge_params.top_digit = 2;
  const la::LevelArenaStashSizing edge(
      la::LevelArenaGeometry(edge_params), uint64_t{1} << 56);
  Expect(edge.At(3).stages == 8 &&
             edge.At(3).rebuilds == static_cast<double>((uint64_t{1} << 47) + 1) &&
             edge.At(3).target_log2 == -119.0,
         "stage budget rounded away initialization at a log boundary");
  std::printf("  stash: certified depths, %zu buckets deepest\n",
              sizing.DeepestBuckets());
}

}  // namespace

// THE FOLD IS THE CAPACITY CHECK (laned stages fold their stashes back).  Two lanes of 40
// entries each fit a 64-slot stash of their own, and together do not: the
// second fold must refuse.  And a fold that fits lays the entries out lane
// after lane, each lane's in its own slot order, which is the one-lane stash
// exactly.
void TestLaneFold() {
  const bs::Layout layout = LayoutOf(Case{});
  const size_t entry = layout.EntryBytes();
  std::vector<bs::Aligned64Ptr> storage;
  const auto make = [&](size_t buckets) {
    storage.push_back(
        bs::AllocateAligned64(buckets * entry * bs::kBucketCapacity));
    bs::ResidualStash stash;
    stash.data = storage.back().get();
    stash.num_buckets = buckets;
    stash.entry_bytes = entry;
    return stash;
  };
  // Entry `j` of a bucket is the byte `tag` in every line, at slot j.
  const auto fill = [&](bs::ResidualStash* stash, size_t count, uint8_t tag) {
    for (size_t j = 0; j < count; ++j) {
      for (size_t line = 0; line < entry; ++line) {
        stash->Bucket(0)[line * bs::kBucketCapacity + j] =
            static_cast<uint8_t>(tag + j);
      }
    }
    stash->masks[0] = count >= 64 ? ~uint64_t{0} : (uint64_t{1} << count) - 1;
  };
  {
    bs::ResidualStash own = make(1), a = make(1), b = make(1);
    fill(&a, 40, 0x10);
    fill(&b, 40, 0x80);
    Expect(la::FoldLaneStash(own, a, entry), "the first lane's fold refused");
    Expect(!la::FoldLaneStash(own, b, entry),
           "two lanes that each fit but together overflow folded silently");
  }
  {
    bs::ResidualStash own = make(2), a = make(1), b = make(1);
    fill(&a, 50, 0x10);
    fill(&b, 30, 0x80);
    Expect(la::FoldLaneStash(own, a, entry) && la::FoldLaneStash(own, b, entry),
           "a fold that fits refused");
    Expect(own.Count() == 80 && a.Count() == 0 && b.Count() == 0,
           "the fold lost or kept entries");
    bool ordered = true;
    for (size_t k = 0; k < 80; ++k) {
      const uint8_t want = k < 50 ? static_cast<uint8_t>(0x10 + k)
                                  : static_cast<uint8_t>(0x80 + (k - 50));
      const size_t bucket = k / bs::kBucketCapacity;
      const size_t slot = k % bs::kBucketCapacity;
      ordered &= (own.masks[bucket] >> slot & 1) != 0 &&
                 own.Bucket(bucket)[slot] == want &&
                 own.Bucket(bucket)[(entry - 1) * bs::kBucketCapacity + slot] ==
                     want;
    }
    Expect(ordered, "the fold did not lay the lanes out one after another");
  }
  std::printf("  lanes: the fold refuses a sum that overflows, and "
              "concatenates lanes in order\n");
}

int main() {
  std::printf("level arena, the merge job\n");
  TestLaneFold();
  TestStashSizing();
  TestScratchIsChecked();
  TestJobRefusals();
  TestTheInstanceKeyRoutes();

  // Level 1: the dense builder at every digit, including the digit-1 shape
  // whose sheds have no route to ride.
  for (unsigned digit : {1u, 2u, 3u, 4u}) {
    Case c;
    c.name = "dense";
    c.branching = 4;
    c.level = 1;
    c.digit = digit;
    c.forced_fresh = 70;
    c.forced_older = digit > 1 ? 60 : 0;
    RunAndReport(c);
  }

  // Level 2: the sparse install, every digit at B = 4, so both fusion sites
  // (a power-of-two digit's last cross level, an odd digit's radix pass).
  for (unsigned digit : {2u, 3u, 4u}) {
    Case c;
    c.name = "sparse";
    c.branching = 4;
    c.level = 2;
    c.digit = digit;
    // Only the OLDER half is forced onto one index.  A sparse carry is a
    // published table that its own producer had to route without shedding, so
    // overloading one of ITS buckets makes a fixture that could not exist --
    // and the install re-tags without routing, so it never sheds anyway.  The
    // fresher class's content comes from the carry's tier instead.
    c.forced_older = 60;
    RunAndReport(c);
  }

  for (unsigned digit : {2u, 3u, 4u}) {
    Case c;
    c.name = "two-page B tier"; c.branching = 4; c.level = 2;
    c.digit = digit; c.tier_buckets = 2; c.forced_older = 60;
    c.tombstones = true;
    RunAndReport(c);
  }

  // B = 8's higher digits.  5 and 7 are odd parts no B = 4 case reaches, and
  // 6 = 3 * 2 is the only shape in the whole ladder that runs cross levels AND
  // a radix pass: every other radix case here has e = 0 and so no cross level
  // at all, which changes which pass the residual second chance rides.
  for (unsigned digit : {5u, 6u, 7u, 8u}) {
    Case c;
    c.name = "mixed radix";
    c.branching = 8;
    c.levels = 3;
    c.level = 2;
    c.digit = digit;
    c.forced_older = 60;
    RunAndReport(c);
  }

  for (unsigned digit : {5u, 6u, 7u, 8u}) {
    Case c;
    c.name = "wide dense DFS coverage";
    c.branching = 8;
    c.level = 1;
    c.digit = digit;
    c.value_bytes = 257;
    c.forced_older = 60;
    c.forced_fresh = 70;
    RunAndReport(c);
  }

  // A DIRECTLY BUILT LEVEL ONE:
  // B built by one scan per home and inserted by the separated finish, at
  // every digit of B = 4 (digit 1 builds into the output itself), with and
  // without tombstones; B = 8's odd parts and digit 6 with wide values; wide
  // keys; the packed digit; Z >= 256, where homes cross a byte; and the
  // bank-first run.  Same model, battery and byte-identity gates.
  for (bool tombstones : {false, true}) {
    for (unsigned digit : {1u, 2u, 3u, 4u}) {
      Case c;
      c.name = "direct";
      c.branching = 4;
      c.level = 1;
      c.digit = digit;
      c.forced_fresh = 70;
      c.forced_older = digit > 1 ? 60 : 0;
      c.tombstones = tombstones;

      RunAndReport(c);
    }
  }
  for (unsigned digit : {5u, 6u, 7u, 8u}) {
    Case c;
    c.name = "direct wide values";
    c.branching = 8;
    c.level = 1;
    c.digit = digit;
    c.value_bytes = 257;
    c.forced_older = 60;
    c.forced_fresh = 70;

    RunAndReport(c);
  }
  {
    Case c;
    c.name = "direct wide keys";
    c.branching = 4;
    c.level = 1;
    c.digit = 3;
    c.key_bytes = 16;
    c.value_bytes = 24;
    c.tag_bytes = 5;
    c.forced_older = 60;
    c.forced_fresh = 70;

    RunAndReport(c);
  }
  {
    Case c;
    c.name = "direct packed digit";
    c.branching = 4;
    c.level = 1;
    c.digit = 3;
    c.tag_bytes = 1;
    c.digit_bits = 4;
    c.forced_older = 60;
    c.forced_fresh = 70;

    RunAndReport(c);
  }
  for (unsigned digit : {1u, 2u, 3u}) {
    Case c;
    c.name = "direct Z>=256";
    c.branching = 4;
    c.levels = 3;
    c.prefix_flushes = 8;
    c.stash_buckets = 16;  // U_1 = 256: 8 home bits
    c.level = 1;
    c.digit = digit;
    // B's leftovers at home 0 are the forced fresh keys, the forced older
    // keys the prefix shadows (about half of them here) and home 0's natural
    // load of ~32, less 64, into a tier of 64.  70 fresh keys on top of the
    // shadows put that at ~67 above digit one: a fixture that fits only by
    // luck of the instance key.  40 keeps it near half the tier.
    c.forced_fresh = digit > 1 ? 40 : 70;
    c.forced_older = digit > 1 ? 60 : 0;

    RunAndReport(c);
  }
  {
    Case c;
    c.name = "direct Z=512";
    c.branching = 2;
    c.levels = 3;
    c.prefix_flushes = 8;
    c.stash_buckets = 32;  // U_1 = 512: homes take two byte lines
    c.level = 1;
    c.digit = 2;
    c.forced_fresh = 40;  // the margin above: B's tier holds 64
    c.forced_older = 60;
    c.sliced = true;

    RunAndReport(c);
  }
  {
    Case base;
    base.name = "direct bank-first";
    base.branching = 8;
    base.levels = 3;
    base.level = 1;
    base.bank_first = la::BankFirst::kNoClone;

    const la::LevelArenaGeometry g(ParamsOf(base));
    for (unsigned digit = 1; digit <= g.ForwardingLeaseDigit(1); ++digit) {
      Case c = base;
      c.digit = digit;
      c.forced_older = digit > 1 ? 60 : 0;
      c.forced_fresh = 70;
      RunAndReport(c);
    }
  }
  // THE SHED-KEY TRAP itself: A overfull at
  // final home 0, so A sheds into its residual pool there, and B forced
  // nowhere, so B's main bucket 0 holds the A keys B rewrote -- the ones
  // whose A copy shed included.  Destination 0 is then full of A before B's
  // insertion, which sheds one of them into the merge stash while its older
  // copy waits in the pool (g_direct_trap_witnesses), with and without
  // tombstones on both sides.
  for (bool tombstones : {false, true}) {
    for (unsigned digit : {2u, 3u, 4u}) {
      Case c;
      c.name = "direct trap";
      c.branching = 4;
      c.prefix_flushes = 4;
      c.level = 1;
      c.digit = digit;
      c.forced_older = 90;
      c.tombstones = tombstones;

      RunAndReport(c);
    }
  }
  // A PINNED TWO-BUCKET LEVEL-ONE TIER: the direct build's merge stash
  // widens to it (MergeStashBuckets), the route stashes keep their depth.
  for (unsigned digit : {2u, 3u, 4u}) {
    Case c;
    c.name = "direct two-bucket tier";
    c.branching = 4;
    c.level = 1;
    c.digit = digit;
    c.tier_buckets = 2;
    c.forced_older = 60;
    c.forced_fresh = 70;
    c.tombstones = true;

    RunAndReport(c);
  }
  TestDirectProducerOverflow();

  // Binary installation and forwarding both use the common merge pipeline.
  // Digit 1's carry is level 1's forward with both routing phases forced (the
  // older half onto final bucket 0, the prefix onto dense index 0, which sends
  // about half of it to bucket 0 too), so bucket 0 overflows and the tier
  // holds real leftovers: the digit-1 pass gets what an engine can hand it.
  for (unsigned digit : {1u, 2u}) {
    Case c;
    c.name = "binary";
    c.branching = 2;
    c.levels = 3;
    c.level = 2;
    c.digit = digit;
    c.forced_older = 60;
    c.forced_fresh = digit == 1 ? 70 : 0;
    c.produced_carry = digit == 1;
    c.tombstones = digit == 1;
    RunAndReport(c);
  }

  // Tombstones: a non-top merge preserves every one of them, in both sources
  // and in both tiers.  Only the top's FIFO position makes forgetting one safe.
  {
    Case c;
    c.name = "tombstones";
    c.level = 2;
    c.digit = 3;
    c.branching = 4;
    c.tombstones = true;
    c.forced_older = 70;
    RunAndReport(c);
  }

  // Wide keys and an unpacked tag layout, then a narrow one: the re-tag writes
  // tag BYTES, and a layout with a different tag width puts the routing bits
  // and the radix digit in different lines.
  {
    Case c;
    c.name = "wide keys";
    c.level = 2;
    c.digit = 3;
    c.key_bytes = 16;   // the stored width of every user key above 8 bytes
    c.value_bytes = 24;
    c.tag_bytes = 5;
    c.forced_older = 70;
    RunAndReport(c);
  }
  {
    Case c;
    c.name = "narrow tags";
    c.level = 2;
    c.digit = 2;
    c.key_bytes = 4;
    c.value_bytes = 4;
    c.tag_bytes = 2;
    c.forced_older = 70;
    RunAndReport(c);
  }

  // Z >= 256: B's home cache crosses a byte boundary; the direct selection
  // and the later complete A route must preserve the full routing tag.
  {
    Case c;
    c.name = "Z>=256";
    c.branching = 4;
    c.levels = 3;
    c.prefix_flushes = 8;
    c.stash_buckets = 16;  // Z = 2 r0 s = 256
    c.level = 1;
    c.digit = 2;
    c.forced_fresh = 70;
    RunAndReport(c);
  }

  // The PACKED tag layout: at digit 3 the index is 4 bits and the radix digit
  // packs into the same byte above them, rather than into a reserved byte of
  // its own.  Every re-tag, the radix pass and the residual retag then read
  // the digit at a different offset, and the merge is only correct if all
  // three agree with the layout rather than with each other.
  {
    Case c;
    c.name = "packed digit";
    c.branching = 4;
    c.level = 2;
    c.digit = 3;
    c.tag_bytes = 1;
    c.digit_bits = 4;  // U_2 = 16 buckets, so the index is 4 bits
    c.forced_older = 70;
    RunAndReport(c);
  }

  // The fixed default key, which is what every standalone rebuild kernel and
  // benchmark uses: the job takes the key it is given, and that includes this
  // one.  Every other case above runs under an instance key.
  {
    Case c;
    c.name = "default key";
    c.level = 2;
    c.digit = 3;
    c.branching = 4;
    c.key_seed = 0;
    c.forced_older = 70;
    RunAndReport(c);
  }

  // The same merge issued under a tight subtask budget, which slices every
  // phase into many small tasks: the plan is the same work either way, and a
  // phase that depended on being issued whole would show up here.
  {
    Case c;
    c.name = "sliced";
    c.level = 2;
    c.digit = 3;
    c.branching = 4;
    c.sliced = true;
    c.forced_older = 70;
    RunAndReport(c);
  }

  // THE BANK-FIRST RUN, every digit it places
  // differently, at both levels: the run's partials at the bank's top and
  // base beside the live one before them, and the first digit that takes the
  // lease again.
  {
    struct Run {
      unsigned branching;
      unsigned level;
      la::BankFirst mode;
    };
    const Run runs[] = {
        {8, 1, la::BankFirst::kNoClone}, {8, 2, la::BankFirst::kNoClone},
    };
    for (const Run& run : runs) {
      Case base;
      base.name = "bank-first";
      base.branching = run.branching;
      base.levels = 3;
      base.level = run.level;
      base.bank_first = run.mode;
      const la::LevelArenaGeometry g(ParamsOf(base));
      const unsigned lease = g.ForwardingLeaseDigit(run.level);
      Expect(lease > 2, Describe(base) + ": the run is empty");
      for (unsigned digit = run.level == 1 ? 1 : 2; digit <= lease;
           ++digit) {
        Case c = base;
        c.digit = digit;
        c.forced_older = digit > 1 ? 60 : 0;
        c.forced_fresh = run.level == 1 ? 70 : 0;
        RunAndReport(c);
      }
    }
  }

  Expect(g_residual_charge_checks > 0,
         "no run checked its residual charges against the estimate");
  std::printf("  residual charges matched LevelMergeResidualTouches in %llu "
              "runs\n", (unsigned long long)g_residual_charge_checks);
  Expect(g_laned_stages > 0,
         "no case ran a stage in more than one lane, so the lane gate "
         "compared nothing");
  std::printf("  lanes: %llu stages ran divided\n",
              (unsigned long long)g_laned_stages);
  // The offer stages are the ones private masks let lanes divide at all at
  // these sizes, whose range words span the whole stage.
  Expect(g_private_mask_stages > 0,
         "no offer stage ran its lanes on private range masks, so the lane "
         "gates never compared the AND against the one-lane masks");
  std::printf("  lanes: %llu offer stages ran on private range masks\n",
              (unsigned long long)g_private_mask_stages);
  Expect(g_helper_lanes.load() > 0,
         "no helper thread ran a lane, so the helper gate compared nothing");
  std::printf("  helpers: %llu lanes run by helper threads\n",
              (unsigned long long)g_helper_lanes.load());
  Expect(g_helper_opened_stages > 0,
         "no interleaved helper opened a stage, so who is told of one was "
         "never checked");
  std::printf("  helpers: %llu stages opened by an interleaved helper\n",
              (unsigned long long)g_helper_opened_stages);
  Expect(g_dfs_finishes != 0,
         "no finish ran the DFS distributor, so its gate compared nothing");
  Expect(g_direct_trap_witnesses != 0,
         "no directly built level-one finish shed a B-main key whose older "
         "copy was in A's residual pool, so the freshness epilogue was never "
         "loaded");
  std::printf("  direct: %zu B-main sheds met an older A residual\n",
              g_direct_trap_witnesses);
  std::printf("  DFS: %zu finishes distributed\n", g_dfs_finishes);
  if (failures != 0) {
    std::fprintf(stderr, "%d level-arena job checks failed\n", failures);
    return 1;
  }
  std::printf("level arena merge job: OK\n");
  return 0;
}
