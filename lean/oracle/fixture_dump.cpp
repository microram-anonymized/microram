// Fixture dumper for the Lean differential-test oracle's round trip.
//
// Runs ONE real ordinary rebuild merge of the level-arena engine -- the d = 2
// separated-sources merge that RunCase in
// tests/oram/cpu_byteslice_level_arena_job_test.cpp runs for its "binary" case
// (branching 2, levels 3, level 2, digit 2, forced_older 60, forced_fresh 0,
// no tombstones, DFS routing with separated sources) -- and writes the job's
// inputs, the public geometry, the routing words of every key, and the
// engine's output as JSON, for `lake exe oracle` to check against the O1
// semantic spec.
//
// Nothing here edits the engine or its tests: the setup below is a faithful,
// minimal replica of RunCase for that one case (same helper headers, same
// call sequence, same RNG stream), kept outside tests/oram on purpose so the
// top-level CMake glob does not pick it up.
//
//   fixture_dump                      run, self-check, exit 0, write nothing
//   fixture_dump OUT.json             the above, and write the fixture
//   fixture_dump OUT.json --seed HEX --forced-older N --forced-fresh N
//                                     other instances / other forcing
//
// Exit status: 0 the job ran and the dumper's own C++ self-check passed (a
// job that FAILED with a capacity error is a legitimate `failure` fixture and
// exits 0 too); 1 the self-check found a violation; 2 usage / harness error.

#include <immintrin.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
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

// The job's fixed coordinates (the "binary" case, digit 2).
constexpr unsigned kBranching = 2;
constexpr unsigned kLevels = 3;
constexpr unsigned kPrefixFlushes = 2;
constexpr size_t kStashBuckets = 1;
constexpr size_t kTierBuckets = 1;
constexpr unsigned kLevel = 2;
constexpr unsigned kDigit = 2;
constexpr uint64_t kMaxAccesses = uint64_t{1} << 32;

struct Config {
  uint64_t key_seed = 0x5EED0C0DEull;  // the instance's AES key seed
  size_t forced_older = 60;
  size_t forced_fresh = 0;
};

// One stored record of a published table or tier.
struct Rec {
  size_t bucket = 0;
  size_t lane = 0;
  bs::KeyWords key;
  std::vector<uint8_t> value;  // value_bytes bytes; the last is the meta byte
  bool tombstone = false;
};

struct Fixture {
  Config cfg;
  // Public geometry, in dump order.
  std::vector<std::pair<std::string, uint64_t>> geometry;
  size_t bucket_capacity = bs::kBucketCapacity;
  size_t out_buckets = 0;
  size_t key_bytes = 0, value_bytes = 0;
  uint64_t nonce_lo = 0, nonce_hi = 0;
  unsigned family_level = 0;
  uint64_t family_ordinal = 0;
  std::vector<std::array<uint8_t, 16>> round_keys;
  std::vector<Rec> a_main, a_tier, b_main, b_tier;
  std::vector<Rec> out_main, out_tier;
  std::map<bs::KeyWords, uint64_t> words;  // routing word of every A u B key
  bool failed = false;
  std::string message;
  // The test's own model (winners, planted as the fixture is built) and the
  // engine-side collected output, for the engine-level checks.
  std::map<bs::KeyWords, ts::LiveEntry> model;
  std::map<bs::KeyWords, ts::LiveEntry> live;
  bool live_unique = true;
  size_t live_damaged = 0;
  bool sources_unchanged = true;
  // Where the test's own DestinationBuckets recipe puts every key.
  std::map<bs::KeyWords, size_t> test_homes;
};

// ---------------------------------------------------------------------------
// Reading storage back
// ---------------------------------------------------------------------------

template <class Store>
std::vector<Rec> Collect(const bs::Layout& layout, const Store& s) {
  std::vector<Rec> out;
  for (size_t b = 0; b < s.num_buckets; ++b) {
    for (size_t lane = 0; lane < bs::kBucketCapacity; ++lane) {
      if (((s.masks[b] >> lane) & 1) == 0) continue;
      Rec r;
      r.bucket = b;
      r.lane = lane;
      r.key = ts::SlotKeyWordsOf(layout, s.Bucket(b), lane);
      r.value.resize(layout.value_bytes);
      for (size_t i = 0; i < layout.value_bytes; ++i) {
        r.value[i] = s.Bucket(b)[(layout.key_bytes + i) * bs::kBucketCapacity +
                                 lane];
      }
      // kMetaResidualClass is engine scratch, not data (see
      // ts::SlotMetaOf): mask it out of the meta byte, the last value byte.
      r.value.back() = static_cast<uint8_t>(r.value.back() &
                                            ~bs::kMetaResidualClass);
      r.tombstone = (r.value.back() & bs::kMetaErased) != 0;
      out.push_back(std::move(r));
    }
  }
  return out;
}

// Where the TEST recomputes each key's destination bucket: the flat map's low
// tag bits through ComputeRoutingTags (job_test.cpp DestinationBuckets).
std::vector<size_t> TestDestinationBuckets(
    const bs::Layout& layout, const bs::RebuildNonce& nonce,
    const la::MergeShape& shape, const bs::AesTagKeys& aes_keys,
    const std::vector<bs::KeyWords>& keys) {
  bs::RoutingIndexMap flat;
  if (shape.has_radix_pass()) {
    flat.kind = bs::TagMapKind::kRadixDigit;
    flat.low_bits = shape.block_bits;
    flat.modulus = shape.odd_part;
    flat.digit_shift = shape.block_bits;
  }
  const unsigned bits = shape.block_bits + (shape.has_radix_pass() ? 3 : 0);
  std::vector<size_t> buckets;
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

// ---------------------------------------------------------------------------
// The job (a minimal replica of RunCase for the binary d = 2 case)
// ---------------------------------------------------------------------------

Fixture Run(const Config& cfg) {
  Fixture fx;
  fx.cfg = cfg;

  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = 4;
  layout.digit_bits = 0;
  fx.key_bytes = layout.key_bytes;
  fx.value_bytes = layout.value_bytes;

  const microram::crypto::AesRoundKeys round_keys =
      microram::crypto::DeriveAesRoundKeys(
          microram::crypto::SecretKeySeed::Fixed(cfg.key_seed));
  const std::unique_ptr<bs::AesTagKeys> instance_keys =
      bs::MakeAesTagKeys(round_keys);
  const bs::AesTagKeys& keys = *instance_keys;
  for (int r = 0; r < 11; ++r) {
    std::array<uint8_t, 16> bytes;
    _mm_storeu_si128(reinterpret_cast<__m128i*>(bytes.data()), round_keys.rk[r]);
    fx.round_keys.push_back(bytes);
  }

  la::LevelArenaGeometry::Params p;
  p.tier_buckets = kTierBuckets;
  p.branching = kBranching;
  p.levels = kLevels;
  p.top_digit = 2;
  p.prefix_flushes = kPrefixFlushes;
  p.stash_buckets = kStashBuckets;
  p.bank_first = la::BankFirst::kOff;
  const la::LevelArenaGeometry geometry(p);
  const la::LevelArenaStashSizing sizing(geometry, kMaxAccesses);
  la::LevelArenaSet arenas(geometry, layout);

  const unsigned level = kLevel;
  const unsigned digit = kDigit;
  const uint64_t ordinal = digit;
  const size_t carry_buckets = geometry.CarryBuckets(level);
  const unsigned carry_bits = bs::Log2Exact(carry_buckets);
  const la::Family family = la::CanonicalFamily(geometry, level, ordinal);
  const bs::RebuildNonce nonce = la::FamilyNonce(family);
  const la::CarryPlan carry_plan = geometry.PlanCarry(level, ordinal);
  if (carry_plan.outcome == la::CarryOutcome::kAdopt) {
    throw std::logic_error("this digit is not a plain ordinary merge");
  }
  const unsigned radix = digit >> static_cast<unsigned>(_tzcnt_u32(digit));
  const la::MergeShape shape = la::MakeMergeShape(carry_buckets, digit, radix);
  bs::RoutingIndexMap map;
  if (radix > 1) {
    throw std::logic_error("d = 2 has no radix pass");
  }

  // The engine's one routing: DFS, with separated sources at a sparse digit
  // above one below the top (no routing option is left to choose).
  const bool separated = la::SeparatedSources(geometry, level, digit);

  fx.nonce_lo = nonce.real_lo;
  fx.nonce_hi = nonce.real_hi;
  fx.family_level = family.level;
  fx.family_ordinal = family.ordinal;
  fx.out_buckets = shape.out_buckets;

  // ---- public geometry ----------------------------------------------------
  {
    const size_t older_tier = geometry.OlderTierBuckets(level, digit);
    const size_t carry_tier = geometry.CarryTierBuckets(level);
    const la::LevelMergePoolShape pool = la::LevelMergePoolShapeOf(
        shape, sizing.Buckets(level), older_tier, carry_tier);
    const bs::ResidualRangePlan plan = la::LevelFinishRangePlan(pool);
    auto& g = fx.geometry;
    g.emplace_back("bucket_capacity", bs::kBucketCapacity);
    g.emplace_back("key_bytes", layout.key_bytes);
    g.emplace_back("value_bytes", layout.value_bytes);
    g.emplace_back("tag_bytes", layout.tag_bytes);
    g.emplace_back("branching", kBranching);
    g.emplace_back("levels", kLevels);
    g.emplace_back("level", level);
    g.emplace_back("digit", digit);
    g.emplace_back("odd_part", shape.odd_part);
    g.emplace_back("power", shape.power);
    g.emplace_back("U", carry_buckets);
    g.emplace_back("K", shape.carry_bits);
    g.emplace_back("block_bits", shape.block_bits);
    g.emplace_back("block_buckets", shape.block_buckets);
    g.emplace_back("out_buckets", shape.out_buckets);
    g.emplace_back("older_buckets", shape.older_buckets);
    g.emplace_back("older_tier_buckets", older_tier);
    g.emplace_back("carry_tier_buckets", carry_tier);
    g.emplace_back("out_tier_buckets", geometry.TierBucketsOf(level));
    g.emplace_back("stage_stash_buckets", sizing.Buckets(level));
    g.emplace_back("prefix_flushes", kPrefixFlushes);
    g.emplace_back("stash_buckets", kStashBuckets);
    g.emplace_back("routed_prefix_buckets", geometry.RoutedPrefixBuckets());
    g.emplace_back("pool_swept_buckets", pool.swept_buckets);
    g.emplace_back("pool_main_levels", pool.main_levels);
    g.emplace_back("pool_fused", pool.fused ? 1 : 0);
    g.emplace_back("pool_direct_buckets", pool.direct_buckets);
    g.emplace_back("range_bits", plan.range_bits);
    g.emplace_back("range_index_bits", plan.index_bits);
    g.emplace_back("range_groups", plan.groups);
    g.emplace_back("range_buckets", plan.range_buckets);
    g.emplace_back("range_scatter_per_bucket", plan.scatter_per_bucket);
    g.emplace_back("separated_sources", separated ? 1 : 0);
    // Actual completed-A leaf width for this finish; B is offered directly.
    g.emplace_back("dfs_pages", la::FinishDfsPages(pool));
    g.emplace_back("max_accesses_log2", 32);
  }

  std::map<bs::KeyWords, ts::LiveEntry>& model = fx.model;
  uint64_t next_key = 1;
  std::mt19937_64 rng(0xA55E + 97 * level + 7 * digit + kBranching);
  const uint8_t tomb = 0;

  // ---- the older operand (source A, byte 1) -------------------------------
  la::LevelArena& arena = arenas.At(level);
  std::vector<bs::KeyWords> older_keys;
  const size_t older_buckets = shape.older_buckets;
  const la::CarryPlan older_plan = geometry.PlanCarry(level, ordinal - 1);
  la::LevelArena& older_arena = arenas.At(older_plan.destination_level);
  unsigned older_slot = older_arena.plan().inbox[0];
  if (older_plan.outcome == la::CarryOutcome::kAdopt) {
    older_slot = older_arena.plan().inbox[1];
  } else if (older_plan.destination_kind == la::SlotKind::kOddBank) {
    older_slot = older_arena.plan().odd_bank;
  } else if (older_plan.destination_kind == la::SlotKind::kRunBank) {
    older_slot = older_arena.plan().run_bank;
  }
  std::vector<bs::KeyWords> forced =
      cfg.forced_older == 0
          ? std::vector<bs::KeyWords>()
          : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, map,
                               shape.block_bits, shape.block_bits,
                               /*target=*/0, cfg.forced_older, &next_key,
                               keys);
  ts::PublishedSource older = ts::PublishSlot(
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
        // A NONEMPTY OLDER TIER, disjoint from the main.
        std::vector<bs::KeyWords> tier_keys;
        for (int i = 0; i < 12; ++i) {
          tier_keys.push_back(ts::FixtureKey(next_key++, layout.key_bytes));
          older_keys.push_back(tier_keys.back());
        }
        ts::PlantTier(layout, tier, tier_keys, 1, tomb, &model);
      },
      older_plan.destination_offset);

  // ---- the fresher operand (source B, byte 2) -----------------------------
  const size_t fresh_keys_wanted = carry_buckets * 16;
  const std::vector<bs::KeyWords> forced_fresh =
      cfg.forced_fresh == 0
          ? std::vector<bs::KeyWords>()
          : ts::KeysAtTagIndex(layout, nonce.real_lo, nonce.real_hi, map,
                               shape.block_bits, shape.block_bits,
                               /*target=*/0, cfg.forced_fresh, &next_key,
                               keys);
  // A third of the fresher keys shadow the older operand.
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

  const unsigned inbox = arena.plan().inbox[0];
  ts::PublishedSource carry = ts::PublishSlot(
      &arena, inbox, carry_buckets, layout,
      [&](bs::TableView main, bs::ResidualStash* tier) {
        std::vector<bs::KeyWords> used;
        const size_t per_bucket = 16;
        for (size_t i = 0; i < fresh_keys_wanted; ++i) {
          used.push_back(fresher_key(i, &used));
        }
        for (size_t b = 0; b < main.num_buckets; ++b) {
          const size_t count =
              b * per_bucket < used.size()
                  ? std::min(per_bucket, used.size() - b * per_bucket)
                  : 0;
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
        // under the FAMILY nonce.
        bs::ComputeRoutingTags(main, nonce.real_lo, nonce.real_hi,
                               bs::RoutingIndexMap{}, carry_bits, keys);
        // The fixture's own route, at the certified depth: a carry that shed
        // here would be a broken fixture and not a result.
        const size_t route_depth = sizing.Buckets(level);
        const size_t route_bytes =
            carry_bits * route_depth * layout.BucketBytes();
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
        // A NONEMPTY FRESHER TIER, holding keys the older operand also has.
        std::vector<bs::KeyWords> tier_keys;
        for (size_t i = 0; i < older_keys.size() && tier_keys.size() < 12; ++i) {
          const auto key = older_keys[(i + 3) % older_keys.size()];
          if (std::find(used.begin(), used.end(), key) == used.end())
            tier_keys.push_back(key);
        }
        ts::PlantTier(layout, tier, tier_keys, 2, tomb, &model);
      });

  {
    std::map<bs::KeyWords, ts::LiveEntry> union_b;
    bool unique_b = true;
    size_t damage_b = 0;
    ts::CollectLive(carry.Main(), &union_b, &unique_b, &damage_b);
    ts::CollectLiveStashes(layout, carry.Tier(), 1, &union_b, &unique_b,
                           &damage_b);
    if (!unique_b || damage_b != 0) {
      throw std::logic_error("B main/tier contract violated by the fixture");
    }
  }

  // The inputs, exactly as the job will read them.
  fx.a_main = Collect(layout, older.Main());
  fx.a_tier = Collect(layout, *older.Tier());
  fx.b_main = Collect(layout, carry.Main());
  fx.b_tier = Collect(layout, *carry.Tier());

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
  la::LevelMergeJob job(geometry, sizing, layout, level, keys, /*lanes=*/1);
  la::LevelMergeScratch scratch(
      layout, la::MaxLevelMergeRangeBuckets(geometry, sizing, level),
      la::MaxLevelDfsAllocation(geometry, sizing, level));
  const bs::SubtaskBudget budget = la::WholeLevelMergeBudget();

  la::LevelMergeBinding binding;
  binding.ordinal = ordinal;
  binding.out = dest_arena.WritableMain(dest, carry_plan.destination_offset,
                                        shape.out_buckets);
  binding.out_tier = dest_arena.WritableTier(dest);
  binding.destination_generation = dest.generation;
  binding.older_main = older.Main();
  binding.older_tier = older.Tier();
  // A previous occupancy's bytes are still in a leased slot; a merge that
  // wrote only part of its output must not look correct by accident.
  std::memset(binding.out.data, 0xA5,
              shape.out_buckets * layout.BucketBytes());
  for (size_t b = 0; b < shape.out_buckets; ++b) binding.out.masks[b] = 0;
  std::memset(binding.out_tier->data, 0xA5,
              binding.out_tier->num_buckets * layout.BucketBytes());

  la::LevelCarry incoming;
  incoming.ordinal = ordinal;
  incoming.family = family;
  incoming.main = carry.Main();
  incoming.tier = carry.Tier();

  try {
    job.Begin(binding);
    // The job derives its own coordinate; the fixture placed its carry, and
    // the words below are computed, under the family it was built for.
    if (job.digit() != digit || job.family() != family ||
        job.nonce().real_hi != nonce.real_hi ||
        job.nonce().real_lo != nonce.real_lo) {
      throw std::logic_error("the job derived a different coordinate than "
                             "the fixture placed its carry under");
    }
    job.PrepareOlder(budget);
    job.InstallCarry(incoming, budget);
    job.FinishMerge(&scratch, budget);
  } catch (const std::runtime_error& e) {
    fx.failed = true;
    fx.message = e.what();
  }

  // ---- the routing word of every key of A u B -----------------------------
  microram::crypto::AesRoundKeys rk;
  for (int r = 0; r < 11; ++r) rk.rk[r] = keys.rk[r];
  std::vector<bs::KeyWords> all_keys;
  for (const auto* v : {&fx.a_main, &fx.a_tier, &fx.b_main, &fx.b_tier}) {
    for (const Rec& r : *v) {
      if (fx.words.emplace(r.key, 0).second) all_keys.push_back(r.key);
    }
  }
  for (auto& kv : fx.words) {
    kv.second = microram::crypto::AesCtrTagU128WordsHost(
        nonce.real_lo, nonce.real_hi, kv.first.w0, kv.first.w1, rk);
  }
  {
    const std::vector<size_t> homes =
        TestDestinationBuckets(layout, nonce, shape, keys, all_keys);
    for (size_t i = 0; i < all_keys.size(); ++i) {
      fx.test_homes[all_keys[i]] = homes[i];
    }
  }

  fx.sources_unchanged = older.Unchanged(layout) && carry.Unchanged(layout);

  if (!fx.failed) {
    fx.out_main = Collect(layout, binding.out);
    fx.out_tier = Collect(layout, *binding.out_tier);
    ts::CollectLive(binding.out, &fx.live, &fx.live_unique, &fx.live_damaged);
    ts::CollectLiveStashes(layout, binding.out_tier, 1, &fx.live,
                           &fx.live_unique, &fx.live_damaged);
  }
  return fx;
}

// ---------------------------------------------------------------------------
// The dumper's own check: the O1 spec, in C++, independent of the model the
// test builds (the Lean oracle re-checks it from the JSON alone).
// ---------------------------------------------------------------------------

using Key = std::pair<uint64_t, uint64_t>;
Key KeyOf(const bs::KeyWords& k) { return {k.w1, k.w0}; }

std::vector<std::string> SelfCheck(const Fixture& fx, size_t* winners_out,
                                   size_t* tier_expected_out,
                                   std::vector<size_t>* homes_x) {
  std::vector<std::string> bad;
  const auto note = [&](const std::string& s) {
    if (bad.size() < 20) bad.push_back(s);
  };
  const size_t cap = bs::kBucketCapacity;

  // Structural sanity of the inputs: each source's keys are distinct across
  // its main and its tier.
  const auto distinct = [&](const char* name, const std::vector<Rec>& main,
                            const std::vector<Rec>& tier) {
    std::set<Key> seen;
    for (const auto* v : {&main, &tier}) {
      for (const Rec& r : *v) {
        if (!seen.insert(KeyOf(r.key)).second)
          note(std::string(name) + " key repeated");
      }
    }
  };
  distinct("A", fx.a_main, fx.a_tier);
  distinct("B", fx.b_main, fx.b_tier);

  // Winners: B beats A.
  struct Val {
    std::vector<uint8_t> value;
    bool tombstone;
    int source;
  };
  std::map<Key, Val> want;
  for (const auto* v : {&fx.a_main, &fx.a_tier}) {
    for (const Rec& r : *v) want[KeyOf(r.key)] = {r.value, r.tombstone, 1};
  }
  for (const auto* v : {&fx.b_main, &fx.b_tier}) {
    for (const Rec& r : *v) want[KeyOf(r.key)] = {r.value, r.tombstone, 2};
  }
  *winners_out = want.size();

  // Conservation.
  std::map<Key, size_t> got_count;
  for (const auto* v : {&fx.out_main, &fx.out_tier}) {
    for (const Rec& r : *v) {
      const Key k = KeyOf(r.key);
      ++got_count[k];
      const auto it = want.find(k);
      if (it == want.end()) {
        note("output holds a key no input has");
      } else if (it->second.value != r.value ||
                 it->second.tombstone != r.tombstone) {
        note("output holds a non-newest version of a key");
      }
    }
  }
  for (const auto& kv : want) {
    const auto it = got_count.find(kv.first);
    if (it == got_count.end()) note("a winner is missing from the output");
    else if (it->second != 1) note("a key occurs more than once in the output");
  }

  // Placement, against both the direct AES word and the test's own recipe.
  const size_t mask = fx.out_buckets - 1;
  for (const Rec& r : fx.out_main) {
    const uint64_t w = fx.words.at(r.key);
    if ((w & mask) != r.bucket) note("output main record not at its home");
    if (fx.test_homes.at(r.key) != r.bucket)
      note("output main record not at the test-recipe home");
  }
  for (const auto& kv : fx.words) {
    if (fx.test_homes.at(kv.first) != (kv.second & mask))
      note("AES word & mask disagrees with the test's DestinationBuckets");
  }

  // Counts.
  std::vector<size_t> x(fx.out_buckets, 0), main_n(fx.out_buckets, 0),
      tier_n(fx.out_buckets, 0);
  for (const auto& kv : want) {
    bs::KeyWords k;
    k.w1 = kv.first.first;
    k.w0 = kv.first.second;
    ++x[fx.words.at(k) & mask];
  }
  for (const Rec& r : fx.out_main) ++main_n[r.bucket];
  for (const Rec& r : fx.out_tier) ++tier_n[fx.words.at(r.key) & mask];
  size_t tier_expected = 0;
  for (size_t v = 0; v < fx.out_buckets; ++v) {
    const size_t excess = x[v] > cap ? x[v] - cap : 0;
    tier_expected += excess;
    if (main_n[v] != std::min(x[v], cap)) note("main bucket count != min(X,64)");
    if (tier_n[v] != excess) note("tier records of a home != (X-64)+");
  }
  if (fx.out_tier.size() != tier_expected) note("tier size != sum (X-64)+");
  *tier_expected_out = tier_expected;
  *homes_x = x;

  // Engine-level checks the test makes.
  if (!fx.live_unique) note("engine: a key survives twice");
  if (fx.live_damaged != 0) note("engine: damaged payloads");
  if (fx.live != fx.model) note("engine: output != the test's model");
  if (!fx.sources_unchanged) note("engine: a source was written");
  return bad;
}

// ---------------------------------------------------------------------------
// JSON
// ---------------------------------------------------------------------------

std::string Hex64(uint64_t v) {
  char buf[17];
  std::snprintf(buf, sizeof(buf), "%016llx", static_cast<unsigned long long>(v));
  return buf;
}

std::string HexBytes(const uint8_t* p, size_t n) {
  std::string s;
  char buf[3];
  for (size_t i = 0; i < n; ++i) {
    std::snprintf(buf, sizeof(buf), "%02x", p[i]);
    s += buf;
  }
  return s;
}

std::string Escape(const std::string& s) {
  std::string out;
  for (char c : s) {
    if (c == '"' || c == '\\') {
      out += '\\';
      out += c;
    } else if (c == '\n') {
      out += "\\n";
    } else if (static_cast<unsigned char>(c) < 0x20) {
      out += ' ';
    } else {
      out += c;
    }
  }
  return out;
}

// A key is written as its low 8 bytes (this layout stores 8-byte keys, so the
// high word is zero; the dumper refuses anything else).
std::string RecJson(const Rec& r) {
  if (r.key.w1 != 0) throw std::logic_error("wide key in an 8-byte layout");
  std::string s = "{\"bucket\":" + std::to_string(r.bucket) +
                  ",\"lane\":" + std::to_string(r.lane) + ",\"key\":\"" +
                  Hex64(r.key.w0) + "\",\"value\":\"" +
                  HexBytes(r.value.data(), r.value.size()) +
                  "\",\"tombstone\":" + (r.tombstone ? "true" : "false") + "}";
  return s;
}

void RecList(std::string* out, const char* name, const std::vector<Rec>& v,
             bool last) {
  *out += "    \"";
  *out += name;
  *out += "\": [";
  for (size_t i = 0; i < v.size(); ++i) {
    *out += i == 0 ? "\n      " : ",\n      ";
    *out += RecJson(v[i]);
  }
  *out += v.empty() ? "]" : "\n    ]";
  *out += last ? "\n" : ",\n";
}

std::string ToJson(const Fixture& fx) {
  std::string j;
  j += "{\"format\":\"rebuild-fixture/0\",\n";
  j += " \"job\":{\"kind\":\"ordinary_merge\",\"digit\":" + std::to_string(kDigit) +
       ",\"level\":" + std::to_string(kLevel) +
       ",\"separated_sources\":true,\"shape\":\"dfs\",\"seed\":\"" +
       Hex64(fx.cfg.key_seed) + "\",\"forced_older\":" +
       std::to_string(fx.cfg.forced_older) + ",\"forced_fresh\":" +
       std::to_string(fx.cfg.forced_fresh) + ",\"aes_round_keys\":[";
  for (size_t i = 0; i < fx.round_keys.size(); ++i) {
    j += (i ? ",\"" : "\"") + HexBytes(fx.round_keys[i].data(), 16) + "\"";
  }
  j += "]},\n";
  j += " \"geometry\":{";
  for (size_t i = 0; i < fx.geometry.size(); ++i) {
    j += (i ? "," : "") + std::string("\"") + fx.geometry[i].first +
         "\":" + std::to_string(fx.geometry[i].second);
  }
  j += "},\n";
  j += " \"families\":{\"merge\":{\"level\":" + std::to_string(fx.family_level) +
       ",\"ordinal\":" + std::to_string(fx.family_ordinal) +
       ",\"nonce_lo\":\"" + Hex64(fx.nonce_lo) + "\",\"nonce_hi\":\"" +
       Hex64(fx.nonce_hi) + "\"}},\n";
  j += " \"inputs\":{\n";
  RecList(&j, "A_main", fx.a_main, false);
  RecList(&j, "A_tier", fx.a_tier, false);
  RecList(&j, "B_main", fx.b_main, false);
  RecList(&j, "B_tier", fx.b_tier, true);
  j += " },\n \"words\":[";
  bool first = true;
  for (const auto& kv : fx.words) {
    j += first ? "\n  " : ",\n  ";
    first = false;
    j += "{\"family\":\"merge\",\"key\":\"" + Hex64(kv.first.w0) +
         "\",\"word\":\"" + Hex64(kv.second) + "\"}";
  }
  j += "],\n \"outputs\":{\"verdict\":\"";
  j += fx.failed ? "failure" : "success";
  j += "\",\"message\":\"" + Escape(fx.message) + "\",\n";
  RecList(&j, "main", fx.out_main, false);
  RecList(&j, "tier", fx.out_tier, true);
  j += " }}\n";
  return j;
}

}  // namespace

int main(int argc, char** argv) {
  Config cfg;
  const char* out_path = nullptr;
  for (int i = 1; i < argc; ++i) {
    const std::string a = argv[i];
    const auto arg = [&]() -> const char* {
      if (i + 1 >= argc) {
        std::fprintf(stderr, "fixture_dump: %s needs a value\n", a.c_str());
        std::exit(2);
      }
      return argv[++i];
    };
    if (a == "--seed") cfg.key_seed = std::strtoull(arg(), nullptr, 16);
    else if (a == "--forced-older") cfg.forced_older = std::strtoull(arg(), nullptr, 10);
    else if (a == "--forced-fresh") cfg.forced_fresh = std::strtoull(arg(), nullptr, 10);
    else if (a.size() > 0 && a[0] != '-' && out_path == nullptr) out_path = argv[i];
    else {
      std::fprintf(stderr,
                   "usage: fixture_dump [OUT.json] [--seed HEX] "
                   "[--forced-older N] [--forced-fresh N]\n");
      return 2;
    }
  }

  try {
    const Fixture fx = Run(cfg);
    int status = 0;
    if (fx.failed) {
      std::printf("job verdict: failure (%s)\n", fx.message.c_str());
      std::printf("inputs: A_main=%zu A_tier=%zu B_main=%zu B_tier=%zu\n",
                  fx.a_main.size(), fx.a_tier.size(), fx.b_main.size(),
                  fx.b_tier.size());
    } else {
      size_t winners = 0, tier_expected = 0;
      std::vector<size_t> x;
      const std::vector<std::string> bad =
          SelfCheck(fx, &winners, &tier_expected, &x);
      size_t shadowed = 0;
      {
        std::set<Key> a;
        for (const auto* v : {&fx.a_main, &fx.a_tier})
          for (const Rec& r : *v) a.insert(KeyOf(r.key));
        for (const auto* v : {&fx.b_main, &fx.b_tier})
          for (const Rec& r : *v) shadowed += a.count(KeyOf(r.key));
      }
      size_t full = 0, maxx = 0;
      for (size_t v : x) {
        full += v >= bs::kBucketCapacity;
        maxx = std::max(maxx, v);
      }
      std::printf("job verdict: success\n");
      std::printf("inputs: A_main=%zu A_tier=%zu B_main=%zu B_tier=%zu "
                  "(keys in both A and B: %zu)\n",
                  fx.a_main.size(), fx.a_tier.size(), fx.b_main.size(),
                  fx.b_tier.size(), shadowed);
      std::printf("winners=%zu  out_main=%zu out_tier=%zu (expected %zu)  "
                  "homes=%zu full_homes=%zu max_X=%zu\n",
                  winners, fx.out_main.size(), fx.out_tier.size(),
                  tier_expected, x.size(), full, maxx);
      if (!bad.empty()) {
        status = 1;
        for (const std::string& s : bad)
          std::fprintf(stderr, "self-check: %s\n", s.c_str());
      } else {
        std::printf("self-check: pass\n");
      }
    }
    if (out_path != nullptr) {
      const std::string json = ToJson(fx);
      std::FILE* f = std::fopen(out_path, "wb");
      if (f == nullptr) {
        std::fprintf(stderr, "fixture_dump: cannot write %s\n", out_path);
        return 2;
      }
      std::fwrite(json.data(), 1, json.size(), f);
      std::fclose(f);
      std::printf("wrote %s (%zu bytes)\n", out_path, json.size());
    }
    return status;
  } catch (const std::exception& e) {
    std::fprintf(stderr, "fixture_dump: harness error: %s\n", e.what());
    return 2;
  }
}
