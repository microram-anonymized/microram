// The residual SECOND CHANCE fed from a DFS-built range table: entries a
// rebuild shed into residual stashes are offered their main bucket again, and
// may take a free lane or, where they are the fresher copy, replace a stale
// duplicate.  Covered here:
//   * offers from a DFS leaf's stacked pages: the production offer kernel,
//     page by page for each main bucket (DfsResidualRangePlan's pairing, one
//     leaf), against a deliberately scalar oracle that works on records and
//     explicit free slots;
//   * the order in which the native finish lists its pool sources;
//   * a combined pass whose two sources must not spend each other's capacity;
//   * the fused fixed merge (merge plus every offer in one pass) against the
//     same steps run one after another, byte for byte;
//   * the coarse-range cap of the DFS plan.
// Any disagreement would either lose an entry or publish a stale copy next to
// a fresher one.  The integrated pass is tested end to end by the level-arena
// job test.

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <stdexcept>
#include <vector>

#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/rebuild/cpu_byteslice_second_chance.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"

namespace bs = microram::byteslice;
using Record = std::vector<uint8_t>;
using Records = std::map<uint64_t, Record>;
using Rule = bs::ResidualDedupRule;

void Check(bool ok, const char* message) {
  if (!ok) throw std::runtime_error(message);
}
bs::Table Empty(size_t pages, bs::Layout layout) {
  auto t = bs::Table::Create(pages, layout);
  std::memset(t.data.get(), 0xef, pages * layout.BucketBytes());
  return t;
}
bs::Table Clone(bs::Table& t) {
  auto copy = Empty(t.num_buckets, t.layout);
  std::memcpy(copy.data.get(), t.data.get(), t.num_buckets * t.layout.BucketBytes());
  std::copy_n(t.masks.get(), t.num_buckets, copy.masks.get());
  return copy;
}
Record Read(bs::TableView t, size_t slot) {
  Record r(t.layout.EntryBytes());
  bs::ReadEntry(t.Bucket(slot / 64), slot % 64, r.data(), r.size());
  return r;
}
bool Live(bs::TableView t, size_t slot) {
  return ((t.masks[slot / 64] >> (slot % 64)) & 1) != 0;
}
void Clear(bs::TableView t, size_t slot) {
  t.masks[slot / 64] &= ~(uint64_t{1} << (slot % 64));
}
void Put(bs::TableView t, size_t slot, const Record& record, size_t lines) {
  bs::WriteEntry(t.Bucket(slot / 64), slot % 64, record.data(), lines);
  t.masks[slot / 64] |= uint64_t{1} << (slot % 64);
}
uint64_t Key(const Record& r) {
  uint64_t k = 0;
  for (unsigned i = 0; i < 8; ++i) k |= uint64_t(r[i]) << (8 * i);
  return k;
}
size_t Home(const Record& r, bs::Layout layout, unsigned bits) {
  uint64_t tag = 0;
  for (size_t i = 0; i < layout.tag_bytes; ++i)
    tag |= uint64_t(r[layout.TagLine(unsigned(i * 8))]) << (8 * i);
  return tag & ((uint64_t{1} << bits) - 1);
}
Record Make(bs::Layout layout, uint64_t key, size_t home, bool fresh, unsigned version) {
  Record r(layout.EntryBytes(), uint8_t(version));
  for (size_t i = 0; i < layout.key_bytes; ++i) r[i] = i < 8 ? uint8_t(key >> (i * 8)) : uint8_t(0x9a);
  // Includes tombstones while preserving unrelated metadata bits.
  r[layout.MetaLine()] = uint8_t((version & ~bs::kMetaResidualClass) |
      (fresh ? bs::kMetaResidualClass : 0));
  for (size_t i = 0; i < layout.tag_bytes; ++i)
    r[layout.TagLine(unsigned(i * 8))] = uint8_t(home >> (i * 8));
  return r;
}
void Same(bs::TableView a, bs::TableView b) {
  for (size_t page = 0; page < a.num_buckets; ++page)
    Check(a.masks[page] == b.masks[page], "mask differs from scalar offer");
  for (size_t s = 0; s < a.num_buckets * 64; ++s)
    if (Live(a, s)) Check(Read(a, s) == Read(b, s), "record differs from scalar offer");
}
void Collect(bs::TableView t, Records& out) {
  for (size_t s = 0; s < t.num_buckets * 64; ++s) if (Live(t, s)) {
    auto r = Read(t, s);
    Check(out.emplace(Key(r), r).second, "duplicate published key");
  }
}

// One leaf of a DFS leaf table, offered to main bucket b: its pages in
// order, each through the production kernel with the stacked plan's pairing
// (page g of the leaf is range bucket g of a one-leaf table).
void OfferLeaf(bs::TableView main, size_t b, bs::TableView leaf, unsigned bits,
               Rule rule, size_t lines) {
  bs::ResidualRangePlan plan;
  plan.range_bits = 0;
  plan.index_bits = bits;
  plan.groups = leaf.num_buckets;
  plan.range_buckets = leaf.num_buckets;
  plan.scatter_per_bucket = 64;
  for (size_t g = 0; g < leaf.num_buckets; ++g)
    bs::OfferResidualsToBucket(main, leaf, plan, rule, lines, b, g);
}

// Deliberately scalar, variable-work oracle: operate on records and explicit
// free slots, independent of the SIMD masks/permutation planner.
void Oracle(bs::TableView main, size_t b, bs::TableView leaf, unsigned bits,
            Rule rule, size_t lines) {
  for (size_t page = 0; page < leaf.num_buckets; ++page) {
    std::vector<size_t> stale, fresh;
    for (size_t i = page * 64; i < (page + 1) * 64; ++i) {
      if (!Live(leaf, i)) continue;
      const auto r = Read(leaf, i);
      if (Home(r, leaf.layout, bits) != b) continue;
      const bool f = rule == Rule::kResidualWins ||
          (rule == Rule::kClassMark && (r[leaf.layout.MetaLine()] & bs::kMetaResidualClass));
      (f ? fresh : stale).push_back(i);
    }
    auto duplicate = [&](const Record& r) {
      for (size_t s = 64 * b; s < 64 * (b + 1); ++s)
        if (Live(main, s) && Key(Read(main, s)) == Key(r)) return s;
      return main.num_buckets * 64;
    };
    auto insert = [&](size_t i) {
      for (size_t s = 64 * b; s < 64 * (b + 1); ++s) if (!Live(main, s)) {
        Put(main, s, Read(leaf, i), lines);
        Clear(leaf, i);
        return;
      }
    };
    for (auto i : stale) {
      if (rule != Rule::kNoDedup && duplicate(Read(leaf, i)) < main.num_buckets * 64)
        Clear(leaf, i);
      else insert(i);
    }
    for (auto i : fresh) {
      const size_t s = duplicate(Read(leaf, i));
      if (s < main.num_buckets * 64) Clear(main, s);
    }
    for (auto i : fresh) insert(i);
  }
}

void OracleCases() {
  for (bs::Layout layout : {bs::Layout{8, 17, 4}, bs::Layout{16, 257, 8}})
    for (Rule rule : {Rule::kNoDedup, Rule::kTableWins, Rule::kResidualWins, Rule::kClassMark})
      for (size_t occupancy : {size_t{0}, size_t{1}, size_t{31}, size_t{63}, size_t{64}})
        for (unsigned seed = 0; seed < 3; ++seed) {
          std::mt19937_64 rng(seed + 17);
          auto main = Empty(8, layout), leaf = Empty(3, layout);
          for (size_t b = 0; b < 8; ++b)
            for (size_t s = 0; s < occupancy; ++s)
              Put(bs::View(main), b * 64 + (s * 17) % 64,
                  Make(layout, b * 1000 + s + 1, b, false, 2), layout.EntryBytes());
          for (size_t i = 0; i < 192; ++i) {
            uint64_t key = 100000 + i;
            size_t b = rng() % 8;
            if (rule != Rule::kNoDedup && (i < 64 || i >= 128)) {
              b = i % 8;
              key = b * 1000 + i / 8 + 1;
            }
            if (seed != 0 && rng() % 3 == 0) continue;
            Put(bs::View(leaf), i, Make(layout, key, b, bool(rng() & 1),
                unsigned(i + 3)), layout.EntryBytes());
          }
          auto expected_main = Clone(main), expected_leaf = Clone(leaf);
          auto chained_main = Clone(main), chained_leaf = Clone(leaf);
          const size_t lines = seed == 2 ? layout.PayloadLines() : layout.EntryBytes();
          bs::ResidualOfferSet set;
          set.range = bs::View(chained_leaf);
          set.plan.index_bits = 3;
          set.plan.groups = 3;
          set.plan.range_buckets = 3;
          set.plan.scatter_per_bucket = 64;
          set.rule = rule;
          set.lines = lines;
          for (size_t b = 0; b < 8; ++b) {
            Oracle(bs::View(expected_main), b, bs::View(expected_leaf), 3, rule, lines);
            OfferLeaf(bs::View(main), b, bs::View(leaf), 3, rule, lines);
            bs::OfferResidualGroupsToBucket(set, bs::View(chained_main), b);
          }
          Same(bs::View(main), bs::View(expected_main));
          Same(bs::View(leaf), bs::View(expected_leaf));
          // Chaining the pages into one pass over the bucket is the same
          // bytes as offering them one after another, dummy lanes included.
          Check(std::memcmp(chained_main.data.get(), main.data.get(),
                            8 * layout.BucketBytes()) == 0 &&
                    std::equal(main.masks.get(), main.masks.get() + 8,
                               chained_main.masks.get()) &&
                    std::equal(leaf.masks.get(), leaf.masks.get() + 3,
                               chained_leaf.masks.get()),
                "chained pages differ from sequential offers");
          Records published;
          Collect(bs::View(main), published);
          Collect(bs::View(leaf), published);
          for (size_t i = 0; i < 192; ++i) if (Live(bs::View(leaf), i))
            Check(main.masks[Home(Read(bs::View(leaf), i), layout, 3)] == ~uint64_t{0},
                  "leftover destination is not full");
        }
}

void CrossPageWitness() {
  const bs::Layout layout{8, 17, 4};
  auto main = Empty(1, layout), leaf = Empty(2, layout);
  for (size_t i = 0; i < 64; ++i)
    Put(bs::View(main), i, Make(layout, i + 1, 0, false, 2), layout.EntryBytes());
  Put(bs::View(leaf), 0, Make(layout, 1000, 0, true, 3), layout.EntryBytes());
  Put(bs::View(leaf), 64, Make(layout, 1, 0, true, 5), layout.EntryBytes());
  auto sequential_main = Clone(main), sequential_leaf = Clone(leaf);
  bs::ResidualRangePlan plan;
  plan.range_buckets = 2; plan.groups = 2; plan.index_bits = 0;
  for (size_t page = 0; page < 2; ++page)
    bs::OfferResidualsToBucket(bs::View(sequential_main), bs::View(sequential_leaf),
                               plan, Rule::kClassMark, layout.EntryBytes(), 0, page);
  OfferLeaf(bs::View(main), 0, bs::View(leaf), 0,
                                  Rule::kClassMark, layout.EntryBytes());
  Same(bs::View(main), bs::View(sequential_main));
  Same(bs::View(leaf), bs::View(sequential_leaf));
  Check(Live(bs::View(leaf), 0) && !Live(bs::View(leaf), 64),
        "page-local priority changed or earlier page was revisited");
  Check(main.masks[0] == ~uint64_t{0}, "later page made an earlier leftover absorbable");
}

void SinglePageParity() {
  const bs::Layout layout{8, 17, 4};
  for (Rule rule : {Rule::kNoDedup, Rule::kTableWins, Rule::kResidualWins, Rule::kClassMark}) {
    auto main = Empty(1, layout), leaf = Empty(1, layout);
    for (size_t i = 0; i < 63; ++i)
      Put(bs::View(main), i, Make(layout, i + 1, 0, false, 2), layout.EntryBytes());
    for (size_t i = 0; i < 64; ++i)
      Put(bs::View(leaf), i, Make(layout, (i < 32 || rule == Rule::kNoDedup) ?
          1000 + i : i, 0, (i % 3) == 0, unsigned(i + 4)), layout.EntryBytes());
    auto old_main = Clone(main), old_leaf = Clone(leaf);
    bs::ResidualRangePlan plan;
    plan.range_buckets = 1; plan.groups = 1; plan.index_bits = 0;
    bs::OfferResidualsToBucket(bs::View(old_main), bs::View(old_leaf), plan,
                               rule, layout.EntryBytes(), 0, 0);
    OfferLeaf(bs::View(main), 0, bs::View(leaf), 0,
                                    rule, layout.EntryBytes());
    Same(bs::View(main), bs::View(old_main));
    Same(bs::View(leaf), bs::View(old_leaf));
  }
}

// Native recipes order by storage/class, not by freshness. Equal-rank sheds
// are emitted in route-level order; distinctness still comes from producers.
// Every ordinary digit above one has separated sources (A's completed route, then B's tier as the direct tail).
void ProducerOrder() {
  namespace la = bs::levelarena;
  for (unsigned digit = 2; digit <= 8; ++digit) {
    const unsigned radix = digit >> unsigned(_tzcnt_u32(digit));
    const auto shape = la::MakeMergeShape(8, digit, radix);
    std::vector<la::PoolSlot> slots;
    const auto recipe = la::FinishPoolSlotsOf(shape,
        [&](const la::PoolSlot& slot) { slots.push_back(slot); });
    Check(recipe.rule == Rule::kClassMark && slots[0].drain_only,
          "native finish prefix/rule");
    size_t at = 1;
      // The insertion's shed leads; A's route sheds follow, all of them,
      // then its radix shed.
    Check(slots[0].storage == la::PoolSlotStorage::kOlderShed &&
              slots[0].index == shape.block_bits +
                                    la::kLevelMergeMergeStashOffset &&
              slots[0].rank == la::kLevelMergeFresherRank,
          "separated insertion shed");
    for (unsigned bit = 0; bit < shape.block_bits; ++bit) {
      const auto& slot = slots.at(at++);
      Check(slot.storage == la::PoolSlotStorage::kOlderShed &&
            slot.index == bit && slot.rank == la::kLevelMergeOlderRank &&
            !slot.tier_class && !slot.drain_only, "A shed order");
    }
    if (radix > 1) {
      const auto& slot = slots.at(at++);
      Check(slot.storage == la::PoolSlotStorage::kOlderShed &&
            slot.index == shape.block_bits + la::kLevelMergeRadixStashOffset &&
            slot.rank == la::kLevelMergeOlderRank && !slot.tier_class,
            "A radix shed order");
    }
    const auto& older = slots.at(at++);
    Check(older.storage == la::PoolSlotStorage::kOlderTier &&
        older.rank == la::kLevelMergeOlderRank && !older.tier_class &&
        !older.drain_only, "older tier order");
    const auto& fresh = slots.at(at++);
    Check(fresh.storage == la::PoolSlotStorage::kCarryTier &&
        fresh.index == 0 && fresh.rank == la::kLevelMergeFresherRank &&
          fresh.tier_class && !fresh.drain_only, "fresh suffix order");
    Check(at == slots.size(), "unexpected native finish source");
  }
}


// One combined pass with a two-page A source and a full/empty private B tier.
// All A keys map to home 0; B spans all 16 homes (including equal low bits
// in different ranges). Gathering 65 A records fails; deleting one against
// B first admits exactly 64. B never spends A's leaf capacity.
void SeparatedBoundaries() {
  const bs::Layout layout{8, 17, 4};
  for (size_t pages : {size_t{1}, size_t{2}})
    for (size_t count : {size_t{0}, size_t{64}, size_t{65}})
      for (bool full_b : {false, true})
        for (bool overlap : {false, true}) {
          if (overlap && (!full_b || count == 0)) continue;
          auto main = Empty(16, layout), carry = Empty(8, layout);
          auto a = Empty(2, layout), b = Empty(pages, layout);
          auto shed = Empty(2, layout), drain = Empty(4, layout);
          auto tag = Empty(1, layout);
          uint64_t key = 1000;
          std::vector<Record> a_records;
          while (a_records.size() < count) {
            Put(bs::View(tag), 0, Make(layout, key++, 0, false, 2), layout.EntryBytes());
            bs::ComputeRoutingTags(bs::View(tag), 0, 0);
            if (Home(Read(bs::View(tag), 0), layout, 4) == 0)
              a_records.push_back(Read(bs::View(tag), 0));
          }
          for (size_t i = 0; i < count; ++i) Put(bs::View(a), i, a_records[i], layout.EntryBytes());
          if (full_b) for (size_t i = 0; i < 64 * pages; ++i) {
            auto record = Make(layout, overlap && i == 0 ? Key(a_records[0]) : key++, 0, true, 5);
            Put(bs::View(b), i, record, layout.EntryBytes());
          }
          auto b_original = Clone(b);
          auto stash_of = [&](bs::Table& table) {
            bs::ResidualStash stash;
            stash.data = table.data.get(); stash.entry_bytes = layout.EntryBytes();
            stash.num_buckets = table.num_buckets;
            std::copy_n(table.masks.get(), table.num_buckets, stash.masks);
            return stash;
          };
          auto sa = stash_of(a), sb = stash_of(b), ss = stash_of(shed), sd = stash_of(drain);
          bs::ResidualPassSpec spec;
          spec.main = bs::View(main); spec.main_levels = 4; spec.scratch = 0;
          spec.drain = &sd; spec.lines = layout.PayloadLines();
          spec.drain_only_slots = 1; spec.fuse = bs::ResidualFuseSite::kFixedMerge;
          spec.rule = Rule::kClassMark;
          spec.dfs_pages = 1; spec.separate_direct_tier = true;
          spec.AddOwned(&ss, 0); spec.AddOwned(&sa, 2); spec.AddOwnedTierClass(&sb, 0);
          bs::RebuildStepContext ctx;
          ctx.out = bs::View(main); ctx.fresher = bs::View(carry);
          ctx.merge_stash = &ss; ctx.aes_keys = &bs::DefaultAesTagKeys();
          ctx.retag_fresher_digits = true;
          std::vector<bs::ResidualStash*> pool;
          std::vector<uint8_t> rank;
          const size_t needed = bs::BuildResidualPassFields(&ctx, 0, &pool, &rank, spec);
          auto ranges = Empty(needed, layout);
          bs::AttachResidualRange(&ctx.residual[0], bs::View(ranges));
          bs::DfsResidualWorkspace dfs(layout, 2, 4, 1);
          bs::AttachResidualDfs(&ctx.residual[0], &dfs, 1);
          Check(needed == 16 + pages && dfs.Gather().num_buckets == 2,
                "B entered A's DFS allocation");
          const auto budget = bs::levelarena::WholeLevelMergeBudget();
          std::vector<bs::Subtask> tasks;
          bs::PlanFixedMerge(ctx, budget, &tasks);
          bool ok = true;
          for (const auto& task : tasks) {
            // Slice every public unit, including the DFS partition.
            for (size_t i = task.begin; i < task.end; ++i) {
              auto unit = task; unit.begin = i; unit.end = i + 1;
              if (!bs::RunSubtask<true>(ctx, unit)) { ok = false; break; }
            }
            if (!ok) break;
          }
          Check(ok == (count <= 64 || overlap), "A leaf 64/65 boundary or combined dedup");
          Check(std::memcmp(b.data.get(), b_original.data.get(), pages * layout.BucketBytes()) == 0,
                "borrowed B payload changed");
          if (!ok) continue;
          Records records;
          Collect(bs::View(main), records);
          Collect(bs::TableView{layout, sd.num_buckets, sd.data, sd.masks}, records);
          Check(records.size() == count + (full_b ? 64 * pages : 0) - overlap,
                "separated drain lost or duplicated records");
          if (overlap) Check(records.at(Key(a_records[0]))[layout.key_bytes] == 5,
                              "B replacement lost to A");
          for (size_t i = 0; i < 16 * 64; ++i) if (Live(bs::View(main), i)) {
            Put(bs::View(tag), 0, Read(bs::View(main), i), layout.EntryBytes());
            bs::ComputeRoutingTags(bs::View(tag), 0, 0);
            Check(Home(Read(bs::View(tag), 0), layout, 4) == i / 64,
                  "direct B offer compared only partial home bits");
          }
        }
}

// THE FUSED FIXED MERGE AGAINST ITS PARTS.  MergeFixedLevelSourcesOffersRange
// runs each destination's merge and every (set, group) offer in one pass and
// appends a source bucket's sheds to the stash once; the oracle runs the same
// steps one after another -- per direction the merge, then each (set, group)
// as its own offer.  Byte for byte, garbage in dummy lanes and the stash
// included, over ways, mixed rules (kNoDedup between readers), the three
// tombstone policies, both overflow modes and a shape too wide for one chain.
template <bool CheckOverflow>
bool SequentialFixedMerge(bs::TableView c, bs::TableView b, unsigned r,
                          bs::ResidualStash& stash,
                          const std::vector<bs::ResidualOfferSet>& sets,
                          bs::FixedMergeTombstones skip) {
  const bool resolved = skip == bs::FixedMergeTombstones::kAll;
  for (size_t i = 0; i < b.num_buckets; ++i) {
    const uint8_t* source = b.Bucket(i);
    const bool ok = bs::MergeRadixSourceBucket(
        c, source, b.masks[i],
        bs::FixedMergeSourceDigits(source, c.layout, r, nullptr), r,
        b.num_buckets, i, skip,
        [&](uint8_t* dst, const uint8_t* src, uint64_t* dst_mask,
            uint64_t src_mask, uint64_t shadowing, uint64_t direction,
            size_t ci) {
          if (resolved) {
            bs::ResolveTopDestination(sets.data(), sets.size(), ci, src,
                                      direction, dst, dst_mask, c.layout);
            src_mask &= ~shadowing;
          }
          if (!bs::MergeBucketIntoWithStash<CheckOverflow>(
                  dst, src, dst_mask, &src_mask, c.layout.PayloadLines(),
                  stash)) {
            return false;
          }
          for (const auto& set : sets)
            for (size_t g = 0; g < set.plan.groups; ++g)
              bs::OfferResidualsToBucket(c, set.range, set.plan,
                                         resolved ? Rule::kNoDedup : set.rule,
                                         set.lines, ci, g);
          return true;
        });
    if (!ok) return false;
  }
  return true;
}

// Garbage bytes everywhere; real lanes get keys from a small universe (so
// every kind of duplicate occurs), assorted meta bits and the tag `home(b)`.
template <typename Home>
void FillRandom(bs::Table& t, std::mt19937_64& rng, unsigned density8,
                uint64_t universe, Home home) {
  const bs::Layout& l = t.layout;
  for (size_t i = 0; i < t.num_buckets * l.BucketBytes(); ++i)
    t.data.get()[i] = uint8_t(rng());
  const uint8_t metas[] = {0, 0, bs::kMetaErased,
                           uint8_t(bs::kMetaErased | bs::kMetaUnshadowed),
                           bs::kMetaResidualClass,
                           uint8_t(bs::kMetaResidualClass | bs::kMetaErased)};
  for (size_t b = 0; b < t.num_buckets; ++b) {
    t.masks[b] = 0;
    for (size_t s = 0; s < 64; ++s) {
      if (rng() % 8 >= density8) continue;
      t.masks[b] |= uint64_t{1} << s;
      uint8_t* bucket = t.Bucket(b);
      const uint64_t key = rng() % universe;
      for (size_t k = 0; k < l.key_bytes; ++k)
        bucket[k * 64 + s] = k < 8 ? uint8_t(key >> (8 * k)) : uint8_t(0x5c);
      bucket[l.MetaLine() * 64 + s] = metas[rng() % 6];
      const uint64_t tag = home(b);
      for (size_t tb = 0; tb < l.tag_bytes; ++tb)
        bucket[(l.TagOffset() + l.tag_bytes - 1 - tb) * 64 + s] =
            uint8_t(tag >> (8 * tb));
    }
  }
}

template <bool CheckOverflow>
size_t FusedFixedMergeCases(unsigned seed) {
  std::mt19937_64 rng(seed);
  const std::vector<std::vector<Rule>> fixed_rules = {
      {Rule::kTableWins, Rule::kResidualWins},
      {Rule::kTableWins, Rule::kNoDedup, Rule::kResidualWins},
      {Rule::kNoDedup, Rule::kClassMark},
      {Rule::kClassMark, Rule::kNoDedup}};
  size_t compared = 0;
  for (int c = 0; c < 240; ++c) {
    const bs::Layout layout = c % 3 == 0 ? bs::Layout{8, 9, 3}
                            : c % 3 == 1 ? bs::Layout{16, 5, 3}
                                         : bs::Layout{4, 11, 3};
    const unsigned r = 1 + unsigned(rng() % 4);
    const size_t block = size_t{1} << (rng() % 3);
    const uint64_t universe = 64 + rng() % 400;
    auto any = [&](size_t) { return rng(); };
    auto older = bs::Table::Create(block * r, layout);
    auto fresher = bs::Table::Create(block, layout);
    FillRandom(older, rng, unsigned(rng() % 9), universe, any);
    FillRandom(fresher, rng, unsigned(rng() % 9), universe, any);
    for (size_t b = 0; b < block; ++b)
      for (size_t s = 0; s < 64; ++s)
        fresher.Bucket(b)[layout.DigitLine() * 64 + s] = uint8_t(rng() % r);
    std::vector<Rule> rules = c < 4 * 3 ? fixed_rules[c / 3] : std::vector<Rule>{};
    if (c >= 12) for (size_t n = rng() % 4; n > 0; --n) rules.push_back(Rule(rng() % 4));
    const bool wide = c % 40 == 39;  // 17 plans: the unchained shape
    if (wide) rules = {Rule::kTableWins, Rule::kResidualWins, Rule::kClassMark};
    const unsigned levels = bs::levelarena::ResidualCeilLog2(block * r);
    std::vector<bs::Table> ranges;
    std::vector<bs::ResidualOfferSet> sets;
    for (size_t o = 0; o < rules.size(); ++o) {
      const unsigned k = unsigned(rng() % (levels + 1)), ib = levels - k;
      const size_t groups = wide ? (o < 2 ? 8 : 1) : 1 + rng() % 3;
      ranges.push_back(bs::Table::Create(groups << k, layout));
      FillRandom(ranges.back(), rng, 1 + unsigned(rng() % 8), universe,
                 [&](size_t rb) {
                   const uint64_t low = rng() & ((uint64_t{1} << ib) - 1);
                   return rng() % 7 == 0 ? rng()
                                         : ((uint64_t(rb & ((size_t{1} << k) - 1)) << ib) | low);
                 });
      bs::ResidualOfferSet set;
      set.plan.range_bits = k;
      set.plan.index_bits = ib;
      set.plan.groups = groups;
      set.plan.range_buckets = groups << k;
      set.plan.scatter_per_bucket = 64;
      set.rule = rules[o];
      set.lines = layout.PayloadLines();
      sets.push_back(set);
    }
    const size_t depth = 1 + rng() % 3;
    auto stash_storage = bs::Table::Create(depth, layout);
    FillRandom(stash_storage, rng, unsigned(rng() % 9), universe, any);
    const auto skip = bs::FixedMergeTombstones(rng() % 3);

    auto run = [&](bool fused, bs::Table& c_out, std::vector<bs::Table>& r_out,
                   bs::Table& s_out, bs::ResidualStash& stash) {
      c_out = Clone(older);
      s_out = Clone(stash_storage);
      r_out.clear();
      std::vector<bs::ResidualOfferSet> views = sets;
      for (size_t o = 0; o < sets.size(); ++o) {
        r_out.push_back(Clone(ranges[o]));
        views[o].range = bs::View(r_out.back());
      }
      stash.data = s_out.data.get();
      stash.num_buckets = depth;
      stash.entry_bytes = layout.EntryBytes();
      std::copy_n(s_out.masks.get(), depth, stash.masks);
      auto b_view = bs::View(fresher);
      return fused ? bs::MergeFixedLevelSourcesOffersRange<CheckOverflow>(
                         bs::View(c_out), b_view, r, stash, views.data(),
                         views.size(), 0, block, skip)
                   : SequentialFixedMerge<CheckOverflow>(
                         bs::View(c_out), b_view, r, stash, views, skip);
    };
    auto fresher_before = Clone(fresher);
    bs::Table c_fused = Empty(1, layout), c_seq = Empty(1, layout);
    bs::Table s_fused = Empty(1, layout), s_seq = Empty(1, layout);
    std::vector<bs::Table> r_fused, r_seq;
    bs::ResidualStash st_fused, st_seq;
    const bool ok_fused = run(true, c_fused, r_fused, s_fused, st_fused);
    const bool ok_seq = run(false, c_seq, r_seq, s_seq, st_seq);
    Check(ok_fused == ok_seq, "fused fixed merge overflowed differently");
    Check(std::memcmp(fresher.data.get(), fresher_before.data.get(),
                      block * layout.BucketBytes()) == 0 &&
              std::equal(fresher.masks.get(), fresher.masks.get() + block,
                         fresher_before.masks.get()),
          "fused fixed merge wrote its source");
    if (!ok_fused) continue;  // an overflow is a failed rebuild
    ++compared;
    const size_t c_bytes = block * r * layout.BucketBytes();
    Check(std::memcmp(c_fused.data.get(), c_seq.data.get(), c_bytes) == 0 &&
              std::equal(c_fused.masks.get(), c_fused.masks.get() + block * r,
                         c_seq.masks.get()),
          "fused fixed merge: destination bytes differ from single offers");
    for (size_t o = 0; o < sets.size(); ++o)
      Check(std::equal(r_fused[o].masks.get(),
                       r_fused[o].masks.get() + r_fused[o].num_buckets,
                       r_seq[o].masks.get()),
            "fused fixed merge: range masks differ from single offers");
    Check(std::memcmp(s_fused.data.get(), s_seq.data.get(),
                      depth * layout.BucketBytes()) == 0 &&
              std::equal(st_fused.masks, st_fused.masks + depth, st_seq.masks),
          "fused fixed merge: stash differs from per-direction appends");
  }
  return compared;
}

// The coarse-range cap: a DFS plan keeps the production width until a range
// would span more than 2^kDfsMaxRangeIndexBits homes, and past that splits
// the main into more ranges, never fewer homes than the cap per range.  The
// pool that meets it is the top finish's retained carry, two buckets over a
// 2^23-home top or larger.
void RangeWidthCap() {
  const unsigned cap = bs::kDfsMaxRangeIndexBits;
  for (size_t pool : {size_t{1}, size_t{2}, size_t{3}, size_t{44}}) {
    for (unsigned main = 4; main <= 34; ++main) {
      for (size_t pages : {size_t{1}, size_t{2}}) {
        if (!bs::DfsResidualRangeApplies(pool, main)) continue;
        const bs::ResidualRangePlan production =
            bs::PlanResidualRange(pool, main);
        const bs::ResidualRangePlan dfs =
            bs::DfsResidualRangePlan(pool, main, pages);
        Check(dfs.range_bits + dfs.index_bits == main,
              "range cap: the ranges no longer tile the main");
        Check(dfs.index_bits ==
                  std::min<unsigned>(production.index_bits, cap),
              "range cap: a range is not the production width, capped");
        Check(dfs.groups == pages && dfs.range_buckets ==
                                         pages << dfs.range_bits,
              "range cap: the leaf table is not pages per range");
        Check(bs::IsDfsResidualRangePlan(dfs, pool, main, pages),
              "range cap: the capped plan is not recognised as the DFS plan");
      }
    }
  }
  // The worked top finish keeps its width; a 2^24-home top gains ranges.
  Check(bs::DfsResidualRangePlan(2, 22, 1).index_bits == 18 &&
            bs::DfsResidualRangePlan(2, 22, 1).range_bits == 4,
        "range cap: the 2^22-home top finish changed width");
  Check(bs::DfsResidualRangePlan(2, 24, 1).index_bits == cap &&
            bs::DfsResidualRangePlan(2, 24, 1).range_bits == 24 - cap,
        "range cap: a 2^24-home top finish is not capped");
}

int main() {
  RangeWidthCap();
  SeparatedBoundaries();
  ProducerOrder();
  OracleCases();
  CrossPageWitness();
  SinglePageParity();
  const size_t fused = FusedFixedMergeCases<false>(5) + FusedFixedMergeCases<true>(6);
  std::printf("DFS second chance: range width cap, native producer order, 120 scalar oracle cases, cross-page order, single-page parity and %zu fused fixed merges passed\n", fused);
}
