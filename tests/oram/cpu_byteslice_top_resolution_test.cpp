// The top finish resolves before it compresses (ResolveTopDestination, riding
// MergeFixedLevelSourcesOffersRange under FixedMergeTombstones::kAll), checked
// against a scalar RESOLVE-THEN-COMPRESS oracle on hand-built inputs at the
// native bucket capacity of 64.
//
// The oracle is the Lemma "resolved-compression" of
// analysis/bound_certification/REPORT.tex: over the complete
// population -- A's main (C after the preparation), A's retained carry, B's
// main and B's tier -- every key resolves to its freshest version (B over A),
// a winning tombstone disappears with everything it shadows, and the X_v live
// winners of final home v leave min(X_v, 64) in C and (X_v - 64)+ for the
// tier.  The run is the real sweep plus the real epilogue of the top's merge
// pass: the range leftovers drain into the tier, the leftover dedup, then the
// merge stash drains.  The APPEND PREFIXES are instrumented where they happen
// -- the merge stash after the sweep, the tier after each drain phase -- and
// each must stay within E = sum_v (X_v - 64)+, not only the final tier.
//
// Every fixture satisfies the input premises the engine provides: A and B are
// each distinct by key (main and tier together); every record sits at the
// home its key selects (C at its final home, B at carry bucket i = v mod U
// with way v / U, a range candidate tagged with v); B has tier records only at
// carry buckets its main fills (the fullness identity), and A retains records
// only at final homes C fills; and a key in both the retained carry and B's
// tier reaches the range table once, as the pool dedup before the scatter
// leaves it.  A's tombstones, which the engine never produces (the previous
// top drop removed them), appear in one variant only, to check the rule does
// not depend on that premise.
//
// Covered: the local counterexample of analysis/bound_certification/REPORT.tex
// at native capacity (compressing before resolving sheds a live key the
// reference keeps); a deleting B-tier version on a later
// range page than the candidates it makes room for; ways 1 to 8, binary and
// not, with one to three pages; B-main tombstones, B-tier tombstones over
// C's and over retained copies, live B-tier replacements, absent-key
// tombstones; mixed full and nonfull homes; the merge stash and the tier at
// exactly their capacity and one over; empty sources; slice-by-slice
// (pause/resume) and two-lane (private range masks, AND fold) runs against
// the whole sweep; and B's bytes and masks unchanged.

#include <immintrin.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <map>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_second_chance.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"

namespace {

namespace bs = microram::byteslice;
namespace ts = bs::test_support;

void Check(bool good, const std::string& message) {
  if (!good) throw std::runtime_error(message);
}

const bs::Layout kLayout{8, 8, 2};  // tag byte 1 is the digit line
constexpr uint8_t kOlder = 1;       // PlantEntry's source byte: A
constexpr uint8_t kFresher = 2;     // B

struct Rec {
  bs::KeyWords key;
  size_t home = 0;   // final bucket of C
  bool tomb = false;
};

struct Fixture {
  size_t u = 1;       // carry buckets
  size_t r = 1;       // ways (the top's digit)
  size_t groups = 1;  // range pages
  std::vector<std::vector<Rec>> c;       // A's main, per final home
  std::vector<Rec> retained;             // A's retained carry
  std::vector<std::vector<Rec>> b_main;  // B's main, per carry bucket
  std::vector<Rec> b_tier;
  size_t stash_buckets = 8;  // merge stash
  size_t tier_buckets = 8;   // the published tier
  size_t Homes() const { return u * r; }
};

unsigned IndexBits(const Fixture& f) {
  unsigned bits = 0;
  while ((size_t{1} << bits) < f.Homes()) ++bits;
  return bits;
}

// The oracle: live winners per home, and the excess.
struct Reference {
  std::map<bs::KeyWords, ts::LiveEntry> live;
  std::vector<size_t> x;
  size_t excess = 0;
};

Reference Resolve(const Fixture& f) {
  std::map<bs::KeyWords, std::pair<const Rec*, uint8_t>> newest;
  const auto offer = [&](const Rec& rec, uint8_t source) {
    auto it = newest.find(rec.key);
    if (it == newest.end() || it->second.second < source) {
      newest[rec.key] = {&rec, source};
    }
  };
  for (const auto& home : f.c) {
    for (const Rec& rec : home) offer(rec, kOlder);
  }
  for (const Rec& rec : f.retained) offer(rec, kOlder);
  for (const auto& bucket : f.b_main) {
    for (const Rec& rec : bucket) offer(rec, kFresher);
  }
  for (const Rec& rec : f.b_tier) offer(rec, kFresher);
  Reference ref;
  ref.x.assign(f.Homes(), 0);
  for (const auto& kv : newest) {
    if (kv.second.first->tomb) continue;
    ref.live[kv.first] = {kv.second.second, 0};
    ++ref.x[kv.second.first->home];
  }
  for (size_t x : ref.x) ref.excess += x > 64 ? x - 64 : 0;
  return ref;
}

struct Tables {
  bs::Table c, b, range;
  ts::OwnedLevelStashes stash, tier;
  bs::ResidualOfferSet offer;
  Tables(const Fixture& f)
      : c(ts::ZeroedTable(f.Homes(), kLayout)),
        b(ts::ZeroedTable(f.u, kLayout)),
        range(ts::ZeroedTable(f.groups, kLayout)),
        stash(1, f.stash_buckets, kLayout),
        tier(1, f.tier_buckets, kLayout) {}
};

uint8_t Meta(const Rec& rec) { return rec.tomb ? bs::kMetaErased : 0; }

void SetTagByte(uint8_t* bucket, size_t slot, size_t tag_byte, uint8_t v) {
  bucket[kLayout.TagLine(unsigned(8 * tag_byte)) * 64 + slot] = v;
}

// Builds the sweep's inputs.  Slots are scattered, and free slots hold junk,
// so nothing depends on a record's lane.
void Build(const Fixture& f, Tables* t, std::mt19937_64& rng) {
  const auto junk = [&](bs::Table& table) {
    for (size_t i = 0; i < table.num_buckets * kLayout.BucketBytes(); ++i) {
      table.data.get()[i] = static_cast<uint8_t>(rng());
    }
  };
  junk(t->c);
  junk(t->b);
  junk(t->range);
  const auto plant = [&](bs::Table& table, size_t bucket,
                         const std::vector<const Rec*>& recs, uint8_t source,
                         bool fresh_class, bool candidate) {
    Check(recs.size() <= 64, "a fixture bucket holds more than 64");
    std::vector<unsigned> slots(64);
    for (unsigned s = 0; s < 64; ++s) slots[s] = s;
    std::shuffle(slots.begin(), slots.end(), rng);
    table.masks[bucket] = 0;
    for (size_t n = 0; n < recs.size(); ++n) {
      const Rec& rec = *recs[n];
      const unsigned slot = slots[n];
      uint8_t meta = Meta(rec);
      if (fresh_class) meta |= bs::kMetaResidualClass;
      ts::PlantEntry(kLayout, table.Bucket(bucket), slot, rec.key, source,
                     meta);
      if (candidate) {
        SetTagByte(table.Bucket(bucket), slot, 0,
                   static_cast<uint8_t>(rec.home));
      } else if (&table == &t->b) {
        SetTagByte(table.Bucket(bucket), slot, 1,
                   static_cast<uint8_t>(rec.home / f.u));  // the way
      }
      table.masks[bucket] |= uint64_t{1} << slot;
    }
  };
  for (size_t v = 0; v < f.Homes(); ++v) {
    std::vector<const Rec*> recs;
    for (const Rec& rec : f.c[v]) recs.push_back(&rec);
    plant(t->c, v, recs, kOlder, false, false);
  }
  for (size_t i = 0; i < f.u; ++i) {
    std::vector<const Rec*> recs;
    for (const Rec& rec : f.b_main[i]) recs.push_back(&rec);
    plant(t->b, i, recs, kFresher, false, false);
  }
  // The range pages: retained and B-tier candidates dealt at random.
  std::vector<std::pair<const Rec*, bool>> cands;
  for (const Rec& rec : f.retained) cands.push_back({&rec, false});
  for (const Rec& rec : f.b_tier) cands.push_back({&rec, true});
  std::shuffle(cands.begin(), cands.end(), rng);
  std::vector<std::vector<std::pair<const Rec*, bool>>> pages(f.groups);
  for (const auto& cand : cands) {
    size_t g = rng() % f.groups;
    while (pages[g].size() == 64) g = (g + 1) % f.groups;
    pages[g].push_back(cand);
  }
  for (size_t g = 0; g < f.groups; ++g) {
    t->range.masks[g] = 0;
    std::vector<unsigned> slots(64);
    for (unsigned s = 0; s < 64; ++s) slots[s] = s;
    std::shuffle(slots.begin(), slots.end(), rng);
    for (size_t n = 0; n < pages[g].size(); ++n) {
      const Rec& rec = *pages[g][n].first;
      const bool fresh = pages[g][n].second;
      const unsigned slot = slots[n];
      ts::PlantEntry(kLayout, t->range.Bucket(g), slot, rec.key,
                     fresh ? kFresher : kOlder,
                     static_cast<uint8_t>(
                         Meta(rec) | (fresh ? bs::kMetaResidualClass : 0)));
      SetTagByte(t->range.Bucket(g), slot, 0, static_cast<uint8_t>(rec.home));
      t->range.masks[g] |= uint64_t{1} << slot;
    }
  }
  t->offer.range = bs::View(t->range);
  t->offer.plan.range_bits = 0;
  t->offer.plan.index_bits = IndexBits(f);
  t->offer.plan.groups = f.groups;
  t->offer.plan.range_buckets = f.groups;
  t->offer.rule = bs::ResidualDedupRule::kClassMark;
  t->offer.lines = kLayout.PayloadLines();
}

struct Outcome {
  bool sweep_ok = true, drain_ok = true;
  size_t sheds = 0;         // merge stash after the sweep
  size_t after_range = 0;   // tier after the range leftovers drained
  size_t after_dedup = 0;   // tier after the leftover dedup
  size_t tier = 0;          // tier after the merge stash drained
  size_t tombstones = 0;    // left in C or the tier before any drop
  std::map<bs::KeyWords, ts::LiveEntry> live;
  bool unique = true;
  size_t damaged = 0;
  std::vector<size_t> main_count;
  size_t misplaced = 0;     // C records off their home
  uint64_t b_digest_before = 0, b_digest_after = 0;
};

enum class Schedule { kWhole, kSlices, kTwoLanes };

uint64_t DigestB(const Tables& t) {
  return ts::DigestBytes(t.b.data.get(), t.b.num_buckets * kLayout.BucketBytes()) ^
         ts::DigestBytes(reinterpret_cast<const uint8_t*>(t.b.masks.get()),
                         t.b.num_buckets * sizeof(uint64_t));
}

bool Sweep(const Fixture& f, Tables* t, bs::ResidualStash& stash,
           size_t begin, size_t end) {
  return bs::MergeFixedLevelSourcesOffersRange</*CheckOverflow=*/true>(
      bs::View(t->c), bs::View(t->b), static_cast<unsigned>(f.r), stash,
      &t->offer, 1, begin, end, bs::FixedMergeTombstones::kAll);
}

Outcome Run(const Fixture& f, Schedule schedule, uint64_t seed) {
  std::mt19937_64 rng(seed);
  Tables t(f);
  Build(f, &t, rng);
  Outcome out;
  out.b_digest_before = DigestB(t);
  bs::ResidualStash& stash = t.stash.slots[0];
  switch (schedule) {
    case Schedule::kWhole:
      out.sweep_ok = Sweep(f, &t, stash, 0, f.u);
      break;
    case Schedule::kSlices:  // a pause after every source bucket
      for (size_t i = 0; i < f.u && out.sweep_ok; ++i) {
        out.sweep_ok = Sweep(f, &t, stash, i, i + 1);
      }
      break;
    case Schedule::kTwoLanes: {
      // Each lane on its own copy of the range masks and its own stash,
      // then the fold: masks ANDed, stashes appended in lane order.
      const size_t mid = f.u / 2;
      std::vector<uint64_t> shared(t.range.masks.get(),
                                   t.range.masks.get() + f.groups);
      std::vector<uint64_t> folded = shared;
      ts::OwnedLevelStashes lane_stash(2, f.stash_buckets, kLayout);
      for (size_t lane = 0; lane < 2 && out.sweep_ok; ++lane) {
        std::copy(shared.begin(), shared.end(), t.range.masks.get());
        out.sweep_ok = Sweep(f, &t, lane_stash.slots[lane],
                             lane == 0 ? 0 : mid, lane == 0 ? mid : f.u);
        for (size_t g = 0; g < f.groups; ++g) folded[g] &= t.range.masks[g];
      }
      std::copy(folded.begin(), folded.end(), t.range.masks.get());
      for (size_t lane = 0; lane < 2 && out.sweep_ok; ++lane) {
        const bs::ResidualStash& from = lane_stash.slots[lane];
        for (size_t b = 0; b < from.num_buckets && out.sweep_ok; ++b) {
          out.sweep_ok = bs::MergeBucketIntoResidualStash<true>(
              stash, from.Bucket(b), from.masks[b], kLayout.EntryBytes());
        }
      }
      break;
    }
  }
  out.b_digest_after = DigestB(t);
  if (!out.sweep_ok) return out;
  out.sheds = stash.Count();
  // The top merge pass's epilogue (PlanResidualFinishPhases): range
  // leftovers, the leftover dedup against the drain-only merge stash, then
  // the merge stash.  The pool dedup's drain-only window has nothing
  // fresher than the merge stash to clear it against.
  bs::ResidualStash& tier = t.tier.slots[0];
  bs::ResidualStash* pool[1] = {&stash};
  out.drain_ok = bs::DrainResidualTableRange(bs::View(t.range), tier,
                                             kLayout.PayloadLines(), 0,
                                             f.groups);
  out.after_range = tier.Count();
  if (out.drain_ok) {
    bs::ResidualLeftoverDedupRange(
        bs::ResidualDedupRule::kClassMark, kLayout, tier, pool, 1, 0,
        bs::ResidualLeftoverDedupUnits(tier, pool, 1));
    out.after_dedup = tier.Count();
    out.drain_ok = bs::DrainResidualPoolRange(pool, 1, tier,
                                              kLayout.PayloadLines(), 0,
                                              stash.num_buckets);
  }
  out.tier = tier.Count();
  if (!out.drain_ok) return out;
  // No tombstone may reach C or the tier: the trailing drop must be empty.
  for (size_t v = 0; v < f.Homes(); ++v) {
    out.tombstones += bs::Popcount64(
        t.c.masks[v] & bs::ErasedSlotMask(t.c.Bucket(v), kLayout.MetaLine()));
  }
  for (size_t b = 0; b < tier.num_buckets; ++b) {
    out.tombstones += bs::Popcount64(
        tier.masks[b] & bs::ErasedSlotMask(tier.Bucket(b), kLayout.MetaLine()));
  }
  ts::CollectLive(bs::View(t.c), &out.live, &out.unique, &out.damaged);
  ts::CollectLiveStashes(kLayout, &tier, 1, &out.live, &out.unique,
                         &out.damaged);
  std::map<bs::KeyWords, size_t> home_of;
  for (const auto& home : f.c) for (const Rec& r : home) home_of[r.key] = r.home;
  for (const Rec& r : f.retained) home_of[r.key] = r.home;
  for (const auto& bucket : f.b_main) for (const Rec& r : bucket) home_of[r.key] = r.home;
  for (const Rec& r : f.b_tier) home_of[r.key] = r.home;
  for (size_t v = 0; v < f.Homes(); ++v) {
    out.main_count.push_back(bs::Popcount64(t.c.masks[v]));
    uint64_t mask = t.c.masks[v];
    while (mask != 0) {
      const unsigned slot = static_cast<unsigned>(_tzcnt_u64(mask));
      mask &= mask - 1;
      if (home_of[ts::SlotKeyWordsOf(kLayout, t.c.Bucket(v), slot)] != v) {
        ++out.misplaced;
      }
    }
  }
  return out;
}

size_t g_runs = 0, g_emitted = 0, g_tier_tombstones = 0, g_c_deletions = 0;

// Every schedule against the oracle, and the append prefixes against E.
void Expect(const Fixture& f, uint64_t seed, const std::string& what) {
  const Reference ref = Resolve(f);
  for (Schedule s : {Schedule::kWhole, Schedule::kSlices, Schedule::kTwoLanes}) {
    if (s == Schedule::kTwoLanes && f.u < 2) continue;
    const Outcome o = Run(f, s, seed);
    const std::string where =
        what + (s == Schedule::kWhole ? "" : s == Schedule::kSlices
                                                 ? " (slices)"
                                                 : " (two lanes)");
    Check(o.b_digest_before == o.b_digest_after, where + ": B was written");
    Check(o.sweep_ok && o.drain_ok,
          where + ": a capacity test failed although E = " +
              std::to_string(ref.excess) + " fits");
    Check(o.sheds <= ref.excess && o.after_range <= ref.excess &&
              o.after_dedup <= ref.excess,
          where + ": an append prefix exceeded E = " +
              std::to_string(ref.excess) + " (sheds " +
              std::to_string(o.sheds) + ", range " +
              std::to_string(o.after_range) + ")");
    Check(o.tier == ref.excess,
          where + ": the tier holds " + std::to_string(o.tier) +
              ", the resolved excess is " + std::to_string(ref.excess));
    Check(o.tombstones == 0, where + ": a tombstone reached C or the tier");
    Check(o.unique && o.damaged == 0, where + ": duplicate or damaged record");
    Check(o.live == ref.live,
          where + ": not exactly the newest live version of every key");
    Check(o.misplaced == 0, where + ": a record of C is off its home");
    for (size_t v = 0; v < f.Homes(); ++v) {
      Check(o.main_count[v] == std::min<size_t>(ref.x[v], 64),
            where + ": home " + std::to_string(v) + " holds " +
                std::to_string(o.main_count[v]) + ", not min(X_v, 64)");
    }
    ++g_runs;
    g_emitted += o.tier;
  }
}

uint64_t g_next_key = 1;
Rec NewRec(size_t home, bool tomb = false) {
  return Rec{ts::FixtureKey(g_next_key++, kLayout.key_bytes), home, tomb};
}

Fixture Empty(size_t u, size_t r, size_t groups) {
  Fixture f;
  f.u = u;
  f.r = r;
  f.groups = groups;
  f.c.resize(u * r);
  f.b_main.resize(u);
  return f;
}

// REPORT.tex's capacity-one illustration at native capacity.  Home 0 of C
// holds 64 live A keys; B's carry bucket 0 is full (so it may have a tier):
// one live new key b of way 0 and 63 of way 1; B's tier holds a tombstone for
// one of home 0's A keys.  Resolved, home 0 keeps 63 A keys plus b: E = 0.
// Merging B's main first sheds b, and the tier's tombstone frees its slot
// only afterwards.
void LocalCounterexample() {
  Fixture f = Empty(2, 2, 1);
  for (int i = 0; i < 64; ++i) f.c[0].push_back(NewRec(0));
  f.b_main[0].push_back(NewRec(0));
  for (int i = 0; i < 63; ++i) f.b_main[0].push_back(NewRec(2));
  f.b_tier.push_back(Rec{f.c[0][17].key, 0, true});
  Check(Resolve(f).excess == 0, "the counterexample's reference sheds");
  Expect(f, 1, "local counterexample");
  ++g_tier_tombstones;
  ++g_c_deletions;
}

// The deleting version on a LATER page than the candidates it makes room
// for.  Home 0: 64 live A keys in C, 8 retained A keys on page 0; B's tier
// on page 1 deletes 16 of C's keys; B's full carry bucket 0 adds 8 live keys
// at home 0.  X_0 = 48 + 8 + 8 = 64: nothing may shed or be left over.
// Allocating page by page would leave page 0's candidates over.
void LaterPageDeletes() {
  Fixture f = Empty(1, 2, 2);
  for (int i = 0; i < 64; ++i) f.c[0].push_back(NewRec(0));
  for (int i = 0; i < 8; ++i) f.retained.push_back(NewRec(0));
  for (int i = 0; i < 16; ++i) f.b_tier.push_back(Rec{f.c[0][i].key, 0, true});
  for (int i = 0; i < 8; ++i) f.b_main[0].push_back(NewRec(0));
  for (int i = 0; i < 56; ++i) f.b_main[0].push_back(NewRec(1));
  Check(Resolve(f).excess == 0, "the later-page case's reference sheds");
  // Build deals pages at random; seeds that put every retained key on one
  // page and every tombstone on the other are among them.
  for (uint64_t seed = 0; seed < 16; ++seed) {
    Expect(f, 100 + seed, "later page deletes, seed " + std::to_string(seed));
  }
  g_tier_tombstones += 16;
  g_c_deletions += 16;
}

// Merge stash and tier exactly full, and one over.  Home 0 is full of live
// A keys and B's carry bucket 0 sends it n live new keys, all of way 0.
void Boundaries() {
  for (size_t n : {size_t{64}, size_t{65}}) {
    Fixture f = Empty(2, 1, 1);
    f.stash_buckets = 1;
    f.tier_buckets = 1;
    for (int i = 0; i < 64; ++i) f.c[0].push_back(NewRec(0));
    // 64 from carry bucket 0 and n - 64 from bucket 1, whose home is also
    // full: every one of them sheds.
    for (int i = 0; i < 64; ++i) f.c[1].push_back(NewRec(1));
    for (size_t i = 0; i < 64; ++i) f.b_main[0].push_back(NewRec(0));
    for (size_t i = 64; i < n; ++i) f.b_main[1].push_back(NewRec(1));
    Check(Resolve(f).excess == n, "boundary fixture");
    const Outcome o = Run(f, Schedule::kWhole, 7);
    Check(o.sweep_ok == (n == 64),
          n == 64 ? "a merge stash exactly full refused"
                  : "a merge stash one over its capacity took the shed");
    if (n == 64) {
      Expect(f, 7, "merge stash and tier exactly full");
    }
  }
  // The tier alone one over: 64 sheds fit the merge stash, and one retained
  // key at a full home adds a range leftover.
  Fixture f = Empty(2, 1, 1);
  f.stash_buckets = 1;
  f.tier_buckets = 1;
  for (int i = 0; i < 64; ++i) f.c[0].push_back(NewRec(0));
  for (int i = 0; i < 64; ++i) f.c[1].push_back(NewRec(1));
  for (int i = 0; i < 64; ++i) f.b_main[0].push_back(NewRec(0));
  f.retained.push_back(NewRec(1));
  const Outcome o = Run(f, Schedule::kWhole, 9);
  Check(o.sweep_ok && !o.drain_ok,
        "a tier one over its capacity took the drain");
}

void EmptySources() {
  for (int shape = 0; shape < 8; ++shape) {
    Fixture f = Empty(2, 3, 1);
    if (shape & 1) for (int i = 0; i < 40; ++i) f.c[i % 6].push_back(NewRec(i % 6));
    if (shape & 2) for (int i = 0; i < 30; ++i) f.b_main[i % 2].push_back(NewRec(i % 6));
    if (shape & 4) {
      // A tier needs a full carry bucket.
      f.b_main[0].clear();
      for (int i = 0; i < 64; ++i) f.b_main[0].push_back(NewRec((i % 3) * 2));
      f.b_tier.push_back(NewRec(0));
      f.b_tier.push_back(NewRec(2, /*tomb=*/true));
    }
    Expect(f, 11 + shape, "empty sources, shape " + std::to_string(shape));
  }
}

// Premise-respecting random fixtures.
Fixture Random(size_t u, size_t r, size_t groups, bool older_tombstones,
               std::mt19937_64& rng) {
  Fixture f = Empty(u, r, groups);
  const size_t homes = u * r;
  std::vector<Rec> a_keys;  // every A record, for B to shadow
  const size_t fills[] = {0, 12, 40, 63, 64, 64, 64};
  for (size_t v = 0; v < homes; ++v) {
    const size_t fill = fills[rng() % 7];
    for (size_t i = 0; i < fill; ++i) {
      f.c[v].push_back(NewRec(v, older_tombstones && rng() % 9 == 0));
      a_keys.push_back(f.c[v].back());
    }
    if (fill == 64) {  // A retains only where C is full
      for (size_t i = rng() % 7; i-- > 0;) {
        f.retained.push_back(NewRec(v, older_tombstones && rng() % 9 == 0));
        a_keys.push_back(f.retained.back());
      }
    }
  }
  std::set<bs::KeyWords> b_used;
  const size_t b_fills[] = {0, 30, 63, 64, 64};
  for (size_t i = 0; i < u; ++i) {
    const size_t fill = b_fills[rng() % 5];
    while (f.b_main[i].size() < fill) {
      Rec rec;
      if (rng() % 3 == 0 && !a_keys.empty()) {
        // Shadow an A key whose home this carry bucket serves.
        const Rec& a = a_keys[rng() % a_keys.size()];
        if (a.home % u != i || b_used.count(a.key)) continue;
        rec = Rec{a.key, a.home, rng() % 3 == 0};
      } else {
        rec = NewRec(i + (rng() % r) * u, rng() % 5 == 0);  // absent-key
      }
      b_used.insert(rec.key);
      f.b_main[i].push_back(rec);
    }
    if (fill != 64) continue;  // the fullness identity
    for (size_t n = rng() % 12; n-- > 0;) {
      Rec rec;
      if (rng() % 2 == 0 && !a_keys.empty()) {
        const Rec& a = a_keys[rng() % a_keys.size()];
        if (a.home % u != i || b_used.count(a.key)) continue;
        rec = Rec{a.key, a.home, rng() % 2 == 0};  // delete or replace
        g_tier_tombstones += rec.tomb;
      } else {
        rec = NewRec(i + (rng() % r) * u, rng() % 4 == 0);
      }
      b_used.insert(rec.key);
      f.b_tier.push_back(rec);
    }
  }
  // The pool dedup: a retained key B's tier also holds reaches the range
  // table once, as B's version.
  std::set<bs::KeyWords> tier_keys;
  for (const Rec& rec : f.b_tier) tier_keys.insert(rec.key);
  std::vector<Rec> kept;
  for (const Rec& rec : f.retained) {
    if (!tier_keys.count(rec.key)) kept.push_back(rec);
  }
  f.retained = kept;
  while (f.retained.size() + f.b_tier.size() > 64 * f.groups) ++f.groups;
  return f;
}

void RandomFixtures() {
  std::mt19937_64 rng(0x70FD);
  for (size_t r = 1; r <= bs::kMaxFixedMergeWays; ++r) {
    for (size_t u : {size_t{2}, size_t{4}}) {
      for (size_t groups : {size_t{1}, size_t{2}, size_t{3}}) {
        for (bool older_tombstones : {false, true}) {
          for (int trial = 0; trial < 6; ++trial) {
            const Fixture f = Random(u, r, groups, older_tombstones, rng);
            Expect(f, rng(),
                   "random r=" + std::to_string(r) + " u=" + std::to_string(u) +
                       " groups=" + std::to_string(f.groups) +
                       (older_tombstones ? " with A tombstones" : "") +
                       " trial " + std::to_string(trial));
          }
        }
      }
    }
  }
}

}  // namespace

int main() {
  try {
    LocalCounterexample();
    LaterPageDeletes();
    Boundaries();
    EmptySources();
    RandomFixtures();
  } catch (const std::exception& e) {
    std::printf("top resolution test FAILED: %s\n", e.what());
    return 1;
  }
  std::printf("  %zu runs matched resolve-then-compress (%zu records emitted, "
              "%zu B-tier tombstones over A keys)\n",
              g_runs, g_emitted, g_tier_tombstones);
  std::printf("  append prefixes stayed within the resolved excess; merge "
              "stash and tier exact at capacity, refused one over\n");
  std::printf("top resolution: OK\n");
  return 0;
}
