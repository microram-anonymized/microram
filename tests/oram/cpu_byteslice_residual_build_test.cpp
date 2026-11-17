// The fused scatter-and-retag must retain every live tag byte, including
// future radix bits; and a residual pass the kernels would mishandle is refused
// where it is built or planned.
#include "src/oram/scheduler/cpu_byteslice_residual_pass.hpp"
#include "src/oram/scheduler/cpu_byteslice_subtask_plan.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <stdexcept>
#include <vector>

namespace bs = microram::byteslice;

void Require(bool condition, const char* message) {
  if (!condition) {
    std::fprintf(stderr, "%s\n", message);
    std::abort();
  }
}

void Equal(const bs::Table& a, const bs::Table& b, bool all_bytes) {
  const size_t bytes = a.layout.BucketBytes();
  for (size_t bucket = 0; bucket < a.num_buckets; ++bucket) {
    Require(a.masks[bucket] == b.masks[bucket], "occupancy mismatch");
    if (all_bytes) {
      Require(std::memcmp(a.Bucket(bucket), b.Bucket(bucket), bytes) == 0,
              "full bucket mismatch");
    } else {
      for (size_t line = 0; line < a.layout.EntryBytes(); ++line) {
        for (unsigned lane = 0; lane < 64; ++lane) {
          if ((a.masks[bucket] >> lane) & 1) {
            Require(a.Bucket(bucket)[64 * line + lane] ==
                        b.Bucket(bucket)[64 * line + lane],
                    "live entry mismatch");
          }
        }
      }
    }
  }
}

void TestEmptyResidualPool() {
  const bs::Layout layout{8, 17, 8};
  bs::ResidualStash empty;
  empty.entry_bytes = layout.EntryBytes();
  empty.masks[0] = ~uint64_t{0};  // Outside its zero capacity; must be ignored.
  bs::ResidualStash* pool[] = {&empty};
  const uint8_t ranks[] = {0};
  for (unsigned levels : {0u, 1u, 3u, 4u, 8u, 16u, 32u, 63u}) {
    const auto plan = bs::PlanResidualRange(0, levels);
    Require(plan.range_bits == 0 && plan.index_bits == levels &&
                plan.groups == 1 && plan.range_buckets == 1 &&
                bs::ResidualScatterFanout(plan) == 1,
            "empty pool must plan one padding group without routing");
    // The shared finishing helper must give the same canonical empty plan,
    // including when its caller requested routing bits.
    const auto finished = bs::FinishResidualRangePlan(0, levels, levels);
    Require(finished.range_bits == plan.range_bits &&
                finished.index_bits == plan.index_bits &&
                finished.groups == plan.groups &&
                finished.range_buckets == plan.range_buckets &&
                finished.scatter_per_bucket == plan.scatter_per_bucket,
            "empty finishing plan differs from the canonical plan");
    for (size_t slots : {size_t{0}, size_t{1}}) {
      // Both an empty source list and a list containing a zero-capacity stash
      // must clear dirty scratch. No source data exists to read in either case.
      for (unsigned path = 0; path < 3; ++path) {
        auto range = bs::Table::Create(plan.range_buckets, layout);
        std::memset(range.data.get(), 0xCD, layout.BucketBytes());
        range.masks[0] = ~uint64_t{0};
        const size_t groups = bs::ResidualScatterGroups(bs::View(range), plan);
        Require(groups == 1, "empty pool scatter skipped its padding bucket");
        if (path == 0) {
          bs::ScatterResidualPoolRange(pool, slots, bs::View(range), plan, 0,
                                       groups);
          bs::ComputeRoutingTags(bs::View(range), 17, 29);
        } else if (path == 1) {
          bs::ScatterAndRetagResidualPoolRange(
              pool, slots, bs::View(range), plan, 0, groups, 17, 29, {},
              bs::DefaultAesTagKeys());
        } else {
          bs::RebuildStepContext ctx;
          ctx.out = bs::View(range);
          ctx.nonce_lo = 17;
          ctx.nonce_hi = 29;
          auto& rp = ctx.residual[1];
          rp.active = true;
          rp.sweep_active = true;
          rp.range = bs::View(range);
          rp.plan = plan;
          rp.pool = pool;
          rp.rank = ranks;
          rp.pool_slots = slots;
          bs::SubtaskBudget budget;
          std::vector<bs::Subtask> tasks;
          bs::PlanResidualBuildPhases(ctx, budget, 1, &tasks);
          Require(!tasks.empty(), "empty scheduled build skipped scratch clear");
          for (const auto& task : tasks) {
            Require(bs::RunSubtask<true>(ctx, task),
                    "empty scheduled build failed");
          }
        }
        Require(range.masks[0] == 0, "empty pool resurrected dirty scratch");
      }
    }
  }
  Require(empty.masks[0] == ~uint64_t{0}, "zero-capacity source was mutated");
}

// ---------------------------------------------------------------------------
// What the pass builder and the fused planners refuse
// ---------------------------------------------------------------------------
//
// Pass shapes the kernels would mishandle, none of which any engine builds:
// refusing them where they are built or planned keeps a future caller from
// reaching a kernel outside its contract.  Each refusal sits next to an
// accepted control that differs from it in one field, so a fixture mistake
// cannot pass for a refusal.  Failures are counted rather than aborting on
// the first, so a run shows every shape that got through.

int refusal_failures = 0;

template <class Fn>
void ExpectRefused(const char* what, Fn&& fn) {
  try {
    fn();
  } catch (const std::logic_error&) {
    return;
  }
  std::fprintf(stderr, "not refused: %s\n", what);
  ++refusal_failures;
}

template <class Fn>
void ExpectAccepted(const char* what, Fn&& fn) {
  try {
    fn();
  } catch (const std::logic_error& e) {
    std::fprintf(stderr, "refused (%s): %s\n", e.what(), what);
    ++refusal_failures;
  }
}

// One context, one-bucket stashes, and the pool storage each pass binds to.
// Planning reads public sizes only, so nothing here holds entries.
struct PassFixture {
  bs::Layout layout{8, 17, 8};
  bs::test_support::OwnedLevelStashes stashes{8, 1, layout};
  bs::ResidualStash* s = stashes.slots.data();
  bs::ResidualStash* drain = &stashes.slots[7];
  bs::RebuildStepContext ctx;
  std::vector<bs::ResidualStash*> pool[bs::kResidualPasses];
  std::vector<uint8_t> rank[bs::kResidualPasses];
  bs::Table range[bs::kResidualPasses];
  bs::SubtaskBudget budget;

  bs::ResidualPassSpec Spec(bs::Table& main) {
    bs::ResidualPassSpec spec;
    spec.main = bs::View(main);
    spec.main_levels = bs::Log2Exact(main.num_buckets);
    spec.scratch = 0;
    spec.lines = layout.PayloadLines();
    spec.drain = drain;
    return spec;
  }
  // BuildResidualPassFields, then the range table it asked for.
  void Build(unsigned pass, const bs::ResidualPassSpec& spec) {
    const size_t buckets = bs::BuildResidualPassFields(
        &ctx, pass, &pool[pass], &rank[pass], spec);
    if (buckets != 0) {
      range[pass] = bs::Table::Create(buckets, layout);
      bs::AttachResidualRange(&ctx.residual[pass], bs::View(range[pass]));
    }
  }
};

void TestSameStashAtTwoRanks() {
  // THE HARM, shown on the kernel directly: listed at two ranks, the pool
  // dedup compares the stash with itself and clears every live lane of it.
  {
    const bs::Layout layout{8, 17, 8};
    bs::test_support::OwnedLevelStashes one(1, 1, layout);
    bs::ResidualStash& stash = one.slots[0];
    for (unsigned lane = 0; lane < 16; ++lane) {
      bs::WriteSlotKey(stash.Bucket(0), lane, layout.key_bytes,
                       bs::KeyWords{1000 + lane, 0});
    }
    stash.masks[0] = 0xffff;
    bs::ResidualStash* pool[] = {&stash, &stash};
    const uint8_t ranks[] = {0, 1};
    const size_t units = bs::ResidualPoolDedupPairs(
        pool, ranks, 2, 0, bs::ResidualDedupWindow::kFull);
    bs::ResidualPoolDedupRange(pool, ranks, 2, 0,
                               bs::ResidualDedupWindow::kFull,
                               layout.key_bytes, 0, units);
    Require(stash.masks[0] == 0,
            "a stash deduplicated against itself kept a lane; the refusal "
            "below no longer guards a real loss");
  }
  PassFixture f;
  bs::Table main = bs::Table::Create(16, f.layout);
  auto build = [&](bs::ResidualStash* second) {
    bs::ResidualPassSpec spec = f.Spec(main);
    spec.rule = bs::ResidualDedupRule::kTableWins;
    spec.AddOwned(&f.s[0], 0);
    spec.AddOwned(second, 1);
    f.Build(1, spec);
  };
  ExpectAccepted("two stashes at two ranks", [&] { build(&f.s[1]); });
  ExpectRefused("one stash at two ranks", [&] { build(&f.s[0]); });
}

void TestDrainAliasingASource() {
  PassFixture f;
  bs::Table main = bs::Table::Create(16, f.layout);
  auto build = [&](bs::ResidualStash* drain) {
    bs::ResidualPassSpec spec = f.Spec(main);
    spec.rule = bs::ResidualDedupRule::kTableWins;
    spec.AddOwned(&f.s[0], 1);
    spec.AddBorrowed(&f.s[1], 0);
    spec.drain = drain;
    f.Build(1, spec);
  };
  ExpectAccepted("a drain distinct from every source", [&] { build(f.drain); });
  ExpectRefused("a drain that is a swept source", [&] { build(&f.s[0]); });
  ExpectRefused("a drain that is a borrowed source", [&] { build(&f.s[1]); });
}

void TestCrossLevelFusionNeedsDrainOnly() {
  PassFixture f;
  bs::Table main = bs::Table::Create(16, f.layout);
  auto build = [&](size_t drain_only) {
    bs::ResidualPassSpec spec = f.Spec(main);
    spec.fuse = bs::ResidualFuseSite::kCrossLevel;
    spec.rule = bs::ResidualDedupRule::kNoDedup;
    spec.AddOwned(&f.s[0], 0);
    spec.AddOwned(&f.s[1], 0);
    spec.drain_only_slots = drain_only;
    f.Build(2, spec);
  };
  ExpectAccepted("a cross-fused pass with a drain-only prefix",
                 [&] { build(1); });
  ExpectRefused("a cross-fused pass whose cross shed would be swept",
                [&] { build(0); });
}

void TestMainLevelsMatchMain() {
  PassFixture f;
  bs::Table main = bs::Table::Create(16, f.layout);
  // A mixed-radix main, 3 * 2^3 buckets: its index width is the CEILING, 5.
  bs::Table mixed = bs::Table::Create(24, f.layout);
  auto build = [&](bs::Table& table, unsigned levels) {
    bs::ResidualPassSpec spec = f.Spec(table);
    spec.main_levels = levels;
    spec.rule = bs::ResidualDedupRule::kNoDedup;
    spec.AddOwned(&f.s[0], 0);
    spec.AddOwned(&f.s[1], 0);
    f.Build(0, spec);
  };
  // What a short value does: the last main bucket pairs past its sub-table.
  const auto short_plan = bs::PlanResidualRange(2, 3);
  Require((main.num_buckets - 1) >> short_plan.index_bits >=
              (size_t{1} << short_plan.range_bits),
          "a short main_levels no longer pairs past the range table");
  ExpectAccepted("main_levels = log2 of a power-of-two main",
                 [&] { build(main, 4); });
  ExpectRefused("main_levels one short of the main", [&] { build(main, 3); });
  ExpectRefused("main_levels one past the main", [&] { build(main, 5); });
  ExpectAccepted("main_levels = ceil log2 of a mixed-radix main",
                 [&] { build(mixed, 5); });
  ExpectRefused("main_levels = floor log2 of a mixed-radix main",
                [&] { build(mixed, 4); });
}

void TestNoDedupSingleRank() {
  PassFixture f;
  bs::Table main = bs::Table::Create(16, f.layout);
  auto build = [&](uint8_t second_rank) {
    bs::ResidualPassSpec spec = f.Spec(main);
    spec.rule = bs::ResidualDedupRule::kNoDedup;
    spec.AddOwned(&f.s[0], 0);
    spec.AddOwned(&f.s[1], second_rank);
    f.Build(0, spec);
  };
  ExpectAccepted("a kNoDedup pass at one rank", [&] { build(0); });
  ExpectRefused("a kNoDedup pass at two ranks", [&] { build(1); });
}

// The fused planners, one per call site, each against the stash its runner
// arm hands the kernel.  The builder cannot see that stash, so a pass that
// leads with any other one builds -- and is refused where it is planned.
void TestFusedPassLeadsWithItsShed() {
  std::vector<bs::Subtask> tasks;
  {  // kFixedMerge: the merge sheds into ctx.merge_stash.
    PassFixture f;
    // 8 buckets: a direct range plan (a non-DFS pass routes nothing).
    bs::Table out = bs::Table::Create(8, f.layout);
    bs::Table fresher = bs::Table::Create(8, f.layout);
    f.ctx.out = bs::View(out);
    f.ctx.fresher = bs::View(fresher);
    f.ctx.merge_stash = &f.s[0];
    auto plan = [&](bs::ResidualStash* lead) {
      bs::ResidualPassSpec spec = f.Spec(out);
      spec.fuse = bs::ResidualFuseSite::kFixedMerge;
      spec.rule = bs::ResidualDedupRule::kClassMark;
      spec.AddOwned(lead, 0);
      spec.drain_only_slots = 1;
      spec.AddOwned(&f.s[2], 2);
      spec.AddOwnedTierClass(&f.s[3], 0);
      f.Build(2, spec);
      bs::PlanFixedMerge(f.ctx, f.budget, &tasks);
    };
    ExpectAccepted("a merge-fused pass leading with the merge's shed",
                   [&] { plan(&f.s[0]); });
    ExpectRefused("a merge-fused pass leading with another stash",
                  [&] { plan(&f.s[1]); });
  }
  {  // kRadixPass: the pass sheds into radix_stash.
    PassFixture f;
    bs::Table out = bs::Table::Create(6, f.layout);  // r = 3 blocks of 2
    f.ctx.out = bs::View(out);
    f.ctx.older = bs::View(out);
    f.ctx.map.kind = bs::TagMapKind::kRadixDigit;
    f.ctx.map.low_bits = 1;
    f.ctx.map.modulus = 3;
    f.ctx.radix_stash = &f.s[0];
    auto build = [&](unsigned pass, bs::ResidualStash* lead,
                     bs::ResidualStash* swept) {
      bs::ResidualPassSpec spec = f.Spec(out);
      spec.fuse = bs::ResidualFuseSite::kRadixPass;
      spec.rule = bs::ResidualDedupRule::kNoDedup;
      spec.AddOwned(lead, 0);
      spec.drain_only_slots = 1;
      spec.AddOwned(swept, 0);
      f.Build(pass, spec);
    };
    auto finish = [&] { bs::PlanMergeFinish(f.ctx, 1, 3, 0, f.budget, &tasks); };
    ExpectAccepted("a radix-fused finish leading with the radix shed", [&] {
      build(2, &f.s[0], &f.s[2]);
      finish();
    });
    ExpectRefused("a radix-fused finish leading with another stash", [&] {
      build(2, &f.s[1], &f.s[2]);
      finish();
    });
    // Two passes fused at one site, BOTH leading with its shed: each builds,
    // and together they would drain it twice.
    ExpectRefused("two radix-fused passes draining one shed", [&] {
      build(1, &f.s[0], &f.s[3]);
      build(2, &f.s[0], &f.s[2]);
      finish();
    });
  }
  {  // kCrossLevel: the LAST cross level, bit block_bits - 1 = 2, sheds into
     // level_stashes[2].  Leading with bit 1's is the off-by-one.
    PassFixture f;
    bs::Table out = bs::Table::Create(8, f.layout);  // carry 2^2, digit 2
    f.ctx.out = bs::View(out);
    f.ctx.level_stashes = f.s;
    auto plan = [&](bs::ResidualStash* lead, bs::ResidualStash* swept) {
      bs::ResidualPassSpec spec = f.Spec(out);
      spec.fuse = bs::ResidualFuseSite::kCrossLevel;
      spec.rule = bs::ResidualDedupRule::kClassMark;
      spec.AddOwned(lead, 2);
      spec.drain_only_slots = 1;
      spec.AddOwned(swept, 2);
      spec.AddOwnedTierClass(&f.s[4], 0);
      f.Build(2, spec);
      bs::PlanMergeFinish(f.ctx, 2, 1, 1, f.budget, &tasks);
    };
    ExpectAccepted("a cross-fused pass leading with the last cross shed",
                   [&] { plan(&f.s[2], &f.s[1]); });
    ExpectRefused("a cross-fused pass leading with the previous level's shed",
                  [&] { plan(&f.s[1], &f.s[2]); });
  }
  {  // kOwnLastLevel: A's last butterfly level, bit 2 of 8 buckets, sheds
     // into level_stashes[2].
    PassFixture f;
    bs::Table out = bs::Table::Create(8, f.layout);
    f.ctx.out = bs::View(out);
    f.ctx.older = bs::View(out);
    f.ctx.level_stashes = f.s;
    auto plan = [&](bs::ResidualStash* lead, bs::ResidualStash* swept) {
      bs::ResidualPassSpec spec = f.Spec(out);
      spec.fuse = bs::ResidualFuseSite::kOwnLastLevel;
      spec.rule = bs::ResidualDedupRule::kNoDedup;
      spec.AddOwned(lead, 0);
      spec.drain_only_slots = 1;
      spec.AddOwned(&f.s[0], 0);
      spec.AddOwned(swept, 0);
      f.Build(0, spec);
      bs::PlanPrepareOlderHalf(f.ctx, f.budget, &tasks);
    };
    ExpectAccepted("an own-last-level pass leading with the last level's shed",
                   [&] { plan(&f.s[2], &f.s[1]); });
    ExpectRefused("an own-last-level pass leading with the level below's shed",
                  [&] { plan(&f.s[1], &f.s[2]); });
  }
}

void TestResidualPassRefusals() {
  TestSameStashAtTwoRanks();
  TestDrainAliasingASource();
  TestCrossLevelFusionNeedsDrainOnly();
  TestMainLevelsMatchMain();
  TestNoDedupSingleRank();
  TestFusedPassLeadsWithItsShed();
  Require(refusal_failures == 0, "a malformed residual pass got through");
  std::printf("residual pass refusals: a stash at two ranks, a drain that is "
              "a source, a cross fusion with no drain-only slot, a wrong "
              "main_levels, a mixed-rank kNoDedup, a fused pass not led by "
              "its site's shed\n");
}

int main() {
  TestEmptyResidualPool();
  TestResidualPassRefusals();
  std::mt19937_64 rng(20260914);
  size_t cases = 0;
  for (size_t key_bytes : {size_t{8}, size_t{16}})
  for (bool mapped : {false, true})
  for (bool drop : {false, true})
  for (bool class_mark : {false, true})
  for (size_t tag_bytes : {size_t{2}, size_t{4}, size_t{8}})
  for (unsigned levels : {3u, 4u, 5u, 6u, 9u})
  for (size_t depth : {size_t{3}, size_t{8}}) {
    const bs::Layout layout{key_bytes, 17, tag_bytes,
                            tag_bytes == 2 ? size_t{2} : size_t{0}};
    bs::test_support::OwnedLevelStashes owned(4, depth, layout);
    for (size_t i = 0; i < owned.bytes; ++i) owned.data.get()[i] = rng();
    std::vector<const bs::ResidualStash*> pool;
    for (size_t slot = 0; slot < 3; ++slot) {
      auto& stash = owned.slots[slot];
      stash.num_buckets = depth - slot;
      for (size_t b = 0; b < stash.num_buckets; ++b) {
        // Sparse but nonempty: exercise occupied lanes throughout the bucket
        // without turning this equivalence probe into an overflow stress test.
        stash.masks[b] = uint64_t{0x1111111111111111} >> (b % 4);
        stash.Bucket(b)[64 * layout.MetaLine()] =
            bs::kMetaErased | bs::kMetaUnshadowed;
        stash.masks[b] |= 1;
        if (b == 2) stash.masks[b] = 0;  // empty capacity still must be hashed
      }
      pool.push_back(&stash);
    }
    const std::vector<uint8_t> saved(owned.data.get(),
                                    owned.data.get() + owned.bytes);
    const auto saved_slots = owned.slots;
    const size_t capacity = bs::ResidualPoolBuckets(pool.data(), pool.size());
    // A direct plan at this depth (fanout one, the separated B tail's shape).
    const auto plan = bs::DirectResidualRangePlan(capacity, levels);
    auto reference = bs::Table::Create(plan.range_buckets, layout);
    auto grouped = bs::Table::Create(plan.range_buckets, layout);
    auto source_hashed = bs::Table::Create(plan.range_buckets, layout);
    const size_t bytes = plan.range_buckets * layout.BucketBytes();
    for (size_t i = 0; i < bytes; ++i) reference.data.get()[i] = rng();
    std::memcpy(grouped.data.get(), reference.data.get(), bytes);
    std::memcpy(source_hashed.data.get(), reference.data.get(), bytes);
    for (size_t b = 0; b < plan.range_buckets; ++b) {
      reference.masks[b] = grouped.masks[b] = source_hashed.masks[b] = ~uint64_t{0};
    }
    bs::RoutingIndexMap map;
    if (mapped) {
      map.kind = bs::TagMapKind::kRadixDigit;
      map.low_bits = levels;
      map.modulus = 3;
      map.digit_shift = 8 * (tag_bytes - 1) + layout.digit_bits;
    }
    const size_t groups = bs::ResidualScatterGroups(bs::View(reference), plan);
    const size_t fanout = bs::ResidualScatterFanout(plan);
    const size_t class_from = owned.slots[0].num_buckets;
    auto retag_stamp = [&](bs::Table& table, size_t begin, size_t end) {
      bs::ComputeRoutingTagsRange(bs::View(table), 17, 29, begin, end, map, 0);
      if (class_mark) {
        bs::WriteResidualClassBitsRange(bs::View(table), plan, class_from,
                                        begin, end);
      }
    };
    bs::ScatterResidualPoolRange(pool.data(), pool.size(), bs::View(reference),
                                 plan, 0, groups, drop);
    retag_stamp(reference, 0, plan.range_buckets);
    // Reverse group order also checks that disjoint groups have no dependency.
    for (size_t g = groups; g-- > 0;) {
      bs::ScatterResidualPoolRange(pool.data(), pool.size(), bs::View(grouped),
                                   plan, g, g + 1, drop);
      retag_stamp(grouped, g * fanout, (g + 1) * fanout);
    }
    // Nonzero group starts, reverse issue order, and poisoned padding/masks.
    for (size_t g = groups; g-- > 0;) {
      bs::ScatterAndRetagResidualPoolRange(
          pool.data(), pool.size(), bs::View(source_hashed), plan, g, g + 1,
          17, 29, map, bs::DefaultAesTagKeys(), class_mark, class_from, drop);
    }
    Equal(reference, grouped, true);
    Equal(reference, source_hashed, false);
    // Exercise the planner/runner with a drain-only prefix excluded from the
    // scatter and a class boundary relative to the SWEPT pool. The context's
    // own map deliberately differs; residual retagging must use rp.map.
    bs::ResidualStash* run_pool[] = {&owned.slots[3], &owned.slots[0],
                                    &owned.slots[1], &owned.slots[2]};
    const uint8_t ranks[] = {0, 0, 0, 0};
    for (size_t width : {size_t{1}, size_t{7}}) {
      auto scheduled = bs::Table::Create(plan.range_buckets, layout);
      std::memset(scheduled.data.get(), 0xCD, bytes);
      for (size_t b = 0; b < plan.range_buckets; ++b) scheduled.masks[b] = ~uint64_t{0};
      bs::RebuildStepContext ctx;
      ctx.out = bs::View(scheduled);
      ctx.nonce_lo = 17;
      ctx.nonce_hi = 29;
      ctx.drop_unshadowed = drop;
      auto& rp = ctx.residual[1];
      rp.active = true;
      rp.range = bs::View(scheduled);
      rp.plan = plan;
      rp.pool = run_pool;
      rp.rank = ranks;
      rp.pool_slots = 4;
      rp.drain_only = 1;
      rp.map = map;
      rp.rule = class_mark ? bs::ResidualDedupRule::kClassMark
                          : bs::ResidualDedupRule::kNoDedup;
      rp.tier_class_from = class_from;
      bs::SubtaskBudget budget;
      budget.residual_build_buckets = width;
      budget.residual_scatter_buckets = width;
      budget.retag_buckets = width;
      std::vector<bs::Subtask> plan;
      bs::PlanResidualBuildPhases(ctx, budget, 1, &plan);
      for (const bs::Subtask& task : plan) {
        Require(bs::RunSubtask<true>(ctx, task), "scheduled range build overflow");
      }
      Equal(reference, scheduled, false);
    }
    Require(std::memcmp(saved.data(), owned.data.get(), owned.bytes) == 0,
            "source payload mutated");
    for (size_t s = 0; s < owned.slots.size(); ++s) {
      Require(std::memcmp(saved_slots[s].masks, owned.slots[s].masks,
                          sizeof(saved_slots[s].masks)) == 0, "source mask mutated");
    }
    ++cases;
  }
  std::printf("%zu cases passed: grouped full-byte equivalence; scatter-and-retag live-entry equivalence; source immutability\n", cases);
}
