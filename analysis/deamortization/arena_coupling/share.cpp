// Static per-(level, digit) touch split: preparation vs after arrival.
// Uses the engine's own planners and pricing (no tables are allocated).
#include <cstdio>
#include <cstdlib>
#include "src/oram/levelarena/cpu_byteslice_level_arena_capacity.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_owner.hpp"
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"

using namespace microram::byteslice;
using namespace microram::byteslice::levelarena;

int main(int argc, char** argv) {
  unsigned logn = argc > 1 ? atoi(argv[1]) : 27;
  unsigned owners = argc > 2 ? atoi(argv[2]) : 0;
  LevelArenaCapacityRequest req;
  req.entries = uint64_t{1} << logn;
  req.key_bytes = 4;
  req.value_bytes = 8;
  req.branching = 8;
  req.owner_threads = owners;
  LevelArenaCapacityChoice choice = PlanLevelArenaCapacity(req);
  LevelArenaGeometry geometry(choice.geometry);
  const Layout& layout = choice.layout;
  LevelArenaStashSizing sizing(geometry, req.max_accesses);
  printf("N=2^%u L=%u D=%u r0=%u s=%zu bucket_bytes=%zu fanouts:", logn,
         geometry.Levels(), geometry.TopDigit(),
         (unsigned)choice.geometry.prefix_flushes, choice.geometry.stash_buckets,
         layout.BucketBytes());
  for (unsigned l = 1; l < geometry.Levels(); ++l) printf(" %u", geometry.Fanout(l));
  printf("\n");
  const SubtaskBudget whole = WholeLevelMergeBudget();
  const size_t bucket_bytes = layout.BucketBytes();
  for (unsigned level = 1; level < geometry.Levels(); ++level) {
    const size_t carry = geometry.CarryBuckets(level);
    const unsigned k = Log2Exact(carry);
    printf("level %u U=%zu (2^%u) fanout %u tier %zu stash %zu\n", level, carry, k,
           geometry.Fanout(level), geometry.TierBucketsOf(level), sizing.Buckets(level));
    for (unsigned d = 1; d <= geometry.Fanout(level); ++d) {
      const CarryPlan plan = geometry.PlanCarry(level, d);
      if (plan.outcome == CarryOutcome::kAdopt) {
        printf("  d=%u adopt\n", d);
        continue;
      }
      double prep = 0, install = 0, sweep = 0;
      if (level == 1) {
        const size_t z = geometry.RoutedPrefixBuckets();
        const size_t m = geometry.DensePrefixBuckets();
        install = double(DensePrefixDedupPairs(geometry)) + 2.0 * double(m) +
                  double(DenseSelectHomeTouches(static_cast<unsigned>(m))) * double(z);
      }
      const bool separated = SeparatedSources(geometry, level, d);
      if (separated) sweep = double(FixedMergeUnitTouches(d)) * double(carry);
      else if (level != 1) install += (d == 1 ? 1.0 : 2.0) * double(carry);
      if (d > 1) {
        const unsigned r = d >> static_cast<unsigned>(_tzcnt_u32(d));
        const unsigned e = Log2Exact(d / r);
        SubtaskTouchCounter older;
        PlanMergeOlderBlocks(k, r, e, bucket_bytes, whole, &older);
        prep += double(older.touches);
        for (unsigned c = k; c < k + e; ++c) prep += 2.0 * double(size_t{1} << c);
        if (r > 1) prep += double(RadixTupleTouches(r)) * double(size_t{1} << (k + e));
      }
      ResidualTouchSplit res = LevelMergeResidualTouchSplit(geometry, layout, sizing, level, d);
      const double late = install + sweep + res.passes + res.offers;
      const double total = prep + late;
      printf("  d=%u k=%u prep=%.0f install=%.0f sweep=%.0f res_passes=%.0f res_offers=%.0f"
             "  late/total=%.3f  route-only late=%.3f  (per output bucket: prep %.2f late %.2f)\n",
             d, d - 1, prep, install, sweep, res.passes, res.offers, late / total,
             (install + sweep) / (prep + install + sweep),
             prep / double(d * carry), late / double(d * carry));
    }
  }
  return 0;
}
