// What the probe cascade is actually made of: the size composition of the live
// probe plan, sampled over a full fixed-level cycle.
//
// The per-level arena engine (`ByteMap`, src/oram/levelarena/) reports the
// LENGTH of its probe list -- `last_probe_tables()` -- and every cascade
// estimate the design documents make has had to assume a distribution behind
// that mean.  A per-table cost is strongly size-dependent -- a 64-bucket table
// is L1-resident and a 2^19-bucket one is a DRAM round trip -- so the mean
// alone cannot say what a change to the probe path is worth.  This fills a map
// at the chosen geometry, walks a full cycle of accesses over it, samples
// `PlanSnapshot()` periodically, and prints the histogram: how many tables of
// each size an average access probes, and what share of the cascade each size
// class is.
//
// The owner threads are real threads here, so the dense occupancies are the
// snapshot's own counts, taken inside the reader epoch.  A snapshot is made of
// TableShape, which has no storage pointer to misuse: the arena behind a dense
// table can be recycled for the owner's next table the instant the epoch is
// left, so counting through a copied pointer after that point would be
// silently wrong (the arena stays mapped and reads succeed).
//
// EVERY ACCESS.  Besides the sampled snapshots, each scalar `find`
// is followed by a read of `last_probe_tables()` / `last_probe_buckets()`;
// count, sum, sum of squares, min, max and an exact tables-per-access histogram
// are kept, and a final machine-readable JSON line is printed.  Reading them is
// safe against the owner threads: both fields are written only by the request
// thread, in the scalar `Cascade` (level-arena engine, `last_probe_tables_ =
// n`) and, per CHUNK, in `ClaimBatchDummies`; the owner threads never touch
// them.  Only the scalar API is measured here.  A batch access sets the
// numbers once per call of ClaimBatchDummies (a chunk of lanes sharing one
// plan), not per lane, so batch mode would need a per-chunk reading.
// The large K4/V8 shape is `--key-bytes 4 --value-bytes 8 --capacity 134217728`
// (2^27, which needs tens of GiB of memory; 2^16..2^20 suffice for a quick
// check).
//
// Usage: cpu_byteslice_probe_plan_shape_benchmark [capacity] [branching]
//                                       [top_digit] [sample_every] [flushes]
//        cpu_byteslice_probe_plan_shape_benchmark [flags]
// Positional defaults: 1048576 8 0 997 0.  Flags (any flag selects flag mode;
// the positional form is a short form of the first five):
//   --capacity N  --branching B  --top-digit D  --key-bytes K  --value-bytes V
//   --accesses N        (default: one full cycle = the actual capacity)
//   --seed N            engine key schedule (default: a fixed seed, printed in
//                       the header); --access-seed N
//                       draws the accessed keys (default 7)
//   --sample-every N    PlanSnapshot period (default 997)
//   --owners N          owner threads (default 2 = the library default)
//   --prefix-flushes N  --dense-prefixes N  --stash-entries N
//   --rebuild-threads N --top-helpers N     --bottom-helpers N
// Thread/shape knobs not given keep the library defaults, which are printed.
//
// The knobs are the public `Options` ones.  The geometry is not given as a
// last level: the arena ladder chooses the level count L (and, at 0, the top
// digit D and level 0's radix r0) from the requested capacity.  Level 0's own
// radix r0 is `deamortized_prefix_flushes`, the complete stash flushes that
// make one dense prefix.  `4194304 8 4 997 2` is the 2^22 rung at B = 8,
// D = 4, r0 = 2.
// A capacity of 2^24 is the production point and takes minutes to fill.

#include "include/cpu_byteslice_oram/oram.hpp"

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <map>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

namespace oram = cpu_byteslice_oram;
namespace bs = microram::byteslice;

// Dense integer keys in the low `key.size()` bytes (little endian).
struct Args {
  size_t capacity = size_t{1} << 20;
  unsigned branching = 8, top_digit = 0;
  size_t key_bytes = 8, value_bytes = 16;
  uint64_t accesses = 0;  // 0: one full cycle
  uint64_t seed = 20260831, access_seed = 7, sample_every = 997;
  oram::Options defaults;  // library defaults, for printing
  unsigned prefix_flushes = 0;
  unsigned owners = defaults.deamortized_owner_threads;
  unsigned dense_prefixes = defaults.deamortized_dense_prefixes;
  size_t stash_entries = defaults.deamortized_online_stash_entries;
  unsigned rebuild_threads = defaults.deamortized_rebuild_threads;
  unsigned top_helpers = defaults.deamortized_top_helpers;
  unsigned bottom_helpers = defaults.deamortized_bottom_helpers;
};

// Count, sum, sum of squares, min, max of a small integer per access.
struct Stat {
  uint64_t n = 0, min = ~uint64_t{0}, max = 0;
  long double sum = 0, sum2 = 0;
  void Add(uint64_t x) {
    ++n;
    sum += x;
    sum2 += static_cast<long double>(x) * x;
    min = std::min(min, x);
    max = std::max(max, x);
  }
  double Mean() const { return n ? static_cast<double>(sum / n) : 0; }
  double Std() const {
    if (!n) return 0;
    const long double m = sum / n;
    const long double v = sum2 / n - m * m;
    return v > 0 ? std::sqrt(static_cast<double>(v)) : 0;
  }
};

struct SizeClass {
  uint64_t hashed = 0;  // samples in which a hashed table of this size appeared
  uint64_t dense = 0;
  // Occupancy of the dense ones.  A dense table is scanned in FULL, so what it
  // costs is its capacity while what it holds is its occupancy -- and the gap
  // between the two is the whole question of whether a 64-slot tier is the
  // right size for what a rebuild actually sheds.
  uint64_t dense_entries = 0;
  unsigned dense_max = 0;
};

// The dense tables are not all the same thing, and for "how big should a dense
// table be" they are three different questions: the CURRENT online stash unit
// fills to its insertion unit by construction (that is what triggers a flush),
// a DENSE PREFIX is complete-or-assembling stash units waiting to be consumed
// by level 1, and a residual SECOND TIER holds only what a rebuild's second
// chance could not re-offer.  Only the last is a candidate for shrinking, so
// they are counted apart.
struct DenseClass {
  const char* name;
  uint64_t seen = 0;
  uint64_t entries = 0;
  unsigned max = 0;
  void Add(unsigned occupied) {
    ++seen;
    entries += occupied;
    max = std::max(max, occupied);
  }
};

void EncodeKey(uint64_t key, uint8_t* out, size_t key_bytes) {
  std::memset(out, 0, key_bytes);
  std::memcpy(out, &key, std::min(key_bytes, sizeof(key)));
}

Args ParseArgs(int argc, char** argv) {
  Args a;
  const bool flags = argc > 1 && std::strncmp(argv[1], "--", 2) == 0;
  if (!flags) {
    if (argc > 1) a.capacity = std::strtoull(argv[1], nullptr, 10);
    if (argc > 2) a.branching = std::strtoul(argv[2], nullptr, 10);
    if (argc > 3) a.top_digit = std::strtoul(argv[3], nullptr, 10);
    if (argc > 4) a.sample_every = std::strtoull(argv[4], nullptr, 10);
    if (argc > 5) a.prefix_flushes = std::strtoul(argv[5], nullptr, 10);
    if (a.sample_every == 0) throw std::invalid_argument("sample_every 0");
    return a;
  }
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    auto next = [&]() -> uint64_t {
      if (i + 1 >= argc) throw std::invalid_argument(arg + " needs a value");
      return std::strtoull(argv[++i], nullptr, 10);
    };
    if (arg == "--capacity") a.capacity = next();
    else if (arg == "--branching") a.branching = unsigned(next());
    else if (arg == "--top-digit") a.top_digit = unsigned(next());
    else if (arg == "--key-bytes") a.key_bytes = next();
    else if (arg == "--value-bytes") a.value_bytes = next();
    else if (arg == "--accesses") a.accesses = next();
    else if (arg == "--seed") a.seed = next();
    else if (arg == "--access-seed") a.access_seed = next();
    else if (arg == "--sample-every") a.sample_every = next();
    else if (arg == "--owners") a.owners = unsigned(next());
    else if (arg == "--prefix-flushes") a.prefix_flushes = unsigned(next());
    else if (arg == "--dense-prefixes") a.dense_prefixes = unsigned(next());
    else if (arg == "--stash-entries") a.stash_entries = next();
    else if (arg == "--rebuild-threads") a.rebuild_threads = unsigned(next());
    else if (arg == "--top-helpers") a.top_helpers = unsigned(next());
    else if (arg == "--bottom-helpers") a.bottom_helpers = unsigned(next());
    else throw std::invalid_argument("unknown flag " + arg);
  }
  if (a.sample_every == 0) throw std::invalid_argument("--sample-every 0");
  return a;
}

}  // namespace

int main(int argc, char** argv) {
  Args args;
  try {
    args = ParseArgs(argc, argv);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "%s\n", e.what());
    return 2;
  }
  const size_t requested = args.capacity;
  const size_t kKeyBytes = args.key_bytes, kValueBytes = args.value_bytes;
  const uint64_t sample_every = args.sample_every;

  oram::Options options;
  options.deamortized_branching_factor = args.branching;
  options.deamortized_top_digit = args.top_digit;
  options.deamortized_prefix_flushes = args.prefix_flushes;
  options.deamortized_owner_threads = args.owners;
  options.deamortized_dense_prefixes = args.dense_prefixes;
  options.deamortized_online_stash_entries = args.stash_entries;
  options.deamortized_rebuild_threads = args.rebuild_threads;
  options.deamortized_top_helpers = args.top_helpers;
  options.deamortized_bottom_helpers = args.bottom_helpers;
  options.secret_seed = microram::crypto::SecretKeySeed::Fixed(args.seed);

  // The geometry the ladder chooses, before anything is built: this is what
  // the sampled plan is a plan OF, so it is printed rather than inferred.  A
  // shape no geometry supports is refused here.  The keys are the ids
  // 0 .. capacity() - 1, so the ROUNDED capacity must fit the key space.
  bs::levelarena::LevelArenaCapacityChoice choice;
  std::unique_ptr<oram::ByteMap<>> built;
  try {
    choice = oram::ByteMap<>::plan_geometry(requested, kKeyBytes, kValueBytes,
                                            options);
    if (kKeyBytes < 8 && choice.capacity > (uint64_t{1} << (8 * kKeyBytes))) {
      throw std::invalid_argument(
          "capacity " + std::to_string(choice.capacity) + " exceeds the " +
          std::to_string(kKeyBytes) + "-byte key space");
    }
    built = std::make_unique<oram::ByteMap<>>(requested, kKeyBytes,
                                              kValueBytes, options);
  } catch (const std::exception& e) {
    std::fprintf(stderr, "%s\n", e.what());
    return 2;
  }
  oram::ByteMap<>& map = *built;

  const bs::Layout& layout = choice.layout;
  const size_t capacity = map.capacity();
  std::printf("probe plan shape: B = %u, r0 = %u, D = %u, L = %u, load 0.50\n",
              choice.geometry.branching, choice.geometry.prefix_flushes,
              choice.geometry.top_digit, choice.geometry.levels);
  std::printf("  requested %zu, capacity %zu entries, bytes %.0f MiB, entry"
              " %zu B (key %zu, value %zu, tag %zu)\n",
              requested, capacity,
              static_cast<double>(map.arena_bytes()) / (1 << 20),
              layout.EntryBytes(), layout.key_bytes, layout.value_bytes,
              layout.tag_bytes);
  std::printf("  knobs: owners %u, rebuild_threads %u, top_helpers %u,"
              " bottom_helpers %u, dense_prefixes %u, stash_entries %zu,"
              " prefix_flushes (request) %u, seed %llu, access_seed %llu\n",
              args.owners, args.rebuild_threads, args.top_helpers,
              args.bottom_helpers, args.dense_prefixes, args.stash_entries,
              args.prefix_flushes,
              static_cast<unsigned long long>(args.seed),
              static_cast<unsigned long long>(args.access_seed));
  std::fflush(stdout);

  std::vector<uint8_t> key(kKeyBytes, 0);
  std::vector<uint8_t> value(kValueBytes, 0);
  for (size_t i = 0; i < capacity; ++i) {
    EncodeKey(i, key.data(), kKeyBytes);
    value[0] = static_cast<uint8_t>(i);
    map.insert_or_assign(key.data(), value.data());
  }
  std::printf("  filled; probe list now %zu tables\n",
              map.engine().ProbeListLength());
  std::fflush(stdout);

  // One full cycle of accesses: any half-open window of capacity accesses
  // contains exactly one top-level carry whatever phase it starts at, so the
  // sampled distribution is the steady state and not a phase of it.
  std::map<size_t, SizeClass> by_buckets;
  DenseClass residual_tier{"residual second tier"};
  DenseClass online_unit{"online stash (current)"};
  DenseClass dense_prefix{"dense prefix"};
  uint64_t samples = 0, tables_total = 0;
  std::mt19937_64 rng(args.access_seed);
  const uint64_t accesses = args.accesses ? args.accesses : capacity;
  Stat tables_stat, buckets_stat;
  std::map<size_t, uint64_t> tables_hist;
  for (uint64_t i = 0; i < accesses; ++i) {
    EncodeKey(rng() % capacity, key.data(), kKeyBytes);
    map.find(key.data(), value.data());
    // Request-thread fields of the access just made (see the header).
    const size_t lt = map.last_probe_tables();
    tables_stat.Add(lt);
    buckets_stat.Add(map.last_probe_buckets());
    ++tables_hist[lt];
    if (i % sample_every != 0) continue;
    const bs::ProbePlanSnapshot plan = map.engine().PlanSnapshot();
    ++samples;
    tables_total += plan.tables.size();
    for (size_t k = 0; k < plan.tables.size(); ++k) {
      const bs::TableShape& t = plan.tables[k];
      SizeClass& sc = by_buckets[t.num_buckets];
      if (t.kind == bs::TableKind::kHashed) {
        ++sc.hashed;
      } else {
        ++sc.dense;
        // Counted under the reader epoch, by the snapshot (see the header).
        const unsigned occupied = static_cast<unsigned>(plan.occupancy[k]);
        sc.dense_entries += occupied;
        sc.dense_max = std::max(sc.dense_max, occupied);
        DenseClass& dc = t.tier != 0 ? residual_tier
                                     : (t.removable ? online_unit
                                                    : dense_prefix);
        dc.Add(occupied);
      }
    }
  }

  const double per_access = static_cast<double>(tables_total) /
                            static_cast<double>(samples);
  std::printf("\n  %zu samples over %llu accesses; mean %.2f probed tables"
              " per access\n\n", static_cast<size_t>(samples),
              static_cast<unsigned long long>(accesses), per_access);
  std::printf("  %12s %12s %10s %10s %10s %12s %8s\n", "buckets", "entries",
              "MiB", "hashed/acc", "dense/acc", "dense mean n", "max n");
  const size_t bucket_bytes = layout.BucketBytes();
  // A hashed table of `b` buckets holds 32 b entries: the load-0.5 occupancy
  // the arena ladder's certificate is computed at.
  const size_t entries_per_bucket = bs::kBucketCapacity / 2;
  for (const auto& kv : by_buckets) {
    std::printf("  %12zu %12zu %10.3f %10.3f %10.3f", kv.first,
                kv.first * entries_per_bucket,
                static_cast<double>(kv.first * bucket_bytes) / (1 << 20),
                static_cast<double>(kv.second.hashed) /
                    static_cast<double>(samples),
                static_cast<double>(kv.second.dense) /
                    static_cast<double>(samples));
    if (kv.second.dense != 0) {
      std::printf(" %12.3f %8u",
                  static_cast<double>(kv.second.dense_entries) /
                      static_cast<double>(kv.second.dense),
                  kv.second.dense_max);
    }
    std::printf("\n");
  }

  // What a dense table holds against what a probe of it costs.  A dense probe
  // reads key + value lines of EVERY bucket, so its cost is capacity, not
  // occupancy: 64 slots is 1536 B at this payload whether one entry is in it
  // or sixty.
  std::printf("\n  dense tables by role (bucket %zu slots, probe %zu B each):\n",
              bs::kBucketCapacity,
              (layout.key_bytes + layout.value_bytes) * bs::kBucketCapacity);
  std::printf("  %-24s %10s %10s %8s\n", "role", "per access", "mean n",
              "max n");
  for (const DenseClass* d : {&residual_tier, &online_unit, &dense_prefix}) {
    if (d->seen == 0) continue;
    std::printf("  %-24s %10.3f %10.3f %8u\n", d->name,
                static_cast<double>(d->seen) / static_cast<double>(samples),
                static_cast<double>(d->entries) /
                    static_cast<double>(d->seen),
                d->max);
  }

  // Every-access aggregate.
  const double log2n = std::log2(static_cast<double>(capacity));
  std::printf("\n  every access (%llu): tables mean %.3f sd %.3f min %llu"
              " max %llu; buckets mean %.1f sd %.1f min %llu max %llu\n",
              static_cast<unsigned long long>(tables_stat.n),
              tables_stat.Mean(), tables_stat.Std(),
              static_cast<unsigned long long>(tables_stat.min),
              static_cast<unsigned long long>(tables_stat.max),
              buckets_stat.Mean(), buckets_stat.Std(),
              static_cast<unsigned long long>(buckets_stat.min),
              static_cast<unsigned long long>(buckets_stat.max));
  std::printf("  log2(capacity) = %.3f: tables mean/log2N %.3f, max/log2N"
              " %.3f\n", log2n, tables_stat.Mean() / log2n,
              static_cast<double>(tables_stat.max) / log2n);
  std::printf("  tables histogram:");
  for (const auto& kv : tables_hist) {
    std::printf(" %zu:%llu", kv.first,
                static_cast<unsigned long long>(kv.second));
  }
  std::printf("\n");

  std::printf("{\"key_bytes\":%zu,\"value_bytes\":%zu,\"requested_capacity\":%zu,"
              "\"actual_capacity\":%zu,\"B\":%u,\"D\":%u,\"r0\":%u,\"L\":%u,"
              "\"accesses\":%llu,"
              "\"tables\":{\"mean\":%.6f,\"max\":%llu,\"min\":%llu},"
              "\"buckets\":{\"mean\":%.6f,\"max\":%llu,\"min\":%llu},"
              "\"tables_hist\":{",
              kKeyBytes, kValueBytes, requested, capacity,
              choice.geometry.branching, choice.geometry.top_digit,
              choice.geometry.prefix_flushes, choice.geometry.levels,
              static_cast<unsigned long long>(accesses), tables_stat.Mean(),
              static_cast<unsigned long long>(tables_stat.max),
              static_cast<unsigned long long>(tables_stat.min),
              buckets_stat.Mean(),
              static_cast<unsigned long long>(buckets_stat.max),
              static_cast<unsigned long long>(buckets_stat.min));
  bool first = true;
  for (const auto& kv : tables_hist) {
    std::printf("%s\"%zu\":%llu", first ? "" : ",", kv.first,
                static_cast<unsigned long long>(kv.second));
    first = false;
  }
  std::printf("},\"log2_capacity\":%.6f,\"tables_mean_over_log2N\":%.6f,"
              "\"tables_max_over_log2N\":%.6f,"
              "\"knobs\":{\"owners\":%u,\"rebuild_threads\":%u,"
              "\"top_helpers\":%u,\"bottom_helpers\":%u,"
              "\"dense_prefixes\":%u,\"stash_entries\":%zu,"
              "\"prefix_flushes\":%u,\"seed\":%llu,\"access_seed\":%llu}}\n",
              log2n, tables_stat.Mean() / log2n,
              static_cast<double>(tables_stat.max) / log2n, args.owners,
              args.rebuild_threads, args.top_helpers, args.bottom_helpers,
              args.dense_prefixes, args.stash_entries, args.prefix_flushes,
              static_cast<unsigned long long>(args.seed),
              static_cast<unsigned long long>(args.access_seed));
  return 0;
}
