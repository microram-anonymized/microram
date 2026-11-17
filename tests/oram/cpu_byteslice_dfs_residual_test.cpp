// The public-capacity DFS distributor against a scalar expanded filter: every
// leaf page's mask and every byte of every live record, overflow exactly when
// some leaf exceeds its capacity, identical results however the unit list is
// cut into pieces, padding leaves cleared on dirty reuse, and the allocation
// bill.  The distributor's use inside a merge is tested by the level-arena job
// test.
//
// The distributor (src/oram/rebuild/cpu_byteslice_dfs_residual.hpp) builds
// the range table from which the residual second chance offers shed entries
// back to their main buckets.  A record it drops or misplaces is a lost map
// entry, and its only permitted failure is the one declared capacity event
// (some coarse range holding more candidates than its pages), whose
// probability is bounded in analysis/bound_certification/REPORT.tex.  Its
// work and addresses depend only on public shapes, which is why the
// comparison is against a separate, non-oblivious oracle
// (cpu_byteslice_dfs_reference.hpp).
#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <random>
#include <set>
#include <stdexcept>
#include <tuple>
#include <vector>

#include "src/oram/rebuild/cpu_byteslice_dfs_residual.hpp"
#include "tests/oram/cpu_byteslice_dfs_reference.hpp"

namespace bs = microram::byteslice;
namespace ts = microram::byteslice::test_support;
using Shape = bs::DfsResidualWorkspace::Shape;

void Check(bool ok, const char* message) {
  if (!ok) throw std::runtime_error(message);
}

template <class F>
bool Throws(F&& f) {
  try {
    f();
  } catch (const std::exception&) {
    return true;
  }
  return false;
}

// Scenario: 0 empty, 1 all live, 2 random two thirds, 3 one leaf at exactly
// its capacity, 4 one leaf one past it, 5 everything into the last live leaf,
// 6 a live all-ones record (the only live one).
void Fill(bs::TableView gather, const Shape& shape, size_t pages,
          unsigned scenario, std::mt19937_64& rng) {
  const bs::Layout layout = gather.layout;
  const size_t slots = gather.num_buckets * 64;
  const size_t cap = std::min(slots, pages * 64);
  const size_t homes = size_t{1} << shape.index_bits;
  const size_t last = (shape.main_buckets - 1) >> shape.index_bits;
  std::vector<uint8_t> r(layout.EntryBytes());
  std::fill_n(gather.masks, gather.num_buckets, 0);
  for (size_t id = 0; id < slots; ++id) {
    for (auto& byte : r) byte = uint8_t(rng());
    uint64_t home = rng() % shape.main_buckets;
    bool live = rng() % 3 != 0;
    if (scenario == 0) live = false;
    if (scenario == 1) live = true;
    if (scenario == 3 || scenario == 4) {
      live = id < cap + (scenario == 4 ? 1 : 0);
      home = rng() % std::min(homes, shape.main_buckets);  // leaf 0
    }
    if (scenario == 5) {
      live = true;
      home = std::min(shape.main_buckets - 1, last * homes + rng() % homes);
    }
    if (scenario == 6) live = id == slots / 2;
    const unsigned bits = shape.index_bits + shape.coarse_bits;
    const uint64_t low = bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    uint64_t tag = (uint64_t(rng()) & ~low) | (home & low);
    for (size_t k = 0; k < layout.tag_bytes; ++k) {
      r[layout.TagLine(unsigned(k * 8))] = uint8_t(tag >> (k * 8));
    }
    if (scenario == 6 && live) std::fill(r.begin(), r.end(), uint8_t{0xff});
    bs::WriteEntry(gather.Bucket(id / 64), id % 64, r.data(), r.size());
    gather.masks[id / 64] |= uint64_t(live) << (id % 64);
  }
}

bool SameLeaves(const bs::TableView& a, const bs::TableView& b) {
  const size_t lines = a.layout.EntryBytes();
  for (size_t p = 0; p < a.num_buckets; ++p) {
    if (a.masks[p] != b.masks[p]) return false;
    for (size_t lane = 0; lane < 64; ++lane) {
      if (((a.masks[p] >> lane) & 1) == 0) continue;
      for (size_t l = 0; l < lines; ++l) {
        if (a.Bucket(p)[l * 64 + lane] != b.Bucket(p)[l * 64 + lane])
          return false;
      }
    }
  }
  return true;
}

// A direct unit per direct child and a pair per split below it: one unit per
// internal node of 2^(coarse - direct) full trees of 2^direct leaves each.
size_t FullUnits(unsigned coarse) { return size_t{1} << coarse; }

size_t cases = 0;

void Case(bs::DfsResidualWorkspace& ws, const Shape& shape, unsigned scenario,
          uint64_t seed) {
  const bs::Layout layout = ws.Gather().layout;  // configured by the caller
  const size_t pages = ws.pages();
  std::mt19937_64 rng(seed);
  const bs::TableView gather = ws.Gather();
  Fill(gather, shape, pages, scenario, rng);
  const std::vector<uint8_t> saved(gather.data,
                                   gather.data + gather.num_buckets * layout.BucketBytes());
  const std::vector<uint64_t> saved_masks(gather.masks,
                                          gather.masks + gather.num_buckets);
  const size_t leaf_buckets = pages << shape.coarse_bits;
  bs::Table reference = bs::Table::Create(leaf_buckets, layout);
  const bool fits = ts::ExpandedDfsLeaves(gather, shape, pages, bs::View(reference));
  Check(ws.Units() <= (size_t{1} << shape.coarse_bits), "unit list above its bound");
  if (shape.main_buckets == (size_t{1} << (shape.index_bits + shape.coarse_bits))) {
    Check(ws.Units() == FullUnits(shape.coarse_bits), "unpadded unit count");
  }
  bs::Table first;
  for (size_t width : {size_t{1}, size_t{3}, ~size_t{0}}) {
    // Leaf tables arrive dirty: a previous pass's pages and masks.
    bs::Table leaves = bs::Table::Create(leaf_buckets, layout);
    std::memset(leaves.data.get(), 0x5a, leaf_buckets * layout.BucketBytes());
    std::fill_n(leaves.masks.get(), leaf_buckets, ~uint64_t{0});
    ws.Configure(shape);  // restarts the unit list; the gather is untouched
    bool ok = true;
    for (size_t u = 0; u < ws.Units() && ok;) {
      const size_t end = ws.Units() - u > width ? u + width : ws.Units();
      ok = ws.Run(bs::View(leaves), u, end);
      u = end;
    }
    Check(ok == fits, "overflow disagrees with the leaf-capacity oracle");
    Check(std::memcmp(gather.data, saved.data(), saved.size()) == 0 &&
              std::equal(saved_masks.begin(), saved_masks.end(), gather.masks),
          "the gathered pool changed");
    if (!fits) {
      Check(Throws([&] { ws.Run(bs::View(leaves), ws.Units(), ws.Units()); }),
            "a failed pass was resumed");
      continue;
    }
    Check(ws.Done(), "units left over");
    Check(SameLeaves(bs::View(leaves), bs::View(reference)),
          "leaf pages differ from the scalar filter");
    if (width == 1) {
      first = std::move(leaves);
    } else {
      Check(SameLeaves(bs::View(leaves), bs::View(first)),
            "cutting the unit list changed the leaves");
    }
  }
  ++cases;
}

// Which unit kinds the sweep ran, by height, one page or several, and a
// parent of a power-of-two block count or not: the network's last level and
// a leaf's direct writes differ between them.  An unpadded pass runs a
// direct unit at its direct height and a pair (both children of a split)
// below it; a split whose right child is padding is a lone left unit.
enum Kind { kDirect, kLeft, kPair };
std::set<std::tuple<int, unsigned, bool, bool>> covered;

// And which tiles the networks ran, by the compactions sharing them: the
// whole network of a parent of at most eight blocks, or in a larger one its
// leading remainder of n2 blocks (a network) and its groups of eight.
enum TileShape { kWhole, kRemainder, kGroup };
std::set<std::tuple<size_t, int, size_t>> tiles;

bool Pow2(size_t n) { return (n & (n - 1)) == 0; }

void NoteTiles(size_t blocks, size_t sides) {
  if (blocks <= 8) {
    tiles.insert({sides, kWhole, blocks});
    return;
  }
  for (size_t n = blocks;;) {
    size_t n1 = 1;
    while (2 * n1 <= n) n1 *= 2;
    const size_t n2 = n - n1;
    tiles.insert({sides, kGroup, 8});
    if (n2 <= 8) {
      if (n2 > 0) tiles.insert({sides, kRemainder, n2});
      return;
    }
    n = n2;
  }
}

bool Padding(const Shape& shape, unsigned height, size_t node) {
  return (node << (height + shape.index_bits)) >= shape.main_buckets;
}

// The splits below a live node at height h >= 1, as Configure lists them.
void NoteSplits(const Shape& shape, unsigned h, size_t node, size_t pages) {
  const unsigned child = h - 1;
  const bool right = !Padding(shape, child, 2 * node + 1);
  const size_t parent = std::min(shape.pool_buckets, pages << h);
  covered.insert({right ? kPair : kLeft, child, pages > 1, Pow2(parent)});
  NoteTiles(parent, right ? 2 : 1);
  if (child == 0) return;
  NoteSplits(shape, child, 2 * node, pages);
  if (right) NoteSplits(shape, child, 2 * node + 1, pages);
}

void NoteUnits(const Shape& shape, unsigned direct_height, size_t pages) {
  for (size_t c = 0; c < (size_t{1} << (shape.coarse_bits - direct_height)); ++c) {
    if (Padding(shape, direct_height, c)) continue;
    covered.insert({kDirect, direct_height, pages > 1, Pow2(shape.pool_buckets)});
    NoteTiles(shape.pool_buckets, 1);
    if (direct_height > 0) NoteSplits(shape, direct_height, c, pages);
  }
}

// Every kind at heights 0 to 3.  A split's parent is 2^(h+1) pages, a power
// of two at one page, so only several pages give the other shape.  Every
// whole tile of one compaction and every even one of a pair (a pair's parent
// is an even number of blocks), every remainder of one compaction, and a
// pair's remainders at three pages (12 and 24 blocks).
void CheckCoverage() {
  for (unsigned h = 0; h <= 3; ++h) {
    for (bool multi : {false, true}) {
      for (bool pow2 : {false, true}) {
        Check(covered.count({kDirect, h, multi, pow2}) == 1,
              "the sweep missed a direct unit shape");
        if (!multi && !pow2) continue;
        Check(covered.count({kPair, h, multi, pow2}) == 1 &&
                  covered.count({kLeft, h, multi, pow2}) == 1,
              "the sweep missed a split unit shape");
      }
    }
  }
  for (size_t n = 1; n <= 8; ++n) {
    Check(tiles.count({1, kWhole, n}) == 1 && tiles.count({1, kRemainder, n}) == 1,
          "the sweep missed a tile of one compaction");
    if (n % 2 == 0) {
      Check(tiles.count({2, kWhole, n}) == 1, "the sweep missed a pair's whole tile");
    }
  }
  Check(tiles.count({1, kGroup, 8}) == 1 && tiles.count({2, kGroup, 8}) == 1 &&
            tiles.count({2, kRemainder, 4}) == 1 && tiles.count({2, kRemainder, 8}) == 1,
        "the sweep missed a tile of a larger network");
}

void Sweep(const bs::Layout& layout) {
  struct Geometry {
    size_t max_pool;
    unsigned max_coarse;
    size_t pages;
  };
  // Allocations wider than the passes they run, so reuse at smaller shapes
  // and different direct heights shares one workspace.
  for (const Geometry g : {Geometry{12, 7, 2}, Geometry{40, 9, 1},
                           Geometry{40, 9, 2}, Geometry{40, 9, 3},
                           Geometry{64, 9, 3}, Geometry{5, 3, 2}}) {
    bs::DfsResidualWorkspace ws(layout, g.max_pool, g.max_coarse, g.pages);
    const auto planned = bs::DfsResidualWorkspace::Planned(
        layout, g.max_pool, g.max_coarse, g.pages);
    Check(planned.data_bytes == ws.Allocated().data_bytes &&
              planned.plain_bytes == ws.Allocated().plain_bytes,
          "the byte bill disagrees with the allocation");
    uint64_t seed = 1;
    // Pools that are and are not powers of two at every direct height; the
    // rest give every whole tile and every remainder of a larger network
    // (NoteTiles), which depend on the pool only, at one partition width.
    std::vector<size_t> pools{1, 2, 3, 4, 5, 8, 12, 16, 32, g.max_pool};
    const std::vector<size_t> tile_pools{6, 7, 9, 10, 11, 13, 14, 15};
    pools.insert(pools.end(), tile_pools.begin(), tile_pools.end());
    std::sort(pools.begin(), pools.end());
    pools.erase(std::unique(pools.begin(), pools.end()), pools.end());
    for (size_t pool : pools) {
      if (pool > g.max_pool) continue;
      const bool tile_only = std::count(tile_pools.begin(), tile_pools.end(), pool) &&
                             pool != g.max_pool;
      for (unsigned coarse : {0u, 1u, 3u, g.max_coarse}) {
        if (coarse > g.max_coarse || (tile_only && coarse != 3)) continue;
        for (unsigned index : {0u, 2u}) {
          const size_t full = size_t{1} << (index + coarse);
          // Full, one short of full (a padded top leaf), a mixed-radix 5/8
          // of it, whose top three eighths are padding, and one home past
          // half, whose right children are padding at every height.
          const size_t half_and_one = full / 2 + 1;
          for (size_t main : {full, full - 1, full * 5 / 8, half_and_one}) {
            if (main == 0 ||
                (main == half_and_one && (tile_only || coarse < 3))) {
              continue;
            }
            Shape shape{pool, coarse, index, main};
            ws.Configure(shape);
            NoteUnits(shape, ws.DirectHeight(), g.pages);
            for (unsigned scenario = 0; scenario < 7; ++scenario) {
              if (scenario == 6 && main != full) continue;
              ws.Configure(shape);
              Case(ws, shape, scenario, seed++);
            }
          }
        }
      }
    }
    Check(ws.Allocated().data_bytes == planned.data_bytes,
          "storage grew while running");
  }
}

void Refusals() {
  const bs::Layout layout{8, 17, 4};
  Check(Throws([&] { bs::DfsResidualWorkspace w(layout, 0, 2, 2); }), "empty pool");
  Check(Throws([&] { bs::DfsResidualWorkspace w(layout, 4, 2, 0); }), "no pages");
  Check(Throws([&] { bs::DfsResidualWorkspace w(layout, 4, 17, 2); }), "deep");
  Check(Throws([&] { bs::DfsResidualWorkspace w({0, 17, 4}, 4, 2, 2); }), "layout");
  bs::DfsResidualWorkspace ws(layout, 4, 3, 2);
  Check(Throws([&] { ws.Gather(); }), "an unconfigured gather was handed out");
  Check(Throws([&] { ws.Configure({5, 3, 0, 8}); }), "pool wider than storage");
  Check(Throws([&] { ws.Configure({4, 4, 0, 16}); }), "partition deeper than storage");
  Check(Throws([&] { ws.Configure({4, 3, 0, 9}); }), "main beyond the partition");
  Check(Throws([&] { ws.Configure({4, 3, 30, 8}); }), "partition beyond the tag");
  Check(Throws([&] { ws.Configure({4, 1, ~0u, 1}); }),
        "wrapped partition width");
  ws.Configure({4, 3, 0, 8});
  bs::Table leaves = bs::Table::Create(2 << 3, layout);
  bs::Table short_leaves = bs::Table::Create(8, layout);
  Check(Throws([&] { ws.Run(bs::View(short_leaves), 0, 1); }), "wrong leaf table");
  Check(Throws([&] { ws.Run(bs::View(leaves), 1, 2); }), "units out of order");
  Check(Throws([&] { ws.Run(bs::View(leaves), 0, ws.Units() + 1); }), "past the list");
}

// The certification report's (REPORT.tex) widest ordinary pass, level 5
// digit 8: 40 pool buckets, 512
// coarse ranges of 1024 homes.  Capacities bind below 2560 slots from height
// 4 at two pages (2048) and height 3 at three (1536).  One unit per internal
// node of the partition, whatever the direct height.
void ReportShape() {
  const bs::Layout layout{8, 17, 4};
  const Shape shape{40, 9, 10, size_t{1} << 19};
  for (const auto want : {std::array<size_t, 3>{2, 4, 512},
                          std::array<size_t, 3>{3, 3, 512},
                          std::array<size_t, 3>{1, 5, 512}}) {
    bs::DfsResidualWorkspace ws(layout, 40, 9, want[0]);
    ws.Configure(shape);
    Check(ws.DirectHeight() == want[1], "direct height at L5/d8");
    Check(ws.Units() == want[2], "unit count at L5/d8");
    Check(ws.Capacity(0) == 64 * want[0] && ws.Capacity(9) == 2560,
          "leaf and root capacities at L5/d8");
  }
  // Independent byte inventory for the two-page shape: gather and direct
  // buffers of 40 buckets, then split buffers of 4, 8, 16 and 32 buckets.
  // All six buffers have a capacity and an offset descriptor. The widest
  // split selects 32 buckets; the direct pass selects 40. Each of the 512
  // unit descriptors has four one-byte fields and one uint32_t node number.
  // In particular, include both descriptor vectors: comparing Planned with
  // Allocated alone cannot catch an allocation omitted by both methods.
  const size_t data_bytes = 140 * layout.BucketBytes();
  const size_t plain_bytes = 12 * sizeof(size_t) + 212 * sizeof(uint64_t) +
                             74 * sizeof(uint32_t) + 512 * 8;
  bs::DfsResidualWorkspace ws(layout, 40, 9, 2);
  const auto planned = bs::DfsResidualWorkspace::Planned(layout, 40, 9, 2);
  Check(planned.data_bytes == data_bytes && planned.plain_bytes == plain_bytes &&
            ws.Allocated().data_bytes == data_bytes &&
            ws.Allocated().plain_bytes == plain_bytes,
        "the byte bill omitted part of the workspace inventory");
}

int main() {
  for (const bs::Layout layout : {bs::Layout{8, 17, 4}, bs::Layout{16, 257, 8},
                                  bs::Layout{4, 4, 2}}) {
    Sweep(layout);
  }
  CheckCoverage();
  Refusals();
  ReportShape();
  std::printf("DFS residual: %zu cases match the scalar leaf filter at every "
              "piece width, with padding, reuse and overflow\n", cases);
}
