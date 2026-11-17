// Native A-only final-offer/drain boundaries and initialization scatter.
// Adversarial kernel fixtures test the count witness, not ideal-source laws.
#include "src/oram/levelarena/cpu_byteslice_level_arena_job.hpp"
#include "src/oram/rebuild/cpu_byteslice_initialization.hpp"
#include "tests/oram/cpu_byteslice_level_arena_test_support.hpp"
#include "tests/oram/cpu_byteslice_rebuild_test_support.hpp"

#include <array>
#include <cstdio>
#include <set>
#include <stdexcept>
#include <vector>

namespace bs = microram::byteslice;
namespace ts = bs::test_support;

void Require(bool condition) {
  if (!condition) throw std::runtime_error("top preparation count witness mismatch");
}

void Packing(const bs::Layout& layout, size_t tier_pages, size_t excess,
             bool earlier_pool) {
  auto main = ts::ZeroedTable(8, layout);
  const auto plan = bs::PlanResidualRange(4, 3);  // Direct candidate pages.
  auto range = ts::ZeroedTable(plan.range_buckets, layout);
  ts::OwnedLevelStashes route(1, 4, layout), drain(1, tier_pages, layout);
  auto& shed = route.slots[0];
  auto& tier = drain.slots[0];
  std::vector<size_t> homes;
  std::array<size_t, 8> counts{};
  auto plant = [&](uint8_t* bucket, size_t slot, size_t home) {
    const auto key = ts::FixtureKey(homes.size(), layout.key_bytes);
    ts::PlantEntry(layout, bucket, slot, key, 1);
    for (size_t byte = 0; byte < layout.tag_bytes; ++byte)
      bucket[layout.TagLine(unsigned(8*byte))*64+slot] = uint8_t(home >> (8*byte));
    homes.push_back(home);
    ++counts[home];
  };
  // The last binary stage joins bucket i with i+4. All its input keys
  // choose i, creating a known drain-only shed spread across four homes.
  for (size_t i = 0; i < 4; ++i) {
    const size_t extra = excess/4+(i < excess%4);
    for (size_t slot = 0; slot < 64; ++slot) plant(main.Bucket(i), slot, i);
    for (size_t slot = 0; slot < extra; ++slot) plant(main.Bucket(i+4), slot, i);
    main.masks[i] = ~uint64_t{0};
    main.masks[i+4] = bs::LowMask64(extra);
    if (earlier_pool) {
      // Four candidates encounter a full home; two fill a previously empty
      // home. All are distinct from the remaining main and final sheds.
      for (size_t slot = 0; slot < 6; ++slot)
        plant(range.Bucket(i), slot, slot < 4 ? i : i+4);
      range.masks[i] = bs::LowMask64(6);
    }
  }
  bs::ResidualOfferSet offer{bs::View(range), plan,
                            bs::ResidualDedupRule::kNoDedup, layout.PayloadLines()};
  Require(bs::ButterflyLevelOffersRange<true>(bs::View(main), 2, shed, offer, 0, 4));
  Require(shed.Count() == excess);
  size_t witnessed = 0;
  for (size_t home = 0; home < 8; ++home) {
    Require(bs::Popcount64(main.masks[home]) == std::min(size_t{64}, counts[home]));
    if (counts[home] > 64) witnessed += counts[home]-64;
  }
  std::set<uint64_t> seen;
  auto inspect = [&](const uint8_t* bucket, uint64_t mask, size_t expected_home, bool residual) {
    for (size_t slot = 0; slot < 64; ++slot) {
      if (!(mask & (uint64_t{1} << slot))) continue;
      const auto key = ts::SlotKeyWordsOf(layout, bucket, slot).w0;
      Require(key > 0 && key <= homes.size() && seen.insert(key).second);
      const size_t home = homes[key-1];
      if (residual) Require(main.masks[home] == ~uint64_t{0});
      else Require(home == expected_home);
    }
  };
  for (size_t i = 0; i < 8; ++i) inspect(main.Bucket(i), main.masks[i], i, false);
  for (size_t i = 0; i < range.num_buckets; ++i) inspect(range.Bucket(i), range.masks[i], 0, true);
  for (size_t i = 0; i < shed.num_buckets; ++i) inspect(shed.Bucket(i), shed.masks[i], 0, true);
  Require(seen.size() == homes.size());
  // Same order as the native no-dedup pass: range first, drain-only second.
  Require(bs::DrainResidualTableRange(bs::View(range), tier, layout.PayloadLines(), 0, range.num_buckets));
  Require(tier.Count() == (earlier_pool ? 16 : 0) && tier.Count() <= witnessed);
  bs::ResidualStash* pool[] = {&shed};
  const bool ok = bs::DrainResidualPoolRange(pool, 1, tier, layout.PayloadLines(), 0, shed.num_buckets);
  Require(ok == (witnessed <= tier.Capacity()));
  if (ok) Require(tier.Count() == witnessed);
  std::printf("{\"kind\":\"packing\",\"tier_slots\":%zu,\"final_shed\":%zu,"
      "\"earlier_pool\":%s,\"witness_excess\":%zu,\"drain_succeeded\":%s,\"passed\":true}\n",
      tier.Capacity(), excess, earlier_pool ? "true" : "false", witnessed, ok ? "true" : "false");
}

void InitialScatter(const bs::Layout& layout, size_t count) {
  auto table = ts::ZeroedTable(8, layout);
  std::vector<std::array<uint8_t, 8>> keys(count), values(count);
  std::vector<bs::InitializationEntry> records;
  for (size_t n = 0; n < count; ++n) {
    const uint64_t key = n+1;
    std::memcpy(keys[n].data(), &key, sizeof(key));
    records.push_back({keys[n].data(), values[n].data()});
  }
  auto first = records.begin();
  bs::ScatterInitialRecords(bs::View(table), bs::PlanInitialLoad(8, 32, count), first,
      [](const uint8_t* key) { uint64_t n; std::memcpy(&n, key, sizeof(n)); return bs::KeyWords{n}; });
  Require(first == records.end());
  for (size_t b = 0; b < 8; ++b) Require(bs::Popcount64(table.masks[b]) <= 32);
  // All tag bits initially zero is the maximally concentrated first split.
  ts::OwnedLevelStashes storage(1, 1, layout);
  Require(bs::ButterflyRouteStash<true>(bs::View(table), 1, storage.ptr()));
  Require(storage.Count() == 0);
  std::printf("{\"kind\":\"initial_scatter\",\"records\":%zu,\"first_stage_shed\":0,\"passed\":true}\n", count);
}

void FinalStageBoundary(const bs::Layout& layout, size_t pages, size_t excess) {
  auto main = ts::ZeroedTable(8, layout);
  auto range = ts::ZeroedTable(1, layout);
  ts::OwnedLevelStashes storage(1, pages, layout);
  for (size_t b = 0; b < 8; ++b) {
    const size_t count = b < 4 ? 64 : excess/4+((b-4) < excess%4);
    for (size_t slot = 0; slot < count; ++slot) {
      ts::PlantEntry(layout, main.Bucket(b), slot, ts::FixtureKey(64*b+slot, 8), 1);
      // Already routed low bits agree with this pair's destination index.
      main.Bucket(b)[layout.TagLine(0)*64+slot] = uint8_t(b % 4);
    }
    main.masks[b] = bs::LowMask64(count);
  }
  // All top bits are zero, so all upper records shed at this final stage.
  bs::ResidualOfferSet empty{bs::View(range), bs::PlanResidualRange(0, 3),
                            bs::ResidualDedupRule::kNoDedup, layout.PayloadLines()};
  const bool ok = bs::ButterflyLevelOffersRange<true>(bs::View(main), 2, storage.slots[0], empty, 0, 4);
  Require(ok == (excess <= 64*pages));
  if (ok) Require(storage.Count() == excess);
  std::printf("{\"kind\":\"final_stage\",\"capacity\":%zu,\"excess\":%zu,"
              "\"succeeded\":%s,\"passed\":true}\n", 64*pages, excess, ok ? "true" : "false");
}

int main() {
  const bs::Layout layout{8, 9, 4};
  for (size_t pages : {size_t{1}, size_t{2}})
    for (size_t excess : {size_t{0}, size_t{63}, size_t{64}, size_t{65}, size_t{127}, size_t{128}, size_t{129}, size_t{160}})
      for (bool earlier : {false, true}) Packing(layout, pages, excess, earlier);
  for (size_t count : {size_t{0}, size_t{193}, size_t{256}}) InitialScatter(layout, count);
  for (size_t pages : {size_t{1}, size_t{2}})
    for (size_t excess : {64*pages-1, 64*pages, 64*pages+1}) FinalStageBoundary(layout, pages, excess);
}
