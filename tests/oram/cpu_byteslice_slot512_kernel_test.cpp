// The 512-slot MergeSplit (benchmarks/oram/cpu_byteslice_slot512_kernel.hpp)
// against a scalar reference of its contract.
//
// THE CONTRACT.  `first`'s records stay at their slot on the side their tag bit
// selects (side 0 = first's memory, side 1 = second's); `second`'s records of a
// direction fill that side's free slots in slot order; a surplus is an overflow
// and the call returns false with nothing modified.  Output slots holding no
// record are zero.  The reference is written slot by slot, with no mask
// arithmetic.  Cases cover empty and full buckets, one-sided tags, loads that
// overflow exactly and by one, byte lines outside `lines` (left unchanged), and
// a tag line inside and outside the routed prefix.

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <random>
#include <string>
#include <vector>

#include "benchmarks/oram/cpu_byteslice_slot512_kernel.hpp"

namespace {

namespace bs = microram::byteslice;
namespace s5 = microram::byteslice::slot512;

int failures = 0;

void Expect(bool value, const std::string& message) {
  if (!value) {
    if (failures < 20) std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

constexpr size_t kSlots = s5::kSlots;

struct Pair {
  size_t lines;  // byte lines allocated
  bs::Aligned64Ptr data_a, data_b;
  uint64_t mask_a[s5::kWords] = {}, mask_b[s5::kWords] = {};
  explicit Pair(size_t n) : lines(n) {
    data_a = bs::AllocateAligned64(lines * kSlots);
    data_b = bs::AllocateAligned64(lines * kSlots);
  }
  uint8_t* a() { return data_a.get(); }
  uint8_t* b() { return data_b.get(); }
};

bool Has(const uint64_t* mask, size_t slot) { return (mask[slot / 64] >> (slot % 64)) & 1; }
void Set(uint64_t* mask, size_t slot) { mask[slot / 64] |= uint64_t{1} << (slot % 64); }

// Fills a bucket: `load` random slots occupied; every byte of every line random
// (tag lines included), so unoccupied slots carry junk the kernel must not use.
void Fill(uint8_t* bucket, uint64_t* mask, size_t lines, size_t load, std::mt19937_64& rng) {
  for (size_t i = 0; i < lines * kSlots; ++i) bucket[i] = static_cast<uint8_t>(rng());
  std::memset(mask, 0, s5::kWords * sizeof(uint64_t));
  std::vector<size_t> slots(kSlots);
  for (size_t i = 0; i < kSlots; ++i) slots[i] = i;
  for (size_t i = 0; i < load; ++i) {
    std::swap(slots[i], slots[i + rng() % (kSlots - i)]);
    Set(mask, slots[i]);
  }
}

// Forces the tag bit of every occupied slot of one bucket (0, 1) or leaves it
// random (-1).
void ForceTags(uint8_t* bucket, const uint64_t* mask, size_t tag_line, unsigned bit, int force) {
  if (force < 0) return;
  for (size_t s = 0; s < kSlots; ++s) {
    uint8_t& b = bucket[tag_line * kSlots + s];
    b = static_cast<uint8_t>((b & ~(1u << (bit & 7))) | (static_cast<unsigned>(force) << (bit & 7)));
  }
  (void)mask;
}

struct Result {
  bool ok = true;
  std::vector<uint8_t> a, b;
  uint64_t mask_a[s5::kWords] = {}, mask_b[s5::kWords] = {};
};

// Slot-by-slot reference.
Result Reference(const Pair& in_, size_t lines, size_t tag_line, unsigned bit) {
  const uint8_t* fa = in_.data_a.get();
  const uint8_t* sb = in_.data_b.get();
  const size_t total = in_.lines;
  Result r;
  r.a.assign(fa, fa + total * kSlots);
  r.b.assign(sb, sb + total * kSlots);
  std::memcpy(r.mask_a, in_.mask_a, sizeof(r.mask_a));
  std::memcpy(r.mask_b, in_.mask_b, sizeof(r.mask_b));
  const auto dir = [&](const uint8_t* bucket, size_t s) {
    return (bucket[tag_line * kSlots + s] >> (bit & 7)) & 1;
  };
  // out[side][slot] = (occupied, source: 0 = first, 1 = second, slot)
  struct Cell { bool used = false; int from = 0; size_t slot = 0; };
  std::vector<Cell> out[2] = {std::vector<Cell>(kSlots), std::vector<Cell>(kSlots)};
  for (size_t s = 0; s < kSlots; ++s) {
    if (Has(in_.mask_a, s)) out[dir(fa, s)][s] = {true, 0, s};
  }
  for (int side = 0; side < 2; ++side) {
    size_t next = 0;
    for (size_t s = 0; s < kSlots; ++s) {
      if (!Has(in_.mask_b, s) || static_cast<int>(dir(sb, s)) != side) continue;
      while (next < kSlots && out[side][next].used) ++next;
      if (next == kSlots) {
        r.ok = false;  // surplus: nothing modified
        r.a.assign(fa, fa + total * kSlots);
        r.b.assign(sb, sb + total * kSlots);
        std::memcpy(r.mask_a, in_.mask_a, sizeof(r.mask_a));
        std::memcpy(r.mask_b, in_.mask_b, sizeof(r.mask_b));
        return r;
      }
      out[side][next] = {true, 1, s};
    }
  }
  for (size_t line = 0; line < lines; ++line) {
    for (int side = 0; side < 2; ++side) {
      uint8_t* dst = (side == 0 ? r.a.data() : r.b.data()) + line * kSlots;
      for (size_t s = 0; s < kSlots; ++s) {
        const Cell& c = out[side][s];
        dst[s] = !c.used ? 0 : c.from == 0 ? fa[line * kSlots + c.slot] : sb[line * kSlots + c.slot];
      }
    }
  }
  std::memset(r.mask_a, 0, sizeof(r.mask_a));
  std::memset(r.mask_b, 0, sizeof(r.mask_b));
  for (size_t s = 0; s < kSlots; ++s) {
    if (out[0][s].used) Set(r.mask_a, s);
    if (out[1][s].used) Set(r.mask_b, s);
  }
  return r;
}

void RunCase(const std::string& name, std::mt19937_64& rng, size_t load_a, size_t load_b,
             int force_a, int force_b, size_t total_lines, size_t lines, size_t tag_line,
             unsigned bit) {
  Pair p(total_lines);
  Fill(p.a(), p.mask_a, total_lines, load_a, rng);
  Fill(p.b(), p.mask_b, total_lines, load_b, rng);
  ForceTags(p.a(), p.mask_a, tag_line, bit, force_a);
  ForceTags(p.b(), p.mask_b, tag_line, bit, force_b);
  const Result want = Reference(p, lines, tag_line, bit);
  const bool got = s5::MergeSplit(p.a(), p.b(), p.mask_a, p.mask_b, lines, tag_line, bit);
  Expect(got == want.ok, name + ": overflow verdict " + std::to_string(got) + " != " +
                             std::to_string(want.ok));
  Expect(std::memcmp(p.mask_a, want.mask_a, sizeof(p.mask_a)) == 0, name + ": first mask");
  Expect(std::memcmp(p.mask_b, want.mask_b, sizeof(p.mask_b)) == 0, name + ": second mask");
  Expect(std::memcmp(p.a(), want.a.data(), total_lines * kSlots) == 0, name + ": first bytes");
  Expect(std::memcmp(p.b(), want.b.data(), total_lines * kSlots) == 0, name + ": second bytes");
}

}  // namespace

int main() {
  std::mt19937_64 rng(0x512512);
  // Random loads and tags, tag line inside / outside the routed prefix, several
  // bits (the probe is bit & 7 of the line).
  for (int round = 0; round < 400; ++round) {
    const size_t load_a = rng() % (kSlots + 1), load_b = rng() % (kSlots + 1);
    const size_t total = 2 + rng() % 4;
    const size_t lines = 1 + rng() % total;
    const size_t tag_line = rng() % total;  // may be >= lines: read, not routed
    RunCase("random " + std::to_string(round), rng, load_a, load_b, -1, -1, total, lines,
            tag_line, static_cast<unsigned>(rng() % 16));
  }
  // The production shape: load 0.5 (the case the benchmark runs).
  for (int round = 0; round < 100; ++round) {
    RunCase("half " + std::to_string(round), rng, 256, 256, -1, -1, 5, 5, 4, 0);
  }
  // Edges: empty, one-sided, full, and the overflow boundary.
  RunCase("both empty", rng, 0, 0, -1, -1, 3, 3, 2, 0);
  RunCase("first empty", rng, 0, 300, -1, -1, 3, 3, 2, 1);
  RunCase("second empty", rng, 300, 0, -1, -1, 3, 3, 2, 2);
  RunCase("all side 0", rng, 256, 256, 0, 0, 3, 3, 2, 0);
  RunCase("all side 1", rng, 256, 256, 1, 1, 3, 3, 2, 0);
  RunCase("first 1 second 0", rng, 400, 400, 1, 0, 3, 3, 2, 0);
  RunCase("full buckets", rng, 512, 512, -1, -1, 3, 3, 2, 0);
  RunCase("full first, one-sided second", rng, 512, 100, 0, 0, 3, 3, 2, 0);  // side 0 is already full: second overflows
  // Overflow exactly at the boundary: first all on side 0 with 411 records,
  // second all on side 0 with 101: 512 total fits; 102 does not.
  RunCase("boundary fits", rng, 411, 101, 0, 0, 3, 3, 2, 0);
  RunCase("boundary overflows", rng, 411, 102, 0, 0, 3, 3, 2, 0);
  RunCase("overflow on side 1", rng, 450, 200, 1, 1, 3, 3, 2, 5);
  if (failures == 0) std::printf("slot512 kernel: all cases match the reference\n");
  return failures == 0 ? 0 : 1;
}
