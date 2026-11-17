// How wide a routing tag has to be, and where the radix digit sits in it
// (src/oram/table/cpu_byteslice_routing_map.hpp).
//
// Pure arithmetic, and it earns its own binary because THREE statements of one
// rule have to agree and two engines read them:
//
//   - `PlanRoutingTag`, which every hierarchy sizes its tag from;
//   - `RoutingDigitShift`, which says where in that tag the digit lives and is
//     what a kRadixDigit map's `digit_shift` must be;
//   - `RoutingDigitFits`, which says whether a layout can carry a digit at
//     all, and which both the synchronous constructor and the level-arena
//     merge check call before they route anything.
//
// The third exists because a digit that does not fit is NOT detectable
// downstream: the re-tag writes the digit's byte by truncating the mapped tag
// word to eight bits, so a digit with too few bits is a perfectly good digit
// and every entry that needed the missing ones routes to a block that is not
// its own.  For example, with tag_bytes = 1 and digit_bits = 7 a level-arena
// merge completes without error, yet it loses entries and routes survivors to
// the wrong blocks.
//
// What is asserted: the three agree on every layout a `Layout` can express;
// `PlanRoutingTag`'s output is exactly the set they accept; it is MINIMAL, so
// nothing here silently buys a tag byte (a whole 64-byte line per bucket,
// moved at every butterfly level); and the three reserved bits really are the
// width of the widest radix.

#include "src/oram/rebuild/cpu_byteslice_radix_stash.hpp"
#include "src/oram/table/cpu_byteslice_layout.hpp"
#include "src/oram/table/cpu_byteslice_routing_map.hpp"
#include <algorithm>
#include <cstdio>
#include <random>
#include <string>
#include <vector>

#include "src/crypto/hash_primitives.hpp"
#include "src/oram/table/cpu_byteslice_meta.hpp"

namespace bs = microram::byteslice;

namespace {

int failures = 0;

// Counts rather than exits: this file sweeps a small space exhaustively, and
// which layouts disagree is the whole diagnosis.
void Expect(bool value, const std::string& message) {
  if (!value) {
    std::fprintf(stderr, "test failed: %s\n", message.c_str());
    ++failures;
  }
}

// The only two fields of a Layout the tag rules read.
bs::Layout TagLayout(size_t tag_bytes, size_t digit_bits) {
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = tag_bytes;
  layout.digit_bits = digit_bits;
  return layout;
}

std::string At(size_t tag_bytes, size_t digit_bits) {
  return " (tag_bytes=" + std::to_string(tag_bytes) +
         " digit_bits=" + std::to_string(digit_bits) + ")";
}

// The digit's reserved width is the width of the widest radix.  The constant
// cannot say so itself: kMaxRadix lives in rebuild/ and routing_map.hpp is a
// table/ header, so the two are tied together here instead.
void TestTheReservedWidthIsTheWidestRadix() {
  Expect((1u << bs::kRoutingDigitBits) - 1u == bs::kMaxRadix,
         "the reserved digit width does not hold every radix");
  std::printf("  the digit is %u bits, which is radix 1..%u\n",
              bs::kRoutingDigitBits, bs::kMaxRadix);
}

// Three spellings, one predicate, over every layout the type can express.
void TestTheThreeStatementsAgree() {
  size_t fitting = 0;
  for (size_t tag_bytes = 1; tag_bytes <= 8; ++tag_bytes) {
    for (size_t digit_bits = 0; digit_bits < 8; ++digit_bits) {
      const bs::Layout layout = TagLayout(tag_bytes, digit_bits);
      const bool fits = bs::RoutingDigitFits(layout);
      // 1. the arithmetic, spelled out: the three bits at the digit's
      //    position are inside the tag.
      const unsigned shift = bs::RoutingDigitShift(layout);
      Expect(fits == (shift + bs::kRoutingDigitBits <= 8 * tag_bytes),
             "RoutingDigitFits is not its own arithmetic" + At(tag_bytes, digit_bits));
      // 2. the residue rule the Layout comment states.
      Expect(fits == (digit_bits + bs::kRoutingDigitBits <= 8),
             "the digit fits on a different set of digit_bits than the layout "
             "documents" + At(tag_bytes, digit_bits));
      // 3. "this is a layout PlanRoutingTag produces", asked backwards: plan a
      //    tag for an index that fills this one up to its digit.
      const bs::RoutingTagPlan plan =
          bs::PlanRoutingTag(shift, /*has_radix_digit=*/true);
      const bool planned =
          plan.tag_bytes == tag_bytes && plan.digit_bits == digit_bits;
      Expect(fits == planned,
             "the planner and the fit test disagree about this layout" +
                 At(tag_bytes, digit_bits));
      fitting += fits ? 1 : 0;
    }
  }
  // Six residues per width, i.e. digit_bits 0..5, and nothing else.
  Expect(fitting == 8 * 6, "the accepted set is not digit_bits 0..5");
  std::printf("  %zu of %d layouts carry a digit: digit_bits 0..5, any width\n",
              fitting, 8 * 8);
}

// And the planner's own output: it fits, it holds the index bits BELOW the
// digit, and no narrower tag would have done.
void TestThePlanIsSoundAndMinimal() {
  // From 1: a hierarchy routes at least one bit, and PlanRoutingTag(0, false)
  // is the degenerate no-tag answer rather than a layout anything uses.
  for (unsigned index_bits = 1; index_bits <= 61; ++index_bits) {
    const bs::RoutingTagPlan plan =
        bs::PlanRoutingTag(index_bits, /*has_radix_digit=*/true);
    const bs::Layout layout = TagLayout(plan.tag_bytes, plan.digit_bits);
    const std::string where = " (index_bits=" + std::to_string(index_bits) + ")";
    Expect(bs::RoutingDigitFits(layout),
           "a planned tag cannot carry its own digit" + where);
    // The index field is everything below the digit, so the route may use
    // `index_bits` of it without touching the digit.
    Expect(bs::RoutingDigitShift(layout) >= index_bits,
           "a planned tag puts the digit inside the index bits" + where);
    // MINIMAL: one byte narrower cannot hold both, at any digit position.
    // A tag byte is a 64-byte line per bucket that every butterfly level
    // moves and pruning can never retire, so "round it up just in case" is
    // not free.
    if (plan.tag_bytes > 1) {
      for (size_t digit_bits = 0; digit_bits < 8; ++digit_bits) {
        const bs::Layout narrower = TagLayout(plan.tag_bytes - 1, digit_bits);
        Expect(!bs::RoutingDigitFits(narrower) ||
                   bs::RoutingDigitShift(narrower) < index_bits,
               "a narrower tag would have held this index and its digit" +
                   where + At(plan.tag_bytes - 1, digit_bits));
      }
    }
    // RoutingDigitPacks is the rule for WHICH FORM was planned...
    const size_t index_bytes = (index_bits + 7) / 8;
    const size_t packed = (index_bits + bs::kRoutingDigitBits + 7) / 8;
    const size_t reserved = index_bytes + 1;
    Expect(plan.tag_bytes == (bs::RoutingDigitPacks(index_bits) ? packed
                                                                : reserved),
           "the planned width is not the form RoutingDigitPacks chose" + where);
    // ...and packing is worth a byte on exactly the residues 1..5.  At 0 the
    // digit starts a fresh byte and the two forms coincide; at 6 and 7 the
    // reserved byte is the same WIDTH a packed tag would have been, which is
    // why refusing to pack there costs nothing and is not merely allowed.
    Expect((packed < reserved) ==
               (index_bits % 8 >= 1 && index_bits % 8 <= 8 - bs::kRoutingDigitBits),
           "packing saves a byte on a different set of index widths" + where);
    Expect(bs::RoutingDigitPacks(index_bits)
               ? plan.digit_bits == index_bits % 8
               : (plan.tag_bytes == index_bytes + 1 && plan.digit_bits == 0),
           "the planned form is neither packed nor reserved" + where);
    // B = 2 has no digit at all: the tag is the index bits and nothing more.
    const bs::RoutingTagPlan binary =
        bs::PlanRoutingTag(index_bits, /*has_radix_digit=*/false);
    Expect(binary.tag_bytes == index_bytes && binary.digit_bits == 0,
           "a binary hierarchy's tag is not its index bytes" + where);
  }
  std::printf("  plans for 0..61 index bits: sound, minimal, packed when it "
              "pays\n");
}

// A RAW ROUTE DEEPER THAN THE INDEX (the level arena's binary top, which
// routes K + log2 D raw bits over a hierarchy whose digit-bearing tables
// route K; the top routes one binary butterfly over all of its D blocks, so it
// needs no radix-D kernel).  Three claims:
// it never narrows the tag; wherever a digit is reserved it never widens it
// either, for up to three extra bits, because ceil((K+3)/8) bytes are already
// there in every residue; and without a digit it widens the tag to exactly
// what the route needs and no more.
void TestARawRouteFitsWhereADigitIs() {
  for (unsigned index_bits = 1; index_bits <= 58; ++index_bits) {
    const std::string where = " (index_bits=" + std::to_string(index_bits) + ")";
    const bs::RoutingTagPlan digit =
        bs::PlanRoutingTag(index_bits, /*has_radix_digit=*/true);
    const bs::RoutingTagPlan binary =
        bs::PlanRoutingTag(index_bits, /*has_radix_digit=*/false);
    for (unsigned extra = 0; extra <= bs::kRoutingDigitBits; ++extra) {
      const unsigned route = index_bits + extra;
      const bs::RoutingTagPlan with_digit =
          bs::PlanRoutingTag(index_bits, true, route);
      Expect(with_digit.tag_bytes == digit.tag_bytes &&
                 with_digit.digit_bits == digit.digit_bits,
             "a raw route of up to three bits past the index changed a tag "
             "that already reserves a digit" + where);
      Expect(8 * with_digit.tag_bytes >= route,
             "a digit-bearing tag does not hold the raw route" + where);
      const bs::RoutingTagPlan without =
          bs::PlanRoutingTag(index_bits, false, route);
      Expect(without.tag_bytes == std::max<size_t>(binary.tag_bytes,
                                                   (route + 7) / 8) &&
                 without.digit_bits == 0,
             "a raw route widened a digitless tag to other than what it "
             "needs" + where);
    }
    // A shallower raw route is no route at all.
    const bs::RoutingTagPlan shallow =
        bs::PlanRoutingTag(index_bits, true, index_bits > 1 ? index_bits - 1 : 0);
    Expect(shallow.tag_bytes == digit.tag_bytes,
           "a raw route no deeper than the index changed the tag" + where);
  }
  std::printf("  a raw route past the index fits wherever a digit is "
              "reserved, and widens a digitless tag exactly\n");
}

// The low `bits` bits of a slot's stored tag: bit b in bit b % 8 of line
// TagLine(b).
uint64_t StoredTagBits(const bs::Layout& layout, const uint8_t* bucket,
                       size_t slot, unsigned bits) {
  uint64_t tag = 0;
  for (unsigned b = 0; b < bits; ++b) {
    const uint8_t byte = bucket[layout.TagLine(b) * bs::kBucketCapacity + slot];
    tag |= uint64_t{static_cast<uint8_t>((byte >> (b & 7)) & 1)} << b;
  }
  return tag;
}

// ModSmallLanes<M> against v % M on every word of `values`.
template <unsigned M>
size_t CheckModLanes(const std::vector<uint64_t>& values) {
  size_t checked = 0;
  for (size_t i = 0; i < values.size(); i += 8) {
    alignas(64) uint64_t in[8];
    alignas(64) uint64_t out[8];
    for (size_t j = 0; j < 8; ++j) in[j] = values[(i + j) % values.size()];
    _mm512_store_si512(reinterpret_cast<void*>(out),
                       bs::ModSmallLanes<M>(_mm512_load_si512(
                           reinterpret_cast<const void*>(in))));
    for (size_t j = 0; j < 8; ++j) {
      if (out[j] != in[j] % M) {
        Expect(false, "ModSmallLanes<" + std::to_string(M) + ">(" +
                          std::to_string(in[j]) + ") = " +
                          std::to_string(out[j]));
      }
      ++checked;
    }
  }
  return checked;
}

// THE VECTOR MODULUS IS EXACT.  Its reductions are exact only below 2^16
// (the byte sums reach 2040 for 3, 5 and 6, and the weighted sum 4845 for 7),
// so beside every word below 2^16 and random 64-bit ones, each reachable sum
// is hit on purpose, both at its greedy byte spelling and at its mirror.
void TestModSmallLanesIsExact() {
  std::vector<uint64_t> values;
  for (uint64_t v = 0; v < (uint64_t{1} << 16); ++v) values.push_back(v);
  const auto spell = [](unsigned sum, const unsigned (&order)[8],
                        const unsigned (&weight)[8]) {
    uint64_t v = 0;
    for (unsigned i = 0; i < 8; ++i) {
      const unsigned byte = std::min(255u, sum / weight[order[i]]);
      sum -= byte * weight[order[i]];
      v |= uint64_t{byte} << (8 * order[i]);
    }
    return v;
  };
  const unsigned ones[8] = {1, 1, 1, 1, 1, 1, 1, 1};
  const unsigned sevens[8] = {1, 4, 2, 1, 4, 2, 1, 4};  // 256^i mod 7
  const unsigned forward[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  const unsigned backward[8] = {7, 6, 5, 4, 3, 2, 1, 0};
  const unsigned by_weight[8] = {1, 4, 7, 2, 5, 0, 3, 6};  // 4s, 2s, 1s
  for (unsigned sum = 0; sum <= 8 * 255; ++sum) {
    values.push_back(spell(sum, forward, ones));
    values.push_back(spell(sum, backward, ones));
  }
  for (unsigned sum = 0; sum <= 19 * 255; ++sum) {
    const uint64_t v = spell(sum, by_weight, sevens);
    unsigned weighted = 0;
    for (unsigned i = 0; i < 8; ++i) {
      weighted += sevens[i] * static_cast<unsigned>((v >> (8 * i)) & 0xFF);
    }
    Expect(weighted == sum, "the weighted spelling missed its sum");
    values.push_back(v);
  }
  std::mt19937_64 rng(0x5AD);
  for (int i = 0; i < (1 << 16); ++i) values.push_back(rng());
  for (uint64_t v : {~uint64_t{0}, uint64_t{1} << 63, ~(uint64_t{1} << 63)}) {
    values.push_back(v);
  }
  size_t checked = 0;
  checked += CheckModLanes<1>(values);
  checked += CheckModLanes<2>(values);
  checked += CheckModLanes<3>(values);
  checked += CheckModLanes<4>(values);
  checked += CheckModLanes<5>(values);
  checked += CheckModLanes<6>(values);
  checked += CheckModLanes<7>(values);
  checked += CheckModLanes<8>(values);
  std::printf("  vector modulus: %zu words exact mod 1..8, every reachable "
              "byte sum included\n", checked);
}

// THE VECTOR INDEX MAP IS THE SCALAR ONE (ApplyRoutingIndexMapToTags against
// ApplyRoutingIndexMap, the per-entry function every probe uses), for both
// modular kinds, every modulus 1..8, low_bits across the word and each
// digit_shift a layout can give it.  Tags: every word below 2^16, every
// 12-bit field value placed just above low_bits over random low bits, and
// random 64-bit words.
void TestVectorIndexMapIsTheScalarOne() {
  std::mt19937_64 rng(0x1DE);
  size_t checked = 0, maps = 0;
  const auto run = [&](const bs::RoutingIndexMap& map,
                       const std::vector<uint64_t>& words) {
    const std::string where =
        std::string(map.kind == bs::TagMapKind::kRadixDigit ? " radix"
                                                            : " fold") +
        " m=" + std::to_string(map.modulus) +
        " low_bits=" + std::to_string(map.low_bits) +
        " digit_shift=" + std::to_string(map.digit_shift);
    size_t bad = 0;
    for (size_t i = 0; i < words.size(); i += bs::kBucketCapacity) {
      alignas(64) uint64_t in[bs::kBucketCapacity];
      alignas(64) uint64_t out[bs::kBucketCapacity];
      __m512i tags[8];
      for (size_t j = 0; j < bs::kBucketCapacity; ++j) {
        in[j] = words[(i + j) % words.size()];
      }
      for (int r = 0; r < 8; ++r) {
        tags[r] = _mm512_load_si512(reinterpret_cast<const void*>(in + 8 * r));
      }
      bs::ApplyRoutingIndexMapToTags(map, tags);
      for (int r = 0; r < 8; ++r) {
        _mm512_store_si512(reinterpret_cast<void*>(out + 8 * r), tags[r]);
      }
      for (size_t j = 0; j < bs::kBucketCapacity; ++j) {
        bad += out[j] != bs::ApplyRoutingIndexMap(map, in[j]) ? 1 : 0;
        ++checked;
      }
    }
    Expect(bad == 0, std::to_string(bad) + " tags mapped differently" + where);
    ++maps;
  };
  for (unsigned low_bits : {0u, 1u, 2u, 3u, 5u, 7u, 8u, 9u, 12u, 13u, 15u, 16u,
                            17u, 21u, 24u, 29u, 31u, 32u, 40u, 47u, 48u, 55u,
                            56u, 60u, 63u}) {
    std::vector<uint64_t> words;
    for (uint64_t v = 0; v < (uint64_t{1} << 16); ++v) words.push_back(v);
    for (uint64_t v = 0; v < (uint64_t{1} << 12); ++v) {
      words.push_back((v << low_bits) | (rng() & bs::LowMask64(low_bits)));
    }
    for (int i = 0; i < 8192; ++i) words.push_back(rng());
    // Where a layout routing low_bits index bits puts the digit, and the
    // compact probe form (digit_shift == low_bits).
    std::vector<unsigned> shifts = {low_bits};
    if (low_bits <= 61) {
      const bs::RoutingTagPlan plan = bs::PlanRoutingTag(low_bits, true);
      const unsigned planned = bs::RoutingDigitShift(
          TagLayout(plan.tag_bytes, plan.digit_bits));
      if (planned != low_bits && planned <= 61) shifts.push_back(planned);
    }
    for (unsigned m = 1; m <= 8; ++m) {
      for (unsigned shift : shifts) {
        if (shift > 61) continue;
        bs::RoutingIndexMap radix;
        radix.kind = bs::TagMapKind::kRadixDigit;
        radix.low_bits = low_bits;
        radix.modulus = m;
        radix.digit_shift = shift;
        run(radix, words);
      }
      // A fold's block (at most m) sits at low_bits; the scalar shift is
      // defined below 61.
      if (low_bits <= 60) {
        bs::RoutingIndexMap fold;
        fold.kind = bs::TagMapKind::kFoldDuplicate;
        fold.low_bits = low_bits;
        fold.modulus = m;
        run(fold, words);
      }
    }
  }
  std::printf("  vector index map: %zu tags under %zu maps, all equal to the "
              "scalar map\n", checked, maps);
}

// The byte-level re-tag the kernels must reproduce, spelled per entry: tag
// byte tb of the mapped word to line TagOffset() + tag_bytes-1-tb for
// tb < routed, and the most significant byte to TagOffset() when write_digit.
void OracleTagLines(const bs::Layout& layout, const bs::RoutingIndexMap& map,
                    size_t routed, bool write_digit, const uint8_t* keys,
                    size_t slot, uint64_t nonce_lo, uint64_t nonce_hi,
                    uint8_t* bucket, size_t dest_slot) {
  const bs::KeyWords k = bs::ReadSlotKey(keys, slot, layout.key_bytes);
  const uint64_t w = bs::ApplyRoutingIndexMap(
      map, microram::crypto::AesCtrTagU128WordsHost(nonce_lo, nonce_hi, k.w0,
                                                    k.w1));
  const size_t base = layout.TagOffset();
  for (size_t tb = 0; tb < routed; ++tb) {
    bucket[(base + layout.tag_bytes - 1 - tb) * bs::kBucketCapacity +
           dest_slot] = static_cast<uint8_t>(w >> (8 * tb));
  }
  if (write_digit) {
    bucket[base * bs::kBucketCapacity + dest_slot] =
        static_cast<uint8_t>(w >> (8 * (layout.tag_bytes - 1)));
  }
}

void FillRandom(std::mt19937_64& rng, uint8_t* p, size_t n) {
  for (size_t i = 0; i < n; ++i) p[i] = static_cast<uint8_t>(rng());
}

// THE RE-TAG PATHS WRITE EXACTLY THE ORACLE'S BYTES: whole images, so a byte
// written where it should not be (a slot past per_bucket, a line past the
// routed ones) fails as surely as a wrong tag.  In place, fused with a copy,
// and fused with the dense scatter at every per_bucket, over tag widths
// 1..8, every routed width, and the raw, radix and fold maps; and the
// payload-only dense scatter in place.
void TestRetagPathsWriteTheOracleBytes() {
  const uint64_t nonce_lo = 0x2345, nonce_hi = 0x6789;
  std::mt19937_64 rng(0xB17E);
  size_t images = 0;
  for (size_t key_bytes : {size_t{3}, size_t{8}, size_t{16}}) {
    for (size_t tag_bytes = 1; tag_bytes <= 8; ++tag_bytes) {
      bs::Layout layout;
      layout.key_bytes = key_bytes;
      layout.value_bytes = 5;
      layout.tag_bytes = tag_bytes;
      const size_t bucket_bytes = layout.BucketBytes();
      // Maps: raw, and a radix and a fold map over low bits that fit.
      std::vector<bs::RoutingIndexMap> maps(1);
      for (unsigned m : {3u, 5u, 6u, 7u}) {
        bs::RoutingIndexMap radix;
        radix.kind = bs::TagMapKind::kRadixDigit;
        radix.low_bits = static_cast<unsigned>(8 * tag_bytes - 3 - (m & 1));
        radix.modulus = m;
        radix.digit_shift = static_cast<unsigned>(8 * (tag_bytes - 1));
        if (radix.low_bits > radix.digit_shift) radix.low_bits = radix.digit_shift;
        maps.push_back(radix);
        bs::RoutingIndexMap fold;
        fold.kind = bs::TagMapKind::kFoldDuplicate;
        fold.low_bits = static_cast<unsigned>(4 * tag_bytes - 1);
        fold.modulus = m;
        maps.push_back(fold);
      }
      const size_t buckets = 3;
      bs::Table src = bs::Table::Create(buckets, layout);
      FillRandom(rng, src.data.get(), buckets * bucket_bytes);
      for (size_t b = 0; b < buckets; ++b) src.masks[b] = rng();
      for (const bs::RoutingIndexMap& map : maps) {
        for (unsigned route_levels = 0; route_levels <= 8 * tag_bytes;
             route_levels += 4) {
          const size_t routed = bs::RoutedTagBytes(layout, route_levels);
          const bool write_digit =
              bs::RetagWritesDigitLine(layout, map, routed);
          const std::string where =
              " (key " + std::to_string(key_bytes) + ", tag " +
              std::to_string(tag_bytes) + ", kind " +
              std::to_string(static_cast<int>(map.kind)) + ", m " +
              std::to_string(map.modulus) + ", route " +
              std::to_string(route_levels) + ")";
          // In place.
          {
            bs::Table t = bs::Table::Create(buckets, layout);
            std::copy_n(src.data.get(), buckets * bucket_bytes, t.data.get());
            std::vector<uint8_t> want(src.data.get(),
                                      src.data.get() + buckets * bucket_bytes);
            for (size_t b = 0; b < buckets; ++b) {
              for (size_t s = 0; s < bs::kBucketCapacity; ++s) {
                OracleTagLines(layout, map, routed, write_digit, src.Bucket(b),
                               s, nonce_lo, nonce_hi,
                               want.data() + b * bucket_bytes, s);
              }
            }
            bs::ComputeRoutingTags(bs::View(t), nonce_lo, nonce_hi, map,
                                   route_levels);
            Expect(std::equal(want.begin(), want.end(), t.data.get()),
                   "ComputeRoutingTags wrote other bytes" + where);
            ++images;
          }
          // Fused with a copy, over a canary destination.
          {
            bs::Table t = bs::Table::Create(buckets, layout);
            FillRandom(rng, t.data.get(), buckets * bucket_bytes);
            std::vector<uint8_t> want(t.data.get(),
                                      t.data.get() + buckets * bucket_bytes);
            const size_t copy_lines = layout.EntryBytes() - routed;
            for (size_t b = 0; b < buckets; ++b) {
              std::copy_n(src.Bucket(b), copy_lines * bs::kBucketCapacity,
                          want.data() + b * bucket_bytes);
              for (size_t s = 0; s < bs::kBucketCapacity; ++s) {
                OracleTagLines(layout, map, routed, write_digit, src.Bucket(b),
                               s, nonce_lo, nonce_hi,
                               want.data() + b * bucket_bytes, s);
              }
            }
            bs::CopyAndRetagRange(bs::View(t), bs::View(src), 0, buckets, 0,
                                  nonce_lo, nonce_hi, map, route_levels);
            Expect(std::equal(want.begin(), want.end(), t.data.get()) &&
                       std::equal(src.masks.get(), src.masks.get() + buckets,
                                  t.masks.get()),
                   "CopyAndRetagRange wrote other bytes" + where);
            ++images;
          }
          // Fused with the dense scatter, at every per_bucket.
          for (size_t per = 1; per <= bs::kBucketCapacity; per *= 2) {
            const size_t fanout = bs::kBucketCapacity / per;
            bs::Table t = bs::Table::Create(fanout, layout);
            FillRandom(rng, t.data.get(), fanout * bucket_bytes);
            for (size_t b = 0; b < fanout; ++b) t.masks[b] = rng();
            std::vector<uint8_t> want(t.data.get(),
                                      t.data.get() + fanout * bucket_bytes);
            const uint8_t* source = src.Bucket(1);
            for (size_t s = 0; s < bs::kBucketCapacity; ++s) {
              uint8_t* dest = want.data() + (s / per) * bucket_bytes;
              for (size_t line = 0; line < layout.PayloadLines(); ++line) {
                dest[line * bs::kBucketCapacity + s % per] =
                    source[line * bs::kBucketCapacity + s];
              }
              OracleTagLines(layout, map, routed, write_digit, source, s,
                             nonce_lo, nonce_hi, dest, s % per);
            }
            bs::ScatterAndRetagDenseBucket(
                source, src.masks[1], t.data.get(), t.masks.get(), per, layout,
                microram::crypto::PackAesCtrHighWord(nonce_lo, nonce_hi), map,
                routed, write_digit, bs::DefaultAesTagKeys());
            bool masks_ok = true;
            for (size_t b = 0; b < fanout; ++b) {
              masks_ok &= t.masks[b] == ((src.masks[1] >> (b * per)) &
                                         bs::LowMask64(
                                             static_cast<unsigned>(per)));
            }
            Expect(std::equal(want.begin(), want.end(), t.data.get()) &&
                       masks_ok,
                   "ScatterAndRetagDenseBucket wrote other bytes at per " +
                       std::to_string(per) + where);
            ++images;
            // The payload-only scatter, IN PLACE (the source is destination
            // bucket 0), over the same canary.
            if (map.kind != bs::TagMapKind::kRaw || route_levels != 0) continue;
            bs::Table u = bs::Table::Create(fanout, layout);
            FillRandom(rng, u.data.get(), fanout * bucket_bytes);
            std::copy_n(source, bucket_bytes, u.data.get());
            std::vector<uint8_t> in_place(u.data.get(),
                                          u.data.get() + fanout * bucket_bytes);
            for (size_t s = 0; s < bs::kBucketCapacity; ++s) {
              for (size_t line = 0; line < layout.PayloadLines(); ++line) {
                in_place[(s / per) * bucket_bytes + line * bs::kBucketCapacity +
                         s % per] = source[line * bs::kBucketCapacity + s];
              }
            }
            bs::ScatterDenseBucket(u.Bucket(0), src.masks[1], u.data.get(),
                                   u.masks.get(), per, layout.EntryBytes(),
                                   layout.PayloadLines());
            Expect(std::equal(in_place.begin(), in_place.end(), u.data.get()),
                   "ScatterDenseBucket in place wrote other bytes at per " +
                       std::to_string(per) + where);
            ++images;
          }
        }
      }
    }
  }
  std::printf("  re-tag paths: %zu whole images equal the per-entry oracle "
              "(in place, fused copy, dense scatter at every per_bucket)\n",
              images);
}

// STREAMED COPY-AND-RE-TAG, for real: a destination past the streaming
// threshold (StreamStoresForTable), whose image must equal a cached run's
// and the oracle's.  The small tables above never stream.
void TestStreamedCopyAndRetagMatches() {
  const uint64_t nonce_lo = 0x77, nonce_hi = 0x99;
  std::mt19937_64 rng(0x57EA);
  bs::Layout layout;
  layout.key_bytes = 8;
  layout.value_bytes = 8;
  layout.tag_bytes = 4;
  const size_t bucket_bytes = layout.BucketBytes();
  size_t buckets = 1;
  while (buckets * bucket_bytes < 2 * bs::StreamStoreMinBytes()) buckets *= 2;
  bs::RoutingIndexMap map;
  map.kind = bs::TagMapKind::kRadixDigit;
  map.low_bits = 20;
  map.modulus = 7;
  map.digit_shift = bs::RoutingDigitShift(layout);
  bs::Table src = bs::Table::Create(buckets, layout);
  FillRandom(rng, src.data.get(), buckets * bucket_bytes);
  for (size_t b = 0; b < buckets; ++b) src.masks[b] = rng();
  for (unsigned route_levels : {12u, 20u, 32u}) {
    bs::Table streamed = bs::Table::Create(buckets, layout);
    bs::Table cached = bs::Table::Create(buckets, layout);
    Expect(bs::StreamStoresForTable(bs::View(streamed)),
           "the large table does not stream");
    bs::CopyAndRetagRange(bs::View(streamed), bs::View(src), 0, buckets, 0,
                          nonce_lo, nonce_hi, map, route_levels);
    bs::CopyAndRetagRange(bs::View(cached), bs::View(src), 0, buckets, 0,
                          nonce_lo, nonce_hi, map, route_levels,
                          bs::DefaultAesTagKeys(), /*cached_stores=*/true);
    Expect(std::equal(cached.data.get(),
                      cached.data.get() + buckets * bucket_bytes,
                      streamed.data.get()),
           "the streamed copy-and-re-tag differs from the cached one at route " +
               std::to_string(route_levels));
    const size_t routed = bs::RoutedTagBytes(layout, route_levels);
    const bool write_digit = bs::RetagWritesDigitLine(layout, map, routed);
    size_t bad = 0;
    for (size_t b = 0; b < buckets; b += 97) {
      std::vector<uint8_t> want(src.Bucket(b), src.Bucket(b) + bucket_bytes);
      for (size_t s = 0; s < bs::kBucketCapacity; ++s) {
        OracleTagLines(layout, map, routed, write_digit, src.Bucket(b), s,
                       nonce_lo, nonce_hi, want.data(), s);
      }
      bad += std::equal(want.begin(), want.end(), streamed.Bucket(b)) ? 0 : 1;
    }
    Expect(bad == 0, std::to_string(bad) + " streamed buckets differ from "
                     "the oracle at route " + std::to_string(route_levels));
  }
  std::printf("  streamed copy-and-re-tag over %zu buckets equals the cached "
              "one and the oracle\n", buckets);
}

}  // namespace

int main() {
  std::printf("routing tag width and digit placement\n");
  TestTheReservedWidthIsTheWidestRadix();
  TestTheThreeStatementsAgree();
  TestThePlanIsSoundAndMinimal();
  TestARawRouteFitsWhereADigitIs();
  TestModSmallLanesIsExact();
  TestVectorIndexMapIsTheScalarOne();
  TestRetagPathsWriteTheOracleBytes();
  TestStreamedCopyAndRetagMatches();
  if (failures != 0) {
    std::fprintf(stderr, "%d routing tag checks failed\n", failures);
    return 1;
  }
  std::printf("routing tag: OK\n");
  return 0;
}
