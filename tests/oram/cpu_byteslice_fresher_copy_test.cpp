// The pruned fresher-prefix copy (PlanCopyFresherPrefix with
// CPU_BYTESLICE_PRUNE_FRESHER_COPY).  A rebuild step copies an already-routed
// power-of-two prefix of 2^p buckets under the same nonce and map; the low tag
// bytes that routing has already consumed are dead ("retired") and the pruned
// copy skips writing them.  The test poisons those retired lines in the
// destination and checks, against an unpruned copy, that the poison never
// matters: the masks and every retained byte agree, the published source is
// untouched, and the next cross level, the radix digit read, and a later
// copy-and-retag produce identical results.  Large public extents touch only
// three sample bucket pairs, to keep the test fast.
#include "src/oram/scheduler/cpu_byteslice_subtask_plan.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"

#include <cstdio>
#include <cstring>
#include <vector>

namespace bs = microram::byteslice;
using bs::test_support::Expect;

int main() {
  size_t cases = 0;
  for (unsigned p : {7u, 8u, 15u, 16u})
  for (size_t key_bytes : {size_t{8}, size_t{16}})
  for (unsigned digit : {0u, 1u, 2u})
  for (bool drop : {false, true}) {
    auto tag = bs::PlanRoutingTag(p + 1, digit != 0);
    if (digit == 2) tag = {(p + 8) / 8 + 1, 0};  // reserved digit byte
    const bs::Layout layout{key_bytes, 17, tag.tag_bytes, tag.digit_bits};
    const size_t prefix = size_t{1} << p;
    auto source = bs::Table::Create(prefix, layout);
    auto reference = bs::Table::Create(2 * prefix, layout);
    auto actual = bs::Table::Create(2 * prefix, layout);
    bs::RebuildStepContext ctx;
    ctx.fresher = bs::View(source);
    ctx.drop_unshadowed = drop;
    ctx.route_levels = p + 1;  // deliberately deeper than the copied prefix
    if (digit) {
      ctx.map = {bs::TagMapKind::kRadixDigit, p + 1, 3,
                 static_cast<unsigned>(8 * (layout.tag_bytes - 1) + layout.digit_bits)};
    }
    bs::SubtaskBudget budget;
    budget.copy_buckets = 3;
    std::vector<bs::Subtask> plan;
    bs::PlanCopyFresherPrefix(prefix, budget, &plan);
    size_t covered = 0;
    for (const auto& copy : plan) {
      Expect(copy.begin == covered && copy.levels ==
                 (CPU_BYTESLICE_PRUNE_FRESHER_COPY ? p : 0), "copy prefix contract");
      covered = copy.end;
    }
    Expect(covered == prefix, "copy plan missed buckets");
    for (size_t b : {size_t{3}, prefix / 2 + 1, prefix - 5}) {
      const size_t bytes = layout.BucketBytes();
      std::memset(source.Bucket(b), 0xA5, bytes);
      std::memset(reference.Bucket(b), 0xCD, bytes);
      std::memset(actual.Bucket(b), 0xCD, bytes);
      for (unsigned side = 0; side < 2; ++side) {
        auto* bucket = side ? reference.Bucket(b + prefix) : source.Bucket(b);
        if (side) std::memset(bucket, 0x5A, bytes);
        for (unsigned e = 0; e < 4; ++e) {
          const uint64_t key = 128 * b + 4 * side + e;
          bs::WriteSlotKey(bucket, e, key_bytes, key);
          bucket[64 * layout.MetaLine() + e] = e == 0
              ? bs::kMetaErased | bs::kMetaUnshadowed
              : e == 1 ? bs::kMetaErased : 0;
          uint64_t bits = b | (uint64_t{e & 1} << p);
          if (digit) bits |= (key % 3) << ctx.map.digit_shift;
          for (size_t tb = 0; tb < layout.tag_bytes; ++tb) {
            bucket[64 * layout.TagLine(8 * tb) + e] = bits >> (8 * tb);
          }
        }
      }
      source.masks[b] = 0xF;
      reference.masks[b + prefix] = actual.masks[b + prefix] = 0xF;
      std::memcpy(actual.Bucket(b + prefix), reference.Bucket(b + prefix), bytes);
      const std::vector<uint8_t> saved(source.Bucket(b), source.Bucket(b) + bytes);
      bs::Subtask copy = plan.front();
      copy.begin = b;
      copy.end = b + 1;
      ctx.out = bs::View(actual);
      Expect(bs::RunSubtask<true>(ctx, copy), "pruned copy failed");
      copy.levels = 0;
      ctx.out = bs::View(reference);
      Expect(bs::RunSubtask<true>(ctx, copy), "full copy failed");
      const bool pruning = CPU_BYTESLICE_PRUNE_FRESHER_COPY &&
          (drop || bs::StreamStoresForTable(bs::View(actual)));
      const size_t kept = (layout.EntryBytes() - (pruning ? p / 8 : 0)) * 64;
      Expect(actual.masks[b] == reference.masks[b] &&
                 std::memcmp(actual.Bucket(b), reference.Bucket(b), kept) == 0,
             "copy changed masks or retained bytes");
      for (size_t off = kept; off < bytes; ++off) {
        Expect(actual.Bucket(b)[off] == 0xCD, "copy wrote a retired tag line");
      }
      for (auto* table : {&reference, &actual}) {
        bs::ResidualStash empty;
        empty.entry_bytes = layout.EntryBytes();
        Expect(bs::CrossSourceLevelDedup<true>(bs::View(*table), p, empty, b, b + 1),
               "next cross level failed");
      }
      for (size_t at : {b, b + prefix}) {
        Expect(actual.masks[at] == reference.masks[at] &&
                   std::memcmp(actual.Bucket(at), reference.Bucket(at),
                               64 * layout.RoutedLines(p)) == 0,
               "retired poison reached the next cross level");
        if (digit) {
          alignas(64) uint8_t digits[64];
          _mm512_store_si512(digits, bs::NormalizeDigitLine(
              _mm512_load_si512(actual.Bucket(at) + 64 * layout.DigitLine()),
              layout.digit_bits));
          for (unsigned e = 0; e < 64; ++e) {
            if ((actual.masks[at] >> e) & 1) {
              Expect(digits[e] == bs::ReadSlotKey(actual.Bucket(at), e, key_bytes).w0 % 3,
                     "radix digit lost during copy or cross level");
            }
          }
        }
        auto next_ref = bs::Table::Create(1, layout);
        auto next_actual = bs::Table::Create(1, layout);
        bs::TableView ref_bucket{layout, 1, reference.Bucket(at), reference.masks.get() + at};
        bs::TableView actual_bucket{layout, 1, actual.Bucket(at), actual.masks.get() + at};
        bs::CopyAndRetagRange(bs::View(next_ref), ref_bucket, 0, 1, 0, 91, 73,
                             ctx.map, p + 1);
        bs::CopyAndRetagRange(bs::View(next_actual), actual_bucket, 0, 1, 0, 91, 73,
                             ctx.map, p + 1);
        Expect(next_ref.masks[0] == next_actual.masks[0] &&
                   std::memcmp(next_ref.data.get(), next_actual.data.get(), bytes) == 0,
               "retired poison reached the next rebuild");
      }
      Expect(source.masks[b] == 0xF && std::memcmp(saved.data(), source.Bucket(b), bytes) == 0,
             "copy changed the published source");
      ++cases;
    }
  }
  std::printf("%zu fresher-copy cases passed\n", cases);
}
