// Unit test for the benchmark statistics and checkpoint codec
// (src/oram/support/benchmark_checkpoint.hpp): latency histograms, overflow
// handling, per-block checkpoint deltas whose merge equals the whole trial,
// the CRC and the binary checkpoint format.  With --write-fixture DIR it also
// writes the two checkpoint files that check_aggregate_cli.py feeds to the
// reducer.
#include "src/oram/support/benchmark_checkpoint.hpp"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <memory>
#include <random>
#include <sstream>

namespace {
using namespace oram_bench;
void Check(bool condition, const char* message) {
  if (!condition) throw std::runtime_error(message);
}
template<class Fn> void Reject(Fn fn) {
  bool failed = false;
  try { fn(); } catch (const std::invalid_argument&) { failed = true; }
  catch (const std::overflow_error&) { failed = true; }
  Check(failed, "invalid input was accepted");
}
void Same(const Histogram& a, const Histogram& b) {
  Check(a.bins() == b.bins() && a.count() == b.count() && a.sum_ns() == b.sum_ns() &&
        a.minimum_ns() == b.minimum_ns() && a.maximum_ns() == b.maximum_ns(), "histogram changed on replay/merge");
  for (auto q : {0, 500000, 950000, 990000, 999000, 1000000})
    Check(a.QuantilePpm(q) == b.QuantilePpm(q), "quantile changed on replay/merge");
}
void TestHistogram() {
  Histogram h, left, right;
  Check(!h.QuantilePpm(990000) && !h.minimum_ns(), "empty distribution not null");
  std::mt19937_64 rng(123);
  std::vector<uint64_t> values;
  for (unsigned i = 0; i < 10000; ++i) {
    uint64_t value = rng() % (uint64_t{1} << (i % 36));
    values.push_back(value);
    h.Add(value);
    (i % 2 ? left : right).Add(value);
  }
  left.Merge(right);
  Same(h, left);
  auto restored = Histogram::Restore(h.count(), h.sum_ns(), h.minimum_ns(), h.maximum_ns(), h.bins());
  Same(h, restored);
  std::sort(values.begin(), values.end());
  for (auto q : {0, 500000, 950000, 990000, 999000, 1000000}) {
    const auto rank = std::max(uint64_t{1}, (uint64_t{values.size()} * q + 999999) / 1000000);
    auto exact = values[rank - 1], approx = *h.QuantilePpm(q);
    Check(approx >= exact && approx - exact <= exact / 256 + 1, "quantile outside resolution bound");
  }
  for (size_t i = 0; i < Histogram::kBucketCount; ++i) {
    Check(Histogram::IndexOf(Histogram::LowerBoundOf(i)) == i &&
          Histogram::IndexOf(Histogram::UpperBoundOf(i)) == i, "bin boundary mismatch");
  }
  Reject([&] { Histogram::Restore(h.count() + 1, h.sum_ns(), h.minimum_ns(), h.maximum_ns(), h.bins()); });
  Reject([&] { Histogram::Restore(h.count(), 0, h.minimum_ns(), h.maximum_ns(), h.bins()); });
  Reject([&] { h.QuantilePpm(1000001); });
}
void TestOverflow() {
  Histogram h;
  const auto max = std::numeric_limits<uint64_t>::max();
  h.Add(max);
  Check(h.QuantilePpm(999000) == max && h.sum_ns() == max, "uint64 maximum mishandled");
  Reject([&] { h.Add(1); });
  Check(h.count() == 1 && h.sum_ns() == max, "failed add changed histogram");
  Histogram one; one.Add(1);
  Reject([&] { h.Merge(one); });
  Check(h.count() == 1, "failed merge changed count");
  // Statistics::Merge is in place (a checkpoint closes on the request thread):
  // an overflow in the LAST histogram must still leave the first ones alone.
  Statistics left, right;
  left.response.Add(5); left.queue.Add(1); left.service.Add(4);
  left.completed_requests = left.completed_batches = 1;
  right = left;
  left.service.Add(max - 4);  // service sum is now max: merging right overflows it
  Reject([&] { left.Merge(right); });
  Check(left.response.count() == 1 && left.queue.count() == 1 && left.completed_requests == 1,
        "failed statistics merge changed an earlier field");
  std::array<uint64_t, Histogram::kBucketCount> bins{};
  bins[0] = max;
  auto full = Histogram::Restore(max, 0, 0, 0, bins);
  Reject([&] { full.Add(0); });
  Check(full.QuantilePpm(990000) == 0 && full.HasTailSamples(999000), "large count quantile overflow");
  bins[0] = 100000;
  auto tails = Histogram::Restore(100000, 0, 0, 0, bins);
  Check(tails.HasTailSamples(999000) && !tails.HasTailSamples(999000, 101), "tail sample policy wrong");
  bins[0] = 99999;
  Check(!Histogram::Restore(99999, 0, 0, 0, bins).HasTailSamples(999000), "insufficient tail accepted");
  bins.fill(0); bins[100] = 1;
  Reject([&] { Histogram::Restore(1, 99, 100, 100, bins); });
  Reject([&] { Histogram::Restore(1, 100, 99, 100, bins); });
}
CompletionEvent Batch1() { return {{0, 10, 20}, 30, 90, false}; }
CompletionEvent Batch2() { return {{95}, 100, 150, false}; }
std::unique_ptr<CheckpointEvent> Fixture(unsigned i) {
  auto a = std::make_unique<StatsAccumulator>();
  if (!i) a->observe(Batch1());
  else {
    a->observe(Batch2());
    a->observe(OutcomeEvent{Outcome::kRejected, 2});
    a->observe(OutcomeEvent{Outcome::kTimedOut, 1});
    a->observe(OutcomeEvent{Outcome::kOutstanding, 1});
  }
  return std::make_unique<CheckpointEvent>(a->checkpoint(i, i * 100, (i + 1) * 100));
}
void TestEvents() {
  auto a = std::make_unique<StatsAccumulator>();
  a->observe(Batch1());
  const auto& s = a->finish();
  Check(s.completed_requests == 3 && s.completed_batches == 1, "batch request count wrong");
  Check(s.response.sum_ns() == 240 && s.queue.sum_ns() == 60 && s.service.sum_ns() == 60,
        "response/queue/request versus batch-call weighting wrong");
  Check(s.service.count() == 1 && s.service.minimum_ns() == 60, "batch service was divided");
  Reject([&] { a->observe(CompletionEvent{{20}, 50, 80}); });
  Reject([&] { a->observe(CompletionEvent{{200}, 100, 150}); });
  Reject([&] { a->observe(CompletionEvent{{}, 100, 150}); });
  Reject([&] { a->observe(CompletionEvent{{90}, 100, 99}); });
  Reject([&] { a->checkpoint(0, 0, 89); });
  a->observe(Batch2());
  a->observe(OutcomeEvent{Outcome::kRejected, 2});
  a->observe(OutcomeEvent{Outcome::kTimedOut, 1});
  a->observe(OutcomeEvent{Outcome::kOutstanding, 1});
  Check(a->finish().offered() == 8 && !a->finish().uncensored(), "censored outcomes lost");
  auto compact = std::make_unique<StatsAccumulator>(StatisticsMode::kCheckpoints);
  auto first = Fixture(0), second = Fixture(1);
  compact->observe(*first);
  Reject([&] { compact->observe(*first); });
  second->begin_ns = 99;
  Reject([&] { compact->observe(*second); });
  second->begin_ns = 101;
  Reject([&] { compact->observe(*second); });
  second->begin_ns = 100; second->interval_id = 2;
  Reject([&] { compact->observe(*second); });
  second->interval_id = 1;
  compact->observe(*second);
  Same(a->finish().response, compact->finish().response);
  Same(a->finish().queue, compact->finish().queue);
  Same(a->finish().service, compact->finish().service);
  Check(a->finish().offered() == compact->finish().offered(), "outcomes changed on checkpoint replay");
  Reject([&] { compact->observe(Batch1()); });
  Reject([&] { a->observe(*first); });
  auto diagnostic = Batch1(); diagnostic.diagnostic_only = true;
  compact->observe(diagnostic);
  compact->observe(OutcomeEvent{Outcome::kRejected, 100, true});
  Check(compact->finish().offered() == 8, "diagnostic trace double counted");
}
// Several checkpoints in one trial: each is a delta, and merging the deltas
// reproduces the uncheckpointed totals exactly.
void TestCheckpointDeltas() {
  auto whole = std::make_unique<StatsAccumulator>();
  auto live = std::make_unique<StatsAccumulator>();
  auto merged = std::make_unique<StatsAccumulator>(StatisticsMode::kCheckpoints);
  whole->observe(Batch1()); live->observe(Batch1());
  merged->observe(*std::make_unique<CheckpointEvent>(live->checkpoint(0, 0, 100)));
  for (auto* a : {whole.get(), live.get()}) {
    a->observe(Batch2());
    a->observe(OutcomeEvent{Outcome::kRejected, 2});
  }
  auto second = std::make_unique<CheckpointEvent>(live->checkpoint(1, 100, 200));
  const auto& delta = second->statistics;
  Check(delta.completed_requests == 1 && delta.completed_batches == 1 && delta.rejected == 2 &&
        delta.response.minimum_ns() == 55 && delta.response.count() == 1,
        "checkpoint returned running totals instead of an interval delta");
  merged->observe(*second);
  auto third = std::make_unique<CheckpointEvent>(live->checkpoint(2, 200, 300));
  Check(third->statistics.offered() == 0 && !third->statistics.response.minimum_ns(),
        "empty interval is not an empty delta");
  merged->observe(*third);
  for (const auto* a : {live.get(), merged.get()}) {
    Same(a->finish().response, whole->finish().response);
    Same(a->finish().queue, whole->finish().queue);
    Same(a->finish().service, whole->finish().service);
    Check(a->finish().offered() == whole->finish().offered() &&
          a->finish().rejected == whole->finish().rejected, "checkpointed totals differ");
  }
}
// Bit-at-a-time reference for the table-driven CRC.
uint32_t BitwiseCrc32(const std::string& bytes) {
  uint32_t crc = 0xffffffff;
  for (unsigned char c : bytes) {
    crc ^= c;
    for (unsigned i = 0; i < 8; ++i) crc = (crc >> 1) ^ (0xedb88320u & (0u - (crc & 1)));
  }
  return ~crc;
}
void TestCrc() {
  Check(checkpoint_detail::Crc32("123456789") == 0xcbf43926, "CRC differs from published polynomial fixture");
  std::mt19937_64 random(7);
  std::string bytes(300, '\0');
  for (auto& c : bytes) c = static_cast<char>(random());
  for (size_t begin = 0; begin < 9; ++begin)
    for (size_t size = 0; begin + size <= bytes.size(); size += 1 + size / 16) {
      const auto slice = bytes.substr(begin, size);
      Check(checkpoint_detail::Crc32(slice) == BitwiseCrc32(slice), "table CRC differs from bitwise CRC");
    }
}
std::string Encode(const CheckpointEvent& c) {
  std::ostringstream out(std::ios::binary);
  WriteCheckpoint(out, c);
  return out.str();
}
void DecodeBad(const std::string& bytes) {
  Reject([&] { std::istringstream in(bytes, std::ios::binary); (void)ReadCheckpoint(in); });
}
void TestCodec() {
  Check(checkpoint_detail::Crc32("123456789") == 0xcbf43926, "CRC differs from published polynomial fixture");
  auto fixture = Fixture(0);
  const auto bytes = Encode(*fixture);
  Check(bytes.size() == checkpoint_detail::kPayloadBytes + 24 && bytes.substr(0, 8) == "ORBST01\n",
        "checkpoint framing wrong");
  Check(bytes[24] == 1 && bytes[25] == 0, "checkpoint version not little endian uint64");
  std::istringstream in(bytes, std::ios::binary);
  auto result = std::make_unique<CheckpointEvent>(ReadCheckpoint(in));
  Same(result->statistics.response, fixture->statistics.response);
  Check(Encode(*result) == bytes, "serialization not canonical");
  for (auto length : {size_t{0}, size_t{7}, size_t{23}, size_t{24}, bytes.size() - 1}) DecodeBad(bytes.substr(0, length));
  DecodeBad(bytes + "extra");
  auto bad = bytes; bad[100] ^= 1; DecodeBad(bad);
  bad = bytes; bad[8] ^= 1; DecodeBad(bad); // Must reject before allocating a supplied size.
  bad = bytes; bad[24] = 2;
  auto payload = bad.substr(24);
  std::string crc; checkpoint_detail::Put(crc, checkpoint_detail::Crc32(payload));
  bad.replace(16, 8, crc); DecodeBad(bad); // Valid checksum, unsupported version.
  auto empty = std::make_unique<StatsAccumulator>();
  auto checkpoint = std::make_unique<CheckpointEvent>(empty->checkpoint(0, 0, 1));
  std::istringstream empty_in(Encode(*checkpoint), std::ios::binary);
  auto empty_result = std::make_unique<CheckpointEvent>(ReadCheckpoint(empty_in));
  Check(!empty_result->statistics.response.minimum_ns(), "empty checkpoint fabricated extrema");
}
}  // namespace
int main(int argc, char** argv) {
  try {
    if (argc == 3 && std::string(argv[1]) == "--write-fixture") {
      for (unsigned i = 0; i < 2; ++i) {
        std::ofstream out(std::string(argv[2]) + "/" + std::to_string(i) + ".bin", std::ios::binary);
        WriteCheckpoint(out, *Fixture(i));
      }
      return 0;
    }
    TestHistogram(); TestOverflow(); TestEvents(); TestCheckpointDeltas(); TestCrc(); TestCodec();
    std::cout << "Portable statistics correctness tests passed\n";
    return 0;
  } catch (const std::exception& e) {
    std::cerr << e.what() << '\n'; return 1;
  }
}
