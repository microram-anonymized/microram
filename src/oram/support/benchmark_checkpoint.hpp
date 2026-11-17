#pragma once

// Binary file format for one histogram checkpoint (a CheckpointEvent: the
// statistics delta of one completion-time interval of an offered-load trial).
// The worker writes one checkpoint per file; the offline reducer reads them
// back and merges the deltas.  The encoding is fixed-size, little-endian and
// CRC-protected so files are portable across hosts and truncation or
// corruption is detected rather than silently merged.
#include "src/oram/support/benchmark_statistics.hpp"

#include <istream>
#include <ostream>
#include <string>

namespace oram_bench {
namespace checkpoint_detail {
// Byte-order independent; compilers lower both loops to one load/store on
// little-endian hosts.
inline void StoreLE(char* out, uint64_t value) {
  for (unsigned i = 0; i < 8; ++i) out[i] = static_cast<char>((value >> (8 * i)) & 255);
}
inline uint64_t LoadLE(const char* in) {
  uint64_t value = 0;
  for (unsigned i = 0; i < 8; ++i)
    value |= uint64_t{static_cast<unsigned char>(in[i])} << (8 * i);
  return value;
}
inline void Put(std::string& bytes, uint64_t value) {
  const size_t at = bytes.size();
  bytes.resize(at + 8);
  StoreLE(bytes.data() + at, value);
}
inline uint64_t Get(const std::string& bytes, size_t& offset) {
  Require(offset <= bytes.size() && bytes.size() - offset >= 8, "truncated checkpoint");
  const uint64_t value = LoadLE(bytes.data() + offset);
  offset += 8;
  return value;
}
// Slice-by-8 tables for the reflected polynomial 0xedb88320.
struct Crc32Tables {
  uint32_t table[8][256];
  constexpr Crc32Tables() : table{} {
    for (uint32_t i = 0; i < 256; ++i) {
      uint32_t crc = i;
      for (unsigned k = 0; k < 8; ++k) crc = (crc >> 1) ^ (0xedb88320u & (0u - (crc & 1)));
      table[0][i] = crc;
    }
    for (unsigned s = 1; s < 8; ++s)
      for (uint32_t i = 0; i < 256; ++i)
        table[s][i] = (table[s - 1][i] >> 8) ^ table[0][table[s - 1][i] & 255];
  }
};
inline constexpr Crc32Tables kCrc32Tables{};
// CRC-32/ISO-HDLC detects corruption; campaign manifests still need SHA-256.
inline uint32_t Crc32(const char* data, size_t size) {
  const auto& t = kCrc32Tables.table;
  const auto* p = reinterpret_cast<const unsigned char*>(data);
  uint32_t crc = 0xffffffff;
  for (; size >= 8; p += 8, size -= 8) {
    const uint32_t lo = crc ^ (uint32_t{p[0]} | uint32_t{p[1]} << 8 |
                               uint32_t{p[2]} << 16 | uint32_t{p[3]} << 24);
    crc = t[7][lo & 255] ^ t[6][(lo >> 8) & 255] ^ t[5][(lo >> 16) & 255] ^
          t[4][lo >> 24] ^ t[3][p[4]] ^ t[2][p[5]] ^ t[1][p[6]] ^ t[0][p[7]];
  }
  for (; size; ++p, --size) crc = (crc >> 8) ^ t[0][(crc ^ *p) & 255];
  return ~crc;
}
inline uint32_t Crc32(const std::string& bytes) { return Crc32(bytes.data(), bytes.size()); }
inline void PutHistogram(std::string& bytes, const Histogram& h) {
  Put(bytes, h.count());
  Put(bytes, h.sum_ns());
  Put(bytes, h.minimum_ns().value_or(0));
  Put(bytes, h.maximum_ns().value_or(0));
  for (auto count : h.bins()) Put(bytes, count);
}
inline Histogram GetHistogram(const std::string& bytes, size_t& offset) {
  const auto count = Get(bytes, offset), sum = Get(bytes, offset);
  const auto minimum = Get(bytes, offset), maximum = Get(bytes, offset);
  Require(count || (!minimum && !maximum), "noncanonical empty checkpoint extrema");
  std::array<uint64_t, Histogram::kBucketCount> bins;
  for (auto& bin : bins) bin = Get(bytes, offset);
  return Histogram::Restore(count, sum, count ? std::optional<uint64_t>(minimum) : std::nullopt,
                            count ? std::optional<uint64_t>(maximum) : std::nullopt, bins);
}
// Fixed-size v1: version, histogram version, bin count; interval triple;
// five outcome counts; response, queue, service (4 fields plus all bins).
inline constexpr size_t kPayloadBytes = (11 + 3 * (4 + Histogram::kBucketCount)) * 8;
}  // namespace checkpoint_detail

// One bounded checkpoint per file. No struct dumps, host endian, size_t,
// floating values, or architecture-specific encodings cross this boundary.
inline void WriteCheckpoint(std::ostream& out, const CheckpointEvent& event) {
  using namespace checkpoint_detail;
  event.Validate();
  std::string bytes;
  bytes.reserve(kPayloadBytes);
  Put(bytes, 1); Put(bytes, 1); Put(bytes, Histogram::kBucketCount);
  Put(bytes, event.interval_id); Put(bytes, event.begin_ns); Put(bytes, event.end_ns);
  const auto& s = event.statistics;
  Put(bytes, s.completed_requests); Put(bytes, s.completed_batches);
  Put(bytes, s.rejected); Put(bytes, s.timed_out); Put(bytes, s.outstanding);
  PutHistogram(bytes, s.response); PutHistogram(bytes, s.queue); PutHistogram(bytes, s.service);
  std::string header = "ORBST01\n";
  Put(header, bytes.size());
  Put(header, Crc32(bytes));
  out.write(header.data(), static_cast<std::streamsize>(header.size()));
  out.write(bytes.data(), static_cast<std::streamsize>(bytes.size()));
  if (!out) throw std::runtime_error("cannot write checkpoint");
}

inline CheckpointEvent ReadCheckpoint(std::istream& in) {
  using namespace checkpoint_detail;
  std::string header(24, '\0');
  in.read(header.data(), header.size());
  Require(bool(in) && header.substr(0, 8) == "ORBST01\n", "invalid/truncated checkpoint header");
  size_t offset = 8;
  const auto size = Get(header, offset), crc = Get(header, offset);
  Require(size == kPayloadBytes, "unsupported checkpoint size");
  std::string bytes(kPayloadBytes, '\0');
  in.read(bytes.data(), static_cast<std::streamsize>(bytes.size()));
  Require(bool(in), "truncated checkpoint payload");
  Require(in.peek() == std::char_traits<char>::eof() && !in.bad(), "trailing checkpoint bytes or I/O error");
  Require(Crc32(bytes) == crc, "checkpoint checksum mismatch");
  offset = 0;
  Require(Get(bytes, offset) == 1, "unsupported checkpoint version");
  Require(Get(bytes, offset) == 1, "unsupported histogram version");
  Require(Get(bytes, offset) == Histogram::kBucketCount, "unsupported histogram bins");
  CheckpointEvent event;
  event.interval_id = Get(bytes, offset);
  event.begin_ns = Get(bytes, offset); event.end_ns = Get(bytes, offset);
  auto& s = event.statistics;
  s.completed_requests = Get(bytes, offset); s.completed_batches = Get(bytes, offset);
  s.rejected = Get(bytes, offset); s.timed_out = Get(bytes, offset); s.outstanding = Get(bytes, offset);
  s.response = GetHistogram(bytes, offset);
  s.queue = GetHistogram(bytes, offset);
  s.service = GetHistogram(bytes, offset);
  event.Validate();
  return event;
}
}  // namespace oram_bench
