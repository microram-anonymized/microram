#pragma once
#include "src/oram/support/benchmark_events.hpp"
#include <chrono>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <sstream>

// Per-request event log of a trial: the request thread appends raw events to a
// preallocated buffer, and only after the trial are they encoded into
// checksummed chunk files (worker/events/).
namespace oram_bench {
// One append-only buffer sized for the whole trial, allocated and
// pre-faulted before warmup. The request thread only appends; nothing is
// encoded, checksummed or written while requests are served. After the final
// drain, Write() encodes checksummed chunks and publishes them. A full buffer
// invalidates the trial: the loss count is retained, nothing is dropped silently.
class EventBuffer {
 public:
  explicit EventBuffer(size_t records) : records_(records) {
    Require(records >= 2, "event buffer must hold at least two records");
    // Value-initialized storage is zero-filled here, which touches (and so
    // faults in) every page before the timed phases begin.
  }
  EventBuffer(const EventBuffer&) = delete;
  void Push(RawEvent event) {
    if (size_ == records_.size()) { ++lost_; return; }
    records_[size_++] = event;
  }
  uint64_t lost() const { return lost_; }
  uint64_t size() const { return size_; }
  uint64_t capacity() const { return records_.size(); }
  // Publishes chunks of at most chunk_bytes as 00000000000000000000.bin, ...
  // Each chunk is written to a temporary name and renamed into place.
  void Write(const std::filesystem::path& directory, size_t chunk_bytes) {
    const size_t chunk_records = chunk_bytes / sizeof(RawEvent);
    Require(chunk_records && chunk_bytes <= (64u << 20), "invalid event chunk size");
    Require(std::filesystem::create_directory(directory), "event directory already exists");
    for (size_t first = 0; first < size_; first += chunk_records) {
      const size_t count = std::min<size_t>(chunk_records, size_ - first);
      std::ostringstream name;
      name << std::setw(20) << std::setfill('0') << first << ".bin";
      const auto target = directory / name.str();
      const auto temporary = target.string() + ".tmp";
      std::ofstream out(temporary, std::ios::binary);
      WriteEventChunk(out, first, records_.data() + first, count);
      out.close();
      if (!out) throw std::runtime_error("event chunk close failed");
      std::filesystem::rename(temporary, target);
      written_ += count;
    }
  }
  uint64_t written() const { return written_; }
 private:
  std::vector<RawEvent> records_;
  size_t size_ = 0;
  uint64_t lost_ = 0, written_ = 0;
};

template <typename Writer>
class BasicEventSink {
 public:
  explicit BasicEventSink(Writer& writer) : writer_(writer) {}
  template <typename Clock> void ClockInfo(const Clock& clock) { origin_ns = ClockOriginNs(clock); }
  std::optional<uint64_t> origin_ns;
  void Begin(const TrialOptions& o) {
    writer_.Push(Event(EventKind::kBegin,o.schedule.profile == ArrivalProfile::kSaturating,
        o.horizon_ns,CheckedAdd(o.horizon_ns,o.drain_ns),o.schedule.num_accesses,
        o.queue_limit,o.batch_size,o.window_requests));
  }
  void Offered(PendingRequest r) { writer_.Push(Event(EventKind::kArrival,r.id,r.arrival_ns)); }
  void Completion(const PendingRequest* r, size_t n, InvocationTiming t, uint64_t batch) {
    writer_.Push(Event(EventKind::kBatch,batch,n,t.start,t.end));
    for (size_t i=0; i<n; ++i) writer_.Push(Event(EventKind::kMember,batch,r[i].id,r[i].arrival_ns));
  }
  void Censored(PendingRequest r, Outcome outcome) {
    writer_.Push(Event(EventKind::kOutcome,static_cast<uint64_t>(outcome),r.id,r.arrival_ns));
  }
  void Window(uint64_t begin,uint64_t end,uint64_t requests) {
    writer_.Push(Event(EventKind::kWindow,begin,end,requests));
  }
  void SaturatedService(uint64_t ns,size_t count) { writer_.Push(Event(EventKind::kService,ns,count)); }
  void Finish(const TrialResult& r) {
    writer_.Push(Event(EventKind::kEnd,r.caller_end_ns,r.drain_end_ns,r.offered,
        r.admitted,r.completed,uint64_t(r.request_cap_reached) | (uint64_t(r.deadline_exceeded)<<1),r.minimum_tail_count));
  }
 private:
  Writer& writer_;
};
using EventSink = BasicEventSink<EventBuffer>;
// Histogram-checkpoint trials keep no events, only the clock origin.
struct OriginSink : NullTrialSink {
  template <typename Clock> void ClockInfo(const Clock& clock) { origin_ns = ClockOriginNs(clock); }
  std::optional<uint64_t> origin_ns;
};
}  // namespace oram_bench
