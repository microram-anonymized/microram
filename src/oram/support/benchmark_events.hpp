#pragma once

// Diagnostic raw-event log of a trial and its exact replay.  When full events
// are requested, the worker records every arrival, batch, batch member,
// censored outcome, saturation window and service bracket as a fixed-size
// record; EventReplay re-derives the trial's statistics from those records
// and cross-checks them against the trial-end totals, so a summary can be
// audited independently of the in-process accumulator.
#include "src/oram/support/benchmark_checkpoint.hpp"
#include "src/oram/support/benchmark_trial.hpp"
#include <array>
#include <map>

namespace oram_bench {
// Eight little-endian uint64 words per record. No keys, values, pointers or
// native structs cross the file boundary. Chunk sequence numbers are implicit
// in the contiguous record sequence carried by the header.
enum class EventKind : uint64_t {
  kBegin = 1, kArrival = 2, kBatch = 3, kMember = 4,
  kOutcome = 5, kWindow = 6, kService = 7, kEnd = 8
};
using RawEvent = std::array<uint64_t, 8>;
// Replay keeps every pending request in memory: waiting queue plus one batch.
inline constexpr uint64_t kMaxReplayQueuedRequests = uint64_t{1} << 24;
inline RawEvent Event(EventKind kind, uint64_t a=0, uint64_t b=0, uint64_t c=0,
                      uint64_t d=0, uint64_t e=0, uint64_t f=0, uint64_t g=0) {
  return {static_cast<uint64_t>(kind), a,b,c,d,e,f,g};
}
inline void WriteEventChunk(std::ostream& out, uint64_t sequence,
                            const RawEvent* events, size_t count) {
  using namespace checkpoint_detail;
  Require(count && count <= (64u << 20) / 64, "event chunk exceeds 64 MiB bound");
  std::string bytes(count * 64, '\0');
  for (size_t i=0; i<count; ++i)
    for (size_t w=0; w<8; ++w) StoreLE(bytes.data() + i*64 + w*8, events[i][w]);
  std::string header = "ORBEV01\n";
  Put(header, bytes.size()); Put(header, Crc32(bytes));
  Put(header, sequence); Put(header, count);
  out.write(header.data(), header.size()); out.write(bytes.data(), bytes.size());
  if (!out) throw std::runtime_error("cannot write event chunk");
}
struct EventChunk { uint64_t sequence = 0; std::vector<RawEvent> events; };
inline EventChunk ReadEventChunk(std::istream& in) {
  using namespace checkpoint_detail;
  std::string header(40, '\0'); in.read(header.data(), header.size());
  Require(bool(in) && header.substr(0,8) == "ORBEV01\n", "invalid event header/version");
  size_t at = 8;
  const auto bytes = Get(header, at), crc = Get(header, at);
  EventChunk chunk;
  chunk.sequence = Get(header, at);
  const auto count = Get(header, at);
  Require(count && count <= (64u << 20)/64 && bytes == count*64,
          "invalid/oversized event payload");
  std::string payload(bytes, '\0'); in.read(payload.data(), payload.size());
  Require(bool(in) && in.peek() == std::char_traits<char>::eof() && !in.bad(),
          "truncated/trailing event payload");
  Require(Crc32(payload) == crc, "event checksum mismatch");
  chunk.events.resize(count);
  for (size_t i=0; i<count; ++i)
    for (size_t w=0; w<8; ++w) chunk.events[i][w] = LoadLE(payload.data() + i*64 + w*8);
  return chunk;
}

// Exact bounded-cohort replay: arrivals create pending IDs, terminal outcomes
// remove them. The maximum resident map is waiting queue + active batch + one
// rejected arrival; duplicate/missing IDs cannot disappear in aggregate counts.
class EventReplay {
 public:
  void Observe(const EventChunk& chunk) {
    Require(chunk.sequence == sequence_, "duplicate, missing or reordered event chunk");
    for (const auto& event : chunk.events) { Observe(event); sequence_ = CheckedAdd(sequence_,1); }
  }
  void Observe(const RawEvent& event) {
    Require(!ended_, "event after trial end");
    const auto kind = static_cast<EventKind>(event[0]);
    if (!begun_) Require(kind == EventKind::kBegin, "event log lacks trial begin");
    Require(event[0] >= 1 && event[0] <= 8, "unknown event kind");
    constexpr size_t used[] = {0,8,3,5,4,4,4,3,8};
    for (size_t i=used[event[0]]; i<event.size(); ++i)
      Require(event[i]==0, "noncanonical event padding");
    switch (kind) {
      case EventKind::kBegin:
        Require(!begun_ && event[1] <= 1 && event[2] && event[3] >= event[2] &&
                event[4] && event[5] >= event[6] && event[6] && event[7], "invalid/duplicate trial begin");
        begun_ = true; saturated_ = event[1]; horizon_ = event[2]; deadline_ = event[3];
        cap_ = event[4]; queue_limit_ = event[5]; batch_size_ = event[6];
        Require(CheckedAdd(queue_limit_, batch_size_) <= kMaxReplayQueuedRequests,
                "replay queue exceeds 16M request safety bound"); break;
      case EventKind::kArrival:
        Require(!saturated_ && event[2] < horizon_ && offered_ < cap_, "invalid offered arrival");
        if (!first_id_) first_id_ = event[1];
        Require(event[1] == CheckedAdd(*first_id_,offered_) &&
                (!last_arrival_ || event[2] >= *last_arrival_), "gapped/nonmonotone arrival IDs or time");
        Require(pending_.emplace(event[1],event[2]).second, "duplicate arrival");
        ++offered_; last_arrival_ = event[2];
        Require(pending_.size() <= CheckedAdd(CheckedAdd(queue_limit_, batch_size_), 1),
                "event log exceeds declared queue memory bound"); break;
      case EventKind::kBatch:
        Require(!saturated_ && !remaining_ && event[1] == calls_ && event[2] &&
                event[2] <= batch_size_ && event[3] <= event[4] && event[3] < deadline_,
                "invalid/overlapping batch event");
        batch_id_ = event[1]; remaining_ = event[2];
        dispatch_ = event[3]; completion_ = event[4]; arrivals_.clear();
        arrivals_.reserve(remaining_); break;
      case EventKind::kMember: {
        Require(!saturated_ && remaining_ && event[1] == batch_id_, "member without matching batch");
        const auto at = pending_.find(event[2]);
        Require(at != pending_.end() && at->second == event[3], "duplicate/unknown batch member");
        Require(!last_member_ || event[2] > *last_member_, "FIFO member order changed");
        last_member_ = event[2];
        arrivals_.push_back(at->second); pending_.erase(at);
        if (--remaining_ == 0) {
          accumulator_.observe(CompletionView{arrivals_.data(), arrivals_.size(),dispatch_,completion_,false});
          completed_ += arrivals_.size(); ++calls_;
          if (completion_ < horizon_) completed_during_ += arrivals_.size();
        }
        break;
      }
      case EventKind::kOutcome: {
        Require(!saturated_ && !remaining_ && event[1] <= 2, "invalid/interleaved outcome");
        const auto at = pending_.find(event[2]);
        Require(at != pending_.end() && at->second == event[3], "duplicate/unknown censored request");
        pending_.erase(at);
        accumulator_.observe(OutcomeEvent{static_cast<Outcome>(event[1]),1,false}); break;
      }
      case EventKind::kWindow:
        Require(saturated_ && event[1] == window_end_ && event[2] >= event[1] && event[3],
                "gapped/reversed/empty saturation window");
        window_end_ = event[2]; completed_ = CheckedAdd(completed_,event[3]); break;
      case EventKind::kService:
        Require(saturated_ && event[2] && event[2] <= batch_size_, "invalid saturation service record");
        saturated_service_.Add(event[1]); service_members_ = CheckedAdd(service_members_,event[2]); break;
      case EventKind::kEnd:
        Require(!remaining_ && pending_.empty() && event[1] <= event[2] && event[6] <= 3 && event[7] > 0,
                "incomplete cohort/invalid trial end");
        if (saturated_) {
          Require(event[1] >= window_end_ && (!service_members_ || service_members_ == completed_),
                  "saturation window/service count mismatch");
          offered_ = completed_;
        } else Require(event[1] >= horizon_ &&
                       (!last_completion() || event[1] >= *last_completion()),
                       "caller end precedes horizon/completion");
        // Admission happens at enqueue: only a full queue refuses a request.
        Require(event[3] == offered_ && event[4] == offered_ - accumulator_.finish().rejected &&
                event[5] == completed_, "trial end totals disagree with raw events");
        caller_ = event[1]; drained_ = event[2]; flags_ = event[6]; minimum_tail_count_ = event[7]; ended_ = true;
        Require(bool(flags_ & 2) || drained_ <= deadline_, "unreported drain deadline overrun"); break;
      default: throw std::invalid_argument("unknown event kind");
    }
  }
  void ValidateComplete() const { Require(ended_, "truncated event log: trial end missing"); }
  const Statistics& statistics() const { ValidateComplete(); return accumulator_.finish(); }
  uint64_t offered() const { return offered_; }
  uint64_t completed() const { return completed_; }
  uint64_t completed_during_horizon() const { return completed_during_; }
  uint64_t caller_ns() const { return caller_; }
  uint64_t drained_ns() const { return drained_; }
  uint64_t minimum_tail_count() const { return minimum_tail_count_; }
  uint64_t flags() const { return flags_; }
  bool saturated() const { return saturated_; }
  const Histogram& saturated_service() const { return saturated_service_; }
 private:
  std::optional<uint64_t> last_completion() const {
    return completed_ ? std::optional<uint64_t>(completion_) : std::nullopt;
  }
  StatsAccumulator accumulator_;
  Histogram saturated_service_;
  bool begun_=false, ended_=false, saturated_=false;
  uint64_t sequence_=0, horizon_=0, deadline_=0, cap_=0, queue_limit_=0, batch_size_=0;
  uint64_t offered_=0, completed_=0, calls_=0, remaining_=0, batch_id_=0;
  uint64_t dispatch_=0, completion_=0, completed_during_=0, window_end_=0;
  uint64_t service_members_=0, caller_=0, drained_=0, flags_=0, minimum_tail_count_=100;
  std::optional<uint64_t> first_id_, last_arrival_, last_member_;
  std::map<uint64_t,uint64_t> pending_;
  std::vector<uint64_t> arrivals_;
};
}  // namespace oram_bench
