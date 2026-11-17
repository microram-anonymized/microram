#pragma once
// JSON summary of one trial (worker schema version 1): offered, admitted and
// completed counts, censoring, throughput to the caller's end and to the
// drain end, and response/queue/service histograms reduced to mean and
// percentiles.  Produced either from a live TrialResult or from an
// EventReplay of the raw-event log.
#include "src/oram/support/benchmark_events.hpp"
#include <iomanip>

namespace oram_bench {
inline void JsonNumber(std::ostream& out, std::optional<uint64_t> number) {
  if (number) out << *number; else out << "null";
}
inline void HistogramJson(std::ostream& out, const Histogram& h, const char* weighting, uint64_t minimum_tail_count=100) {
  out << "{\"weighting\":\"" << weighting << "\",\"count\":" << h.count()
      << ",\"sum_ns\":" << h.sum_ns() << ",\"mean_ns\":";
  if (h.count()) out << std::setprecision(17) << double(h.sum_ns())/h.count(); else out << "null";
  for (auto entry : {std::pair<const char*,uint32_t>{"p50_ns",500000},
                     {"p95_ns",950000},{"p99_ns",990000},{"p999_ns",999000}}) {
    out << ",\"" << entry.first << "\":"; JsonNumber(out,h.QuantilePpm(entry.second));
  }
  out << ",\"minimum_ns\":"; JsonNumber(out,h.minimum_ns());
  out << ",\"maximum_ns\":"; JsonNumber(out,h.maximum_ns());
  out << ",\"p99_sufficient_samples\":" << (h.HasTailSamples(990000,minimum_tail_count) ? "true" : "false")
      << ",\"p999_sufficient_samples\":" << (h.HasTailSamples(999000,minimum_tail_count) ? "true" : "false") << '}';
}
inline void TrialSummaryJson(std::ostream& out, bool saturated, uint64_t offered,
    uint64_t completed, uint64_t completed_during, uint64_t caller, uint64_t drained,
    uint64_t flags, const Statistics& statistics, const Histogram& saturated_service, uint64_t minimum_tail_count=100) {
  out << std::setprecision(17) << "{\"worker_schema_version\":1,\"saturated\":"
      << (saturated ? "true" : "false") << ",\"offered\":" << offered
      << ",\"completed\":" << completed << ",\"admitted\":" << offered - statistics.rejected
      << ",\"completed_during_horizon\":";
  if (saturated) out << "null"; else out << completed_during;
  out << ",\"rejected\":" << statistics.rejected << ",\"timed_out\":" << statistics.timed_out
      << ",\"outstanding\":" << statistics.outstanding
      << ",\"caller_end_ns\":" << caller << ",\"drain_end_ns\":" << drained
      << ",\"caller_ops_per_second\":" << (caller ? completed*1e9/caller : 0)
      << ",\"drained_ops_per_second\":" << (drained ? completed*1e9/drained : 0)
      << ",\"request_cap_reached\":" << ((flags&1) ? "true" : "false")
      << ",\"deadline_exceeded\":" << ((flags&2) ? "true" : "false")
      << ",\"uncensored\":" << (statistics.uncensored() ? "true" : "false")
      << ",\"minimum_tail_count\":" << minimum_tail_count
      << ",\"stable_queue\":null,\"response\":";
  HistogramJson(out,statistics.response,"request",minimum_tail_count); out << ",\"queue\":";
  HistogramJson(out,statistics.queue,"request",minimum_tail_count); out << ",\"service\":";
  HistogramJson(out,saturated ? saturated_service : statistics.service,"batch_call",minimum_tail_count);
  out << "}\n";
}
inline void TrialSummaryJson(std::ostream& out,const TrialResult& r,bool saturated) {
  TrialSummaryJson(out,saturated,r.offered,r.completed,r.completed_during_horizon,
      r.caller_end_ns,r.drain_end_ns,uint64_t(r.request_cap_reached) |
      (uint64_t(r.deadline_exceeded)<<1),r.accumulator.finish(),r.saturated_service,r.minimum_tail_count);
}
inline void TrialSummaryJson(std::ostream& out,const EventReplay& replay) {
  TrialSummaryJson(out,replay.saturated(),replay.offered(),replay.completed(),
      replay.completed_during_horizon(),replay.caller_ns(),replay.drained_ns(),
      replay.flags(),replay.statistics(),replay.saturated_service(),replay.minimum_tail_count());
}
}  // namespace oram_bench
