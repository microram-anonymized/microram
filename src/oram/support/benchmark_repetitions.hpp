#pragma once
// JSON summary across repeated trials of one configuration: median, minimum,
// maximum and pooled throughput, measured to the caller's end (the last
// request returned) and to the drain end (background maintenance finished).
// The reported uncertainty is the range across repetitions; latency
// percentiles stay per repetition and are never averaged.
#include "src/oram/support/benchmark_statistics.hpp"
#include <algorithm>
#include <ostream>

namespace oram_bench {
struct RepetitionTotals { uint64_t completed,caller_ns,drained_ns; };
inline void RepetitionSummaryJson(std::ostream& out,const std::vector<RepetitionTotals>& repetitions) {
  Require(!repetitions.empty(),"no completed repetitions");
  uint64_t completed=0, caller=0, drained=0;
  std::vector<long double> caller_rates,drained_rates;
  for (const auto& r:repetitions) {
    Require(r.caller_ns && r.drained_ns>=r.caller_ns,"invalid repetition boundaries");
    completed=CheckedAdd(completed,r.completed);
    caller=CheckedAdd(caller,r.caller_ns); drained=CheckedAdd(drained,r.drained_ns);
    caller_rates.push_back(static_cast<long double>(r.completed)*1e9L/r.caller_ns);
    drained_rates.push_back(static_cast<long double>(r.completed)*1e9L/r.drained_ns);
  }
  auto rates=[&](std::vector<long double>& values,uint64_t duration) {
    std::sort(values.begin(),values.end());
    const size_t middle=values.size()/2;
    const long double median=values.size()%2 ? values[middle] : (values[middle-1]+values[middle])/2;
    out<<"{\"median_ops_per_second\":"<<median<<",\"minimum_ops_per_second\":"<<values.front()
       <<",\"maximum_ops_per_second\":"<<values.back()<<",\"pooled_ops_per_second\":"
       <<static_cast<long double>(completed)*1e9L/duration<<'}';
  };
  out<<"{\"repetitions\":"<<repetitions.size()<<",\"uncertainty\":\"range_of_repetitions\",\"caller\":";
  rates(caller_rates,caller); out<<",\"drained\":"; rates(drained_rates,drained);
  out<<",\"percentiles\":\"retained_per_repetition_not_averaged\"}\n";
}
}  // namespace oram_bench
