// oram_bench_aggregate: the campaign's one C++ reducer of benchmark statistics.
//
// It reads one repetition's binary delta checkpoints (histogram mode) or raw
// event chunks (full-event mode, --events), validates them (CRC, contiguous
// intervals, cohort completeness and call order), and prints the trial summary
// as JSON or CSV: request-weighted response/queue and call-weighted service
// distributions, outcome counts and rates.  The Python campaign tools
// (analysis/oram_bench) call it for every reduction, so no percentile or rate
// is ever recomputed in Python.  Formats and statistics are specified in
// analysis/oram_bench/STATISTICS.md and WORKER.md; the shared histogram,
// accumulator and checkpoint format live in src/oram/support/
// (benchmark_histogram.hpp, benchmark_statistics.hpp, benchmark_checkpoint.hpp).
// It needs no ORAM ISA and builds in the portable analysis/CMakeLists.txt
// project.

#include "src/oram/support/benchmark_checkpoint.hpp"
#include "src/oram/support/benchmark_summary.hpp"
#include "src/oram/support/benchmark_repetitions.hpp"
#include <algorithm>
#include <charconv>
#include <cmath>
#include <sstream>

#include <fstream>
#include <iomanip>
#include <iostream>
#include <locale>
#include <string>
#include <vector>

namespace {
using namespace oram_bench;
uint64_t minimum_tail_count = 100;
void Number(std::optional<uint64_t> value, bool json, std::ostream& out = std::cout) {
  if (value) out << *value;
  else if (json) out << "null";
}
void DistributionJson(std::ostream& out, const char* name, const char* weighting, const Histogram& h) {
  out << '"' << name << "\":{\"weighting\":\"" << weighting
            << "\",\"count\":" << h.count() << ",\"sum_ns\":" << h.sum_ns() << ",\"mean_ns\":";
  if (h.count()) out << static_cast<double>(h.sum_ns()) / static_cast<double>(h.count());
  else out << "null";
  out << ",\"minimum_ns\":"; Number(h.minimum_ns(), true, out);
  out << ",\"p50_ns\":"; Number(h.QuantilePpm(500000), true, out);
  out << ",\"p95_ns\":"; Number(h.QuantilePpm(950000), true, out);
  out << ",\"p99_ns\":"; Number(h.QuantilePpm(990000), true, out);
  out << ",\"p999_ns\":"; Number(h.QuantilePpm(999000), true, out);
  out << ",\"maximum_ns\":"; Number(h.maximum_ns(), true, out);
  out << ",\"p99_sufficient_samples\":" << (h.HasTailSamples(990000, minimum_tail_count) ? "true" : "false")
            << ",\"p999_sufficient_samples\":" << (h.HasTailSamples(999000, minimum_tail_count) ? "true" : "false") << '}';
}
void DistributionCsv(const char* name, const char* weighting, const Histogram& h, const Statistics& s) {
  std::cout << name << ',' << weighting << ',' << h.count() << ',' << h.sum_ns() << ',';
  if (h.count()) std::cout << static_cast<double>(h.sum_ns()) / static_cast<double>(h.count());
  std::cout << ','; Number(h.minimum_ns(), false);
  for (auto q : {500000, 950000, 990000, 999000}) { std::cout << ','; Number(h.QuantilePpm(q), false); }
  std::cout << ','; Number(h.maximum_ns(), false);
  std::cout << ',' << h.HasTailSamples(990000, minimum_tail_count) << ',' << h.HasTailSamples(999000, minimum_tail_count)
            << ',' << s.offered() << ',' << s.completed_requests << ',' << s.completed_batches
            << ',' << s.rejected << ',' << s.timed_out << ',' << s.outstanding
            << ',' << s.uncensored() << ",unknown\n";
}
// Across-time-block spread of one statistic (blocks, mean, sample stddev, min, max); null values are skipped.
struct Spread {
  std::vector<double> values; uint64_t sufficient = 0;
  void Add(std::optional<double> v) { if (v) values.push_back(*v); }
  void Json(std::ostream& out, bool sufficiency) const {
    const double n = static_cast<double>(values.size());
    double sum = 0, lo = 0, hi = 0;
    for (size_t i = 0; i < values.size(); ++i) {
      sum += values[i]; lo = i ? std::min(lo, values[i]) : values[i]; hi = i ? std::max(hi, values[i]) : values[i];
    }
    const double mean = values.empty() ? 0 : sum / n;
    double squares = 0;
    for (double v : values) squares += (v - mean) * (v - mean);
    out << "{\"blocks\":" << values.size();
    if (sufficiency) out << ",\"sufficient_blocks\":" << sufficient;
    if (values.empty()) { out << ",\"mean\":null,\"stddev\":null,\"minimum\":null,\"maximum\":null}"; return; }
    out << ",\"mean\":" << mean << ",\"stddev\":";
    if (values.size() > 1) out << std::sqrt(squares / (n - 1)); else out << "null";
    out << ",\"minimum\":" << lo << ",\"maximum\":" << hi << '}';
  }
};
constexpr const char* kStatNames[] = {"mean_ns", "p50_ns", "p95_ns", "p99_ns", "p999_ns", "maximum_ns"};
std::optional<double> Stat(const Histogram& h, unsigned k) {
  if (k == 0) return h.count() ? std::optional<double>(static_cast<double>(h.sum_ns()) / static_cast<double>(h.count())) : std::nullopt;
  if (k == 5) { const auto m = h.maximum_ns(); return m ? std::optional<double>(static_cast<double>(*m)) : std::nullopt; }
  const auto q = h.QuantilePpm(k == 1 ? 500000 : k == 2 ? 950000 : k == 3 ? 990000 : 999000);
  return q ? std::optional<double>(static_cast<double>(*q)) : std::nullopt;
}
}  // namespace

int main(int argc, char** argv) {
  try {
    std::string format = "json";
    bool events = false, blocks = false;
    std::vector<RepetitionTotals> repetitions;
    std::vector<uint64_t> trial_boundaries;
    std::vector<std::string> paths;
    for (int i = 1; i < argc; ++i) {
      std::string arg = argv[i];
      if (arg == "--help") {
        std::cout << "Usage: oram_bench_aggregate [--events] [--format json|csv|raw-csv] CHUNK...\n"
                     "       oram_bench_aggregate [--minimum-tail-count N] --blocks CHECKPOINT...\n"
                     "       oram_bench_aggregate [--minimum-tail-count N] --trial-boundaries B0 B1 B2 B3 B4 B5 CHECKPOINT...\n"
                     "       oram_bench_aggregate --repeat COMPLETED CALLER_NS DRAINED_NS [--repeat ...]\n"
                     "Reduce one repetition's contiguous delta checkpoints (or, with --events, raw\n"
                     "event chunks) in argument order; --trial-boundaries takes worker.json's\n"
                     "trial_boundaries and prints that trial's summary; --repeat pools repetition rates.\n"
                     "--blocks (json checkpoints) appends each checkpoint block's own statistics and their\n"
                     "across-time-block spread (blocks are not independent repetitions) to the summary.\n"
                     "This checks checkpoint statistics, not campaign completeness or durability.\n";
        return 0;
      }
      if (arg == "--trial-boundaries") {
        Require(trial_boundaries.empty() && i+6<argc,"--trial-boundaries needs six integers once");
        for (unsigned k=0; k<6; ++k) {
          uint64_t value=0; const std::string text=argv[++i];
          const auto parsed=std::from_chars(text.data(),text.data()+text.size(),value);
          Require(parsed.ec==std::errc{} && parsed.ptr==text.data()+text.size(),"invalid trial boundary");
          trial_boundaries.push_back(value);
        }
        continue;
      }
      if (arg == "--minimum-tail-count") {
        Require(++i<argc,"missing tail-count value");
        const std::string text=argv[i];
        const auto parsed=std::from_chars(text.data(),text.data()+text.size(),minimum_tail_count);
        Require(parsed.ec==std::errc{} && parsed.ptr==text.data()+text.size() && minimum_tail_count,
                "invalid minimum tail count");
        continue;
      }
      if (arg == "--repeat") {
        Require(i+3<argc,"--repeat needs completed caller_ns drained_ns");
        uint64_t fields[3]{};
        for (auto& value : fields) {
          const std::string text=argv[++i];
          const auto parsed=std::from_chars(text.data(),text.data()+text.size(),value);
          Require(parsed.ec==std::errc{} && parsed.ptr==text.data()+text.size(),"invalid repetition total");
        }
        repetitions.push_back({fields[0],fields[1],fields[2]}); continue;
      }
      if (arg == "--events") { events = true; continue; }
      if (arg == "--blocks") { blocks = true; continue; }
      if (arg == "--format") {
        Require(++i < argc, "missing --format value");
        format = argv[i];
        Require(format == "json" || format == "csv" || format == "raw-csv", "unknown format");
      } else {
        Require(arg.empty() || arg[0] != '-', "unknown option");
        paths.push_back(arg);
      }
    }
    if (!repetitions.empty()) {
      Require(paths.empty() && !events && trial_boundaries.empty() && format=="json","repetition totals cannot mix with event/checkpoint input");
      std::cout.imbue(std::locale::classic()); std::cout<<std::setprecision(17);
      RepetitionSummaryJson(std::cout,repetitions);
      if (!std::cout) throw std::runtime_error("cannot write repetition summary");
      return 0;
    }
    Require(!paths.empty(), "provide at least one checkpoint; see --help");
    Require(!blocks || !events, "--blocks needs checkpoint input; event chunks carry no block boundaries");
    if (events) {
      Require(trial_boundaries.empty(), "event boundaries must come from the raw stream");
      EventReplay replay;
      uint64_t sequence = 0;
      if (format == "raw-csv")
        std::cout << "sequence,kind,field1,field2,field3,field4,field5,field6,field7\n";
      for (const auto& path : paths) {
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::runtime_error("cannot open " + path);
        const auto chunk = ReadEventChunk(in);
        replay.Observe(chunk);
        if (format == "raw-csv") {
          for (const auto& record : chunk.events) {
            std::cout << sequence++;
            for (auto value : record) std::cout << ',' << value;
            std::cout << '\n';
          }
        }
      }
      replay.ValidateComplete();
      if (format == "json") TrialSummaryJson(std::cout, replay);
      else if (format == "csv") {
        const auto& stats = replay.statistics();
        std::cout << "offered,completed,rejected,timed_out,outstanding,caller_end_ns,drain_end_ns,caller_ops_per_second,drained_ops_per_second,flags\n"
          << std::setprecision(17) << replay.offered() << ',' << replay.completed() << ','
          << stats.rejected << ',' << stats.timed_out << ',' << stats.outstanding << ','
          << replay.caller_ns() << ',' << replay.drained_ns() << ','
          << (replay.caller_ns() ? replay.completed()*1e9/replay.caller_ns() : 0) << ','
          << (replay.drained_ns() ? replay.completed()*1e9/replay.drained_ns() : 0) << ','
          << replay.flags() << '\n';
      }
      if (!std::cout) throw std::runtime_error("cannot write event reduction");
      return 0;
    }
    Require(format != "raw-csv", "raw-csv requires --events");
    Require(!blocks || (!events && format=="json" && trial_boundaries.empty()), "--blocks needs checkpoints and json without --trial-boundaries");
    StatsAccumulator accumulator(StatisticsMode::kCheckpoints);
    std::optional<uint64_t> first_begin; uint64_t last_end=0;
    std::ostringstream block_json; block_json.imbue(std::locale::classic()); block_json<<std::setprecision(17);
    constexpr const char* kKinds[] = {"response", "queue", "service"};
    constexpr const char* kWeights[] = {"request", "request", "batch_call"};
    Spread throughput, spread[3][6];
    for (const auto& path : paths) {
      std::ifstream in(path, std::ios::binary);
      if (!in) throw std::runtime_error("cannot open " + path);
      try {
        const auto checkpoint=ReadCheckpoint(in);
        if (!first_begin) first_begin=checkpoint.begin_ns;
        last_end=checkpoint.end_ns;
        accumulator.observe(checkpoint);
        if (blocks) {
          const auto& bs = checkpoint.statistics;
          const double rate = static_cast<double>(bs.completed_requests) * 1e9 / static_cast<double>(checkpoint.end_ns - checkpoint.begin_ns);
          if (!throughput.values.empty()) block_json << ',';
          block_json << "{\"interval_id\":" << checkpoint.interval_id << ",\"begin_ns\":" << checkpoint.begin_ns
                     << ",\"end_ns\":" << checkpoint.end_ns << ",\"completed_requests\":" << bs.completed_requests
                     << ",\"completed_batches\":" << bs.completed_batches << ",\"throughput_ops_per_second\":" << rate << ',';
          throughput.Add(rate);
          const Histogram* hs[] = {&bs.response, &bs.queue, &bs.service};
          for (unsigned kind = 0; kind < 3; ++kind) {
            DistributionJson(block_json, kKinds[kind], kWeights[kind], *hs[kind]); block_json << (kind < 2 ? "," : "}");
            for (unsigned k = 0; k < 6; ++k) spread[kind][k].Add(Stat(*hs[kind], k));
            spread[kind][3].sufficient += hs[kind]->HasTailSamples(990000, minimum_tail_count);
            spread[kind][4].sufficient += hs[kind]->HasTailSamples(999000, minimum_tail_count);
          }
        }
      }
      catch (const std::exception& e) { throw std::runtime_error(path + ": " + e.what()); }
    }
    const auto& s = accumulator.finish();
    std::cout.imbue(std::locale::classic());
    std::cout << std::setprecision(17);
    if (!trial_boundaries.empty()) {
      const auto& b=trial_boundaries;
      Require(format=="json" && first_begin==0 && b[0]==s.offered() && b[1]==s.completed_requests &&
              b[2]<=b[1] && b[3] && b[3]<=b[4] && b[4]==last_end && b[5]<=3,
              "trial boundaries disagree with checkpoint cohort");
      TrialSummaryJson(std::cout,false,b[0],b[1],b[2],b[3],b[4],b[5],s,Histogram{},minimum_tail_count);
      if (!std::cout) throw std::runtime_error("cannot write trial reduction");
      return 0;
    }
    if (format == "json") {
      std::cout << "{\"statistics_schema_version\":1,\"histogram_version\":1,"
                   "\"scope\":\"supplied_checkpoints_only\",\"stable_queue\":null,"
                   "\"minimum_expected_tail_count\":" << minimum_tail_count << ",\"offered\":" << s.offered()
                << ",\"completed_requests\":" << s.completed_requests
                << ",\"completed_batches\":" << s.completed_batches
                << ",\"rejected\":" << s.rejected << ",\"timed_out\":" << s.timed_out
                << ",\"outstanding\":" << s.outstanding
                << ",\"uncensored\":" << (s.uncensored() ? "true" : "false") << ',';
      DistributionJson(std::cout, "response", "request", s.response); std::cout << ',';
      DistributionJson(std::cout, "queue", "request", s.queue); std::cout << ',';
      DistributionJson(std::cout, "service", "batch_call", s.service);
      if (blocks) {
        std::cout << ",\"blocks\":[" << block_json.str() << "],\"block_spread\":{\"scope\":\"across_time_blocks_not_independent_repetitions\","
                     "\"throughput_ops_per_second\":";
        throughput.Json(std::cout, false);
        for (unsigned kind = 0; kind < 3; ++kind) {
          std::cout << ",\"" << kKinds[kind] << "\":{";
          for (unsigned k = 0; k < 6; ++k) { std::cout << (k ? ",\"" : "\"") << kStatNames[k] << "\":"; spread[kind][k].Json(std::cout, k == 3 || k == 4); }
          std::cout << '}';
        }
        std::cout << '}';
      }
      std::cout << "}\n";
    } else {
      std::cout << "distribution,weighting,count,sum_ns,mean_ns,minimum_ns,p50_ns,p95_ns,p99_ns,p999_ns,maximum_ns,"
                   "p99_sufficient_samples,p999_sufficient_samples,offered,completed_requests,completed_batches,"
                   "rejected,timed_out,outstanding,uncensored,stable_queue\n";
      DistributionCsv("response", "request", s.response, s);
      DistributionCsv("queue", "request", s.queue, s);
      DistributionCsv("service", "batch_call", s.service, s);
    }
    if (!std::cout) throw std::runtime_error("cannot write summary");
    return 0;
  } catch (const std::exception& e) {
    std::cerr << "oram_bench_aggregate: " << e.what() << '\n';
    return 2;
  }
}
