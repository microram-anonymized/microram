#pragma once
// Counted allocations for the baseline workers, so their memory can be compared
// with ours byte for byte.
// Only the audit builds (-DORAM_BASELINE_ALLOCATION_AUDIT, targets
// oram_baseline_*_audit) include this: it brings in the counting global
// allocator, the same one cpu_oram_allocation_audit uses for our engines, so
// both sides report requested/granted bytes alike.  A worker run with
// `--allocation-audit 1` (and the usual --capacity/--key-bytes/--value-bytes/
// --scheme/--override options, no --output) builds the library structure,
// fills it, runs 2 x capacity mixed accesses and prints one ALLOC_AUDIT JSON
// line.
//
// Library vs harness: the baseline is taken after the runtime pools (TBB,
// OpenMP, SONIC's thread pool) start, so their startup is excluded.  Harness
// allocations (the workload generator, key/value buffers, the dataset a
// constructor is handed) are made inside an audit::HarnessScope and reported
// apart; everything else after the baseline is the library's.  Allocations
// the baseline library makes outside operator new (malloc, mmap) are not seen;
// grep of the pinned sources finds none outside SGX/untrusted-file code that
// these builds do not use, and `hwm` (VmHWM) is the check on that.
#include "benchmarks/support/counting_allocator.hpp"
#include "benchmarks/support/worker.hpp"

namespace oram_bench::baseline {

class AllocationAuditor {
 public:
  explicit AllocationAuditor(const WorkerOptions& o, std::string scheme, std::string build)
      : o_(o), scheme_(std::move(scheme)), build_(std::move(build)) {
    base_ = audit::TakeLibrary();
    base_total_ = audit::Take();
    base_status_ = Status();
    audit::Mark();
  }
  // Closes the phase since the previous checkpoint (peaks and the allocation
  // count restart from here).
  void Checkpoint(const char* name) {
    const auto lib = audit::TakeLibrary();
    const auto all = audit::Take();
    const auto st = Status();
    std::ostringstream out;
    out << '"' << name << "\":{\"library\":{\"live_requested\":" << lib.live_requested - base_.live_requested
        << ",\"live_granted\":" << lib.live_granted - base_.live_granted
        << ",\"peak_requested\":" << lib.peak_requested - base_.live_requested
        << ",\"peak_granted\":" << lib.peak_granted - base_.live_granted << ",\"blocks\":" << lib.live_blocks
        << ",\"allocations\":" << lib.allocations << "},\"harness\":{\"live_requested\":"
        << (all.live_requested - base_total_.live_requested) - (lib.live_requested - base_.live_requested)
        << "},\"all_peak_requested\":" << all.peak_requested - base_total_.live_requested
        << ",\"rss\":" << st.rss << ",\"hwm\":" << st.hwm << ",\"threads\":" << st.threads << '}';
    phases_.push_back(out.str());
    audit::Mark();
  }
  // Fill, then 2 x capacity mixed accesses, with the checkpoints the report reads.
  template <class Backend>
  void Run(Backend& backend) {
    std::unique_ptr<WorkloadGenerator> owned;
    std::vector<uint8_t> key, value, out;
    {
      audit::HarnessScope harness;  // only these buffers; the library's calls stay outside
      owned = std::make_unique<WorkloadGenerator>(o_.workload);
      key.resize(o_.workload.key_bytes);
      value.resize(o_.workload.value_bytes);
      out.resize(o_.workload.value_bytes);
    }
    const WorkloadGenerator& generator = *owned;
    audit::Mark();
    backend.Fill(generator);
    Checkpoint("filled");
    accesses_ = 2 * o_.capacity;
    for (uint64_t i = 0; i < accesses_; ++i) {
      const auto r = generator.At(i);
      generator.Key(r.key_id, key.data(), key.size());
      if (r.write) {
        generator.Value(r.key_id, r.value_version, value.data(), value.size());
        backend.Write(key.data(), value.data());
      } else {
        backend.Find(key.data(), out.data());
      }
    }
    backend.Finish();
    Checkpoint("steady");
  }
  // After the library's structures are destroyed.
  void Emit(uint64_t actual_capacity) {
    const auto lib = audit::TakeLibrary();
    std::ostringstream out;
    out << "ALLOC_AUDIT {\"scheme\":" << JsonQuote(scheme_) << ",\"build\":" << JsonQuote(build_)
        << ",\"capacity\":" << o_.capacity << ",\"actual_capacity\":" << actual_capacity
        << ",\"key_bytes\":" << o_.workload.key_bytes << ",\"value_bytes\":" << o_.workload.value_bytes
        << ",\"accesses\":" << accesses_ << ",\"baseline\":{\"live_requested\":" << base_.live_requested
        << ",\"rss\":" << base_status_.rss << ",\"hwm\":" << base_status_.hwm
        << ",\"threads\":" << base_status_.threads << "},\"role_attribution\":\"none\",";
    for (size_t i = 0; i < phases_.size(); ++i) out << (i ? "," : "") << phases_[i];
    out << ",\"leaked_requested\":" << lib.live_requested - base_.live_requested << "}\n";
    std::cout << out.str() << std::flush;
  }

 private:
  struct ProcStatus { uint64_t rss = 0, hwm = 0, threads = 0; };
  static ProcStatus Status() {
    const auto text = ReadProc("/proc/self/status");
    ProcStatus s;
    s.rss = ProcKiB(text, "VmRSS").value_or(0);
    s.hwm = ProcKiB(text, "VmHWM").value_or(0);
    std::istringstream lines(text); std::string line;
    while (std::getline(lines, line))
      if (line.rfind("Threads:", 0) == 0) s.threads = std::stoull(line.substr(8));
    return s;
  }
  const WorkerOptions& o_;
  std::string scheme_, build_;
  audit::Snapshot base_{}, base_total_{};
  ProcStatus base_status_;
  std::vector<std::string> phases_;
  uint64_t accesses_ = 0;
};

// `--allocation-audit 1` is ours: strip it before ParseWorker, which then sees
// a resolve-only call (no --output) that the caller turns back off.
inline bool TakeAuditFlag(std::vector<char*>& args) {
  for (size_t i = 1; i + 1 < args.size(); ++i) {
    if (std::string(args[i]) != "--allocation-audit") continue;
    const bool on = std::string(args[i + 1]) == "1";
    Require(on || std::string(args[i + 1]) == "0", "--allocation-audit 0|1");
    args.erase(args.begin() + i, args.begin() + i + 2);
    return on;
  }
  return false;
}
}  // namespace oram_bench::baseline
