// Unit test for the benchmark worker driver (benchmarks/support/worker.hpp)
// with the synthetic fake and no-op backends: maintenance drains, the
// verification switch (full vs off), detection of wrong reads and lost batch
// writes, the no-op backend at capacities nothing could store, CLI parsing,
// and maintenance-coverage reporting.
#include "benchmarks/support/worker.hpp"
#include "benchmarks/support/fake_backend.hpp"
#include "benchmarks/support/noop_backend.hpp"
#include <iostream>

namespace ob=oram_bench;
namespace fs=std::filesystem;
namespace {
// Counts maintenance drains. The fake backend's other behavior is unchanged.
struct CountingBackend : ob::FakeBackend {
  using ob::FakeBackend::FakeBackend;
  size_t finishes=0;
  void Finish() { ++finishes; }
};
// Returns a wrong last byte for every found read, scalar or batch.
struct WrongRead : CountingBackend {
  size_t width;
  explicit WrongRead(ob::WorkloadSpec s) : CountingBackend(s), width(s.value_bytes) {}
  bool Find(const uint8_t* key,uint8_t* out) {
    const bool found=ob::FakeBackend::Find(key,out);
    if (found) out[width-1]^=1;
    return found;
  }
  void Batch(size_t n,const Request* r,uint8_t* found) {
    ob::FakeBackend::Batch(n,r,found);
    for (size_t i=0;i<n;++i) if (!r[i].write && found[i]) r[i].output[width-1]^=1;
  }
};
// A batch write that reports its existing key absent (a lost record the
// write re-inserts), or returns a wrong old value.
struct BadWrite : CountingBackend {
  bool lose; size_t width;
  BadWrite(ob::WorkloadSpec s,bool lose) : CountingBackend(s), lose(lose), width(s.value_bytes) {}
  void Batch(size_t n,const Request* r,uint8_t* found) {
    ob::FakeBackend::Batch(n,r,found);
    for (size_t i=0;i<n;++i) if (r[i].write) { if (lose) found[i]=0; else r[i].output[width-1]^=1; }
  }
};
ob::WorkerOptions Parse(std::vector<std::string> arguments) {
  std::vector<char*> argv{const_cast<char*>("worker")};
  for (auto& argument:arguments) argv.push_back(argument.data());
  return ob::ParseWorker(static_cast<int>(argv.size()),argv.data());
}
// A short real-clock trial on 64 keys; `extra` overrides the defaults.
ob::WorkerOptions Options(const fs::path& output,std::vector<std::string> extra) {
  std::vector<std::string> a{"--output",output.string(),"--capacity","64","--measurement-ns","2000000",
      "--drain-ns","50000000","--memory-interval-ns","1000000","--read-ppm","500000"};
  a.insert(a.end(),extra.begin(),extra.end());
  return Parse(a);
}
template <typename Backend> int Execute(const ob::WorkerOptions& o,Backend& backend) {
  ob::WorkerArtifacts artifacts(o,"{\"synthetic\":true}",[](bool) { return ob::MemorySnapshot{}; });
  std::streambuf* saved=std::cout.rdbuf(nullptr);  // the worker prints its summary
  try {
    const int status=ob::ExecuteWorker(o,backend,artifacts);
    std::cout.rdbuf(saved); return status;
  } catch (...) { std::cout.rdbuf(saved); throw; }
}
// The exception message, or empty when `fn` succeeds.
template <typename F> std::string Failure(F fn) {
  try { fn(); } catch (const std::exception& error) { return error.what(); }
  return {};
}
template <typename F> void Reject(F fn,const char* message) { ob::Require(!Failure(fn).empty(),message); }
std::string Text(const fs::path& path) {
  std::ifstream in(path); std::ostringstream out; out << in.rdbuf(); return out.str();
}
bool Has(const std::string& text,const char* needle) { return text.find(needle)!=std::string::npos; }

// Warmup and settle leave maintenance running.
void DrainsOnce(const fs::path& root) {
  for (const char* arrival:{"saturated","fixed"}) {
    const auto o=Options(root/arrival,{"--arrival",arrival,"--rate","1000000","--warmup-ns","2000000",
        "--settle-requests","50"});
    CountingBackend backend(o.workload);
    ob::Require(Execute(o,backend)==0,"fake worker trial failed");
    // One final drain after measurement, one closing the final verification.
    ob::Require(backend.finishes==2,"warmup or settle drained the pipeline before measurement");
  }
}
// Verification `off` allocates no version table, compares nothing, skips the final
// sweep, and says so; `full` bills 8 bytes per live key.
void VerificationSwitch(const fs::path& root) {
  for (const bool full:{true,false}) {
    for (const char* api:{"scalar","batch"}) {
      const auto output=root/(std::string("switch-")+(full ? "full-" : "off-")+api);
      const auto o=Options(output,{"--verification",full ? "full" : "off","--api",api,
          "--batch-size",std::string(api)=="batch" ? "8" : "1"});
      CountingBackend backend(o.workload);
      ob::Require(Execute(o,backend)==0,"verification-switch trial failed");
      const auto meta=Text(output/"worker.json");
      ob::Require(Has(meta,full ? "\"verification\":\"full\",\"correctness_verified\":true"
                               : "\"verification\":\"off\",\"correctness_verified\":false"),
                  "worker.json does not record the verification mode");
      ob::Require(Has(meta,full ? "\"version_table_bytes\":512" : "\"version_table_bytes\":0"),
                  "version table allocation does not follow the verification mode");
      ob::Require(full!=Has(meta,"\"verified_reads\":0,") && full!=Has(meta,"\"final_verification_reads\":0,"),
                  "verification off compared values or ran the final sweep");
      ob::Require((full && std::string(api)=="batch")!=Has(meta,"\"verified_old_values\":0,"),
                  "batch write old values were not verified exactly under full");
      ob::Require(backend.finishes==(full ? 2u : 1u),"the final sweep's drain does not follow the mode");
    }
  }
  ob::WorkloadSpec spec; spec.live_entries=1000;
  CountingBackend backend(spec);
  ob::Require(ob::PreparedWorkload<CountingBackend>(backend,spec,1,false,ob::Verification::kOff).version_table_bytes()==0 &&
              ob::PreparedWorkload<CountingBackend>(backend,spec,1,false).version_table_bytes()==8000,
              "adapter version table size");
}
// A wrong returned value fails under full and passes under off.
void WrongValue(const fs::path& root) {
  for (const char* api:{"scalar","batch"}) {
    for (const bool full:{true,false}) {
      const auto o=Options(root/(std::string("wrong-")+api+(full ? "-full" : "-off")),{"--verification",
          full ? "full" : "off","--api",api,"--batch-size",std::string(api)=="batch" ? "8" : "1"});
      WrongRead backend(o.workload);
      const auto failure=Failure([&] { ob::Require(Execute(o,backend)==0,"trial status"); });
      ob::Require(full ? Has(failure,"correctness: full returned value differs") : failure.empty(),
                  full ? "full verification accepted a wrong returned value"
                       : "verification off rejected a trial without value checks");
    }
  }
}
// A batch write must find its existing key (under either mode), and
// under full its old value must be the version before the write.
void WriteResults(const fs::path& root) {
  for (const bool lose:{true,false}) {
    for (const bool full:{true,false}) {
      const auto o=Options(root/(std::string(lose ? "lost-" : "stale-")+(full ? "full" : "off")),
          {"--verification",full ? "full" : "off","--api","batch","--batch-size","8"});
      BadWrite backend(o.workload,lose);
      const auto failure=Failure([&] { ob::Require(Execute(o,backend)==0,"trial status"); });
      if (lose) ob::Require(Has(failure,"correctness: write did not find its existing key"),
                            "a write that lost its key was accepted");
      else ob::Require(full ? Has(failure,"correctness: write returned an old value") : failure.empty(),
                       full ? "a stale batch-write old value was accepted"
                            : "verification off compared a batch-write old value");
    }
  }
}
// The no-op backend returns exactly the fake's values (including a read
// after an earlier write of the same batch), stores nothing, and runs at
// capacities the fake cannot allocate.
void Noop(const fs::path& root) {
  for (size_t batch:{size_t{1},size_t{7}}) {
    ob::WorkloadSpec spec; spec.live_entries=3; spec.read_ppm=500000;
    spec.key_bytes=batch==1 ? 4 : 32; spec.value_bytes=batch==1 ? 8 : 1029;
    ob::TrialOptions options; options.stop_at_request_cap=true; options.batch_size=batch;
    options.schedule.profile=ob::ArrivalProfile::kSaturating; options.schedule.num_accesses=301;
    ob::NullTrialSink sink;
    ob::FakeBackend fake(spec); ob::PreparedWorkload<ob::FakeBackend> reference(fake,spec,batch,batch>1);
    fake.Fill(reference.generator()); ob::RunTrial(options,reference,sink);
    ob::NoopBackend noop(spec,batch); ob::PreparedWorkload<ob::NoopBackend> adapter(noop,spec,batch,batch>1);
    ob::Require(noop.Fill(adapter.generator())==0,"no-op fill issued accesses");
    ob::RunTrial(options,adapter,sink);
    ob::Require(adapter.checksum()==reference.checksum() && adapter.verified_reads()==reference.verified_reads() &&
                adapter.verified_old_values()==reference.verified_old_values() && adapter.verified_reads()>0,
                "no-op backend results differ from the correctness fake");
    ob::Require(adapter.VerifyFinal()==4,"no-op final verification");
  }
  // 2^40 live keys: no value storage, and with verification off no oracle.
  ob::WorkloadSpec spec; spec.live_entries=uint64_t{1}<<40; spec.key_bytes=8; spec.value_bytes=1024;
  ob::NoopBackend noop(spec,16);
  ob::PreparedWorkload<ob::NoopBackend> adapter(noop,spec,16,true,ob::Verification::kOff);
  ob::TrialOptions options; options.stop_at_request_cap=true; options.batch_size=16;
  options.schedule.profile=ob::ArrivalProfile::kSaturating; options.schedule.num_accesses=1000;
  ob::NullTrialSink sink;
  ob::Require(ob::RunTrial(options,adapter,sink).completed==1000 && adapter.version_table_bytes()==0 &&
              adapter.verification_budget()==0 && adapter.VerifyFinal()==0,"large no-op trial");
  // The whole worker, open loop, with full verification.
  const auto o=Options(root/"noop",{"--scheme","noop","--arrival","fixed","--rate","200000",
      "--api","batch","--batch-size","4","--batch-timeout-ns","100000"});
  ob::NoopBackend backend(o.workload,o.trial.batch_size);
  ob::Require(Execute(o,backend)==0 && Has(Text(root/"noop"/"worker.json"),"\"correctness_verified\":true"),
              "no-op worker trial failed");
}
void ParseChecks(const fs::path& root) {
  Reject([&] { Parse({"--output",(root/"q").string(),"--queue-limit","16777216"}); },
         "worker accepted a queue that replay refuses");
  Parse({"--output",(root/"q").string(),"--queue-limit","16777215"});
  Reject([&] { Parse({"--output",(root/"q").string(),"--verification","sampled"}); },
         "worker accepted an unknown verification mode");
  Reject([&] { Parse({"--output",(root/"q").string(),"--scheme","noop","--cores","2","--cpu-ids","0,1"}); },
         "no-op backend accepted CPU placement");
}
// Carries are counted as counter boundaries crossed inside the window.
void Coverage(const fs::path& root) {
  ob::Require(ob::CarriesInWindow({128,1024},100,1100)==std::vector<uint64_t>({8,1}),"carries per level");
  ob::Require(ob::CarriesInWindow({128},128,255)==std::vector<uint64_t>({0}),"a window inside one period");
  Reject([&] { ob::CarriesInWindow({0},0,1); }, "zero period accepted");
  Reject([&] { ob::CarriesInWindow({128},2,1); }, "backwards counter accepted");
  // A synthetic backend has no library counter, so coverage is unknown, not zero.
  const auto dir=root/"coverage";
  auto o=Options(dir,{});
  o.carry_periods={128};
  ob::FakeBackend backend(o.workload);
  ob::Require(Execute(o,backend)==0,"coverage trial failed");
  std::ifstream in(dir/"worker.json"); std::stringstream text; text<<in.rdbuf();
  ob::Require(text.str().find("\"maintenance_coverage\":null")!=std::string::npos,"fake coverage is not null");
}
}  // namespace

// Runs short real-clock fake/no-op trials; no ORAM is constructed and no
// timing is asserted.
int main() {
  const auto root=fs::temp_directory_path()/
      ("oram-worker-fixture-"+std::to_string(std::chrono::steady_clock::now().time_since_epoch().count()));
  fs::create_directory(root);
  try {
    DrainsOnce(root); VerificationSwitch(root); WrongValue(root); WriteResults(root); Noop(root); ParseChecks(root);
    Coverage(root);
    fs::remove_all(root);
  } catch (...) { fs::remove_all(root); throw; }
  std::cout<<"oram_bench_worker_test passed\n";
}
