// The benchmark harness's trial loop (benchmarks/support/) over the real
// engines' CPU backend adapter, checked against a fake in-memory backend on a
// synthetic clock: for every engine, key/value width and batch size, the same
// saturating request sequence must produce the same full-value checksum as
// the reference, and benchmark writes must read and replace the prior value
// in one access, although the library default is a blind (unprobed) write
// (see benchmarks/oram/README.md).  This keeps benchmark numbers tied to
// verified results.
#include "benchmarks/support/cpu_backend.hpp"
#include "benchmarks/support/fake_backend.hpp"
#include "benchmarks/support/prepared_workload.hpp"
#include <iostream>
namespace api=cpu_byteslice_oram;
namespace ob=oram_bench;
struct SyntheticClock {
  uint64_t ticks=0;
  uint64_t Now() { return ++ticks; }
  void WaitUntil(uint64_t ns) { ticks=std::max(ticks,ns); }
};
int main() {
  // Benchmark writes must probe even though the library defaults to blind writes.
  {
    api::Options options;
    options.deamortized_owner_threads=0;
    api::ByteMap<> map(256,8,8,options);
    uint64_t key=1, value=7, out=0;
    auto* key_bytes=reinterpret_cast<uint8_t*>(&key);
    auto* value_bytes=reinterpret_cast<uint8_t*>(&value);
    map.write(key_bytes,value_bytes);
    ob::Require(map.last_probe_tables()==0,"blind setup unexpectedly probed");
    ob::CpuBackend<api::ByteMap<>> backend(map);
    value=9;
    backend.Write(key_bytes,value_bytes);
    ob::Require(map.access_count()==2 && map.last_probe_tables()>0,
                "benchmark scalar write must read and replace in one access");
    ob::Require(map.find(key_bytes,reinterpret_cast<uint8_t*>(&out)) && out==9,
                "benchmark scalar write did not replace the value");
    const auto request=decltype(backend)::MakeRequest(true,key_bytes,value_bytes,nullptr);
    ob::Require(request.op==api::BatchOp::kReadThenWrite,
                "benchmark batch write must explicitly request a read");
  }

  for (auto widths : {std::pair<size_t,size_t>{4,8},{8,48},{16,16},{32,1024}}) {
    ob::WorkloadSpec spec; spec.live_entries=3;
    spec.key_bytes=widths.first; spec.value_bytes=widths.second;
    spec.read_ppm=500000;
    ob::TrialOptions options; options.stop_at_request_cap=true;
    options.schedule.profile=ob::ArrivalProfile::kSaturating;
    options.schedule.num_accesses=301;
    ob::NullTrialSink sink;
    ob::FakeBackend fake(spec); ob::PreparedWorkload<ob::FakeBackend> reference(fake,spec,1,false);
    fake.Fill(reference.generator());
    ob::RunTrial<SyntheticClock>(options,reference,sink);
    for (auto scheme : {api::Scheme::kHierarchicalIncremental,
                        api::Scheme::kHierarchicalSynchronous,api::Scheme::kTree,api::Scheme::kAuto}) {
      for (size_t batch : {size_t{1},size_t{7}}) {
        for (bool synchronous_position : {false,true}) {
          if (synchronous_position && scheme!=api::Scheme::kTree) continue;
          api::OptionOverrides overrides; overrides.scheme=scheme;
          if (synchronous_position) {
            overrides.tree.emplace();
            overrides.tree->position_map.mode=api::Scheme::kHierarchicalSynchronous;
          }
          api::ResourceBudget budget; budget.cores=1;
          api::WorkloadHint hint;
          hint.api_mode=batch==1 ? api::ApiMode::kScalar : api::ApiMode::kBatch;
          hint.expected_batch_size=batch;
          const auto plan=api::resolve_options({256,spec.key_bytes,spec.value_bytes},budget,hint,overrides);
          auto map=api::make_map(plan);
          map.with_backend([&](auto& concrete) {
            ob::CpuBackend<std::decay_t<decltype(concrete)>> backend(concrete);
            ob::PreparedWorkload<decltype(backend)> adapter(backend,spec,batch,batch>1);
            backend.Fill(adapter.generator());
            options.batch_size=batch;
            const auto result=ob::RunTrial<SyntheticClock>(options,adapter,sink);
            ob::Require(result.completed==301 && adapter.checksum()==reference.checksum(),
                        "configured worker scalar/batch full-value results differ");
            // Batch writes returned found and the exact prior value.
            ob::Require(batch==1 || adapter.verified_old_values()>0,"batch write results were not verified");
          });
        }
      }
    }
  }
  std::cout << "cpu_byteslice_trial_adapter_test passed\n";
}
