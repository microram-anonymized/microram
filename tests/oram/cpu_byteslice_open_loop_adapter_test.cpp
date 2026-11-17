// The benchmark harness's offered-load (open-loop) path driven against every
// real engine through its CPU backend adapter (benchmarks/support/), so that
// the latency benchmarks measure only completed, correct requests: on the
// steady clock (no fake clock), at a fixed rate far below saturation, every
// offered request is admitted and completed, nothing is rejected, timed out
// or outstanding, and every returned value is verified. No timing is asserted.
#include "benchmarks/support/cpu_backend.hpp"
#include "benchmarks/support/prepared_workload.hpp"
#include <iostream>
namespace api=cpu_byteslice_oram;
namespace ob=oram_bench;
int main() {
  ob::WorkloadSpec spec; spec.live_entries=64;
  spec.key_bytes=8; spec.value_bytes=48; spec.read_ppm=500000;
  struct Arm { const char* name; api::Scheme scheme; bool synchronous_position; };
  for (const Arm arm : {Arm{"hierarchical_incremental",api::Scheme::kHierarchicalIncremental,false},
                        Arm{"hierarchical_synchronous",api::Scheme::kHierarchicalSynchronous,false},
                        Arm{"tree",api::Scheme::kTree,false},
                        Arm{"tree/synchronous position map",api::Scheme::kTree,true},
                        Arm{"auto",api::Scheme::kAuto,false}}) {
    for (size_t batch : {size_t{1},size_t{4}}) {
      api::OptionOverrides overrides; overrides.scheme=arm.scheme;
      if (arm.synchronous_position) {
        overrides.tree.emplace();
        overrides.tree->position_map.mode=api::Scheme::kHierarchicalSynchronous;
      }
      api::ResourceBudget budget; budget.cores=2;
      api::WorkloadHint hint;
      hint.api_mode=batch==1 ? api::ApiMode::kScalar : api::ApiMode::kBatch;
      hint.expected_batch_size=batch;
      auto map=api::make_map(api::resolve_options({256,spec.key_bytes,spec.value_bytes},budget,hint,overrides));
      map.with_backend([&](auto& concrete) {
        ob::CpuBackend<std::decay_t<decltype(concrete)>> backend(concrete);
        ob::PreparedWorkload<decltype(backend)> adapter(backend,spec,batch,batch>1);
        backend.Fill(adapter.generator());
        ob::TrialOptions options;
        options.schedule.profile=ob::ArrivalProfile::kFixedRate;
        options.schedule.rate_kops=2;        // arrivals at 0, 0.5, ..., 19.5 ms
        options.schedule.num_accesses=1000;  // safety cap, far above the 40
        options.horizon_ns=20000000; options.drain_ns=2000000000;
        options.batch_size=batch;
        options.batch_timeout_ns=batch>1 ? 1000000 : 0;  // timeout batches
        ob::NullTrialSink sink;
        const auto before=backend.AccessCount();
        const auto r=ob::RunTrial(options,adapter,sink);
        // Cycle coverage counts carries by this counter: one position per
        // request, scalar or batched, on every engine (a tree counts its
        // position map's accesses, which its carry periods are in).
        const auto after=backend.AccessCount();
        ob::Require(before && after && *after-*before==r.completed,
                    "access counter does not advance once per completed request");
        const auto& stats=r.accumulator.finish();
        ob::Require(r.offered==40 && r.admitted==r.offered &&
                    r.completed==r.offered && stats.completed_requests==r.offered &&
                    stats.uncensored() && !r.request_cap_reached && !r.deadline_exceeded,
                    "open-loop outcomes are not all accounted as completed");
        adapter.VerifyFinal();
        ob::Require(adapter.verified_reads()>0 && (batch==1 || adapter.verified_old_values()>0),
                    "open-loop trial verified no returned value");
      });
      std::cout << arm.name << " batch " << batch << ": ok\n";
    }
  }
  std::cout << "cpu_byteslice_open_loop_adapter_test passed\n";
}
