#pragma once
#include <cpu_byteslice_oram/configuration.hpp>
#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "benchmarks/support/maintenance_markers.hpp"
#include "src/oram/support/benchmark_workload.hpp"

namespace oram_bench {
// The worker backend for our own maps (ByteMap, the hierarchical ORAM, and
// TreeByteMap, the tree ORAM): it forwards the worker's Fill/Find/Write/Batch calls to the
// public API in include/cpu_byteslice_oram and exposes the access counter and
// top-merge log for maintenance coverage and markers.
template <typename Map>
class CpuBackend {
 public:
  using Request = cpu_byteslice_oram::BatchRequest;
  explicit CpuBackend(Map& map) : map_(map), old_value_(map.value_bytes()) {}
  static Request MakeRequest(bool write, const uint8_t* key,
                             const uint8_t* value, uint8_t* output) {
    namespace api = cpu_byteslice_oram;
    return {write ? api::BatchOp::kReadThenWrite : api::BatchOp::kRead,
            false,key,write ? value : nullptr,output};
  }
  bool Find(const uint8_t* key,uint8_t* output) { return map_.find(key,output); }
  // Measured writes include reading the previous value, in one ORAM access.
  // The presence bit exchange returns is not kept (keeping it would add a
  // store inside the timed call). With insert = true, a write to a record the
  // map has lost inserts it again, and no check sees that loss (WORKER.md).
  void Write(const uint8_t* key,const uint8_t* value) {
    (void)map_.exchange(key,value,old_value_.data(),true);
  }
  void Batch(size_t count,const Request* requests,uint8_t* found) {
    map_.access_batch(count,requests,found);
  }
  uint64_t Fill(const WorkloadGenerator& generator) {
    namespace api = cpu_byteslice_oram;
    const auto& spec = generator.spec();
    if constexpr (std::is_same_v<Map,api::ByteMap<true>> ||
                  std::is_same_v<Map,api::ByteMap<false>>) {
      auto records = microram::byteslice::benchmark_support::MakeGeneratedRecords(
          0,spec.key_bytes,spec.value_bytes,
          [&](uint64_t key,uint8_t* out) { generator.Key(key,out,spec.key_bytes); },
          [&](uint64_t key,uint8_t* out,size_t) { generator.Value(key,0,out,spec.value_bytes); });
      map_.initialize(records,spec.live_entries);
      map_.finish_pending_work();
      return 0;
    } else {
      std::vector<uint8_t> key(spec.key_bytes), value(spec.value_bytes);
      for (uint64_t id=0; id<spec.live_entries; ++id) {
        generator.Key(id,key.data(),key.size()); generator.Value(id,0,value.data(),value.size());
        map_.insert_or_assign(key.data(),value.data());
      }
      map_.finish_pending_work();
      return spec.live_entries;
    }
  }
  void Finish() { map_.finish_pending_work(); }
  // The counter the resolved carry periods are counted in, for cycle
  // coverage: the hierarchy's accesses, or a tree's position-map accesses.
  std::optional<uint64_t> AccessCount() const {
    if constexpr (is_tree) return map_.position_map_access_count();
    else return map_.access_count();
  }
  const char* AccessCounter() const { return is_tree ? "position_map_accesses" : "map_accesses"; }
  // Maintenance markers: the hierarchy's top merges (a tree's: its position map's) from the
  // engine's top-merge log, the last TopMergeLog::kCapacity of them. Drains
  // first: the log is read only from a quiescent engine.
  MaintenanceMarkers Markers() {
    map_.finish_pending_work();
    const auto& engine = [&]() -> const auto& {
      if constexpr (is_tree) return map_.position_byte_map().engine();
      else return map_.engine();
    }();
    const std::string prefix = is_tree ? "position_map_" : "";
    MaintenanceMarkers result{"top_merge_log", "", {}};
    const unsigned top = static_cast<unsigned>(engine.geometry().Levels());
    const auto records = engine.TopMergeRecords();
    // A full log may have overwritten the window's earliest merges.
    if (records.size() == microram::byteslice::levelarena::TopMergeLog::kCapacity)
      result.source += "_last_" + std::to_string(records.size()) + "_merges";
    for (const auto& r : records) {
      // Preparation (which may run ahead of the carry), then the carry-dependent merge to publication.
      if (r.prepare_start_ns && r.merge_start_ns)
        result.spans.push_back({prefix + "top_prepare", top, r.prepare_start_ns, r.merge_start_ns});
      if (r.merge_start_ns && r.publish_ns)
        result.spans.push_back({prefix + "top_merge", top, r.merge_start_ns, r.publish_ns});
    }
    return result;
  }
 private:
  static constexpr bool is_tree = std::is_same_v<Map,cpu_byteslice_oram::TreeByteMap<true>> ||
                                  std::is_same_v<Map,cpu_byteslice_oram::TreeByteMap<false>>;
  Map& map_;
  std::vector<uint8_t> old_value_;
};
}  // namespace oram_bench
