// Allocation coverage: the memory figures a resolved plan reports are the
// memory the engine really uses, and the access path never allocates, so an
// access can neither fail for memory nor grow past the planned footprint.
// The full
// per-component breakdown is the `cpu_oram_allocation_audit` benchmark tool
// (benchmarks/oram/README.md); this test keeps its conclusions true.  For
// every engine a resolved plan builds:
//
//   1. the plan's figure covers the heap: after the fill, the live bytes the
//      library asked for are at least the plan's reserved bytes and at most
//      kUnmodeledBytes above them (the engine objects and small containers no
//      byte bill lists);
//   2. accessing allocates nothing -- construction sized every buffer, the
//      probe's included;
//   3. destruction returns every byte.
//
// The counting allocator replaces operator new for this binary, so it sees
// every library buffer, huge-page arenas included.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include <cpu_byteslice_oram/configuration.hpp>

#include "benchmarks/oram/cpu_byteslice_benchmark_support.hpp"
#include "benchmarks/support/counting_allocator.hpp"

namespace {

namespace api = cpu_byteslice_oram;
namespace bs = microram::byteslice;

constexpr size_t kUnmodeledBytes = size_t{256} << 10;

int failures = 0;

void Expect(bool ok, const std::string& what) {
  if (ok) return;
  std::fprintf(stderr, "FAILED: %s\n", what.c_str());
  ++failures;
}

void Key(uint64_t id, uint8_t* out, size_t bytes) {
  std::memset(out, 0, bytes);
  std::memcpy(out, &id, bytes < sizeof(id) ? bytes : sizeof(id));
  for (size_t b = sizeof(id); b < bytes; ++b) out[b] = static_cast<uint8_t>(id * 31 + b);
}

void Value(uint64_t id, uint8_t* out, size_t bytes) {
  for (size_t b = 0; b < bytes; ++b) out[b] = static_cast<uint8_t>(id + b);
}

const char* Name(api::Scheme s) {
  switch (s) {
    case api::Scheme::kHierarchicalIncremental: return "incremental";
    case api::Scheme::kHierarchicalSynchronous: return "synchronous";
    case api::Scheme::kTree: return "tree";
    default: return "?";
  }
}

void CheckEngine(api::Scheme scheme, size_t capacity, size_t key_bytes,
                 size_t value_bytes) {
  const std::string row = std::string(Name(scheme)) + " " +
                          std::to_string(key_bytes) + ":" +
                          std::to_string(value_bytes) + " at " +
                          std::to_string(capacity);
  api::ResourceBudget budget;
  budget.cores = 4;
  budget.harness_cores = 1;
  api::OptionOverrides overrides;
  overrides.scheme = scheme;
  const api::ResolvedPlan plan =
      api::resolve_options({capacity, key_bytes, value_bytes}, budget, {}, overrides);
  Expect(plan.modeled_reserved_bytes() >= plan.modeled_buffer_bytes(),
         row + ": reserved bytes below the requested bytes they round");
  size_t components = 0;
  for (const auto& c : plan.memory_components()) {
    components += c.requested_bytes;
    Expect(c.coverage != api::MemoryCoverage::kLowerBound,
           row + ": component " + c.component + " is only a lower bound");
  }
  Expect(components == plan.modeled_buffer_bytes(),
         row + ": the components do not sum to the modelled bytes");

  const audit::Snapshot base = audit::Take();
  size_t filled = 0;
  uint64_t access_allocations = 0;
  {
    api::ConfiguredByteMap map = api::make_map(plan);
    std::vector<uint8_t> key(key_bytes), value(value_bytes), out(value_bytes);
    if (map.supports_direct_initialization()) {
      auto records = bs::benchmark_support::MakeGeneratedRecords(
          0, key_bytes, value_bytes,
          [&](uint64_t id, uint8_t* o) { Key(id, o, key_bytes); },
          [&](uint64_t id, uint8_t* o, size_t n) { Value(id, o, n); });
      map.initialize(records, capacity);
    } else {
      for (uint64_t id = 0; id < capacity; ++id) {
        Key(id, key.data(), key_bytes);
        Value(id, value.data(), value_bytes);
        map.insert_or_assign(key.data(), value.data());
      }
    }
    map.finish_pending_work();
    filled = audit::Take().live_requested - base.live_requested;

    // Nothing in this loop may allocate on the test's side either: a miss is
    // counted, not reported, until the phase is over.
    audit::Mark();
    uint64_t state = 99, lost = 0;
    for (uint64_t i = 0; i < 2 * capacity; ++i) {
      const uint64_t r = bs::benchmark_support::SplitMix64(state);
      const uint64_t id = r % capacity;
      Key(id, key.data(), key_bytes);
      if ((r >> 63) != 0) {
        Value(id + i, value.data(), value_bytes);
        map.insert_or_assign(key.data(), value.data());
      } else if (!map.find(key.data(), out.data())) {
        ++lost;
      }
    }
    map.finish_pending_work();
    access_allocations = audit::Take().allocations;
    Expect(lost == 0, row + ": " + std::to_string(lost) + " live keys lost");
  }
  const audit::Snapshot after = audit::Take();

  const size_t reserved = plan.modeled_reserved_bytes();
  Expect(filled >= reserved,
         row + ": the live heap (" + std::to_string(filled) +
             " B) is below the plan's reserved bytes (" +
             std::to_string(reserved) + " B), so the plan counts a buffer "
             "the engine does not allocate");
  Expect(filled <= reserved + kUnmodeledBytes,
         row + ": " + std::to_string(filled - reserved) +
             " B of the live heap are in no component of the plan");
  Expect(access_allocations == 0,
         row + ": " + std::to_string(access_allocations) +
             " allocations while accessing");
  Expect(after.live_requested == base.live_requested,
         row + ": " + std::to_string(after.live_requested - base.live_requested) +
             " B still live after destruction");
  std::printf("  %s: %zu B modelled with rounding, %zu B unmodelled, %llu "
              "allocations while accessing\n",
              row.c_str(), reserved, filled >= reserved ? filled - reserved : 0,
              static_cast<unsigned long long>(access_allocations));
}

}  // namespace

int main() {
  {
    // The unwinder's first call allocates; the allocator never captures
    // here, but make the process state the same as the audit's.
    void* frames[4];
    (void)backtrace(frames, 4);
  }
  std::printf("allocation coverage\n");
  for (auto shape : {std::pair<size_t, size_t>{4, 8}, {8, 48}}) {
    for (size_t capacity : {size_t{4096}, size_t{16384}}) {
      for (api::Scheme scheme : {api::Scheme::kHierarchicalIncremental,
                                 api::Scheme::kHierarchicalSynchronous,
                                 api::Scheme::kTree}) {
        CheckEngine(scheme, capacity, shape.first, shape.second);
      }
    }
  }
  if (failures != 0) {
    std::fprintf(stderr, "%d allocation checks failed\n", failures);
    return 1;
  }
  std::printf("allocation coverage: every engine's plan covers its heap, "
              "and no engine allocates while accessing\n");
  return 0;
}
