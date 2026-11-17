// The tree map's composition boundary (CpuTreeMap in cpu_tree_map.hpp, which
// joins a position map to the tree ORAM engine), with both sides replaced by
// tracing and fault-injecting stand-ins.  Deterministic request tracing: a
// batch must issue exactly the same sequence of tree requests (uids, read and
// new positions, write/create/erase flags) as the same requests issued one at
// a time, so batching changes neither the PRF draws nor what the tree sees.
// Fault injection: a failure in the tree, the position map or a background
// drain must latch the instance as failed, publish results only for the
// requests that completed, and make every later call refuse.
#include "src/oram/tree/cpu_tree_map.hpp"
#include "tests/oram/cpu_byteslice_test_support.hpp"
#include <array>
#include <cstdio>
#include <vector>
using namespace microram::tree;
using microram::byteslice::test_support::Expect;
using microram::byteslice::test_support::ExpectThrowsAs;
namespace o = cpu_byteslice_oram;
struct TraceTree {
  TraceTree(TreeGeometry, TreeKnobs) {}
  bool CapturesValueInput() const { return false; }
  bool Access(const TreeAccessRequest& r, const uint8_t*, uint8_t* out) {
    if (trace.size() == fail_at) throw StashOverflowError("injected tree failure");
    trace.push_back(r);
    if (out) *out = 0x40 + trace.size();
    return true;
  }
  void Drain() {
    if (fail_drain) throw std::runtime_error("injected payload drain failure");
  }
  std::vector<TreeAccessRequest> trace;
  size_t fail_at = size_t(-1);
  bool fail_drain = false;
};
struct FaultPosition : UnorderedPositionMap {
  using UnorderedPositionMap::UnorderedPositionMap;
  void AccessBatch(size_t n, const PositionBatchRequest* req,
                   PositionEntry* old, uint8_t* found) {
    if (fail) {
      UnorderedPositionMap::AccessBatch(1, req, old, found);
      throw std::runtime_error("injected position failure after mutation");
    }
    UnorderedPositionMap::AccessBatch(n, req, old, found);
  }
  bool fail = false;
  bool fail_drain = false;
  void DrainRebuilds() {
    if (fail_drain) throw std::runtime_error("injected position drain failure");
  }
};
using Map = CpuTreeMap<FaultPosition, TraceTree>;
Map Make(bool uid) {
  return Map(TreeGeometry::ForCapacity(512, 0, 1), 8, {}, FaultPosition(512, 8),
             microram::crypto::SecretKeySeed::Fixed(42), uid);
}
void Compare(const TreeAccessRequest& a, const TreeAccessRequest& b) {
  Expect(a.uid_old == b.uid_old && a.uid_new == b.uid_new &&
         a.position_read == b.position_read && a.position_new == b.position_new &&
         a.write == b.write && a.create == b.create && a.erase == b.erase,
         "batch changed PRF/UID/request sequence");
}
int main() {
  constexpr size_t n = 65;
  std::array<uint64_t, n> keys{};
  std::array<uint8_t, n> values{}, outputs{}, found{};
  std::array<o::BatchRequest, n> requests{};
  for (size_t i = 0; i < n; ++i) {
    keys[i] = (i / 9) % 3;
    const o::BatchOp ops[] = {o::BatchOp::kWrite, o::BatchOp::kRead,
        o::BatchOp::kExchange, o::BatchOp::kErase, o::BatchOp::kRead};
    requests[i] = {ops[i % 5], (i % 2) != 0,
        reinterpret_cast<uint8_t*>(&keys[i]), &values[i], &outputs[i]};
  }
  for (bool uid : {false, true}) {
    auto scalar = Make(uid), batch = Make(uid);
    for (const auto& r : requests) {
      switch (r.op) {
        case o::BatchOp::kRead: scalar.Read(r.key, r.value_out); break;
        case o::BatchOp::kWrite: scalar.Exchange(r.key, r.value_in, r.value_out, true); break;
        case o::BatchOp::kExchange: scalar.Exchange(r.key, r.value_in, r.value_out, r.insert); break;
        case o::BatchOp::kErase: scalar.Erase(r.key, r.value_out); break;
      }
    }
    batch.AccessBatch(n, requests.data(), found.data());
    // A subsequent scalar access also catches over/under-consumed PRF draws.
    scalar.Contains(requests[0].key); batch.Contains(requests[0].key);
    for (size_t i = 0; i <= n; ++i)
      Compare(scalar.tree().trace[i], batch.tree().trace[i]);
    Expect(batch.AccessCount() == n + 1, "wrong successful batch count");
  }
  for (size_t fail_at : {0u, 1u, 17u, 64u}) {
    auto map = Make(false);
    map.tree().fail_at = fail_at;
    outputs.fill(0xa5); found.fill(0xa5);
    ExpectThrowsAs<StashOverflowError>([&] {
      map.AccessBatch(n, requests.data(), found.data());
    }, "tree failure did not propagate");
    Expect(map.Failed() && map.AccessCount() == fail_at, "failure/count not latched");
    for (size_t i = 0; i < n; ++i) {
      Expect(found[i] == (i < fail_at ? 1 : 0xa5), "found prefix differs");
      Expect(outputs[i] == (i < fail_at ? 0x41 + i : 0xa5), "output prefix differs");
    }
    ExpectThrowsAs<FailedInstanceError>([&] { map.Contains(requests[0].key); },
                                       "scalar accepted failed instance");
    ExpectThrowsAs<FailedInstanceError>([&] {
      map.AccessBatch(n, requests.data(), found.data());
    }, "batch accepted failed instance");
  }
  auto map = Make(false);
  map.position_map().fail = true;
  outputs.fill(0xa5); found.fill(0xa5);
  ExpectThrowsAs<std::runtime_error>([&] {
    map.AccessBatch(n, requests.data(), found.data());
  }, "position failure did not propagate");
  Expect(map.Failed() && map.AccessCount() == 0 && map.tree().trace.empty(),
         "position failure reached tree or did not latch");
  for (size_t i = 0; i < n; ++i)
    Expect(outputs[i] == 0xa5 && found[i] == 0xa5, "position failure published output");
  for (bool payload : {false, true}) {
    auto drained = Make(false);
    drained.tree().fail_drain = payload;
    drained.position_map().fail_drain = !payload;
    ExpectThrowsAs<std::runtime_error>([&] {
      if (payload) drained.DrainTree();
      else drained.DrainRebuilds();
    }, "background failure did not propagate from drain");
    Expect(drained.Failed(), "background failure was not latched by drain");
    drained.tree().fail_drain = false;
    drained.position_map().fail_drain = false;
    ExpectThrowsAs<FailedInstanceError>([&] { drained.DrainTree(); },
                                       "tree drain accepted failed instance");
    ExpectThrowsAs<FailedInstanceError>([&] { drained.DrainRebuilds(); },
                                       "position drain accepted failed instance");
    ExpectThrowsAs<FailedInstanceError>([&] { drained.Contains(requests[0].key); },
                                       "access accepted failed drained instance");
  }
  std::puts("cpu_tree_batch_test passed");
}
