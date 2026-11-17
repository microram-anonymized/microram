#pragma once

// The layered map (src/oram/tree/DESIGN.md): a position map over a
// CpuReadPathOram.  Every public operation is ONE position-map access and
// ONE tree access, which is one path traversal.
//
//   find(k)              present, old = Exchange(k, fresh, insert = false)
//                        tree.Access(old.uid on old.position if present else
//                                    a fresh random leaf)
//   insert_or_assign     the same with insert = true, then the write
//   exchange             the same, one access, reading and writing the entry
//   erase                Erase(k) on the map; the tree lands nothing
//
// A fresh POSITION is drawn for every access, from the per-instance AES PRF
// over a counter.  A miss reads a fresh random path -- never the zeros an
// absent key comes back with -- so repeated misses do not repeat an address.
// The extra draw is made on every access whatever the outcome, so the PRF
// counter's trace is the same for hits and misses.
//
// THE UID.  An entry needs a name the tree can match on, distinct across live
// entries.  It does NOT need to be nonzero -- what marks a slot as holding an
// entry is the top bit of its position.  There are two ways to get one.
//
//  - `uid_from_key`, when the key fits in 8 bytes: the uid IS the key, and
//    every 64-bit value is a legal uid because the dummy marker lives in the
//    position's top bit and not in the uid (cpu_tree_layout.hpp's THE REAL
//    BIT).  The position map then stores only the position -- and only as
//    many bytes as the tree's depth needs, `ceil(leaf_bits / 8)`, three at
//    2^18 (cpu_tree_position_map.hpp) -- instead of a position and an 8-byte
//    uid, which cuts its arena and its value traffic by 3-5x; the position
//    map is a large share of the cost of a small-value access, so that is
//    the reason to prefer it.  The uid is then STABLE
//    across accesses to the same key, which costs nothing here: the address
//    trace is a function of the leaf alone, and the leaf is redrawn every
//    access.  (An adversary who could read the arena would learn which
//    entries are the same entry -- but such an adversary already reads the
//    values, and encryption at rest is out of scope for both engines.)
//  - otherwise the uid comes from an access counter and is redrawn every
//    access, and the position map stores (position, uid): the position's
//    bytes and then eight of uid.
//
// THE FAILURE EVENT IS FATAL TO THE INSTANCE.  The position map is exchanged
// (or erased) BEFORE the tree is accessed, and the tree access is a pass that
// may throw StashOverflowError.  A throw therefore
// leaves the two structures inconsistent -- a read may have remapped an entry
// that still sits on its old path, an erase may have dropped the only
// reference to data that is still live -- and no local rollback repairs
// that (DESIGN.md, "Security").  So the first exception out of an access
// after the public horizon preflight latches `Failed()`, every later operation
// throws FailedInstanceError, and
// the caller's only recourse is to discard the instance and rebuild it from
// data it holds elsewhere.  How often the event occurs is the stash tail
// measurement (DESIGN.md, "Stash size").

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "src/core/mov_intrinsics.hpp"
#include "src/core/release_guard.hpp"
#include "src/crypto/hash_primitives.hpp"
#include "src/oram/tree/cpu_tree_position_map.hpp"
#include "src/oram/tree/cpu_tree_read_path_oram.hpp"

namespace microram {
namespace tree {

// Thrown by every operation after a previous one failed (see THE FAILURE
// EVENT IS FATAL TO THE INSTANCE above).
struct FailedInstanceError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// `Tree` is the engine holding the values, CpuReadPathOram: synchronous, or
// with one thread per payload plane by `TreeKnobs::payload_max_threads` and
// the public payload width.  A test substitutes its own with the same
// (TreeGeometry, TreeKnobs) constructor and access.
#ifdef MICRORAM_TREE_PHASE_TIMER
// Benchmark instrumentation: CpuTreeMap::phase_nanos(), summed wall ns of
// each access phase.
struct TreePhaseNanos { uint64_t position_map = 0, tree = 0, accesses = 0; };
#endif

template <class PositionMap, class Tree = CpuReadPathOram>
class CpuTreeMap {
 public:
  // `geometry` is the tree to build, as the caller solved it
  // (TreeGeometry::ForCapacity), and `position_map` is constructed by the
  // caller (its arguments differ per type) for `geometry.capacity()` keys of
  // `key_bytes` and the geometry's leaf bits.
  // `uid_from_key` must agree with how `position_map` was built: it stores
  // only the position when the uid is derived from the key.
  CpuTreeMap(const TreeGeometry& geometry, size_t key_bytes, TreeKnobs knobs,
             PositionMap position_map,
             crypto::SecretKeySeed seed = crypto::SecretKeySeed::Random(),
             bool uid_from_key = false)
      : geometry_(geometry),
        tree_(geometry_, knobs),
        position_map_(std::move(position_map)),
        key_bytes_(key_bytes),
        value_bytes_(geometry.value_bytes),
        uid_from_key_(uid_from_key),
        prf_keys_(crypto::DeriveAesRoundKeys(seed)) {
    if (key_bytes == 0) throw std::invalid_argument("key_bytes must be nonzero");
    if (position_map_.key_bytes() != key_bytes) {
      throw std::invalid_argument("position map key width disagrees");
    }
    // The position map stores `ceil(leaf_bits / 8)` bytes of position
    // (cpu_tree_position_map.hpp); one built for a shallower tree would
    // truncate this one's leaves.
    if (position_map_.PositionBits() < geometry_.leaf_bits) {
      throw std::invalid_argument(
          "the position map stores " +
          std::to_string(position_map_.PositionBits()) +
          " bits of position and the tree has " +
          std::to_string(geometry_.leaf_bits) + " leaf bits");
    }
    if (uid_from_key_ && key_bytes > kUidKeyBytes) {
      throw std::invalid_argument(
          "uid_from_key needs a key of at most 8 bytes: a wider key does not "
          "fit the entry's 8-byte uid field");
    }
  }

  bool Read(const uint8_t* key, uint8_t* value_out) {
    return AccessImpl(key, nullptr, value_out, /*insert=*/false, /*erase=*/false);
  }
  // A Read that keeps no value: the same position-map exchange, path read,
  // permutations and eviction, minus the V byte extractions into an output
  // buffer nobody reads.  The choice is on the public operation kind, never
  // on whether the key exists.
  bool Contains(const uint8_t* key) {
    return AccessImpl(key, nullptr, nullptr, /*insert=*/false, /*erase=*/false);
  }
  void Write(const uint8_t* key, const uint8_t* value) {
    (void)AccessImpl(key, value, nullptr, /*insert=*/true, /*erase=*/false);
  }
  // Read and write in ONE access: `old_out` gets the current value (zeros when
  // absent), and the key then holds `value` if it was present or `insert`.
  // The tree does this natively -- the entry is read out and written on the
  // same pass -- so it costs exactly what a Read costs.
  bool Exchange(const uint8_t* key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    // `value` may alias `old_out` (exchange as a swap).  The synchronous
    // engine writes old_out one value chunk at a time while later chunks of
    // the new value are still to be read, so an overlapping buffer would
    // feed old bytes back in as new ones.
    //
    // WHO MAKES THAT COPY.  The threaded engine copies the value into its
    // job slot anyway, because no caller memory may be referenced once the
    // access returns, so a copy here would be a second one.  The engine says
    // whether it already owns the input, and this layer copies only when it
    // does not AND the two buffers actually overlap.  Both are cheap public
    // tests; the overlap one uses `std::less` because `<` on pointers into
    // different objects is unspecified.
    if (tree_.CapturesValueInput() || !Overlaps(value, old_out)) {
      return AccessImpl(key, value, old_out, insert, /*erase=*/false);
    }
    if (exchange_value_.size() != value_bytes_) exchange_value_.resize(value_bytes_);
    std::memcpy(exchange_value_.data(), value, value_bytes_);
    return AccessImpl(key, exchange_value_.data(), old_out, insert,
                      /*erase=*/false);
  }
  bool Erase(const uint8_t* key) {
    return AccessImpl(key, nullptr, nullptr, /*insert=*/false, /*erase=*/true);
  }
  bool Erase(const uint8_t* key, uint8_t* old_out) {
    return AccessImpl(key, nullptr, old_out, /*insert=*/false, /*erase=*/true);
  }

  // Validated independent requests (ByteMap's batch contract). Position
  // remapping is batched; the shared tree/stash still executes in lane order.
  void AccessBatch(size_t n, const cpu_byteslice_oram::BatchRequest* requests,
                   uint8_t* found_out) {
    if (n == 0) return;
    // All position entries are updated before any tree access. Refuse the
    // entire batch before remapping if its public horizon cost does not fit.
    RequireAccessBudget(n);
    // Allocate before mutating either structure. Reuse stable storage on
    // later calls, without introducing a separate batch-width policy.
    batch_positions_.resize(n);
    batch_previous_.resize(n);
    batch_random_.resize(n);
    batch_found_.resize(n);
    try {
      for (size_t i = 0; i < n; ++i) {
        const auto& r = requests[i];
        auto& p = batch_positions_[i];
        p.key = r.key;
        p.next.uid = uid_from_key_ ? KeyUid(r.key) : ++uid_counter_;
        p.next.position = FreshPosition();
        batch_random_[i] = FreshPosition();
        p.erase = r.op == cpu_byteslice_oram::BatchOp::kErase;
        p.insert = r.op == cpu_byteslice_oram::BatchOp::kWrite ||
            r.op == cpu_byteslice_oram::BatchOp::kReadThenWrite ||
            (r.op == cpu_byteslice_oram::BatchOp::kExchange && r.insert);
      }
#ifdef MICRORAM_TREE_PHASE_TIMER
      const uint64_t pm_begin = PhaseNow();
#endif
      position_map_.AccessBatch(n, batch_positions_.data(),
                               batch_previous_.data(), batch_found_.data());
#ifdef MICRORAM_TREE_PHASE_TIMER
      const uint64_t tree_begin = PhaseNow();
      phase_.position_map += tree_begin - pm_begin;
#endif
      for (size_t i = 0; i < n; ++i) {
        const auto& r = requests[i];
        const auto& p = batch_positions_[i];
        const uint8_t* value =
            r.op == cpu_byteslice_oram::BatchOp::kWrite ||
            r.op == cpu_byteslice_oram::BatchOp::kReadThenWrite ||
            r.op == cpu_byteslice_oram::BatchOp::kExchange ? r.value_in : nullptr;
        if (!tree_.CapturesValueInput() && Overlaps(value, r.value_out)) {
          exchange_value_.resize(value_bytes_);
          std::memcpy(exchange_value_.data(), value, value_bytes_);
          value = exchange_value_.data();
        }
        const bool found = AccessTree(p.next, batch_previous_[i], batch_random_[i],
            batch_found_[i] != 0, value, r.value_out, p.insert, p.erase);
        if (found_out) found_out[i] = static_cast<uint8_t>(found);
      }
#ifdef MICRORAM_TREE_PHASE_TIMER
      phase_.tree += PhaseNow() - tree_begin;
      phase_.accesses += n;
#endif
    } catch (...) {
      // Future position entries may already have changed, even when no tree
      // access completed. Only completed tree accesses count or publish found.
      failed_ = true;
      throw;
    }
  }

  size_t Capacity() const { return geometry_.capacity(); }
  size_t KeyBytes() const { return key_bytes_; }
  size_t ValueBytes() const { return value_bytes_; }
  size_t TreeArenaBytes() const { return tree_.ArenaBytes(); }
  double TreeSlotsPerEntry() const { return geometry_.slots_per_entry(); }
  size_t PositionMapArenaBytes() const { return position_map_.ArenaBytes(); }
  size_t ArenaBytes() const { return TreeArenaBytes() + PositionMapArenaBytes(); }
  uint64_t AccessCount() const { return access_count_; }
  // A public preflight for composed callbacks as well as single operations:
  // the position map's access horizon and key-normalization budget.
  // Exhaustion does not corrupt either structure or latch a tree failure.  A
  // position map that has itself failed (a rebuild on an owner thread, its
  // routing budget) refuses here for good, so that refusal latches.
  void RequireAccessBudget(uint64_t accesses) {
    EnsureRunning();
    try {
      position_map_.RequireAccessBudget(accesses);
    } catch (...) {
      if (position_map_.Failed()) failed_ = true;
      throw;
    }
  }
#ifdef MICRORAM_TREE_PHASE_TIMER
  // Benchmark instrumentation: wall time of the two phases of every access since construction
  // (fill included): the position-map exchange (a batch's AccessBatch) and
  // the tree access(es).  Benchmark builds only; refused by release builds.
  const TreePhaseNanos& phase_nanos() const { return phase_; }
#endif
  // Whether an operation failed after its preflight, or the position map
  // has failed. Once true the instance is unusable and every later operation
  // throws FailedInstanceError (the first after a position-map failure
  // rethrows that failure).
  bool Failed() const { return failed_ || position_map_.Failed(); }
  void DrainRebuilds() {
    EnsureRunning();
    try {
      position_map_.DrainRebuilds();
    } catch (...) {
      failed_ = true;
      throw;
    }
  }
  // The tree's own outstanding work: nothing in the synchronous engine, the
  // payload workers' write-back of the last access in the threaded one.  A
  // reader of the storage -- a test, a benchmark's checksum -- must call it;
  // a caller of the map's own operations need not, because the engine
  // orders itself.
  void DrainTree() {
    EnsureRunning();
    try {
      tree_.Drain();
    } catch (...) {
      failed_ = true;
      throw;
    }
  }

  Tree& tree() { return tree_; }
  const Tree& tree() const { return tree_; }
  PositionMap& position_map() { return position_map_; }
  const PositionMap& position_map() const { return position_map_; }
  const TreeGeometry& geometry() const { return geometry_; }
  // Test-only: the leaf the last access read.
  uint64_t LastPositionRead() const { return last_position_read_; }

 private:
  // The key itself, little-endian and zero-extended.  No transformation and no
  // reserved value: the uid field carries no meaning beyond identity, so every
  // 64-bit key is a legal uid, zero included.
  static constexpr size_t kUidKeyBytes = 8;
  uint64_t KeyUid(const uint8_t* key) const {
    uint64_t word = 0;
    std::memcpy(&word, key, key_bytes_);
    return word;
  }

  // Whether the caller's `value` and `old_out` ranges intersect at all --
  // equal buffers, and partial overlap in either direction.
  bool Overlaps(const uint8_t* value, const uint8_t* old_out) const {
    if (old_out == nullptr || value == nullptr) return false;
    std::less<const uint8_t*> before;
    return before(value, old_out + value_bytes_) &&
           before(old_out, value + value_bytes_);
  }

  // One PRF draw: the two-block AES CBC tag (src/crypto) under this map's own
  // key (its seed is independent of the position map's), with the fixed public
  // identity kPositionDomain and the incremented counter as message, so no
  // message repeats.  The leaf is the tag's low L bits.
  uint64_t FreshPosition() {
    const uint64_t tag = crypto::AesCtrTagU64WordsHost(
        kPositionDomain, /*nonce_hi=*/0, ++prf_counter_, prf_keys_);
    return tag & (geometry_.leaves() - 1);
  }

  bool AccessImpl(const uint8_t* key, const uint8_t* value_in,
                  uint8_t* value_out, bool insert, bool erase) {
    RequireAccessBudget(1);
    // Anything thrown from here on may have mutated one structure and not
    // the other: latch, then rethrow.
    try {
      return AccessUnguarded(key, value_in, value_out, insert, erase);
    } catch (...) {
      failed_ = true;
      throw;
    }
  }

  void EnsureRunning() const {
    if (failed_) {
      throw FailedInstanceError(
          "tree ORAM map: a previous operation failed and may have "
          "left the position map and the tree inconsistent; discard this "
          "instance and rebuild it");
    }
  }

  bool AccessUnguarded(const uint8_t* key, const uint8_t* value_in,
                       uint8_t* value_out, bool insert, bool erase) {
    // The uid: the key's, stable, when the position map does not store one;
    // otherwise a fresh one from the access counter.
    const uint64_t uid_new = uid_from_key_ ? KeyUid(key) : ++uid_counter_;
    PositionEntry next;
    next.position = FreshPosition();
    next.uid = uid_new;
    const uint64_t random_path = FreshPosition();
    PositionEntry previous;
#ifdef MICRORAM_TREE_PHASE_TIMER
    const uint64_t pm_begin = PhaseNow();
#endif
    const bool present =
        erase ? position_map_.Erase(key, &previous)
              : position_map_.Exchange(key, next, &previous, insert);
#ifdef MICRORAM_TREE_PHASE_TIMER
    const uint64_t tree_begin = PhaseNow();
    phase_.position_map += tree_begin - pm_begin;
    const bool found = AccessTree(next, previous, random_path, present, value_in, value_out,
                                  insert, erase);
    phase_.tree += PhaseNow() - tree_begin;
    ++phase_.accesses;
    return found;
#else
    return AccessTree(next, previous, random_path, present, value_in, value_out,
                      insert, erase);
#endif
  }
#ifdef MICRORAM_TREE_PHASE_TIMER
  static uint64_t PhaseNow() {
    return static_cast<uint64_t>(std::chrono::duration_cast<std::chrono::nanoseconds>(
        std::chrono::steady_clock::now().time_since_epoch()).count());
  }
  TreePhaseNanos phase_;
#endif

  bool AccessTree(const PositionEntry& next, const PositionEntry& previous,
                  uint64_t random_path, bool present, const uint8_t* value_in,
                  uint8_t* value_out, bool insert, bool erase) {
    TreeAccessRequest req;
    // With the uid derived from the key it is the same before and after, and
    // the position map did not store it.  An absent key names a uid that is
    // simply not on the random path it reads, which finds nothing exactly as
    // a stored-uid miss does.  With a counter uid an absent key comes back
    // with 0, which no live entry carries because the counter starts at 1.
    req.uid_old = uid_from_key_ ? next.uid : previous.uid;
    req.erase = erase;
    req.position_read =
        core::obliSelectU64(random_path, previous.position, present);
    req.uid_new = next.uid;
    req.position_new = next.position;
    req.write = value_in != nullptr;
    req.create = insert;
    last_position_read_ = req.position_read;
    const bool found = tree_.Access(req, value_in, value_out);
    ++access_count_;
    return found;
  }

  // The packed identity's 15-bit level field: a fixed public value, since this
  // key serves only the tree's leaf draws.
  static constexpr uint64_t kPositionDomain = 0x7055ull;

  TreeGeometry geometry_;
  Tree tree_;
  PositionMap position_map_;
  size_t key_bytes_;
  size_t value_bytes_;
  // Exchange's copy of the new value, for the one case that needs it: an
  // aliased buffer on an engine that does not capture its own input.
  // Allocated on first use, so a map that never exchanges never reserves it.
  std::vector<uint8_t> exchange_value_;
  std::vector<PositionBatchRequest> batch_positions_;
  std::vector<PositionEntry> batch_previous_;
  std::vector<uint64_t> batch_random_;
  std::vector<uint8_t> batch_found_;
  bool uid_from_key_ = false;
  crypto::AesRoundKeys prf_keys_;
  uint64_t prf_counter_ = 0;
  uint64_t uid_counter_ = 0;
  uint64_t access_count_ = 0;
  uint64_t last_position_read_ = 0;
  bool failed_ = false;
};

}  // namespace tree
}  // namespace microram
