#pragma once

// The TREE engine's public adapters: `TreeOptions`, `TreeByteMap`, and the
// value-width HYBRID `HybridByteMap` that `Map` is built on.
//
// The tree is a byte-sliced Path ORAM holding the values, with a hierarchical
// position map (a `ByteMap` from byte_map.hpp) holding each key's leaf.  Each
// scalar operation exchanges the key's position-map record for a fresh
// pseudorandom leaf (an AES PRF under a per-instance secret key), then reads,
// evicts and writes back the one root-to-leaf path the OLD leaf names (a
// fresh random path on a miss); the path is therefore independent of the key
// and of earlier accesses.  Values move only along that path, so,
// unlike the hierarchy, the tree never rebuilds a value through levels; only
// the small position records are rebuilt hierarchically.  Wide values are
// split into byte-column planes processed by payload worker threads.  See
// src/oram/tree/DESIGN.md.
//
// Terms: FOLD -- the top levels of the tree held in registers as the STASH
// region instead of in memory; LOAD -- entries per tree slot; UID -- the
// identifier stored with an entry (the key itself when it fits in eight
// bytes, else a counter) so eviction can match it to its position record.

#include <cpu_byteslice_oram/byte_map.hpp>

#include "src/oram/tree/cpu_tree_map.hpp"
#include "src/oram/tree/cpu_tree_position_map.hpp"

#include <cstddef>
#include <cstdint>
#include <functional>
#include <limits>
#include <memory>
#include <optional>
#include <stdexcept>

namespace cpu_byteslice_oram {

// Value bytes per tree payload worker, by default: one worker per started 32
// bytes (PayloadThreadCount).  A worker owning 32 value bytes reads a 128-byte
// run of every four-slot bucket.
inline constexpr size_t kTreePayloadThreshold = 32;
// No fixed cap on the payload workers: the width and the physical cores the
// caller and the position map leave bound the count.
inline constexpr unsigned kTreePayloadUncapped = std::numeric_limits<unsigned>::max();

struct TreeOptions {
  // Top levels omitted from the stored tree: the stash region is the root,
  // with 2^fold children, and the folded levels' slots count against
  // `max_folded_slots`. Zero selects the default rule for the tree's depth L
  // (about log2 N - 2 leaf bits): L - 15 from 17 to 20 leaf bits, which
  // keeps the path at 16 buckets, and 1 otherwise. An explicit fold is 1..5
  // and must leave a path of at most 32 buckets -- at most 16 at fold 5,
  // whose stash was measured only behind a path of one register.
  unsigned fold = 0;
  // Halve the target load once per unit (doubling tree slots per entry);
  // supported range is 0..4.
  unsigned leaf_scale = 0;
  // Zero selects 0.5, the load the stash width was sized for
  // (src/oram/tree/DESIGN.md, "Stash size"). Custom loads need their own
  // stash-failure assessment; this is a sizing parameter.
  double max_load = 0.0;
  // Stash lanes the fold may spend, at most 64 * stash_registers - 1. Zero
  // admits whatever the fold built costs (4 * (2^fold - 1)); a smaller value
  // lowers the default fold to one it pays for.
  unsigned max_folded_slots = 0;
  // 64-lane stash registers: 3 or 4. Zero selects the default rule: 3 up to
  // fold 4 and 4 at fold 5 or from 25 leaf bits (2^27 entries at the default
  // load). An explicit value below the rule's for the depth and fold is
  // refused.
  unsigned stash_registers = 0;
  // Chunks ahead of the transposition to software-prefetch, per path bucket.
  // A performance knob; the buckets read are the same either way.
  unsigned prefetch_ahead = 4;
  // Keys of at most eight bytes can supply their own uid, including zero.
  // The position map then stores only ceil(leaf_bits/8) bytes (at least one);
  // otherwise it also stores an eight-byte counter uid.
  bool uid_from_key = true;
  // Payload chunks after the metadata chunk are split into contiguous planes.
  // Worker count is min(cap, ceil(value_bytes / threshold), available payload
  // chunks) -- one per started `payload_threshold` bytes -- with cap further
  // limited by the physical cores left after the caller and position-map
  // threads. Zero selects the synchronous whole-entry engine.
  unsigned payload_max_threads = kTreePayloadUncapped;
  size_t payload_threshold = kTreePayloadThreshold;
  // Spin before parking. Choose this public policy for the arrival process
  // and idle CPU budget; wake latency depends on the host.
  unsigned payload_spin_micros = 200;
  // Use supported user-mode monitor-wait instructions after the spin window.
  // Unsupported hosts retain the ordinary park/wake path.
  bool payload_monitor_wait = false;
  // Called on each worker at startup with its index; a throw fails construction.
  std::function<void(unsigned)> payload_worker_init;
  // Configuration of the hierarchical position map (a ByteMap): its
  // geometry, threads and `max_accesses`, which also bounds this tree's
  // access horizon.
  Options position_map;
};

// Smaller requested capacities are rounded up to this many entries.
inline constexpr size_t kTreeMinimumCapacity = 128;
// The widest key whose value can serve as the entry's uid.
inline constexpr size_t kUidKeyBytes = 8;

// A fixed-width byte map over the tree ORAM.  DeamortizePositionMap selects
// the position map's engine exactly as ByteMap's template flag does.
//
// THE FAILURE EVENT.  The tree's stash can overflow -- src/oram/tree/DESIGN.md,
// "Stash size", measures how rarely -- and when it does the operation throws
// microram::tree::StashOverflowError.  That exception is FATAL to the map:
// the position map was already updated for the access that failed, so the
// two structures no longer agree, and every later operation throws
// microram::tree::FailedInstanceError.  `failed()` reports the state.  The
// caller must discard the map and reconstruct it from data it holds
// elsewhere; there is no recovery from inside (src/oram/tree/DESIGN.md,
// "Security").
//
// The operations below have ByteMap's contracts (byte_map.hpp): the same
// argument validation, the same zero-filled output on a miss, the same
// secret/public split.  Every operation, hit or miss, read or write, is one
// position-map access plus one path; `access` composes two or three of
// them.
template <bool DeamortizePositionMap = true>
class TreeByteMap {
 public:
  using options_type = TreeOptions;
  static constexpr bool deamortized = DeamortizePositionMap;
  static constexpr bool supports_initialize = false;
  using PositionMap = microram::tree::HierarchicalPositionMap<DeamortizePositionMap>;
  // The tree engine holding the values: synchronous when the PUBLIC width
  // and worker policy select no payload worker, else with one thread per
  // payload plane (src/oram/tree/DESIGN.md, "Parallel payload").
  using Engine = microram::tree::CpuTreeMap<PositionMap>;

  explicit TreeByteMap(size_t requested_capacity, size_t key_bytes,
                       size_t value_bytes, TreeOptions options = {})
      : requested_capacity_(requested_capacity),
        key_bytes_(key_bytes),
        value_bytes_(value_bytes) {
    detail::ValidateCommonArguments(requested_capacity, key_bytes, value_bytes);
    if (requested_capacity < kTreeMinimumCapacity) {
      requested_capacity = kTreeMinimumCapacity;
    }
    uid_from_key_ = options.uid_from_key && key_bytes <= kUidKeyBytes;
    microram::tree::TreeKnobs knobs;
    knobs.fold = options.fold;
    knobs.leaf_scale = options.leaf_scale;
    knobs.shape.max_load = options.max_load;
    knobs.shape.max_folded_slots = options.max_folded_slots;
    knobs.shape.stash_registers = options.stash_registers;
    knobs.prefetch_ahead = options.prefetch_ahead;
    // NO MORE THREADS THAN PHYSICAL CORES (cpu_byteslice_host_cores.hpp):
    // the payload workers get the cores the caller and the position map's own
    // threads leave.
    knobs.payload_max_threads = microram::byteslice::HelpersThatFit(
        options.payload_max_threads,
        detail::SaturatedThreadCount(
            uint64_t{1} + detail::ThreadsBesideCaller<DeamortizePositionMap>(
                              options.position_map)));
    knobs.payload_threshold = options.payload_threshold;
    knobs.payload_spin_micros = options.payload_spin_micros;
    knobs.payload_monitor_wait = options.payload_monitor_wait;
    knobs.payload_worker_init = options.payload_worker_init;
    const microram::tree::TreeGeometry geometry =
        microram::tree::TreeGeometry::ForCapacity(requested_capacity, knobs.fold,
                                                  value_bytes, knobs.leaf_scale,
                                                  knobs.shape);
    // `fold = 0` and `stash_registers = 0` asked the geometry to choose;
    // adopt what it chose so the engine's `knobs()` reports the tree that was
    // actually built.  The engine takes the geometry itself: solved again
    // from the chosen fold and stash, a capacity can fit a level shallower
    // (the stash lanes count toward the load).
    knobs.shape = geometry.shape;
    knobs.fold = geometry.fold;
    engine_ = std::make_unique<Engine>(
        geometry, key_bytes, knobs,
        PositionMap(geometry.capacity(), key_bytes, options.position_map,
                    uid_from_key_, geometry.leaf_bits),
        microram::crypto::SecretKeySeed::Random(), uid_from_key_);
  }

  TreeByteMap(TreeByteMap&&) noexcept = default;
  TreeByteMap& operator=(TreeByteMap&&) noexcept = default;
  TreeByteMap(const TreeByteMap&) = delete;
  TreeByteMap& operator=(const TreeByteMap&) = delete;

  bool find(const uint8_t* key, uint8_t* value_out) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value_out, "value_out must not be null");
    return engine_->Read(key, value_out);
  }
  void insert_or_assign(const uint8_t* key, const uint8_t* value) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value, "value must not be null");
    engine_->Write(key, value);
  }
  void write(const uint8_t* key, const uint8_t* value) {
    insert_or_assign(key, value);
  }

  // The tree's eviction pipeline commits before returning the extracted
  // value, so callback updates use two accesses (three for mutable keys).
  // Invoke before any logical update: a throwing callback preserves data.
  template <class Update>
  bool access(const uint8_t* key, Update&& update) {
    detail::RequirePointer(key, "key must not be null");
    using Callback = detail::AccessCallback<Update, uint8_t*, uint8_t*>;
    // Reject an exhausted composed operation before its first remapping or
    // callback. The source erase must never consume the last available slot
    // before a key-changing callback's destination write.
    engine_->RequireAccessBudget(Callback::changes_key ? 3 : 2);
    access_source_key_.resize(key_bytes_);
    access_key_.resize(key_bytes_);
    access_value_.resize(value_bytes_);
    std::memcpy(access_source_key_.data(), key, key_bytes_);
    std::memcpy(access_key_.data(), key, key_bytes_);
    const bool found = find(access_source_key_.data(), access_value_.data());
    Callback::Invoke(update, access_key_.data(), access_value_.data(), found);
    if constexpr (Callback::changes_key) erase(access_source_key_.data());
    write(access_key_.data(), access_value_.data());
    return found;
  }

  template <class Update>
  bool Access(const uint8_t* key, Update&& update) {
    return access(key, std::forward<Update>(update));
  }
  bool erase(const uint8_t* key) {
    detail::RequirePointer(key, "key must not be null");
    return engine_->Erase(key);
  }
  bool erase(const uint8_t* key, uint8_t* old_out) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(old_out, "old_out must not be null");
    return engine_->Erase(key, old_out);
  }
  // One access that reads and then writes; see ByteMap::exchange.  The tree
  // does it natively -- the entry is read out and written on the same pass.
  bool exchange(const uint8_t* key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    detail::RequirePointer(key, "key must not be null");
    detail::RequirePointer(value, "value must not be null");
    detail::RequirePointer(old_out, "old_out must not be null");
    return engine_->Exchange(key, value, old_out, insert);
  }
  // The same access as `find` -- same position-map exchange, same path,
  // same eviction -- without the value read-out.
  bool contains(const uint8_t* key) {
    detail::RequirePointer(key, "key must not be null");
    return engine_->Contains(key);
  }
  void drain_rebuilds() { engine_->DrainRebuilds(); }
  // The payload workers' outstanding write-back, if any: a reader of the
  // tree's storage must wait for it, a caller of these methods need not.
  void drain_tree() { engine_->DrainTree(); }
  // Both pools may still have work when the API call returns. Neither of the
  // narrower barriers alone is the end of a sustained-throughput trial.
  void finish_pending_work() {
    drain_rebuilds();
    drain_tree();
  }
  // The batch API (ByteMap::access_batch for the independence contract).
  // Batch position-map work, then execute tree accesses in request order.
  // Invalid batches use the scalar path to retain successful-prefix behavior.
  void access_batch(size_t n, const BatchRequest* requests,
                    uint8_t* found_out) {
    if (n == 0) return;
    detail::RequirePointer(requests, "requests must not be null");
    for (size_t i = 0; i < n; ++i) {
      switch (requests[i].op) {
        case BatchOp::kRead:
        case BatchOp::kWrite:
        case BatchOp::kReadThenWrite:
        case BatchOp::kExchange:
        case BatchOp::kErase:
          break;
        default:
          throw std::invalid_argument("invalid batch operation");
      }
    }
    bool valid = n > 1;
    for (size_t i = 0; valid && i < n; ++i) {
      const auto& r = requests[i];
      valid = r.key != nullptr;
      switch (r.op) {
        case BatchOp::kWrite:
        case BatchOp::kReadThenWrite:
        case BatchOp::kExchange:
          valid = valid && r.value_in != nullptr;
          break;
        case BatchOp::kRead:
        case BatchOp::kErase:
          break;
        default:
          valid = false;
      }
    }
    if (valid) {
      engine_->AccessBatch(n, requests, found_out);
      return;
    }
    for (size_t i = 0; i < n; ++i) {
      const BatchRequest& r = requests[i];
      bool found = false;
      switch (r.op) {
        case BatchOp::kRead:
          found = r.value_out ? find(r.key, r.value_out) : contains(r.key);
          break;
        case BatchOp::kWrite:
        case BatchOp::kReadThenWrite:
        case BatchOp::kExchange:
          detail::RequirePointer(r.key, "key must not be null");
          detail::RequirePointer(r.value_in, "value must not be null");
          // A null output skips extraction but still returns membership.
          // This choice depends only on the public request.
          found = engine_->Exchange(r.key, r.value_in, r.value_out,
                                    r.op == BatchOp::kWrite ||
                                        r.op == BatchOp::kReadThenWrite ||
                                        r.insert);
          break;
        case BatchOp::kErase:
          found = r.value_out ? erase(r.key, r.value_out) : erase(r.key);
          break;
      }
      if (found_out != nullptr) found_out[i] = static_cast<uint8_t>(found);
    }
  }
  // Tree execution remains serial; position-map lanes use its own options.
  unsigned batch_participants() const noexcept { return 1; }
  unsigned batch_participant_capacity() const noexcept { return 1; }
  void set_batch_participants(unsigned participants) {
    if (participants != 1)
      throw std::invalid_argument("serial tree backend requires one batch participant");
  }
  unsigned batch_lanes() const noexcept { return 1; }
  unsigned max_combined_batch_lanes() const noexcept { return 1; }
  // Validated as ByteMap validates it, then ignored: the tree's batch width
  // is fixed, and the position map's lanes follow its own options.
  void set_batch_lanes(unsigned lanes) {
    if (lanes < 1 || lanes > kMaxBatchLanes)
      throw std::invalid_argument("tree ORAM map: batch lanes must be in [1, 64]");
  }
  // Whether an operation failed after its preflight, or the position map
  // failed; see above.
  bool failed() const noexcept {
    return engine_->Failed();
  }

  size_t capacity() const noexcept {
    return engine_->Capacity();
  }
  size_t requested_capacity() const noexcept { return requested_capacity_; }
  size_t key_bytes() const noexcept { return key_bytes_; }
  size_t value_bytes() const noexcept { return value_bytes_; }
  // Modeled buffer bytes: the whole map, the tree's planes alone, the tree's
  // physical slots per entry of capacity, and the position map's bytes.
  size_t arena_bytes() const {
    return engine_->ArenaBytes();
  }
  size_t tree_arena_bytes() const {
    return engine_->TreeArenaBytes();
  }
  double tree_slots_per_entry() const {
    return engine_->TreeSlotsPerEntry();
  }
  size_t position_map_arena_bytes() const {
    return engine_->PositionMapArenaBytes();
  }
  uint64_t access_count() const noexcept {
    return engine_->AccessCount();
  }
  // The position map's own map and its access counter: one position-map
  // access per tree access or batch member, and its rebuild carries are the
  // only maintenance cycle longer than one access.
  const ByteMap<DeamortizePositionMap>& position_byte_map() const {
    return engine_->position_map().byte_map();
  }
  uint64_t position_map_access_count() const noexcept {
    return position_byte_map().access_count();
  }
  // Secret: the largest stash-region occupancy seen.  Maintained
  // branch-free inside the engine, so reading it or not changes nothing.
  unsigned max_stash_occupancy() const {
    return engine_->tree().MaxStashOccupancy();
  }
  // Lanes a leftover may occupy, which is what the occupancy above is
  // measured against.
  unsigned stash_capacity() const {
    return engine_->tree().StashCapacity();
  }
  // Whether the tree runs payload workers, and how many payload planes.
  bool uses_payload_workers() const noexcept { return engine_->tree().Threaded(); }
  unsigned payload_planes() const { return engine_->tree().PayloadPlanes(); }
  // How the payload workers wait past their spin window: "none" (parked on
  // a futex, or no workers), "mwaitx" or "umwait" (TreeOptions::payload_monitor_wait).
  const char* payload_monitor_wait_kind() const {
    return microram::core::MonitorWaitKindName(engine_->tree().MonitorWaitKind());
  }
  // Levels, one bucket each, on a stored path: from the fold down to the leaf.
  unsigned path_levels() const {
    return static_cast<unsigned>(engine_->geometry().path_levels());
  }
#ifdef MICRORAM_TREE_PHASE_TIMER
  // Time spent in the position-map and tree phases of every access
  // (benchmark builds only; refused in release builds).
  auto phase_nanos() const { return engine_->phase_nanos(); }
#endif
  // The engine: the position map and the tree, with their own counters.
  Engine& engine() { return *engine_; }
  const Engine& engine() const { return *engine_; }
  // Whether the uid comes from the key, so only the compact position is stored.
  bool uid_from_key() const noexcept { return uid_from_key_; }

 private:
  bool uid_from_key_ = false;
  std::unique_ptr<Engine> engine_;
  size_t requested_capacity_;
  size_t key_bytes_;
  size_t value_bytes_;
  // Callback scratch is allocated on first use and reused thereafter.
  std::vector<uint8_t> access_source_key_;
  std::vector<uint8_t> access_key_;
  std::vector<uint8_t> access_value_;
};

template <typename Key, typename T, bool DeamortizePositionMap = true>
using TreeMap = detail::BasicMap<TreeByteMap<DeamortizePositionMap>, Key, T>;

// The hybrid selects its engine once from public value width and options,
// by the library's default rule (default_rule.hpp) unless a threshold is set.
// Its tree's payload workers are uncapped: the width and the cores bound
// the count.
inline constexpr unsigned kHybridTreePayloadWorkers = kTreePayloadUncapped;
// The hybrid's payload spin window, longer than the tree engine's 200 us
// default: a parked payload worker costs the next access a futex wake on the
// critical path, so a default map trades idle CPU for fewer such wakes.
inline constexpr unsigned kHybridTreePayloadSpinMicros = 2000;

// The payload workers default Map<>'s policy selects at a width (cap
// kHybridTreePayloadWorkers, one per started kTreePayloadThreshold bytes from
// kTreePayloadThreshold on, as PayloadThreadCount).  Fixed by the policy, not
// by host cores.
inline constexpr unsigned HybridPolicyPayloadWorkers(size_t value_bytes) {
  if (value_bytes < kTreePayloadThreshold) return 0;
  const size_t k = value_bytes / kTreePayloadThreshold + (value_bytes % kTreePayloadThreshold != 0);
  return k < kHybridTreePayloadWorkers ? static_cast<unsigned>(k) : kHybridTreePayloadWorkers;
}

// Default Map<>'s tree starts at kHybridTreeValueThreshold (default_rule.hpp),
// where the policy already runs one payload worker.
static_assert(HybridPolicyPayloadWorkers(kHybridTreeValueThreshold) >= 1,
              "the default tree runs at least one payload worker");

inline TreeOptions HybridTreeOptions() {
  TreeOptions options;
  options.payload_max_threads = kHybridTreePayloadWorkers;
  options.payload_spin_micros = kHybridTreePayloadSpinMicros;
  return options;
}

struct HybridOptions {
  // Values of at least this many bytes go to the tree; narrower ones go to the
  // hierarchy.  Set it to 0 to force the tree and to SIZE_MAX to force the
  // hierarchy.
  //
  // Unset, the library's default rule decides (DefaultRule): the tree from
  // kHybridTreeValueThreshold (96) bytes.  That is the crossover at the
  // DEFAULT payload-worker policy, whatever `tree` says; a caller who changes
  // `tree.payload_max_threads` or `tree.payload_threshold` moves the crossover
  // with it and should set this too.
  std::optional<size_t> tree_value_threshold;
  // Whichever engine runs, these configure it.
  Options hierarchical;
  // Initialized with the hybrid's payload-worker budget, not with
  // `TreeOptions{}`; see `HybridTreeOptions`.
  TreeOptions tree = HybridTreeOptions();

  HybridOptions() = default;
  // A plain `Options` configures whichever engine is picked: the hierarchy
  // directly, or the tree's position map (`tree.position_map`).  The tree's
  // own fields keep the hybrid's defaults (`HybridTreeOptions`).
  HybridOptions(const Options& options)  // NOLINT(google-explicit-constructor)
      : hierarchical(options) {
    tree.position_map = options;
  }
};

// ByteMap's interface over whichever engine the value width selects.  The
// choice is made once, at construction, from PUBLIC arguments, so it reveals
// nothing; every operation forwards to that engine with its contract.
template <bool Deamortize = true>
class HybridByteMap {
 public:
  using options_type = HybridOptions;
  static constexpr bool deamortized = Deamortize;
  using Hierarchical = ByteMap<Deamortize>;
  using Tree = TreeByteMap<Deamortize>;
  // No bulk initializer.  Which engine this map is, is decided from the value
  // width at construction, and only the hierarchical one has a largest level
  // to build directly; promising `initialize` here would promise a
  // hierarchical construction for a tree.  `HierarchicalMap` / `ByteMap` have
  // it.
  static constexpr bool supports_initialize = false;

  explicit HybridByteMap(size_t requested_capacity, size_t key_bytes,
                         size_t value_bytes, HybridOptions options = {}) {
    const bool tree = options.tree_value_threshold
                          ? value_bytes >= *options.tree_value_threshold
                          : DefaultRule(value_bytes).tree;
    if (tree) {
      if (options.hierarchical.deamortized_batch_participants > 1)
        throw std::invalid_argument("serial tree backend requires batch_participants <= 1");
      tree_ = std::make_unique<Tree>(requested_capacity, key_bytes, value_bytes,
                                     std::move(options.tree));
    } else {
      hierarchical_ = std::make_unique<Hierarchical>(
          requested_capacity, key_bytes, value_bytes,
          std::move(options.hierarchical));
    }
  }

  // Configured as resolve_options(Scheme::kAuto) at `budget`; defined in
  // configuration.hpp, which <cpu_byteslice_oram/oram.hpp> includes.  Throws
  // std::invalid_argument when neither engine fits the budget.
  HybridByteMap(size_t requested_capacity, size_t key_bytes, size_t value_bytes,
                CoreBudget budget);

  HybridByteMap(HybridByteMap&&) noexcept = default;
  HybridByteMap& operator=(HybridByteMap&&) noexcept = default;
  HybridByteMap(const HybridByteMap&) = delete;
  HybridByteMap& operator=(const HybridByteMap&) = delete;

  bool find(const uint8_t* key, uint8_t* value_out) {
    return tree_ ? tree_->find(key, value_out)
                 : hierarchical_->find(key, value_out);
  }
  void insert_or_assign(const uint8_t* key, const uint8_t* value) {
    if (tree_) {
      tree_->insert_or_assign(key, value);
    } else {
      hierarchical_->insert_or_assign(key, value);
    }
  }
  void write(const uint8_t* key, const uint8_t* value) {
    insert_or_assign(key, value);
  }
  template <class Update>
  bool access(const uint8_t* key, Update&& update) {
    return tree_ ? tree_->access(key, std::forward<Update>(update))
                 : hierarchical_->access(key, std::forward<Update>(update));
  }
  template <class Update>
  bool Access(const uint8_t* key, Update&& update) {
    return access(key, std::forward<Update>(update));
  }
  bool exchange(const uint8_t* key, const uint8_t* value, uint8_t* old_out,
                bool insert) {
    return tree_ ? tree_->exchange(key, value, old_out, insert)
                 : hierarchical_->exchange(key, value, old_out, insert);
  }
  bool erase(const uint8_t* key) {
    return tree_ ? tree_->erase(key) : hierarchical_->erase(key);
  }
  bool erase(const uint8_t* key, uint8_t* old_out) {
    return tree_ ? tree_->erase(key, old_out)
                 : hierarchical_->erase(key, old_out);
  }
  bool contains(const uint8_t* key) {
    return tree_ ? tree_->contains(key) : hierarchical_->contains(key);
  }
  void drain_rebuilds() {
    if (tree_) {
      tree_->drain_rebuilds();
    } else {
      hierarchical_->drain_rebuilds();
    }
  }
  // The batch API (ByteMap::access_batch): the tree batches its position map
  // while retaining ordered tree accesses; the hierarchy batches its cascade.
  void access_batch(size_t n, const BatchRequest* requests,
                    uint8_t* found_out) {
    if (tree_) {
      tree_->access_batch(n, requests, found_out);
    } else {
      hierarchical_->access_batch(n, requests, found_out);
    }
  }
  unsigned batch_participants() const noexcept {
    return tree_ ? tree_->batch_participants() : hierarchical_->batch_participants();
  }
  unsigned batch_participant_capacity() const noexcept {
    return tree_ ? tree_->batch_participant_capacity()
                 : hierarchical_->batch_participant_capacity();
  }
  void set_batch_participants(unsigned participants) {
    if (tree_) tree_->set_batch_participants(participants);
    else hierarchical_->set_batch_participants(participants);
  }
  unsigned batch_lanes() const noexcept {
    return tree_ ? tree_->batch_lanes() : hierarchical_->batch_lanes();
  }
  unsigned max_combined_batch_lanes() const noexcept {
    return tree_ ? tree_->max_combined_batch_lanes()
                 : hierarchical_->max_combined_batch_lanes();
  }
  void set_batch_lanes(unsigned lanes) {
    if (tree_) {
      tree_->set_batch_lanes(lanes);
    } else {
      hierarchical_->set_batch_lanes(lanes);
    }
  }
  // Whether the selected engine has failed and refuses further work
  // (TreeByteMap::failed, ByteMap::failed).
  bool failed() const noexcept {
    return tree_ ? tree_->failed() : hierarchical_->failed();
  }

  size_t capacity() const noexcept {
    return tree_ ? tree_->capacity() : hierarchical_->capacity();
  }
  size_t requested_capacity() const noexcept {
    return tree_ ? tree_->requested_capacity()
                 : hierarchical_->requested_capacity();
  }
  size_t key_bytes() const noexcept {
    return tree_ ? tree_->key_bytes() : hierarchical_->key_bytes();
  }
  size_t value_bytes() const noexcept {
    return tree_ ? tree_->value_bytes() : hierarchical_->value_bytes();
  }
  size_t arena_bytes() const {
    return tree_ ? tree_->arena_bytes() : hierarchical_->arena_bytes();
  }
  void finish_pending_work() {
    if (tree_) tree_->finish_pending_work();
    else hierarchical_->finish_pending_work();
  }
  uint64_t access_count() const noexcept {
    return tree_ ? tree_->access_count() : hierarchical_->access_count();
  }

  // Which engine was picked, and the engines themselves for callers that want
  // the counters only one of them has.  `tree()` and `hierarchical()` return
  // null for the engine that was not built.
  bool uses_tree() const noexcept { return tree_ != nullptr; }
  Tree* tree() noexcept { return tree_.get(); }
  const Tree* tree() const noexcept { return tree_.get(); }
  Hierarchical* hierarchical() noexcept { return hierarchical_.get(); }
  const Hierarchical* hierarchical() const noexcept {
    return hierarchical_.get();
  }

 private:
  std::unique_ptr<Tree> tree_;
  std::unique_ptr<Hierarchical> hierarchical_;
};

}  // namespace cpu_byteslice_oram
