#pragma once
// SONIC's ZingORAM as a map (README.md in this directory): the data tree
// with its position map outside (a plain array, as SONIC's harness keeps it) or
// with a recursive position map built from ZingORAM trees (our construction).
//
// Map level i (1..L) is a ZingORAM tree whose block j holds the leaf labels of
// blocks j*b .. j*b+b-1 of level i-1, level 0 being the data tree; the top map,
// at most C labels, is an array scanned in full. Requests run in windows of W
// lanes (W = 1 for scalar calls), one tree at a time, top first. ZingORAM needs
// concurrent accesses to target distinct blocks, so each tree round lets the
// first lane of each run of lanes sharing a block access it (the run's
// representative) and sends the others to a dummy address on a random leaf.
// The representative's mutator serves the whole run; every access, dummy or
// not, runs the same mutator over all W lanes with masked writes, so the
// instruction trace does not depend on the duplicates. Mutator outputs go to a
// private row per access and are combined after the round's barrier.
#include "sonic/crypto/buffered_prng.hpp"
#include "sonic/obliv/ops/core_ops.hpp"
#include "sonic/obliv/ops/word_ops.hpp"
#include "sonic/oram/zingoram/analysis.hpp"
#include "sonic/oram/zingoram/client.hpp"
#include "sonic/oram/zingoram/detail/bucket_metadata_arena.hpp"
#include "sonic/oram/zingoram/detail/epoch_state.hpp"
#include "sonic/oram/zingoram/traits.hpp"
#include "sonic/threads/thread_team.hpp"

#include <algorithm>
#include <chrono>
#include <array>
#include <cstdint>
#include <cstring>
#include <exception>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <string>
#include <vector>

namespace oram_bench::sonic {
namespace zo = sn::oram::zingoram;
constexpr unsigned kMaxLanes = 16;  // W <= 15 access threads fit the 15-core budget

struct TreeParams {
  uint32_t real = 8, dummy = 12, rate = 0, batch = 1;  // Z, S, A (0: SONIC's largest for Z), E
};
// A tree as SONIC's state derives it (zingoram/state.hpp), without allocating.
struct Geometry {
  uint64_t blocks = 0, base_rate = 0, height = 0, leaves = 0, nodes = 0, stash_bound = 0, bytes = 0;
  uint32_t routing = 0;
};
inline size_t BlockObjectBytes(size_t data_bytes) {  // sizeof(sn::oram::tree::block<data_bytes>) with AVX-512
  const size_t align = data_bytes >= 64 ? 64 : data_bytes >= 32 ? 32 : data_bytes >= 16 ? 16 : 8;
  return (data_bytes + 3 * sizeof(uint64_t) + align - 1) / align * align;
}
// Beside its blocks, SONIC's state keeps one bucket object and one epoch state
// per node (zingoram/state.hpp: storage_ and epoch_states_). Neither depends on
// the block width; ZingTree checks that. They are a large share of the memory,
// so the model counts them.
constexpr size_t kNodeObjectBytes =
    sizeof(zo::traits<8>::bucket_t) + sizeof(zo::detail::bucket_epoch_state);
inline Geometry TreeGeometry(uint64_t blocks, const TreeParams& p, uint32_t routing, size_t data_bytes) {
  Geometry g;
  g.blocks = blocks;
  g.base_rate = p.rate ? p.rate : zo::analysis::max_eviction_rate(p.real);
  g.height = zo::analysis::zingoram_tree_height(blocks, static_cast<uint32_t>(g.base_rate));
  // SONIC's height is ceil(log2(ceil(2N/A))) - 1 in unsigned arithmetic: a tree
  // of at most A/2 blocks wraps it to 2^64 - 1. SONIC's state refuses a height
  // of 63 or more, and the shift below needs one under 64.
  if (g.height >= 63)
    throw std::invalid_argument("sonic: a ZingORAM tree needs more than A/2 = " + std::to_string(g.base_rate / 2) +
                                " blocks; this one has " + std::to_string(blocks));
  g.leaves = uint64_t{1} << g.height;
  g.nodes = 2 * g.leaves - 1;
  g.routing = static_cast<uint32_t>(std::min<uint64_t>(routing, g.height));
  g.stash_bound = zo::analysis::stash_bound(p.real, g.base_rate, 80);  // SONIC's 2^-80
  const size_t block = BlockObjectBytes(data_bytes);
  // Buckets, their metadata and node objects, and a stash of stash_bound blocks
  // (twice, for the global stash's modifications). A small per-node and
  // per-process remainder stays unmodelled; memory telemetry (VmHWM) measures
  // the real peak.
  g.bytes = (g.nodes + 1) * ((p.real + p.dummy) * block + kNodeObjectBytes) +
            zo::detail::bucket_metadata_arena::planned(g.nodes, p.real, p.dummy).total + 2 * g.stash_bound * block;
  return g;
}

// One window's lanes, in lane (request) order.
struct Window {
  unsigned lanes = 0;
  std::array<uint64_t, kMaxLanes> key{};
  std::array<bool, kMaxLanes> write{};
};

// A map round: tree i's blocks, their children's entries and fresh labels.
struct MapRound {
  const Window* window = nullptr;
  std::array<uint64_t, kMaxLanes> block{}, entry{};
  std::array<uint32_t, kMaxLanes> child_next{};  // the child's new label
  std::array<bool, kMaxLanes> child_rep{};       // this lane's child is new in its run
  // Per access row r and lane w: the child's old label, and whether row r served w.
  std::array<std::array<uint32_t, kMaxLanes>, kMaxLanes> out{};
  std::array<std::array<bool, kMaxLanes>, kMaxLanes> valid{};
};

// The data round: each lane's value in (for writes) and its result out.
struct DataRound {
  const Window* window = nullptr;
  size_t block_bytes = 0;
  const uint8_t* values = nullptr;   // lanes x block_bytes
  uint8_t* rows = nullptr;           // rows x lanes x block_bytes
  std::array<std::array<bool, kMaxLanes>, kMaxLanes> valid{};
};

// A map block's mutator, run by every access of a map round as row `row`: for
// each lane of the run whose block this is, the child's old label goes to the
// row's output, and each child new to the run gets its fresh label. Reads come
// first, so every lane of a run sees the old labels. A dummy (real false), or a
// block no lane wants, changes nothing; the work is the same either way.
inline void MapMutate(uint32_t* entries, size_t count, bool real, int64_t address, MapRound& round, unsigned row) {
  const unsigned lanes = round.window->lanes;
  std::array<bool, kMaxLanes> in_run{};
  for (unsigned w = 0; w < lanes; ++w) {
    in_run[w] = real & sn::obliv::ct_eq<int64_t>(address, static_cast<int64_t>(round.block[w]));
    uint32_t old = 0;
    for (size_t j = 0; j < count; ++j) sn::obliv::ct_set<uint32_t>(&old, entries[j], j == round.entry[w]);
    sn::obliv::ct_set<uint32_t>(&round.out[row][w], old, in_run[w]);
    round.valid[row][w] = in_run[w];
  }
  for (unsigned w = 0; w < lanes; ++w) {
    const bool update = in_run[w] & round.child_rep[w];
    for (size_t j = 0; j < count; ++j)
      sn::obliv::ct_set<uint32_t>(&entries[j], round.child_next[w], update & (j == round.entry[w]));
  }
}

// A data block's mutator: the run's lanes in request order. A read returns the
// latest earlier write of its run, or the value before the window; a write
// returns the value before it; the block keeps the last write.
template <size_t Bytes>
void DataMutate(uint8_t* data, bool real, int64_t address, DataRound& round, unsigned row) {
  alignas(64) std::array<uint8_t, Bytes> value;
  std::memcpy(value.data(), data, Bytes);
  for (unsigned w = 0; w < round.window->lanes; ++w) {
    const bool in_run = real & sn::obliv::ct_eq<int64_t>(address, static_cast<int64_t>(round.window->key[w]));
    uint8_t* out = round.rows + (size_t{row} * kMaxLanes + w) * Bytes;
    sn::obliv::ct_set_words<Bytes>(out, value.data(), in_run);
    round.valid[row][w] = in_run;
    sn::obliv::ct_set_words<Bytes>(value.data(), round.values + size_t{w} * Bytes, in_run & round.window->write[w]);
  }
  sn::obliv::ct_set_words<Bytes>(data, value.data(), real);
}

class Tree {
 public:
  virtual ~Tree() = default;
  virtual const Geometry& geometry() const = 0;
  // Access `address` (or -1, a dummy) from worker slot `worker` as row `row`.
  virtual void AccessMap(unsigned worker, unsigned row, int64_t address, uint64_t cur, uint64_t next,
                         MapRound& round) = 0;
  virtual void AccessData(unsigned worker, unsigned row, int64_t address, uint64_t cur, uint64_t next,
                          DataRound& round) = 0;
};

template <size_t Bytes>
class ZingTree final : public Tree {
 public:
  using traits = zo::traits<Bytes>;
  using client_t = zo::client<traits>;
  static constexpr size_t kEntries = Bytes / sizeof(uint32_t);
  static_assert(sizeof(typename traits::bucket_t) == sizeof(zo::traits<8>::bucket_t),
                "kNodeObjectBytes assumes a width-independent bucket object");

  ZingTree(uint64_t blocks, const TreeParams& p, uint32_t routing, unsigned access_threads,
           sn::threads::thread_team eviction, unsigned workers)
      : geometry_(TreeGeometry(blocks, p, routing, Bytes)),
        client_(Options(blocks, p, access_threads, geometry_.routing), std::move(eviction)),
        scratch_(workers), io_(workers) {
    client_.initialize();  // an empty tree: a block comes into existence on its first access
    for (auto& scratch : scratch_) client_.configure_access_scratch(scratch);
    if (client_.shape().leaf_count != geometry_.leaves || client_.shape().height != geometry_.height)
      throw std::logic_error("sonic: tree geometry differs from the resolved one");
  }
  const Geometry& geometry() const override { return geometry_; }

  void AccessMap(unsigned worker, unsigned row, int64_t address, uint64_t cur, uint64_t next,
                 MapRound& round) override {
    Run(worker, address, cur, next, [&](auto& block) {
      MapMutate(reinterpret_cast<uint32_t*>(block.data.data()), kEntries, block.is_real().unwrap(), block.address,
                round, row);
    });
  }
  void AccessData(unsigned worker, unsigned row, int64_t address, uint64_t cur, uint64_t next,
                  DataRound& round) override {
    Run(worker, address, cur, next, [&](auto& block) {
      DataMutate<Bytes>(block.data.data(), block.is_real().unwrap(), block.address, round, row);
    });
  }

 private:
  static typename traits::options_t Options(uint64_t blocks, const TreeParams& p, unsigned access_threads,
                                            uint32_t routing) {
    typename traits::options_t o{};
    o.block_count = blocks;
    o.routing_depth = routing;
    o.bucket_real_size = p.real;
    o.bucket_dummy_size = p.dummy;
    o.eviction_rate = p.rate;
    o.evict_batch = p.batch;
    o.access_concurrency = access_threads;
    return o;
  }
  template <class Mutate> void Run(unsigned worker, int64_t address, uint64_t cur, uint64_t next, Mutate&& mutate) {
    auto& io = io_[worker];
    sn::oram::access_request request{};
    request.address = address;
    request.cur_leaf = static_cast<int64_t>(cur);
    request.new_leaf = static_cast<int64_t>(next);
    request.in = sn::util::span<uint8_t>(io.in.data(), Bytes);
    request.out = sn::util::span<uint8_t>(io.out.data(), Bytes);
    client_.access(request, scratch_[worker], [&](auto& block, const sn::oram::access_request&) { mutate(block); });
  }
  struct Io { alignas(64) std::array<uint8_t, Bytes> in{}, out{}; };
  Geometry geometry_;
  client_t client_;
  std::vector<typename client_t::access_scratch> scratch_;
  std::vector<Io> io_;
};

// The map: windows through the top map, the map trees (level L down to 1) and
// the data tree. With `recursive` false the position map is a plain array.
struct EngineConfig {
  uint64_t entries = 0;
  size_t block_bytes = 8;
  bool recursive = false;
  unsigned branching = 16;
  uint64_t top_entries = 4096;
};
// The map levels for N entries: the smallest L with ceil(N / b^L) <= C.
inline unsigned MapLevels(uint64_t entries, unsigned branching, uint64_t top_entries) {
  unsigned levels = 0;
  for (uint64_t blocks = entries; blocks > top_entries; blocks = (blocks + branching - 1) / branching) ++levels;
  return levels;
}

// Wall time of Engine::Run's two parts, summed on the calling thread: the position map (the top scan and the map
// trees; outside, the plain array) and the data tree. Three clock reads per window (negligible against an
// ORAM access), so a recursive row also reports what SONIC's own ORAM costs inside it.
struct PhaseTimes {
  uint64_t windows = 0, accesses = 0, map_ns = 0, data_ns = 0;
};

class Engine {
 public:
  // `maps` holds levels 1..L; `access` runs a window's rows (null: one lane at a time).
  Engine(EngineConfig config, std::unique_ptr<Tree> data, std::vector<std::unique_ptr<Tree>> maps,
         sn::threads::thread_team* access)
      : config_(config), data_(std::move(data)), maps_(std::move(maps)), access_(access),
        rows_(size_t{kMaxLanes} * kMaxLanes * config.block_bytes) {
    power_.push_back(1);
    for (size_t i = 0; i < maps_.size(); ++i) power_.push_back(power_.back() * config_.branching);
    if (config_.recursive) {
      if (maps_.size() != MapLevels(config_.entries, config_.branching, config_.top_entries))
        throw std::logic_error("sonic: map levels differ from the configuration");
      top_.resize((config_.entries + power_.back() - 1) / power_.back());
      for (auto& label : top_) label = Random(Leaves(maps_.size()));  // level-L blocks start on random paths
    } else {
      if (!maps_.empty()) throw std::logic_error("sonic: map trees without a recursive map");
      position_.resize(config_.entries);
      for (auto& label : position_) label = Random(Leaves(0));
    }
  }
  unsigned levels() const { return static_cast<unsigned>(maps_.size()); }
  uint64_t top_entries() const { return top_.size(); }
  const Tree& tree(unsigned level) const { return level ? *maps_[level - 1] : *data_; }
  const PhaseTimes& phase_times() const { return times_; }

  // One window: `values` and `results` hold lanes x block_bytes, in lane order.
  void Run(const Window& window, const uint8_t* values, uint8_t* results) {
    const unsigned lanes = window.lanes;
    if (!lanes || lanes > kMaxLanes || (lanes > 1 && !access_)) throw std::logic_error("sonic: bad window");
    for (unsigned w = 0; w < lanes; ++w)
      if (window.key[w] >= config_.entries) throw std::logic_error("sonic: key outside the map");
    const auto map_begin = std::chrono::steady_clock::now();
    std::array<uint64_t, kMaxLanes> block{}, label{}, next{};
    std::array<bool, kMaxLanes> rep{};
    const unsigned top = levels();
    if (config_.recursive) {
      // The top map: every lane scans it in full; a run's first lane reads its
      // block's label and replaces it.
      Blocks(window, top, block);
      Reps(lanes, block, rep);
      for (unsigned w = 0; w < lanes; ++w) {
        next[w] = Random(Leaves(top));
        uint32_t old = 0;
        for (uint64_t j = 0; j < top_.size(); ++j) sn::obliv::ct_set<uint32_t>(&old, top_[j], j == block[w]);
        label[w] = old;
        for (uint64_t j = 0; j < top_.size(); ++j)
          sn::obliv::ct_set<uint32_t>(&top_[j], static_cast<uint32_t>(next[w]), rep[w] & (j == block[w]));
      }
      for (unsigned level = top; level >= 1; --level) {
        map_round_ = MapRound{};
        auto& round = map_round_;
        round.window = &window;
        round.block = block;
        std::array<uint64_t, kMaxLanes> child{};
        Blocks(window, level - 1, child);
        Reps(lanes, child, round.child_rep);
        for (unsigned w = 0; w < lanes; ++w) {
          round.entry[w] = child[w] % config_.branching;
          round.child_next[w] = static_cast<uint32_t>(Random(Leaves(level - 1)));
        }
        std::array<Leg, kMaxLanes> legs = Legs(lanes, block, label, next, rep, Leaves(level));
        Rows(lanes, [&](unsigned worker, unsigned w) {
          maps_[level - 1]->AccessMap(worker, w, legs[w].address, legs[w].cur, legs[w].next, round);
        });
        for (unsigned w = 0; w < lanes; ++w) {
          uint32_t old = 0;
          for (unsigned r = 0; r < lanes; ++r) sn::obliv::ct_set<uint32_t>(&old, round.out[r][w], round.valid[r][w]);
          label[w] = old;
          next[w] = round.child_next[w];
        }
        block = child;
        rep = round.child_rep;
      }
    } else {
      // The position map outside: a plain array, as SONIC's harness keeps it.
      Blocks(window, 0, block);
      Reps(lanes, block, rep);
      for (unsigned w = 0; w < lanes; ++w) {
        next[w] = Random(Leaves(0));
        label[w] = position_[block[w]];
        sn::obliv::ct_set<uint32_t>(&position_[block[w]], static_cast<uint32_t>(next[w]), rep[w]);
      }
    }
    // The data tree.
    const auto data_begin = std::chrono::steady_clock::now();
    data_round_ = DataRound{};
    auto& round = data_round_;
    round.window = &window;
    round.block_bytes = config_.block_bytes;
    round.values = values;
    round.rows = rows_.data();
    std::array<Leg, kMaxLanes> legs = Legs(lanes, block, label, next, rep, Leaves(0));
    Rows(lanes, [&](unsigned worker, unsigned w) {
      data_->AccessData(worker, w, legs[w].address, legs[w].cur, legs[w].next, round);
    });
    const size_t bytes = config_.block_bytes;
    for (unsigned w = 0; w < lanes; ++w) {
      auto out = sn::util::span<uint8_t>(results + size_t{w} * bytes, bytes);
      for (unsigned r = 0; r < lanes; ++r)
        sn::obliv::ct_set_words(out, sn::util::span<const uint8_t>(rows_.data() + (size_t{r} * kMaxLanes + w) * bytes,
                                                                    bytes), round.valid[r][w]);
    }
    const auto data_end = std::chrono::steady_clock::now();
    times_.windows += 1;
    times_.accesses += lanes;
    times_.map_ns += std::chrono::duration_cast<std::chrono::nanoseconds>(data_begin - map_begin).count();
    times_.data_ns += std::chrono::duration_cast<std::chrono::nanoseconds>(data_end - data_begin).count();
  }

 private:
  struct Leg { int64_t address; uint64_t cur, next; };
  uint64_t Leaves(unsigned level) const { return tree(level).geometry().leaves; }
  uint64_t Random(uint64_t leaves) { return prng_.random_u64(0, leaves); }
  void Blocks(const Window& window, unsigned level, std::array<uint64_t, kMaxLanes>& out) const {
    for (unsigned w = 0; w < window.lanes; ++w) out[w] = window.key[w] / power_[level];
  }
  // A run's representative is its first lane: no earlier lane has its block.
  static void Reps(unsigned lanes, const std::array<uint64_t, kMaxLanes>& block, std::array<bool, kMaxLanes>& rep) {
    for (unsigned w = 0; w < lanes; ++w) {
      bool first = true;
      for (unsigned v = 0; v < w; ++v) first &= !sn::obliv::ct_eq<uint64_t>(block[v], block[w]);
      rep[w] = first;
    }
  }
  // A representative accesses its block; the others a dummy on random leaves.
  std::array<Leg, kMaxLanes> Legs(unsigned lanes, const std::array<uint64_t, kMaxLanes>& block,
                                  const std::array<uint64_t, kMaxLanes>& label,
                                  const std::array<uint64_t, kMaxLanes>& next, const std::array<bool, kMaxLanes>& rep,
                                  uint64_t leaves) {
    std::array<Leg, kMaxLanes> legs{};
    for (unsigned w = 0; w < lanes; ++w) {
      legs[w].address = sn::obliv::ct_select<int64_t>(static_cast<int64_t>(block[w]), -1, rep[w]);
      legs[w].cur = sn::obliv::ct_select<uint64_t>(label[w], Random(leaves), rep[w]);
      legs[w].next = sn::obliv::ct_select<uint64_t>(next[w], Random(leaves), rep[w]);
    }
    return legs;
  }
  // Row w on worker w, all at once; the team's barrier ends the round.
  template <class F> void Rows(unsigned lanes, F&& f) {
    if (lanes == 1 || !access_) {
      f(0, 0);
      return;
    }
    // SONIC's teams take noexcept callables: keep the first failure, rethrow it here.
    std::exception_ptr failure;
    std::mutex failure_mutex;
    access_->parallel_work([&](size_t worker) noexcept {
      if (worker >= lanes) return;
      try {
        f(static_cast<unsigned>(worker), static_cast<unsigned>(worker));
      } catch (...) {
        std::lock_guard<std::mutex> lock(failure_mutex);
        if (!failure) failure = std::current_exception();
      }
    });
    if (failure) std::rethrow_exception(failure);
  }
  EngineConfig config_;
  std::unique_ptr<Tree> data_;
  std::vector<std::unique_ptr<Tree>> maps_;
  sn::threads::thread_team* access_;
  std::vector<uint64_t> power_;
  std::vector<uint32_t> top_, position_;
  sn::crypto::buffered_prng<> prng_;
  alignas(64) MapRound map_round_;
  DataRound data_round_;
  std::vector<uint8_t> rows_;
  PhaseTimes times_;
};
}  // namespace oram_bench::sonic
