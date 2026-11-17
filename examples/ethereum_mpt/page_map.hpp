// TieredPageMaps: the adapter from packed pages to the library's ORAMs. One map
// per enabled tier (account top, storage top, bulk), page IDs as 8-byte keys,
// and exactly one access_batch call per traversal round.

#pragma once

#include "packing.hpp"
#include "page_store.hpp"
#include <cpu_byteslice_oram/tree_oram.hpp>

#include <algorithm>
#include <array>
#include <memory>
#include <stdexcept>
#include <vector>

namespace ethereum_mpt {

enum class PageBackend { tree, hierarchical };

inline const char* page_backend_name(PageBackend backend) {
  switch (backend) {
    case PageBackend::tree: return "tree";
    case PageBackend::hierarchical: return "hierarchical";
  }
  throw std::invalid_argument("unknown MPT page backend");
}

// Public choices fixed before construction. Bulk pages always use TreeByteMap;
// each top tier can use either engine with the same page representation.
struct TieredPageMapOptions {
  PageBackend account_top = PageBackend::tree;
  PageBackend storage_top = PageBackend::tree;
};

// Loading and appending use public page IDs. Reads preserve fixed-width output
// and every caller lane, including duplicates and dummy page zero.
class PageMap {
 public:
  using Key = std::array<uint8_t, 8>;

  explicit PageMap(const std::vector<Page>& pages,
                   PageBackend backend = PageBackend::tree)
      : PageMap(pages, pages.size(), backend) {}

  PageMap(const std::vector<Page>& pages, size_t capacity,
          PageBackend backend = PageBackend::tree)
      : limit_(checked_capacity(pages, capacity)), next_page_id_(pages.size()),
        backend_(backend) {
    switch (backend_) {
      case PageBackend::tree:
        tree_ = std::make_unique<cpu_byteslice_oram::TreeByteMap<>>(
            limit_, 8, page_bytes, tree_options());
        break;
      case PageBackend::hierarchical:
        hierarchical_ = std::make_unique<cpu_byteslice_oram::ByteMap<>>(
            limit_, 8, page_bytes, hierarchical_options());
        break;
      default:
        throw std::invalid_argument("unknown MPT page backend");
    }
    load_pages(0, pages);
    finish_pending_work();
  }

  // Public append preflight covers the complete extent before any map access.
  // Gaps and failed/uncertain uploads remain reserved until the generation is
  // replaced. Advancing before access_batch prevents reuse after partial load.
  void write_pages_batch(uint64_t first_page_id, const std::vector<Page>& pages) {
    if (first_page_id < next_page_id_)
      throw std::invalid_argument("MPT pages are immutable once reserved");
    if (first_page_id > limit_ || pages.size() > limit_ - first_page_id)
      throw std::invalid_argument("MPT page append exceeds configured capacity");
    if (pages.empty()) return;
    next_page_id_ = first_page_id + pages.size();
    load_pages(first_page_id, pages);
  }

  void finish_pending_work() {
    if (tree_) tree_->finish_pending_work();
    else hierarchical_->finish_pending_work();
  }

  // Caller owns disjoint, preallocated buffers; lane count and pointers are
  // public. Keys can repeat. Presence bytes are returned without interpretation.
  void read_pages_batch(size_t count, const Key* keys, Page* output,
                        uint8_t* found, cpu_byteslice_oram::BatchRequest* scratch) {
    for (size_t i = 0; i < count; ++i) {
      scratch[i] = {cpu_byteslice_oram::BatchOp::kRead, false,
                    keys[i].data(), nullptr, output[i].data()};
    }
    access_batch(count, scratch, found);
  }

  static Key encode_key(uint64_t id) {
    Key key{};
    for (size_t i = 0; i < key.size(); ++i) {
      key[i] = static_cast<uint8_t>(id);
      id >>= 8;
    }
    return key;
  }

  PageBackend backend() const { return backend_; }
  const char* backend_name() const { return page_backend_name(backend_); }
  size_t capacity() const {
    return tree_ ? tree_->capacity() : hierarchical_->capacity();
  }
  size_t arena_bytes() const {
    return tree_ ? tree_->arena_bytes() : hierarchical_->arena_bytes();
  }
  uint64_t access_count() const {
    return tree_ ? tree_->access_count() : hierarchical_->access_count();
  }

 private:
  void access_batch(size_t count, const cpu_byteslice_oram::BatchRequest* requests,
                    uint8_t* found) {
    if (tree_) tree_->access_batch(count, requests, found);
    else hierarchical_->access_batch(count, requests, found);
  }

  void load_pages(uint64_t first_page_id, const std::vector<Page>& pages) {
    // Bound temporary loading scratch by a public tile size.
    for (size_t first = 0; first < pages.size(); first += 16) {
      const size_t count = std::min<size_t>(16, pages.size() - first);
      std::array<Key, 16> keys{};
      std::array<cpu_byteslice_oram::BatchRequest, 16> requests{};
      for (size_t i = 0; i < count; ++i) {
        keys[i] = encode_key(first_page_id + first + i);
        requests[i] = {cpu_byteslice_oram::BatchOp::kWrite, false,
                       keys[i].data(), pages[first + i].data(), nullptr};
      }
      access_batch(count, requests.data(), nullptr);
    }
  }

  static size_t checked_capacity(const std::vector<Page>& pages, size_t capacity) {
    if (pages.empty() || pages.front() != Page{})
      throw std::invalid_argument("page map requires a zero-filled dummy page");
    if (capacity < pages.size())
      throw std::invalid_argument("MPT page map capacity does not fit initial pages");
    return capacity;
  }

  static cpu_byteslice_oram::Options hierarchical_options() {
    cpu_byteslice_oram::Options options;
    // Application-wide budget: one serialized caller and no worker pools,
    // including the hierarchical position maps inside tree-backed tiers.
    options.deamortized_owner_threads = 0;
    options.deamortized_value_workers = 0;
    options.deamortized_batch_participants = 1;
    options.deamortized_rebuild_threads = 0;
    options.deamortized_top_helpers = 0;
    options.deamortized_bottom_helpers = 0;
    return options;
  }

  static cpu_byteslice_oram::TreeOptions tree_options() {
    cpu_byteslice_oram::TreeOptions options;
    options.payload_max_threads = 0;
    options.position_map = hierarchical_options();
    return options;
  }

  size_t limit_;
  uint64_t next_page_id_;
  PageBackend backend_;
  std::unique_ptr<cpu_byteslice_oram::TreeByteMap<>> tree_;
  std::unique_ptr<cpu_byteslice_oram::ByteMap<>> hierarchical_;
};

// Stable immutable pages and scratch for one serialized requester/updater.
// Construction validates the public image before loading any map. A failed
// load cannot return a partially usable reader. No builder tables are queried
// after construction.
class TieredPageMaps final : public PageStore {
 public:
  TieredPageMaps(const PackedSnapshot& snapshot, size_t max_lanes,
                 TieredPageMapOptions options = {})
      : keys_(max_lanes), requests_(max_lanes) {
    if (max_lanes == 0) throw std::invalid_argument("page reader requires lanes");
    validate_packed_snapshot(snapshot);
    load_maps(snapshot.pages, page_counts(snapshot.pages), options);
  }

  TieredPageMaps(const PackedGeneration& generation, size_t max_lanes,
                 TieredPageMapOptions options = {})
      : TieredPageMaps(generation, max_lanes, page_counts(generation.pages), options) {}

  TieredPageMaps(const PackedGeneration& generation, size_t max_lanes,
                 const std::array<size_t, 3>& capacities,
                 TieredPageMapOptions options = {})
      : keys_(max_lanes), requests_(max_lanes) {
    if (max_lanes == 0) throw std::invalid_argument("page reader requires lanes");
    validate_packed_generation(generation);
    load_maps(generation.pages, capacities, options);
  }

  void write_pages_batch(Tier tier, uint64_t first_page_id,
                         const std::vector<Page>& pages) override {
    const auto t = static_cast<size_t>(tier);
    if (t >= maps_.size() || !maps_[t])
      throw std::invalid_argument("unconfigured MPT page append");
    maps_[t]->write_pages_batch(first_page_id, pages);
  }

  void finish_pending_work() override {
    for (const auto& map : maps_)
      if (map) map->finish_pending_work();
  }

  // Logical admission limits, independent of the ORAM's rounded allocation.
  std::array<size_t, 3> capacities() const override { return capacities_; }

  void read_pages_batch(Tier tier, size_t count, const uint64_t* ids,
                        Page* output, uint8_t* found) override {
    const auto t = static_cast<size_t>(tier);
    // Tier and count are public schedule parameters.
    if (t >= maps_.size() || !maps_[t] || count == 0)
      throw std::invalid_argument("unconfigured MPT page batch");
    if (count > keys_.size())
      throw std::invalid_argument("MPT page batch exceeds the reader's lanes");
    for (size_t i = 0; i < count; ++i) keys_[i] = PageMap::encode_key(ids[i]);
    maps_[t]->read_pages_batch(count, keys_.data(), output, found, requests_.data());
    ++calls_[t];
    accesses_[t] += count;
  }

  size_t max_lanes() const override { return keys_.size(); }

  const std::array<uint64_t, 3>& calls() const { return calls_; }
  const std::array<uint64_t, 3>& accesses() const { return accesses_; }
  const PageMap* map(Tier tier) const { return maps_.at(static_cast<size_t>(tier)).get(); }
  size_t arena_bytes() const {
    size_t total = 0;
    for (const auto& map : maps_)
      if (map) total += map->arena_bytes();
    return total;
  }

 private:
  static std::array<size_t, 3> page_counts(
      const std::array<std::vector<Page>, 3>& pages) {
    return {pages[0].size(), pages[1].size(), pages[2].size()};
  }

  void load_maps(const std::array<std::vector<Page>, 3>& pages,
                 const std::array<size_t, 3>& capacities,
                 TieredPageMapOptions options) {
    const std::array<PageBackend, 3> backends{
        options.account_top, options.storage_top, PageBackend::tree};
    // Validate every configured tier before constructing any ORAM instance.
    for (size_t t = 0; t < maps_.size(); ++t) {
      page_backend_name(backends[t]);
      if ((pages[t].empty() != (capacities[t] == 0)) ||
          capacities[t] < pages[t].size())
        throw std::invalid_argument("MPT tier capacity does not fit enabled pages");
    }
    capacities_ = capacities;
    for (size_t t = 0; t < maps_.size(); ++t)
      if (!pages[t].empty())
        maps_[t] = std::make_unique<PageMap>(pages[t], capacities[t], backends[t]);
  }

  std::array<std::unique_ptr<PageMap>, 3> maps_;
  std::array<size_t, 3> capacities_{};
  std::vector<PageMap::Key> keys_;
  std::vector<cpu_byteslice_oram::BatchRequest> requests_;
  std::array<uint64_t, 3> calls_{}, accesses_{};
};

}  // namespace ethereum_mpt
