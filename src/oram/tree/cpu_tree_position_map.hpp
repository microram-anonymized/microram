#pragma once

// Position maps for the tree ORAM (src/oram/tree/DESIGN.md):
// key -> (position, uid), every operation ONE access that reads the current
// entry and stores the next.
//
//  - UnorderedPositionMap is std::unordered_map: NOT oblivious, for tests and
//    for benchmarking the tree alone.
//  - HierarchicalPositionMap<Deamortize> is ByteMap<Deamortize>::exchange over
//    a value of `PositionEntry::StoredBytes` bytes: the position alone when the
//    caller derives the uid from the key (CpuTreeMap's THE UID), the position
//    and an 8-byte uid otherwise.
//
// THE POSITION IS AS WIDE AS THE TREE, NOT AS A WORD.  A leaf index has
// `leaf_bits` bits -- 16 at 2^18 entries, 22 at 2^24, at most 36 -- so it is
// stored in `ceil(leaf_bits / 8)` bytes: three at every capacity up to 2^26,
// against the eight a `uint64_t` would take.  The position map is a
// byte-sliced ORAM whose probe and extract cost scale with the value's byte
// lines and whose arena scales with the entry, so the five bytes saved are
// five of its eleven to nineteen lines.  The
// width is fixed at construction from the geometry's `leaf_bits`, and
// CpuTreeMap refuses a map narrower than its tree.

#include <cstddef>
#include <array>
#include <cstdint>
#include <cstring>
#include <string>
#include <unordered_map>
#include <vector>

#include <cpu_byteslice_oram/byte_map.hpp>

namespace microram {
namespace tree {

// The position map's value: the leaf the entry sits on and the uid it is
// stored under, the position FIRST and little-endian in `PositionBytes(leaf_bits)`
// bytes.  When the uid is derived from the key only the position is stored;
// otherwise the 8-byte uid follows it.
struct PositionEntry {
  uint64_t position = 0;
  uint64_t uid = 0;

  // The widest stored form (a 64-bit position and the uid), which is also
  // the size of every encode/decode buffer.
  static constexpr size_t kBytes = 16;
  static constexpr size_t kUidBytes = 8;
  // Bytes a position of `leaf_bits` bits takes: 1..8.  64 -- the default
  // wherever the tree's depth is not known -- is the whole word.
  static constexpr size_t PositionBytes(unsigned leaf_bits) {
    return leaf_bits >= 64 ? 8 : leaf_bits == 0 ? 1 : (leaf_bits + 7) / 8;
  }
  static constexpr size_t StoredBytes(bool uid_from_key, unsigned leaf_bits = 64) {
    return PositionBytes(leaf_bits) + (uid_from_key ? 0 : kUidBytes);
  }
  void Encode(uint8_t* out, bool uid_from_key = false,
              unsigned leaf_bits = 64) const {
    const size_t pb = PositionBytes(leaf_bits);
    std::memcpy(out, &position, pb);  // the low bytes: little-endian host
    if (!uid_from_key) std::memcpy(out + pb, &uid, kUidBytes);
  }
  static PositionEntry Decode(const uint8_t* in, bool uid_from_key = false,
                              unsigned leaf_bits = 64) {
    const size_t pb = PositionBytes(leaf_bits);
    PositionEntry e;
    std::memcpy(&e.position, in, pb);
    if (!uid_from_key) std::memcpy(&e.uid, in + pb, kUidBytes);
    return e;
  }
};

// Public operation descriptors; keys and next entries must not depend on
// another lane's results. Repeated keys observe earlier lanes in order.
struct PositionBatchRequest {
  const uint8_t* key = nullptr;
  PositionEntry next;
  bool insert = false;
  bool erase = false;
};

class UnorderedPositionMap {
 public:
  UnorderedPositionMap(size_t capacity, size_t key_bytes)
      : key_bytes_(key_bytes) {
    map_.reserve(capacity);
  }

  // Reads the key's entry into *previous (zeros when absent) and stores
  // `next` iff the key was present or `insert`.  Returns whether present.
  bool Exchange(const uint8_t* key, const PositionEntry& next,
                PositionEntry* previous, bool insert) {
    const std::string k(reinterpret_cast<const char*>(key), key_bytes_);
    auto it = map_.find(k);
    const bool present = it != map_.end();
    *previous = present ? it->second : PositionEntry{};
    if (present) {
      it->second = next;
    } else if (insert) {
      map_.emplace(k, next);
    }
    return present;
  }

  bool Erase(const uint8_t* key, PositionEntry* previous) {
    const std::string k(reinterpret_cast<const char*>(key), key_bytes_);
    auto it = map_.find(k);
    const bool present = it != map_.end();
    *previous = present ? it->second : PositionEntry{};
    if (present) map_.erase(it);
    return present;
  }

  void AccessBatch(size_t n, const PositionBatchRequest* requests,
                   PositionEntry* previous, uint8_t* found) {
    for (size_t i = 0; i < n; ++i) {
      const auto& r = requests[i];
      found[i] = r.erase ? Erase(r.key, &previous[i])
                         : Exchange(r.key, r.next, &previous[i], r.insert);
    }
  }

  size_t key_bytes() const { return key_bytes_; }
  // Bits of position this map can store: the whole word.
  unsigned PositionBits() const { return 64; }
  size_t size() const { return map_.size(); }
  // A rough footprint, so the composed map can report something.
  size_t ArenaBytes() const {
    return map_.bucket_count() * 8 + map_.size() * (key_bytes_ + 48);
  }
  uint64_t AccessCount() const { return 0; }
  void RequireAccessBudget(uint64_t) const {}
  bool Failed() const { return false; }
  void DrainRebuilds() {}
  static constexpr bool kOblivious = false;

 private:
  size_t key_bytes_;
  std::unordered_map<std::string, PositionEntry> map_;
};

template <bool Deamortize = true>
class HierarchicalPositionMap {
 public:
  // `uid_from_key`: the caller reconstructs the uid from the key, so only the
  // position is stored.  `leaf_bits` is the tree's depth, which sets the
  // position's width (THE POSITION IS AS WIDE AS THE TREE above); 64 stores
  // the whole word, which is what every geometry fits.
  HierarchicalPositionMap(size_t capacity, size_t key_bytes,
                          cpu_byteslice_oram::Options options = {},
                          bool uid_from_key = false, unsigned leaf_bits = 64)
      : map_(capacity, key_bytes,
             PositionEntry::StoredBytes(uid_from_key, leaf_bits), options),
        key_bytes_(key_bytes),
        uid_from_key_(uid_from_key),
        leaf_bits_(leaf_bits > 64 ? 64u : leaf_bits) {}

  bool Exchange(const uint8_t* key, const PositionEntry& next,
                PositionEntry* previous, bool insert) {
    alignas(16) uint8_t next_bytes[PositionEntry::kBytes] = {};
    alignas(16) uint8_t old_bytes[PositionEntry::kBytes] = {};
    next.Encode(next_bytes, uid_from_key_, leaf_bits_);
    const bool present = map_.exchange(key, next_bytes, old_bytes, insert);
    *previous = PositionEntry::Decode(old_bytes, uid_from_key_, leaf_bits_);
    return present;
  }

  bool Erase(const uint8_t* key, PositionEntry* previous) {
    alignas(16) uint8_t old_bytes[PositionEntry::kBytes] = {};
    const bool present = map_.erase(key, old_bytes);
    *previous = PositionEntry::Decode(old_bytes, uid_from_key_, leaf_bits_);
    return present;
  }

  // Buffers remain stable throughout ByteMap's cascade and are reused across
  // calls. As with scalar position operations, previous/found are required.
  // Outputs are decoded only on success; a caller composing this with a tree
  // must latch failure if the underlying batch throws after partial mutation.
  void AccessBatch(size_t n, const PositionBatchRequest* requests,
                   PositionEntry* previous, uint8_t* found) {
    if (n == 0) return;
    cpu_byteslice_oram::detail::RequirePointer(requests, "requests must not be null");
    cpu_byteslice_oram::detail::RequirePointer(previous, "previous must not be null");
    cpu_byteslice_oram::detail::RequirePointer(found, "found must not be null");
    batch_bytes_.resize(n);
    batch_requests_.resize(n);
    for (size_t i = 0; i < n; ++i) {
      const auto& r = requests[i];
      auto& bytes = batch_bytes_[i];
      r.next.Encode(bytes.next.data(), uid_from_key_, leaf_bits_);
      batch_requests_[i] = {
          r.erase ? cpu_byteslice_oram::BatchOp::kErase
                  : cpu_byteslice_oram::BatchOp::kExchange,
          r.insert, r.key, bytes.next.data(), bytes.previous.data()};
    }
    map_.access_batch(n, batch_requests_.data(), found);
    for (size_t i = 0; i < n; ++i)
      previous[i] = PositionEntry::Decode(batch_bytes_[i].previous.data(),
                                          uid_from_key_, leaf_bits_);
  }

  size_t key_bytes() const { return key_bytes_; }
  // Bits of position this map stores; a tree deeper than this cannot use it.
  unsigned PositionBits() const {
    return static_cast<unsigned>(8 * PositionEntry::PositionBytes(leaf_bits_));
  }
  size_t ArenaBytes() const { return map_.arena_bytes(); }
  size_t Capacity() const { return map_.capacity(); }
  uint64_t AccessCount() const { return map_.access_count(); }
  // Both budgets a position-map access spends, as ByteMap checks them before
  // user code: the access horizon, and one key normalization per access
  // (a scalar exchange or erase, or one batch lane) when keys are rehashed.
  // The second check is a no-op for keys that are not rehashed.
  void RequireAccessBudget(uint64_t accesses) const {
    map_.engine().RequireAccessBudget(accesses);
    map_.engine().RequireKeyNormalizationBudget(accesses);
  }
  // Whether the hierarchy refuses further work (ByteMap::failed).
  bool Failed() const { return map_.failed(); }
  void DrainRebuilds() { map_.drain_rebuilds(); }
  cpu_byteslice_oram::ByteMap<Deamortize>& byte_map() { return map_; }
  const cpu_byteslice_oram::ByteMap<Deamortize>& byte_map() const { return map_; }
  static constexpr bool kOblivious = true;

 private:
  struct BatchBytes {
    std::array<uint8_t, PositionEntry::kBytes> next{};
    std::array<uint8_t, PositionEntry::kBytes> previous{};
  };
  std::vector<BatchBytes> batch_bytes_;
  std::vector<cpu_byteslice_oram::BatchRequest> batch_requests_;
  cpu_byteslice_oram::ByteMap<Deamortize> map_;
  size_t key_bytes_;
  bool uid_from_key_ = false;
  unsigned leaf_bits_ = 64;
};

}  // namespace tree
}  // namespace microram
