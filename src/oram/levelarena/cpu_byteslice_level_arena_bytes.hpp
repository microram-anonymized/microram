#pragma once

// The buffer byte model used by the capacity ladder. Roles cover arena,
// prefix, tier, scratch, plan and selected queue buffers. Job planning buffers
// are included and fixed at construction; borrowed payloads are charged only
// to their owning arena or prefix ring.
//
// This is NOT total engine allocation or resident memory. It excludes the
// engine and heap-owned component objects, geometry/owner wiring containers,
// callback and thread-runtime allocations, allocator overhead and OS stacks.
// These costs vary with geometry and execution settings: a 1% buffer slack
// is not a 1% total-memory guarantee.
//
// `requested` is the modeled buffers' logical size; `reserved` applies the
// aligned allocator's rounding. RoleTotal/Validate check internal arithmetic,
// and component predictions check agreement between tallies. Neither proves
// completeness; independent allocation tests are required for that claim.

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>

#include "src/oram/table/cpu_byteslice_layout.hpp"

namespace microram {
namespace byteslice {
namespace levelarena {

// What a byte is spent ON.  The first roles are the table storage whose
// closed form DESIGN.md "Geometry and storage bound" derives; the rest are the
// buffers the engine allocates beside the tables (scratch, plans, queues).
enum class ByteRole : unsigned {
  // Hashed main tables: the partial banks, the inboxes and the top's two
  // banks.  This is the quantity M of DESIGN.md's storage bound.
  kMains,
  // The second tier that every physical slot carries with its main.
  kTiers,
  // Tier payload regions inside each main arena that stay unused (the tiers
  // live in the shared residual pool) and are kept so main offsets do not move.
  kRetainedTierHoles,
  // One occupancy word per arena bucket, including unused tier mask words.
  kMasks,
  // The (q+1) prefix slots of the dense ring, which hold the online stash and
  // every complete prefix level 1 has not consumed.
  kDense,
  // The dense ring's occupancy words, kept apart from kMasks because the two
  // scale with different things: kMasks with capacity, this with q and r0.
  kDenseMasks,
  // PERSISTENT rebuild storage: one merge job per level, sized once at the widest
  // shape that level can reach -- preparation sheds, level 1's fresh sheds,
  // private input masks and bounded pass-planning buffers.
  kPersistentScratch,
  // TRANSIENT rebuild storage: one residual range table per level, attached for
  // one residual pass at a time.
  kTransientScratch,
  // The request thread's probe scratch and its value buffers.
  kRequestScratch,
  // One BATCH TILE per participant of a batched access: the lane arrays, the per-lane
  // candidate pairs, the sliced accumulator and the forwarding state.  Kept
  // apart from kRequestScratch because the two scale with different things --
  // that one with the cascade's length, this one with the lane width and the
  // participant count -- and because an engine whose caller never batches
  // still pays it, which is a thing a bill should say out loud.
  kBatchScratch,
  // The probe-plan pool, every record reserved at the longest cascade.
  kPlans,
  // Slot directories, boundary credit/ready rings, the dense ring's marks and
  // the publisher's live/retired vectors: queue metadata.
  kBookkeeping,
};

inline constexpr size_t kByteRoleCount =
    static_cast<size_t>(ByteRole::kBookkeeping) + 1;

inline const char* ByteRoleName(ByteRole role) {
  switch (role) {
    case ByteRole::kMains: return "mains";
    case ByteRole::kTiers: return "tiers";
    case ByteRole::kRetainedTierHoles: return "retained tier holes";
    case ByteRole::kMasks: return "masks";
    case ByteRole::kDense: return "dense";
    case ByteRole::kDenseMasks: return "dense masks";
    case ByteRole::kPersistentScratch: return "persistent scratch";
    case ByteRole::kTransientScratch: return "transient scratch";
    case ByteRole::kRequestScratch: return "request scratch";
    case ByteRole::kBatchScratch: return "batch scratch";
    case ByteRole::kPlans: return "plan pool";
    case ByteRole::kBookkeeping: return "bookkeeping";
  }
  return "?";
}

// One allocation serving several roles, such as mains and retained tier holes.
struct RoleShare {
  ByteRole role;
  size_t bytes;
};

class LevelArenaByteBill {
 public:
  // `count` buffers of `bytes` each, from AllocateAligned64, all of one role.
  void AddAligned64(ByteRole role, size_t bytes, size_t count = 1) {
    if (bytes == 0 || count == 0) return;
    allocated_.AddAligned64(bytes, count);
    Role(role) += count * bytes;
  }

  // ONE AllocateAligned64 buffer whose bytes belong to several roles.  The
  // rounding is the whole buffer's, which is why this cannot be spelled as
  // several AddAligned64 calls: two 3 MiB halves of one 6 MiB allocation
  // round to 8 MiB apart and to 6 MiB together.
  void AddAligned64Split(std::initializer_list<RoleShare> shares) {
    size_t total = 0;
    for (const RoleShare& share : shares) {
      total = CheckedSizeAdd(total, share.bytes, "level arena bytes");
    }
    if (total == 0) return;
    allocated_.AddAligned64(total);
    for (const RoleShare& share : shares) Role(share.role) += share.bytes;
  }

  // `count` buffers of `bytes` each from the ordinary allocator.
  void AddPlain(ByteRole role, size_t bytes, size_t count = 1) {
    if (bytes == 0 || count == 0) return;
    allocated_.AddPlain(bytes, count);
    Role(role) += count * bytes;
  }

  // LineAllocator buffers use fixed 128-byte rounding, regardless of huge pages.
  void AddLineAligned(ByteRole role, size_t bytes) {
    if (bytes == 0) return;
    allocated_.AddPlain(bytes);
    allocated_.reserved = CheckedSizeAdd(allocated_.reserved,
        LineAllocator<uint8_t>::Bytes(bytes) - bytes, "line-aligned bytes");
    Role(role) += bytes;
  }

  void Add(const LevelArenaByteBill& other) {
    allocated_.Add(other.allocated_);
    for (size_t i = 0; i < kByteRoleCount; ++i) roles_[i] += other.roles_[i];
  }

  size_t At(ByteRole role) const { return roles_[static_cast<size_t>(role)]; }
  const AllocationTally& allocated() const { return allocated_; }

  // Exact requested bytes over every role, which is the design's figure.
  size_t RoleTotal() const {
    size_t total = 0;
    for (size_t bytes : roles_) total += bytes;
    return total;
  }

  // Logical and allocator-rounded sizes of the modeled buffers.
  size_t requested() const { return allocated_.requested; }
  size_t reserved() const { return allocated_.reserved; }

  // Check that the modeled allocation total agrees with the role breakdown.
  void Validate(const char* what) const {
    if (RoleTotal() == allocated_.requested) return;
    throw std::logic_error(
        std::string("level arena: ") + what + "'s byte roles sum to " +
        std::to_string(RoleTotal()) + " but its allocations requested " +
        std::to_string(allocated_.requested));
  }

  friend bool operator==(const LevelArenaByteBill& a,
                         const LevelArenaByteBill& b) {
    return a.allocated_ == b.allocated_ && a.roles_ == b.roles_;
  }
  friend bool operator!=(const LevelArenaByteBill& a,
                         const LevelArenaByteBill& b) {
    return !(a == b);
  }

  // One line per role, then the allocation totals.  The benchmark's byte
  // breakdown and the diagnostic a failed prediction prints.
  std::string Describe() const {
    std::string out;
    for (size_t i = 0; i < kByteRoleCount; ++i) {
      out += ByteRoleName(static_cast<ByteRole>(i));
      out += " ";
      out += std::to_string(roles_[i]);
      out += " B; ";
    }
    return out + allocated_.Describe();
  }

 private:
  size_t& Role(ByteRole role) { return roles_[static_cast<size_t>(role)]; }

  std::array<size_t, kByteRoleCount> roles_{};
  AllocationTally allocated_;
};

// Allocate AND record, in one step.  A component that buys every buffer
// through these cannot acquire one its own byte bill does not know about:
// the running bill grows, the static predictor beside the constructor does
// not, and the check between them fails at construction.
inline Aligned64Ptr AllocateTallied(size_t bytes, ByteRole role,
                                    LevelArenaByteBill* bill) {
  bill->AddAligned64(role, bytes);
  return AllocateAligned64(bytes);
}

template <class T>
std::unique_ptr<T[]> MakeTalliedArray(size_t count, ByteRole role,
                                      LevelArenaByteBill* bill) {
  bill->AddPlain(role, CheckedSizeMul(count, sizeof(T), "array bytes"));
  return std::make_unique<T[]>(count);
}

// See the header comment: this is what holds a component's static predictor
// to what its constructor actually allocates.
inline void ExpectPredictedBytes(const LevelArenaByteBill& actual,
                                 const LevelArenaByteBill& predicted,
                                 const char* what) {
  if (actual == predicted) return;
  throw std::logic_error(
      std::string("level arena: ") + what +
      " does not allocate what its byte bill predicts.\n  allocated: " +
      actual.Describe() + "\n  predicted: " + predicted.Describe());
}

}  // namespace levelarena
}  // namespace byteslice
}  // namespace microram
