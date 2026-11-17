// Private batched proof traversal: request shape, padded proof slots, result
// masks and the BatchTraversal driver.

#pragma once

#include "packing.hpp"

#include <limits>

namespace ethereum_mpt {

inline constexpr std::size_t proof_rounds = 65;
inline constexpr std::size_t proof_slot_bytes = 536;

// Already-hashed paths also permit adversarial structural fixtures without
// searching for address/slot Keccak preimages.
struct PathRequest {
    Hash account_key{};
    std::vector<Hash> storage_keys;
};

PathRequest make_path_request(const Address& address, const std::vector<Word>& slots);

struct BatchProfile {
    std::size_t requests = 1;
    std::size_t storage_slots = 0;
    std::size_t max_proof_bytes = 64 * 1024 * 1024;
};

struct FixedProof {
    // Explicit wire bytes: little-endian u16 length, u8 include, u8 reserved,
    // followed by 532 canonical bytes with a zero tail.
    std::array<std::array<std::uint8_t, proof_slot_bytes>, proof_rounds> slots{};
};
static_assert(sizeof(FixedProof) == 34840, "fixed proof wire width must not change");

struct TraversalResult {
    // Status uses zero/all-ones masks. Error never means authenticated absence.
    std::uint64_t error = 0, present = 0;
    std::uint64_t nonce = 0;
    Word balance{};
    Hash storage_root{}, code_hash{};
    Word storage_value{};
    FixedProof proof;
};

struct BatchResult {
    std::vector<TraversalResult> accounts;
    // Public ordering q*K+s, including absent accounts and empty storage.
    std::vector<TraversalResult> storage;
};

// Exactly one call per public depth. Implementations must preserve every lane,
// prepare all requests before reading, and use one genuine ORAM batch call.
class PageReader {
 public:
    virtual ~PageReader() = default;
    virtual void read_pages_batch(Tier tier, std::size_t count,
                                 const std::uint64_t* ids, Page* output,
                                 std::uint8_t* found) = 0;
    // Most lanes one read_pages_batch call accepts. BatchTraversal::run
    // refuses a batch that needs more (max(Q, Q*K)) before its first read.
    virtual std::size_t max_lanes() const { return std::numeric_limits<std::size_t>::max(); }
};

class BatchTraversal {
 public:
    // Pins one immutable snapshot/profile for both phases. Admission checks and
    // allocations use public sizes; no public builder dictionary is retained.
    BatchTraversal(Hash state_root, Locator root, TierProfile tiers, BatchProfile batch);
    BatchResult run(PageReader& pages, const std::vector<PathRequest>& requests) const;

 private:
    Hash state_root_;
    Locator root_;
    TierProfile tiers_;
    BatchProfile batch_;
};

// Disclosed/client-side decoding only: variable work, strict padding checks.
// This is not an authenticated or encrypted network envelope.
Proof decode_proof(const FixedProof& proof);

}  // namespace ethereum_mpt
