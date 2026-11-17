// Client-facing API of the example: fixed-size request/response frames, public
// size admission, client-side proof verification and EIP-1186 JSON export.

#pragma once

#include "traversal.hpp"

namespace ethereum_mpt {

// Example-local plaintext framing. A deployed transport must encrypt and
// authenticate the complete frame with an established channel, including its
// context and status bits. These functions provide no channel or replay state.
struct ClientRequest {
    Address address{};
    std::vector<Word> storage_slots;
};

struct ClientContext {
    Hash request_id{}, block_id{}, state_root{};
    TierProfile tiers;
    BatchProfile batch;
    // Local admission limit, not a wire field; applies to each complete frame.
    std::size_t max_frame_bytes = 64 * 1024 * 1024;
};

inline constexpr std::size_t client_header_bytes = 128;
inline constexpr std::size_t client_account_bytes = 140 + sizeof(FixedProof);
inline constexpr std::size_t client_storage_bytes = 80 + sizeof(FixedProof);

struct ClientFrameSizes {
    std::size_t request_bytes = 0, response_bytes = 0;
};

// Checked public arithmetic and buffer admission, before reading private data.
ClientFrameSizes client_frame_sizes(const ClientContext& context);
Bytes encode_request_frame(const ClientContext& context,
                           const std::vector<ClientRequest>& requests);
std::vector<ClientRequest> decode_request_frame(const ClientContext& expected,
                                               const Bytes& frame);
std::vector<PathRequest> make_path_requests(const ClientContext& context,
                                           const std::vector<ClientRequest>& requests);

// Copies every field and all 65 slots, including on errors/absence; no branch,
// allocation size or selected address depends on result masks or proof lengths.
// Context must come from the manifest pinned for the complete traversal batch.
Bytes encode_response_frame(const ClientContext& context,
                            const std::vector<ClientRequest>& requests,
                            const BatchResult& results);

struct VerifiedStorage {
    Word slot{}, value{};
    bool error = false, present = false;
    Proof proof;
};

struct VerifiedAccount {
    Address address{};
    bool error = false;
    // nullopt without error means proven absence, not a failed query.
    std::optional<Account> account;
    Proof proof;
    std::vector<VerifiedStorage> storage;
};

// Client-only variable work. The expected block/root and original requests
// come from the caller, not the response. Verify the account before deriving
// the storage root, and reject contradictory convenience fields or padding.
// Well-formed service errors remain errors; malformed frames/proofs throw.
std::vector<VerifiedAccount> verify_response_frame(
    const ClientContext& expected, const std::vector<ClientRequest>& requests,
    const Bytes& frame);

// Client-only EIP-1186 result object (no JSON-RPC wrapper); refuses any error.
// Absent accounts use zero nonce/balance, empty storage root and empty code hash.
std::string to_eip1186_json(const VerifiedAccount& account);

}  // namespace ethereum_mpt
