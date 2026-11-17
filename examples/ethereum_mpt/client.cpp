// Fixed-size request/response frame encoding (layout in DESIGN.md, "Local
// client framing"). The response encoder visits every field and proof byte at
// addresses fixed by public Q/K, so its work does not depend on results.

#include "client_internal.hpp"

#include <algorithm>
#include <limits>
#include <stdexcept>

namespace ethereum_mpt {
namespace {

constexpr std::array<std::uint8_t, 8> magic{'M', 'P', 'T', 'F', 'R', 'M', '0', '1'};
constexpr std::uint8_t request_kind = 1, response_kind = 2;

std::size_t add(std::size_t a, std::size_t b) {
    if (b > std::numeric_limits<std::size_t>::max() - a)
        throw std::invalid_argument("MPT client frame size overflows");
    return a + b;
}

std::size_t multiply(std::size_t a, std::size_t b) {
    if (b != 0 && a > std::numeric_limits<std::size_t>::max() / b)
        throw std::invalid_argument("MPT client frame size overflows");
    return a * b;
}

// The complete width is checked before construction. All offsets and loop
// bounds below depend only on the public profile, never a wire/result length.
class Writer {
 public:
    explicit Writer(Bytes& bytes) : bytes_(bytes) {}

    void integer(std::uint64_t value, std::size_t width) {
        for (std::size_t i = 0; i < width; ++i) {
            bytes_[offset_++] = static_cast<std::uint8_t>(value);
            value >>= 8;
        }
    }

    template <std::size_t N>
    void bytes(const std::array<std::uint8_t, N>& source) {
        for (std::size_t i = 0; i < N; ++i) bytes_[offset_++] = source[i];
    }

    void proof(const FixedProof& proof) {
        for (const auto& slot : proof.slots) bytes(slot);
    }

 private:
    Bytes& bytes_;
    std::size_t offset_ = 0;
};

class Reader {
 public:
    explicit Reader(const Bytes& bytes) : bytes_(bytes) {}

    std::uint64_t integer(std::size_t width) {
        std::uint64_t result = 0;
        for (std::size_t i = 0; i < width; ++i)
            result |= std::uint64_t{bytes_[offset_++]} << (i * 8);
        return result;
    }

    template <std::size_t N>
    void bytes(std::array<std::uint8_t, N>& target) {
        for (std::size_t i = 0; i < N; ++i) target[i] = bytes_[offset_++];
    }

    void proof(FixedProof& proof) {
        for (auto& slot : proof.slots) bytes(slot);
    }

 private:
    const Bytes& bytes_;
    std::size_t offset_ = client_header_bytes;
};

void header(Writer& out, const ClientContext& context, std::uint8_t kind) {
    static_assert(sizeof(std::size_t) <= sizeof(std::uint64_t), "wire count width");
    out.bytes(magic);
    out.integer(kind, 1);
    out.integer(context.tiers.account_top_depth, 1);
    out.integer(context.tiers.storage_top_depth, 1);
    out.integer(0, 1);
    out.integer(page_bytes, 2);
    out.integer(proof_rounds, 2);
    out.integer(context.batch.requests, 8);
    out.integer(context.batch.storage_slots, 8);
    out.bytes(context.request_id);
    out.bytes(context.block_id);
    out.bytes(context.state_root);
}

void check_frame(const ClientContext& context, const Bytes& frame,
                 std::uint8_t kind, std::size_t expected_bytes) {
    if (frame.size() != expected_bytes)
        throw std::invalid_argument("MPT client frame has the wrong width");
    Bytes expected(client_header_bytes);
    Writer out(expected);
    header(out, context, kind);
    // Public context is supplied by the receiver. No received count, root or
    // profile is used for allocation or to establish the trusted state root.
    if (!std::equal(expected.begin(), expected.end(), frame.begin()))
        throw std::invalid_argument("MPT client frame context mismatch");
}

void check_requests(const ClientContext& context,
                    const std::vector<ClientRequest>& requests) {
    if (requests.size() != context.batch.requests)
        throw std::invalid_argument("MPT client request count differs from public profile");
    for (const auto& request : requests)
        if (request.storage_slots.size() != context.batch.storage_slots)
            throw std::invalid_argument("MPT client slot count differs from public profile");
}

}  // namespace

ClientFrameSizes client_frame_sizes(const ClientContext& context) {
    const auto& batch = context.batch;
    if (batch.requests == 0 || context.tiers.account_top_depth > proof_rounds ||
        context.tiers.storage_top_depth > proof_rounds)
        throw std::invalid_argument("invalid MPT client public profile");
    const auto lanes = multiply(batch.requests, add(batch.storage_slots, 1));
    if (lanes > batch.max_proof_bytes / sizeof(FixedProof))
        throw std::invalid_argument("MPT client profile exceeds proof buffer limit");
    // The decoder materializes traversal results, so admit their size too.
    (void)multiply(lanes, sizeof(TraversalResult));
    ClientFrameSizes sizes;
    sizes.request_bytes = add(client_header_bytes,
        multiply(batch.requests, add(20, multiply(batch.storage_slots, 32))));
    sizes.response_bytes = add(client_header_bytes,
        multiply(batch.requests, add(client_account_bytes,
                                    multiply(batch.storage_slots, client_storage_bytes))));
    if (sizes.request_bytes > context.max_frame_bytes ||
        sizes.response_bytes > context.max_frame_bytes ||
        sizes.response_bytes > Bytes{}.max_size())
        throw std::invalid_argument("MPT client profile exceeds frame buffer limit");
    return sizes;
}

Bytes encode_request_frame(const ClientContext& context,
                           const std::vector<ClientRequest>& requests) {
    const auto sizes = client_frame_sizes(context);
    check_requests(context, requests);
    Bytes frame(sizes.request_bytes);
    Writer out(frame);
    header(out, context, request_kind);
    for (const auto& request : requests) {
        out.bytes(request.address);
        for (const auto& slot : request.storage_slots) out.bytes(slot);
    }
    return frame;
}

std::vector<ClientRequest> decode_request_frame(const ClientContext& expected,
                                               const Bytes& frame) {
    const auto sizes = client_frame_sizes(expected);
    check_frame(expected, frame, request_kind, sizes.request_bytes);
    std::vector<ClientRequest> requests(expected.batch.requests);
    Reader in(frame);
    for (auto& request : requests) {
        in.bytes(request.address);
        request.storage_slots.resize(expected.batch.storage_slots);
        for (auto& slot : request.storage_slots) in.bytes(slot);
    }
    return requests;
}

std::vector<PathRequest> make_path_requests(const ClientContext& context,
                                           const std::vector<ClientRequest>& requests) {
    (void)client_frame_sizes(context);
    check_requests(context, requests);
    std::vector<PathRequest> paths;
    paths.reserve(context.batch.requests);
    for (const auto& request : requests)
        paths.push_back(make_path_request(request.address, request.storage_slots));
    return paths;
}

Bytes encode_response_frame(const ClientContext& context,
                            const std::vector<ClientRequest>& requests,
                            const BatchResult& results) {
    const auto sizes = client_frame_sizes(context);
    check_requests(context, requests);
    if (results.accounts.size() != context.batch.requests ||
        results.storage.size() != context.batch.requests * context.batch.storage_slots)
        throw std::invalid_argument("MPT response count differs from public profile");
    Bytes frame(sizes.response_bytes);
    Writer out(frame);
    header(out, context, response_kind);
    for (std::size_t q = 0; q < context.batch.requests; ++q) {
        const auto& account = results.accounts[q];
        out.bytes(requests[q].address);
        out.integer(account.error, 8);
        out.integer(account.present, 8);
        out.integer(account.nonce, 8);
        out.bytes(account.balance);
        out.bytes(account.storage_root);
        out.bytes(account.code_hash);
        out.proof(account.proof);
        for (std::size_t s = 0; s < context.batch.storage_slots; ++s) {
            const auto& slot = results.storage[q * context.batch.storage_slots + s];
            out.bytes(requests[q].storage_slots[s]);
            out.integer(slot.error, 8);
            out.integer(slot.present, 8);
            out.bytes(slot.storage_value);
            out.proof(slot.proof);
        }
    }
    return frame;
}

namespace client_detail {
BatchResult decode_response_frame(const ClientContext& expected,
                                  const std::vector<ClientRequest>& requests,
                                  const Bytes& frame) {
    const auto sizes = client_frame_sizes(expected);
    check_requests(expected, requests);
    check_frame(expected, frame, response_kind, sizes.response_bytes);
    BatchResult results{std::vector<TraversalResult>(expected.batch.requests),
        std::vector<TraversalResult>(expected.batch.requests * expected.batch.storage_slots)};
    Reader in(frame);
    for (std::size_t q = 0; q < expected.batch.requests; ++q) {
        Address address{};
        in.bytes(address);
        if (address != requests[q].address)
            throw std::invalid_argument("MPT response account does not match request");
        auto& account = results.accounts[q];
        account.error = in.integer(8);
        account.present = in.integer(8);
        account.nonce = in.integer(8);
        in.bytes(account.balance);
        in.bytes(account.storage_root);
        in.bytes(account.code_hash);
        in.proof(account.proof);
        for (std::size_t s = 0; s < expected.batch.storage_slots; ++s) {
            Word key{};
            in.bytes(key);
            if (key != requests[q].storage_slots[s])
                throw std::invalid_argument("MPT response storage slot does not match request");
            auto& slot = results.storage[q * expected.batch.storage_slots + s];
            slot.error = in.integer(8);
            slot.present = in.integer(8);
            in.bytes(slot.storage_value);
            in.proof(slot.proof);
        }
    }
    return results;
}
}  // namespace client_detail
}  // namespace ethereum_mpt
