// Client-side (variable-time) response decoding: checks echoed requests and
// canonical masks/padding, then authenticates account and storage values with
// MPT proofs against the caller's trusted state root.

#include "client_internal.hpp"

#include <limits>
#include <sstream>
#include <stdexcept>

namespace ethereum_mpt {
namespace {

void require(bool condition, const char* message) {
    if (!condition) throw std::invalid_argument(message);
}

void validate_masks(const TraversalResult& result) {
    constexpr auto set = std::numeric_limits<std::uint64_t>::max();
    require((result.error == 0 || result.error == set) &&
                (result.present == 0 || result.present == set),
            "invalid MPT response status mask");
    require(result.error == 0 || result.present == 0,
            "failed MPT response claims presence");
}

std::string quantity(const Word& value) {
    const auto digits = hex(value);
    const auto first = digits.find_first_not_of('0');
    return first == std::string::npos ? "0x0" : "0x" + digits.substr(first);
}

std::string quantity(std::uint64_t value) {
    Word encoded{};
    for (std::size_t i = 0; i < sizeof(value); ++i)
        encoded[encoded.size() - 1 - i] = static_cast<std::uint8_t>(value >> (8 * i));
    return quantity(encoded);
}

void write_proof(std::ostream& output, const Proof& proof) {
    output << '[';
    for (std::size_t i = 0; i < proof.size(); ++i) {
        if (i != 0) output << ',';
        output << "\"0x" << hex(proof[i]) << '"';
    }
    output << ']';
}

}  // namespace

std::vector<VerifiedAccount> verify_response_frame(
    const ClientContext& expected, const std::vector<ClientRequest>& requests,
    const Bytes& frame) {
    const auto results = client_detail::decode_response_frame(expected, requests, frame);
    const auto empty_root = empty_trie_root();
    std::vector<VerifiedAccount> verified(requests.size());
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto& result = results.accounts[q];
        auto& account = verified[q];
        account.address = requests[q].address;
        account.storage.resize(expected.batch.storage_slots);
        validate_masks(result);
        // Slot headers and padding must be canonical even in an error frame.
        account.proof = decode_proof(result.proof);
        account.error = result.error != 0;
        if (account.error) {
            require(result.nonce == 0 && result.balance == Word{} &&
                        result.storage_root == Hash{} && result.code_hash == Hash{} &&
                        account.proof.empty(),
                    "failed MPT account response has uncleared fields or proof");
        } else {
            const auto key = keccak256(account.address.data(), account.address.size());
            const auto value = verify_proof(TrieKind::account, expected.state_root,
                                            key, account.proof);
            require((result.present != 0) == value.has_value(),
                    "MPT account presence disagrees with its proof");
            if (value) {
                account.account = decode_account(*value);
                const auto& fields = *account.account;
                require(result.nonce == fields.nonce && result.balance == fields.balance &&
                            result.storage_root == fields.storage_root &&
                            result.code_hash == fields.code_hash,
                        "MPT account fields disagree with its proof");
            } else {
                require(result.nonce == 0 && result.balance == Word{} &&
                            result.storage_root == empty_root && result.code_hash == Hash{},
                        "absent MPT account response has inconsistent fields");
            }
        }

        for (std::size_t s = 0; s < expected.batch.storage_slots; ++s) {
            const auto& stored = results.storage[q * expected.batch.storage_slots + s];
            auto& storage = account.storage[s];
            storage.slot = requests[q].storage_slots[s];
            validate_masks(stored);
            storage.proof = decode_proof(stored.proof);
            storage.error = stored.error != 0;
            require(!account.error || storage.error,
                    "failed MPT account response has a successful storage lane");
            if (storage.error) {
                require(stored.storage_value == Word{} && storage.proof.empty(),
                        "failed MPT storage response has an uncleared value or proof");
                continue;
            }
            // Only the account value authenticated above supplies this root.
            // Proven account absence implies the empty storage trie.
            const auto root = account.account ? account.account->storage_root : empty_root;
            const auto key = keccak256(storage.slot.data(), storage.slot.size());
            const auto value = verify_proof(TrieKind::storage, root, key, storage.proof);
            storage.present = value.has_value();
            storage.value = value ? decode_storage(*value) : Word{};
            require((stored.present != 0) == storage.present &&
                        stored.storage_value == storage.value,
                    "MPT storage fields disagree with its proof");
        }
    }
    return verified;
}

std::string to_eip1186_json(const VerifiedAccount& account) {
    require(!account.error, "cannot export a failed MPT account proof");
    for (const auto& storage : account.storage)
        require(!storage.error, "cannot export a failed MPT storage proof");

    // The local absent-account wire representation clears code_hash. The
    // Ethereum-facing result uses the canonical empty-code hash instead.
    const auto fields = account.account.value_or(Account{});
    std::ostringstream output;
    output << "{\"address\":\"0x"
           << hex(Bytes(account.address.begin(), account.address.end()))
           << "\",\"accountProof\":";
    write_proof(output, account.proof);
    output << ",\"balance\":\"" << quantity(fields.balance)
           << "\",\"codeHash\":\"0x" << hex(fields.code_hash)
           << "\",\"nonce\":\"" << quantity(fields.nonce)
           << "\",\"storageHash\":\"0x" << hex(fields.storage_root)
           << "\",\"storageProof\":[";
    for (std::size_t s = 0; s < account.storage.size(); ++s) {
        if (s != 0) output << ',';
        const auto& storage = account.storage[s];
        output << "{\"key\":\"" << quantity(storage.slot)
               << "\",\"value\":\"" << quantity(storage.value)
               << "\",\"proof\":";
        write_proof(output, storage.proof);
        output << '}';
    }
    output << "]}";
    return output.str();
}

}  // namespace ethereum_mpt
