// ethereum_mpt_tls_demo: serves framed proof batches from real ORAM maps over a
// local TLS socket pair, with the client on a separate thread.

#include "client.hpp"
#include "fixture.hpp"
#include "page_map.hpp"
#include "transport.hpp"

#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

#include <exception>
#include <iostream>
#include <stdexcept>
#include <string>
#include <thread>

namespace {
using namespace ethereum_mpt;

struct Options {
    std::string ca, server_certificate, server_key, client_certificate, client_key;
    std::string server_name = "localhost";
};

Options options(int argc, char** argv) {
    Options result;
    for (int i = 1; i < argc; ++i) {
        const std::string option = argv[i];
        if (i + 1 == argc) throw std::invalid_argument("missing value for " + option);
        const std::string value = argv[++i];
        if (option == "--ca") result.ca = value;
        else if (option == "--server-cert") result.server_certificate = value;
        else if (option == "--server-key") result.server_key = value;
        else if (option == "--client-cert") result.client_certificate = value;
        else if (option == "--client-key") result.client_key = value;
        else if (option == "--server-name") result.server_name = value;
        else throw std::invalid_argument("unknown option: " + option);
    }
    if (result.ca.empty() || result.server_certificate.empty() || result.server_key.empty() ||
        result.client_certificate.empty() || result.client_key.empty())
        throw std::invalid_argument(
            "usage: ethereum_mpt_tls_demo --ca FILE --server-cert FILE --server-key FILE "
            "--client-cert FILE --client-key FILE [--server-name localhost]");
    return result;
}

// Local stream endpoints exercise TLS without opening a listening network port.
// The transport also accepts connected TCP sockets. Neither endpoint owns maps
// used by the other: only the service thread calls the serialized ORAM adapter.
class SocketPair {
public:
    SocketPair() {
        if (::socketpair(AF_UNIX, SOCK_STREAM, 0, sockets_) != 0)
            throw std::runtime_error("could not create demo sockets");
        const timeval timeout{30, 0};
        for (const auto socket : sockets_) {
            if (::setsockopt(socket, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout)) ||
                ::setsockopt(socket, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof(timeout))) {
                ::close(sockets_[0]);
                ::close(sockets_[1]);
                throw std::runtime_error("could not set demo socket timeout");
            }
        }
    }
    ~SocketPair() { for (const auto socket : sockets_) ::close(socket); }
    SocketPair(const SocketPair&) = delete;
    SocketPair& operator=(const SocketPair&) = delete;
    int client() const { return sockets_[0]; }
    int server() const { return sockets_[1]; }
    void abort() const {
        for (const auto socket : sockets_) ::shutdown(socket, SHUT_RDWR);
    }
private:
    int sockets_[2]{};
};

// This runs on the client, after receiving the entire authenticated frame.
void check_answers(const Snapshot& snapshot, const ClientContext& context,
                   const std::vector<ClientRequest>& requests, const Bytes& response) {
    const auto verified = verify_response_frame(context, requests, response);
    for (std::size_t q = 0; q < requests.size(); ++q) {
        const auto path = make_path_request(requests[q].address, requests[q].storage_slots);
        const auto expected = prove(snapshot.accounts, path.account_key);
        const auto& answer = verified[q];
        if (answer.error || answer.proof != expected)
            throw std::runtime_error("TLS account proof differs from canonical reference");
        const auto root = answer.account ? answer.account->storage_root : empty_trie_root();
        for (std::size_t s = 0; s < requests[q].storage_slots.size(); ++s) {
            const auto storage_proof = root == empty_trie_root() ? Proof{} :
                prove(snapshot.storage_tries.at(root), path.storage_keys[s]);
            if (answer.storage[s].error || answer.storage[s].proof != storage_proof)
                throw std::runtime_error("TLS storage proof differs from canonical reference");
        }
        // Conversion remains on the client. The demo does not emit private JSON.
        (void)to_eip1186_json(answer);
    }
}

void exchange(const TlsContext& client, const TlsContext& server,
              const std::string& server_name, const Snapshot& snapshot,
              const PackedSnapshot& packed, TieredPageMaps& maps,
              const BatchProfile& profile, std::uint64_t request_id) {
    const ClientContext context{word_from_u64(request_id), {}, packed.state_root,
                                packed.profile, profile};
    const auto sizes = client_frame_sizes(context);
    std::vector<ClientRequest> requests;
    for (std::size_t q = 0; q < profile.requests; ++q) {
        // Present/absent accounts, empty storage, duplicates, and absent slots.
        const std::uint8_t id = q % 4 == 3 ? 99 : q % 4 == 2 ? 1 :
                                static_cast<std::uint8_t>(q % 4 + 1);
        ClientRequest request{fixture_address(id), {}};
        for (std::size_t s = 0; s < profile.storage_slots; ++s)
            request.storage_slots.push_back(word_from_u64(s % 2 ? 99 : 1));
        requests.push_back(std::move(request));
    }
    const auto calls_before = maps.calls();
    const auto accesses_before = maps.accesses();
    SocketPair sockets;
    std::exception_ptr client_error, server_error;
    std::thread requester([&] {
        try {
            TlsFrameChannel channel(client, sockets.client(), context, server_name);
            channel.send_request(encode_request_frame(context, requests));
            const auto response = channel.receive_response();
            channel.close();
            check_answers(snapshot, context, requests, response);
        } catch (...) {
            client_error = std::current_exception();
            sockets.abort();
        }
    });
    try {
        TlsFrameChannel channel(server, sockets.server(), context);
        const auto received = decode_request_frame(context, channel.receive_request());
        const auto result = BatchTraversal(packed.state_root, packed.account_root,
            packed.profile, profile).run(maps, make_path_requests(context, received));
        // Both account and storage phases finish before any response is sent.
        const auto response = encode_response_frame(context, received, result);
        channel.send_response(response);
        channel.close();
    } catch (...) {
        server_error = std::current_exception();
        sockets.abort();
    }
    requester.join();
    if (client_error) std::rethrow_exception(client_error);
    if (server_error) std::rethrow_exception(server_error);

    std::uint64_t calls = 0, accesses = 0;
    for (std::size_t t = 0; t < 3; ++t) {
        calls += maps.calls()[t] - calls_before[t];
        accesses += maps.accesses()[t] - accesses_before[t];
    }
    if (calls != (profile.storage_slots ? 130u : 65u) ||
        accesses != 65 * profile.requests * (1 + profile.storage_slots))
        throw std::runtime_error("TLS demo changed the fixed ORAM schedule");
    std::cout << "TLSv1.3 Q=" << profile.requests << " K=" << profile.storage_slots
              << " request_frame_bytes=" << sizes.request_bytes
              << " response_frame_bytes=" << sizes.response_bytes
              << " calls=" << calls << " page_accesses=" << accesses << '\n';
}
}  // namespace

int main(int argc, char** argv) {
    try {
        const auto config = options(argc, argv);
        const auto client = TlsContext::client(config.ca, config.client_certificate,
                                               config.client_key);
        const auto server = TlsContext::server(config.ca, config.server_certificate,
                                               config.server_key);
        const auto snapshot = make_fixture();
        const auto packed = pack_snapshot(snapshot);
        validate_packed_snapshot(packed);
        TieredPageMaps maps(packed, 38);
        std::cout << "MPT mutually authenticated TLS stream demo (local socket pair)\n"
                  << "state_root=0x" << hex(packed.state_root) << '\n';
        exchange(client, server, config.server_name, snapshot, packed, maps, {1, 0}, 1);
        exchange(client, server, config.server_name, snapshot, packed, maps, {4, 2}, 2);
        exchange(client, server, config.server_name, snapshot, packed, maps, {19, 2}, 3);
        maps.finish_pending_work();
        std::cout << "Authenticated fixed-size frames and canonical ORAM proofs verified.\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_tls_demo: " << error.what() << '\n';
        return 1;
    }
}
