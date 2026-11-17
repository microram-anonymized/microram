// Tests the TLS channel: round trips, role/state binding, certificate and host
// name rejection, fragmentation, truncation, tampering and replay, SIGPIPE
// handling and equal ciphertext widths across response outcomes.

#include "transport.hpp"
#include "fixture.hpp"

#include <openssl/ssl.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cerrno>
#include <chrono>
#include <csignal>
#include <exception>
#include <future>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>

#include <fcntl.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

namespace {

using namespace ethereum_mpt;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(std::string("transport test: ") + message);
}

template <class Error, class Operation>
void reject(Operation operation, const char* message) {
    try {
        operation();
    } catch (const Error&) {
        return;
    }
    throw std::runtime_error(std::string("transport test accepted: ") + message);
}

struct SocketPair {
    int sockets[2]{-1, -1};

    SocketPair() {
        require(::socketpair(AF_UNIX, SOCK_STREAM, 0, sockets) == 0, "socketpair");
        const timeval timeout{5, 0};
        for (const auto socket : sockets) {
            require(::setsockopt(socket, SOL_SOCKET, SO_RCVTIMEO, &timeout,
                                 sizeof(timeout)) == 0, "receive timeout");
            require(::setsockopt(socket, SOL_SOCKET, SO_SNDTIMEO, &timeout,
                                 sizeof(timeout)) == 0, "send timeout");
        }
    }

    ~SocketPair() {
        for (const auto socket : sockets) if (socket >= 0) ::close(socket);
    }

    SocketPair(const SocketPair&) = delete;
    SocketPair& operator=(const SocketPair&) = delete;
};

struct PeerErrors {
    std::exception_ptr server, client;

    void success() const {
        if (server) std::rethrow_exception(server);
        if (client) std::rethrow_exception(client);
    }
};

// Each endpoint has a deadline and is shut down on every exit path, so an
// unexpected assertion or TLS failure also wakes its peer before joining.
template <class Server, class Client>
PeerErrors peers(Server server, Client client) {
    SocketPair sockets;
    PeerErrors errors;
    std::thread worker([&] {
        try { server(sockets.sockets[0]); } catch (...) { errors.server = std::current_exception(); }
        ::shutdown(sockets.sockets[0], SHUT_RDWR);
    });
    try { client(sockets.sockets[1]); } catch (...) { errors.client = std::current_exception(); }
    ::shutdown(sockets.sockets[1], SHUT_RDWR);
    worker.join();
    return errors;
}

struct Credentials {
    std::string directory;
    std::string file(const std::string& name) const { return directory + "/" + name + ".pem"; }

    TlsContext server() const {
        return TlsContext::server(file("ca"), file("server"), file("server-key"));
    }

    TlsContext client(const std::string& ca = "ca", const std::string& identity = "client") const {
        return TlsContext::client(file(ca), file(identity), file(identity + "-key"));
    }
};

ClientContext context_for(const PackedSnapshot& image, std::size_t q, std::size_t k) {
    ClientContext context;
    context.request_id = word_from_u64(0x10203);
    context.block_id = word_from_u64(0x40506);
    context.state_root = image.state_root;
    context.tiers = image.profile;
    context.batch = {q, k};
    return context;
}

class FixtureReader final : public PageReader {
public:
    FixtureReader(const PackedSnapshot& image, bool fail) : image_(image), fail_(fail) {}

    void read_pages_batch(Tier tier, std::size_t count, const std::uint64_t* ids,
                          Page* output, std::uint8_t* found) override {
        const auto& pages = image_.pages[static_cast<std::size_t>(tier)];
        for (std::size_t i = 0; i < count; ++i) {
            const bool exists = !fail_ && ids[i] < pages.size();
            found[i] = static_cast<std::uint8_t>(exists);
            output[i] = exists ? pages[static_cast<std::size_t>(ids[i])] : Page{};
        }
    }

private:
    const PackedSnapshot& image_;
    bool fail_;
};

void test_roundtrips(const Credentials& credentials, const PackedSnapshot& image) {
    const auto server = credentials.server();
    const auto client = credentials.client();
    for (const auto k : {std::size_t{0}, std::size_t{2}}) {
        const auto context = context_for(image, k ? 19 : 3, k);
        std::vector<ClientRequest> requests;
        const std::array<std::uint8_t, 3> addresses{{1, 2, 90}};
        for (std::size_t q = 0; q < context.batch.requests; ++q)
            requests.push_back({fixture_address(addresses[q % addresses.size()]),
                               k ? std::vector<Word>{word_from_u64(1), word_from_u64(9)}
                                 : std::vector<Word>{}});
        const auto request = encode_request_frame(context, requests);
        const auto sizes = client_frame_sizes(context);
        require(sizes.response_bytes > 16384, "response spans TLS records");
        for (const bool fail : {false, true}) {
            FixtureReader reader(image, fail);
            BatchTraversal traversal(image.state_root, image.account_root, image.profile,
                                     context.batch);
            const auto result = traversal.run(reader, make_path_requests(context, requests));
            const auto response = encode_response_frame(context, requests, result);
            require(response.size() == sizes.response_bytes,
                    "membership, absence and errors share public response width");
            peers([&](int socket) {
                TlsFrameChannel channel(server, socket, context);
                require(channel.receive_request() == request, "complete request plaintext");
                channel.send_response(response);
                channel.close();
            }, [&](int socket) {
                TlsFrameChannel channel(client, socket, context, "localhost");
                channel.send_request(request);
                const auto received = channel.receive_response();
                require(received == response, "complete multi-record response plaintext");
                const auto verified = verify_response_frame(context, requests, received);
                for (std::size_t q = 0; q < verified.size(); ++q) {
                    require(verified[q].error == fail, "authenticated service error");
                    require(verified[q].account.has_value() == (!fail && q % 3 != 2),
                            "authenticated membership or absence");
                    for (std::size_t s = 0; s < k; ++s)
                        require(verified[q].storage[s].error == fail &&
                                verified[q].storage[s].present == (!fail && q % 3 == 0 && s == 0),
                                "authenticated storage inclusion or absence");
                }
                channel.close();
            }).success();
        }
    }
}

void test_state_and_binding(const Credentials& credentials, const PackedSnapshot& image) {
    const auto context = context_for(image, 1, 0);
    const std::vector<ClientRequest> requests{{fixture_address(1), {}}};
    const auto request = encode_request_frame(context, requests);
    FixtureReader reader(image, false);
    BatchTraversal traversal(image.state_root, image.account_root, image.profile, context.batch);
    const auto response = encode_response_frame(
        context, requests, traversal.run(reader, make_path_requests(context, requests)));
    const auto server = credentials.server();
    const auto client = credentials.client();
    peers([&](int socket) {
        TlsFrameChannel channel(server, socket, context);
        reject<std::logic_error>([&] { channel.send_request(request); }, "server request send");
        reject<std::logic_error>([&] { channel.receive_response(); }, "server response receive");
        reject<std::logic_error>([&] { channel.send_response(response); }, "response before request");
        reject<std::logic_error>([&] { channel.close(); }, "close before exchange");
        require(channel.receive_request() == request, "state checks preserve valid request");
        reject<std::logic_error>([&] { channel.receive_request(); }, "second request receive");
        reject<std::invalid_argument>([&] { channel.send_response(Bytes(response.size() - 1)); },
                                      "short response preflight");
        channel.send_response(response);
        reject<std::logic_error>([&] { channel.send_response(response); }, "second response send");
        channel.close();
    }, [&](int socket) {
        TlsFrameChannel channel(client, socket, context, "localhost");
        reject<std::logic_error>([&] { channel.receive_request(); }, "client request receive");
        reject<std::logic_error>([&] { channel.send_response(response); }, "client response send");
        reject<std::logic_error>([&] { channel.receive_response(); }, "response before request send");
        reject<std::invalid_argument>([&] { channel.send_request(Bytes(request.size() + 1)); },
                                      "oversized request preflight");
        channel.send_request(request);
        reject<std::logic_error>([&] { channel.send_request(request); }, "second request send");
        const auto received = channel.receive_response();
        for (const auto field : {0, 1, 2}) {
            auto changed = context;
            (field == 0 ? changed.request_id : field == 1 ? changed.block_id : changed.state_root)[0] ^= 1;
            reject<std::invalid_argument>([&] { verify_response_frame(changed, requests, received); },
                                          "previous request/block/root response replay");
            reject<std::invalid_argument>([&] { decode_request_frame(changed, request); },
                                          "previous request/block/root request replay");
        }
        auto different = requests;
        different[0].address = fixture_address(2);
        reject<std::invalid_argument>([&] { verify_response_frame(context, different, received); },
                                      "response for different original address");
        channel.close();
        reject<std::logic_error>([&] { channel.receive_response(); }, "receive after close");
    }).success();

    SocketPair sockets;
    auto too_large = context;
    too_large.max_frame_bytes = client_frame_sizes(context).response_bytes - 1;
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, sockets.sockets[0], too_large, "localhost");
    }, "frame budget admission before handshake");
    auto overflow = context;
    overflow.batch.requests = std::numeric_limits<std::size_t>::max();
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, sockets.sockets[0], overflow, "localhost");
    }, "overflow admission before handshake");
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, sockets.sockets[0], context);
    }, "missing server identity before handshake");
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, -1, context, "localhost");
    }, "invalid borrowed socket");
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(server, sockets.sockets[0], context, "localhost");
    }, "server does not accept a client hostname");
    const auto flags = ::fcntl(sockets.sockets[0], F_GETFL);
    require(flags != -1 && ::fcntl(sockets.sockets[0], F_SETFL, flags | O_NONBLOCK) == 0,
            "set nonblocking socket");
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, sockets.sockets[0], context, "localhost");
    }, "nonblocking socket admission");
    ::close(sockets.sockets[0]);
    sockets.sockets[0] = ::socket(AF_UNIX, SOCK_STREAM, 0);
    require(sockets.sockets[0] >= 0, "unconnected socket allocation");
    reject<std::invalid_argument>([&] {
        TlsFrameChannel channel(client, sockets.sockets[0], context, "localhost");
    }, "unconnected socket admission");
}

void test_sigpipe(const Credentials& credentials, const PackedSnapshot& image) {
    // Run before other threaded tests. The raw OpenSSL fixtures below ignore
    // SIGPIPE; this child proves the production socket BIO needs no such handler.
    const auto child = ::fork();
    require(child >= 0, "fork SIGPIPE isolation");
    if (child == 0) {
        try {
            std::signal(SIGPIPE, SIG_DFL);
            const auto server = credentials.server();
            const auto client = credentials.client();
            const auto context = context_for(image, 1, 0);
            const auto request = encode_request_frame(context, {{fixture_address(1), {}}});
            std::promise<void> disconnected;
            auto disconnected_ready = disconnected.get_future();
            peers([&](int socket) {
                TlsFrameChannel channel(server, socket, context);
                require(::shutdown(socket, SHUT_RDWR) == 0, "disconnect authenticated peer");
                disconnected.set_value();
            }, [&](int socket) {
                TlsFrameChannel channel(client, socket, context, "localhost");
                require(disconnected_ready.wait_for(std::chrono::seconds(5)) == std::future_status::ready,
                        "peer disconnects before broken-pipe write");
                reject<std::runtime_error>([&] { channel.send_request(request); }, "broken pipe write");
            }).success();
            ::_exit(0);
        } catch (const std::exception& error) {
            std::cerr << "SIGPIPE child: " << error.what() << '\n';
            ::_exit(1);
        }
    }
    int status = 0;
    pid_t waited;
    do { waited = ::waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    require(waited == child && WIFEXITED(status) && WEXITSTATUS(status) == 0,
            "broken-pipe write raises an exception without terminating on SIGPIPE");
}

// Raw OpenSSL peers deliberately violate the application protocol. Production
// users use TlsFrameChannel; these helpers allow a partial authenticated frame.
struct RawPeer {
    std::unique_ptr<SSL_CTX, decltype(&SSL_CTX_free)> context{nullptr, SSL_CTX_free};
    std::unique_ptr<SSL, decltype(&SSL_free)> ssl{nullptr, SSL_free};

    RawPeer(const Credentials& credentials, int socket, bool certificate = true,
            int version = TLS1_3_VERSION, bool server = false) {
        context.reset(SSL_CTX_new(TLS_method()));
        require(context != nullptr, "raw TLS context");
        require(SSL_CTX_set_min_proto_version(context.get(), version) == 1 &&
                SSL_CTX_set_max_proto_version(context.get(), version) == 1,
                "raw TLS version");
        SSL_CTX_set_verify(context.get(), SSL_VERIFY_PEER, nullptr);
        require(SSL_CTX_load_verify_locations(context.get(), credentials.file("ca").c_str(),
                                              nullptr) == 1, "raw TLS trust");
        if (certificate) {
            const std::string identity = server ? "server" : "client";
            require(SSL_CTX_use_certificate_chain_file(context.get(),
                        credentials.file(identity).c_str()) == 1 &&
                    SSL_CTX_use_PrivateKey_file(context.get(), credentials.file(identity + "-key").c_str(),
                                                SSL_FILETYPE_PEM) == 1, "raw TLS credentials");
        }
        ssl.reset(SSL_new(context.get()));
        require(ssl != nullptr && SSL_set_fd(ssl.get(), socket) == 1 &&
                (server || SSL_set1_host(ssl.get(), "localhost") == 1), "raw TLS socket and hostname");
        require((server ? SSL_accept(ssl.get()) : SSL_connect(ssl.get())) == 1, "raw TLS handshake");
    }

    void send(const Bytes& bytes) {
        std::size_t written = 0;
        require(SSL_write_ex(ssl.get(), bytes.data(), bytes.size(), &written) == 1 &&
                written == bytes.size(), "raw TLS write");
    }

    Bytes receive(std::size_t size) {
        Bytes received(size);
        std::size_t offset = 0;
        while (offset < received.size()) {
            std::size_t read = 0;
            require(SSL_read_ex(ssl.get(), received.data() + offset,
                                received.size() - offset, &read) == 1 && read != 0,
                    "raw TLS complete read");
            offset += read;
        }
        return received;
    }

    void send_fragmented(const Bytes& bytes) {
        const std::array<std::size_t, 3> fragments{{7, 31, 4093}};
        std::size_t offset = 0, fragment = 0;
        while (offset < bytes.size()) {
            const auto size = std::min(fragments[fragment++ % fragments.size()], bytes.size() - offset);
            send(Bytes(bytes.begin() + offset, bytes.begin() + offset + size));
            offset += size;
        }
    }
};

void test_fragmentation(const Credentials& credentials, const PackedSnapshot& image) {
    const auto large_context = context_for(image, 200, 3);
    const auto request = encode_request_frame(large_context,
        std::vector<ClientRequest>(200, ClientRequest{fixture_address(1), std::vector<Word>(3)}));
    const auto server = credentials.server();
    peers([&](int socket) {
        TlsFrameChannel channel(server, socket, large_context);
        require(channel.receive_request() == request, "request reconstruction across uneven records");
    }, [&](int socket) {
        RawPeer raw(credentials, socket);
        raw.send_fragmented(request);
    }).success();

    const auto context = context_for(image, 1, 0);
    const auto small_request = encode_request_frame(context, {{fixture_address(1), {}}});
    const auto response = Bytes(client_frame_sizes(context).response_bytes, 0xa5);
    const auto client = credentials.client();
    peers([&](int socket) {
        RawPeer raw(credentials, socket, true, TLS1_3_VERSION, true);
        require(raw.receive(small_request.size()) == small_request, "raw request before fragmented response");
        raw.send_fragmented(response);
        auto closed = SSL_shutdown(raw.ssl.get());
        if (closed == 0) closed = SSL_shutdown(raw.ssl.get());
        require(closed == 1, "raw authenticated shutdown");
    }, [&](int socket) {
        TlsFrameChannel channel(client, socket, context, "localhost");
        channel.send_request(small_request);
        require(channel.receive_response() == response, "response reconstruction across uneven records");
        channel.close();
    }).success();
}

void test_authentication(const Credentials& credentials, const PackedSnapshot& image) {
    const auto context = context_for(image, 1, 0);
    const auto request = encode_request_frame(context, {{fixture_address(1), {}}});
    const auto server = credentials.server();
    for (const auto mode : {0, 1, 2}) {
        const auto client = mode == 0 ? credentials.client("wrong-ca") :
                            mode == 1 ? credentials.client("ca", "rogue-client") :
                                        credentials.client();
        const auto errors = peers([&](int socket) {
            TlsFrameChannel channel(server, socket, context);
            channel.receive_request();
        }, [&](int socket) {
            TlsFrameChannel channel(client, socket, context,
                                    mode == 2 ? "wrong.example.invalid" : "localhost");
            channel.send_request(request);
            channel.receive_response();
        });
        require(errors.server && errors.client, "untrusted certificate or wrong hostname rejected");
    }
    for (const bool missing_certificate : {false, true}) {
        const auto errors = peers([&](int socket) {
            TlsFrameChannel channel(server, socket, context);
            channel.receive_request();
        }, [&](int socket) {
            RawPeer client(credentials, socket, !missing_certificate,
                             missing_certificate ? TLS1_3_VERSION : TLS1_2_VERSION);
            client.send(request);
        });
        require(errors.server != nullptr, "missing client identity and TLS 1.2 rejected");
    }
}

void test_truncation(const Credentials& credentials, const PackedSnapshot& image) {
    const auto context = context_for(image, 1, 0);
    const auto request = encode_request_frame(context, {{fixture_address(1), {}}});
    const auto server = credentials.server();
    for (const bool authenticated_close : {false, true}) {
        const auto errors = peers([&](int socket) {
            TlsFrameChannel channel(server, socket, context);
            reject<std::runtime_error>([&] { channel.receive_request(); },
                                       "partial frame followed by close or abrupt EOF");
            reject<std::runtime_error>([&] { channel.receive_request(); }, "failed channel reuse");
        }, [&](int socket) {
            RawPeer client(credentials, socket);
            client.send(Bytes(request.begin(), request.end() - 1));
            if (authenticated_close)
                require(SSL_shutdown(client.ssl.get()) >= 0, "raw close_notify write");
        });
        errors.success();
    }
    // A peer that vanishes after its complete frame still cannot complete the
    // exchange: close() must see authenticated close_notify, not an ordinary EOF.
    const auto client = credentials.client();
    const auto response = Bytes(client_frame_sizes(context).response_bytes, 0);
    peers([&](int socket) {
        TlsFrameChannel channel(server, socket, context);
        channel.receive_request();
        channel.send_response(response);
        reject<std::runtime_error>([&] { channel.close(); }, "unnotified EOF after complete response");
    }, [&](int socket) {
        TlsFrameChannel channel(client, socket, context, "localhost");
        channel.send_request(request);
        require(channel.receive_response() == response, "full frame before unnotified shutdown");
    }).success();

    peers([&](int socket) {
        TlsFrameChannel channel(server, socket, context);
        require(channel.receive_request() == request, "complete request before trailing bytes");
        channel.send_response(response);
        reject<std::runtime_error>([&] { channel.close(); }, "trailing authenticated application data");
    }, [&](int socket) {
        RawPeer raw(credentials, socket);
        auto extra = request;
        extra.push_back(0);
        raw.send(extra);
        const auto received = raw.receive(response.size());
        require(received == response, "complete response before trailing-data rejection");
    }).success();
}

bool receive_exact(int socket, std::uint8_t* output, std::size_t size) {
    std::size_t offset = 0;
    while (offset < size) {
        const auto count = ::recv(socket, output + offset, size - offset, 0);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) return false;
        offset += static_cast<std::size_t>(count);
    }
    return true;
}

bool send_exact(int socket, const Bytes& bytes) {
    std::size_t offset = 0;
    while (offset < bytes.size()) {
        const auto count = ::send(socket, bytes.data() + offset, bytes.size() - offset, MSG_NOSIGNAL);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) return false;
        offset += static_cast<std::size_t>(count);
    }
    return true;
}

void relay_records(int from, int to, std::atomic<bool>& armed, std::atomic<bool>& injected,
                   bool replay, bool attack, std::vector<std::size_t>* lengths = nullptr) {
    std::array<std::uint8_t, 5> header{};
    while (receive_exact(from, header.data(), header.size())) {
        const auto length = (static_cast<std::size_t>(header[3]) << 8) | header[4];
        Bytes record(header.size() + length);
        std::copy(header.begin(), header.end(), record.begin());
        if (!receive_exact(from, record.data() + header.size(), length)) break;
        if (lengths && armed.load()) lengths->push_back(record.size());
        const bool inject = attack && armed.load() && !injected.load();
        if (inject && !replay) record.back() ^= 1;
        if (!send_exact(to, record)) break;
        if (inject) {
            injected.store(true);
            if (replay && !send_exact(to, record)) break;
        }
    }
    ::shutdown(to, SHUT_WR);
}

void test_ciphertext_widths(const Credentials& credentials, const PackedSnapshot& image) {
    const auto context = context_for(image, 1, 1);
    const auto server = credentials.server();
    const auto client = credentials.client();
    std::vector<std::size_t> expected_lengths;
    for (const auto mode : {0, 1, 2}) {
        const std::vector<ClientRequest> requests{{fixture_address(mode == 1 ? 90 : 1),
                                                   {word_from_u64(1)}}};
        const auto request = encode_request_frame(context, requests);
        FixtureReader reader(image, mode == 2);
        BatchTraversal traversal(image.state_root, image.account_root, image.profile, context.batch);
        const auto response = encode_response_frame(
            context, requests, traversal.run(reader, make_path_requests(context, requests)));
        SocketPair server_sockets, client_sockets;
        std::atomic<bool> armed{false}, injected{false};
        std::promise<void> server_ready;
        auto ready = server_ready.get_future();
        std::vector<std::size_t> lengths;
        PeerErrors errors;
        std::thread forward([&] {
            relay_records(client_sockets.sockets[1], server_sockets.sockets[1],
                          armed, injected, false, false);
        });
        std::thread reverse([&] {
            relay_records(server_sockets.sockets[1], client_sockets.sockets[1],
                          armed, injected, false, false, &lengths);
        });
        std::thread worker([&] {
            try {
                TlsFrameChannel channel(server, server_sockets.sockets[0], context);
                server_ready.set_value();
                require(channel.receive_request() == request, "record-width request");
                channel.send_response(response);
                channel.close();
            } catch (...) { errors.server = std::current_exception(); }
            ::shutdown(server_sockets.sockets[0], SHUT_RDWR);
        });
        try {
            TlsFrameChannel channel(client, client_sockets.sockets[0], context, "localhost");
            require(ready.wait_for(std::chrono::seconds(5)) == std::future_status::ready,
                    "record-width handshake completes before capture");
            armed.store(true);
            channel.send_request(request);
            require(channel.receive_response() == response, "record-width response");
            channel.close();
        } catch (...) { errors.client = std::current_exception(); }
        ::shutdown(client_sockets.sockets[0], SHUT_RDWR);
        worker.join();
        forward.join();
        reverse.join();
        errors.success();
        require(lengths.size() > 2, "captured multi-record response and shutdown");
        if (mode == 0) expected_lengths = lengths;
        else require(lengths == expected_lengths,
                     "membership, absence and error have equal encrypted record widths");
    }
}

void test_ciphertext_integrity(const Credentials& credentials, const PackedSnapshot& image) {
    // The request exceeds one TLS record, so duplicating the first record must
    // fail inside receive_request(), before any request can be admitted.
    const auto context = context_for(image, 200, 3);
    const auto request = encode_request_frame(context,
        std::vector<ClientRequest>(200, ClientRequest{fixture_address(1), std::vector<Word>(3)}));
    require(request.size() > 16384, "replay test needs multiple request records");
    const auto server = credentials.server();
    const auto client = credentials.client();
    for (const bool replay : {false, true}) {
        SocketPair server_sockets, client_sockets;
        std::atomic<bool> armed{false}, injected{false};
        std::promise<void> server_ready;
        auto ready = server_ready.get_future();
        PeerErrors errors;
        std::thread forward([&] {
            relay_records(client_sockets.sockets[1], server_sockets.sockets[1],
                          armed, injected, replay, true);
        });
        std::thread reverse([&] {
            relay_records(server_sockets.sockets[1], client_sockets.sockets[1],
                          armed, injected, replay, false);
        });
        std::thread worker([&] {
            try {
                TlsFrameChannel channel(server, server_sockets.sockets[0], context);
                server_ready.set_value();
                channel.receive_request();
            } catch (...) { errors.server = std::current_exception(); }
            ::shutdown(server_sockets.sockets[0], SHUT_RDWR);
        });
        try {
            TlsFrameChannel channel(client, client_sockets.sockets[0], context, "localhost");
            require(ready.wait_for(std::chrono::seconds(5)) == std::future_status::ready,
                    "relay handshake completed before ciphertext attack");
            armed.store(true);
            channel.send_request(request);
            channel.receive_response();
        } catch (...) { errors.client = std::current_exception(); }
        ::shutdown(client_sockets.sockets[0], SHUT_RDWR);
        worker.join();
        forward.join();
        reverse.join();
        require(injected.load() && errors.server && errors.client,
                "modified and replayed ciphertext rejected before complete frame delivery");
    }
}

}  // namespace

int main(int argc, char** argv) {
    try {
        require(argc == 2, "usage: ethereum_mpt_transport_test CREDENTIAL_DIRECTORY");
        std::signal(SIGPIPE, SIG_IGN);  // Raw negative-test peers also use OpenSSL's socket BIO.
        const Credentials credentials{argv[1]};
        const auto image = pack_snapshot(make_fixture(), {3, 2});
        test_sigpipe(credentials, image);
        test_roundtrips(credentials, image);
        test_state_and_binding(credentials, image);
        test_fragmentation(credentials, image);
        test_authentication(credentials, image);
        test_truncation(credentials, image);
        test_ciphertext_widths(credentials, image);
        test_ciphertext_integrity(credentials, image);
        std::cout << "TLS transport tests passed\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_transport_test: " << error.what() << '\n';
        return 1;
    }
}
