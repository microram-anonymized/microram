// Optional OpenSSL 3 TLS 1.3 channel carrying exactly one fixed-width request
// and one fixed-width response per connection, with writes in fixed chunks
// chosen from public sizes only.

#include "transport.hpp"

#include <openssl/bio.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/x509v3.h>

#include <algorithm>
#include <array>
#include <cerrno>
#include <cstring>
#include <stdexcept>
#include <utility>

#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/socket.h>

#if OPENSSL_VERSION_MAJOR < 3
#error "The optional MPT transport requires OpenSSL 3 or newer"
#endif
#ifndef MSG_NOSIGNAL
#error "The optional MPT transport requires MSG_NOSIGNAL socket writes"
#endif

namespace ethereum_mpt {
namespace {

constexpr std::size_t fragment_bytes = 16 * 1024;

std::string error_message(const char* operation) {
    std::string message = std::string("MPT TLS ") + operation;
    for (auto error = ERR_get_error(); error != 0; error = ERR_get_error()) {
        std::array<char, 256> text{};
        ERR_error_string_n(error, text.data(), text.size());
        message += ": ";
        message += text.data();
    }
    return message;
}

void configured(int result, const char* operation) {
    if (result != 1) throw std::runtime_error(error_message(operation));
}

void check_path(const std::string& path) {
    if (path.empty() || path.find('\0') != std::string::npos)
        throw std::invalid_argument("MPT TLS requires explicit certificate, key and CA paths");
}

void check_server_name(const std::string& name) {
    if (name.empty() || name.size() > 253)
        throw std::invalid_argument("MPT TLS client requires a DNS server name");
    std::array<unsigned char, 16> address{};
    if (inet_pton(AF_INET, name.c_str(), address.data()) == 1 ||
        inet_pton(AF_INET6, name.c_str(), address.data()) == 1)
        throw std::invalid_argument("MPT TLS server name must be DNS, not an IP address");
    std::size_t label = 0;
    char previous = '.';
    for (const char character : name) {
        const bool alphanumeric = (character >= 'a' && character <= 'z') ||
            (character >= 'A' && character <= 'Z') ||
            (character >= '0' && character <= '9');
        if (character == '.') {
            if (label == 0 || previous == '-')
                throw std::invalid_argument("invalid MPT TLS DNS server name");
            label = 0;
        } else {
            if ((!alphanumeric && character != '-') ||
                (label == 0 && character == '-') || ++label > 63)
                throw std::invalid_argument("invalid MPT TLS DNS server name");
        }
        previous = character;
    }
    if (label == 0 || previous == '-')
        throw std::invalid_argument("invalid MPT TLS DNS server name");
}

void check_socket(int socket) {
    const auto flags = fcntl(socket, F_GETFL);
    int type = 0;
    socklen_t length = sizeof(type);
    sockaddr_storage peer{};
    socklen_t peer_length = sizeof(peer);
    if (flags == -1 || (flags & O_NONBLOCK) != 0 ||
        getsockopt(socket, SOL_SOCKET, SO_TYPE, &type, &length) != 0 ||
        type != SOCK_STREAM || getpeername(socket, reinterpret_cast<sockaddr*>(&peer),
                                          &peer_length) != 0)
        throw std::invalid_argument("MPT TLS requires a connected blocking stream socket");
}

// A borrowed-socket BIO avoids changing the application's SIGPIPE disposition.
// EINTR is retried, but socket timeouts (EAGAIN/EWOULDBLOCK) are fatal rather
// than marked retryable: this interface deliberately accepts blocking I/O only.
int socket_read(BIO* bio, char* output, int bytes) {
    BIO_clear_retry_flags(bio);
    if (bytes <= 0) return 0;
    const auto socket = *static_cast<int*>(BIO_get_data(bio));
    ssize_t result;
    do {
        result = recv(socket, output, static_cast<std::size_t>(bytes), 0);
    } while (result == -1 && errno == EINTR);
    return static_cast<int>(result);
}

int socket_write(BIO* bio, const char* input, int bytes) {
    BIO_clear_retry_flags(bio);
    if (bytes <= 0) return 0;
    const auto socket = *static_cast<int*>(BIO_get_data(bio));
    ssize_t result;
    do {
        result = send(socket, input, static_cast<std::size_t>(bytes), MSG_NOSIGNAL);
    } while (result == -1 && errno == EINTR);
    return static_cast<int>(result);
}

long socket_control(BIO*, int command, long, void*) {
    return command == BIO_CTRL_FLUSH ? 1 : 0;
}

const BIO_METHOD* socket_method() {
    static const std::unique_ptr<BIO_METHOD, decltype(&BIO_meth_free)> method([] {
        std::unique_ptr<BIO_METHOD, decltype(&BIO_meth_free)> created(
            BIO_meth_new(BIO_get_new_index() | BIO_TYPE_SOURCE_SINK, "MPT borrowed socket"),
            BIO_meth_free);
        if (!created) throw std::runtime_error(error_message("BIO allocation failed"));
        configured(BIO_meth_set_read(created.get(), socket_read), "BIO read configuration failed");
        configured(BIO_meth_set_write(created.get(), socket_write), "BIO write configuration failed");
        configured(BIO_meth_set_ctrl(created.get(), socket_control), "BIO control configuration failed");
        return created.release();
    }(), BIO_meth_free);
    return method.get();
}

int refuse_password(char*, int, int, void*) { return 0; }

}  // namespace

struct TlsContext::Impl {
    std::unique_ptr<SSL_CTX, decltype(&SSL_CTX_free)> context{nullptr, SSL_CTX_free};
    bool server;

    Impl(bool is_server, const std::string& ca_file, const std::string& certificate_file,
         const std::string& private_key_file) : server(is_server) {
        check_path(ca_file);
        check_path(certificate_file);
        check_path(private_key_file);
        ERR_clear_error();
        context.reset(SSL_CTX_new(TLS_method()));
        if (!context) throw std::runtime_error(error_message("context allocation failed"));
        auto* ctx = context.get();
        configured(SSL_CTX_set_min_proto_version(ctx, TLS1_3_VERSION), "minimum version failed");
        configured(SSL_CTX_set_max_proto_version(ctx, TLS1_3_VERSION), "maximum version failed");
        SSL_CTX_set_options(ctx, SSL_OP_NO_COMPRESSION | SSL_OP_NO_TICKET |
                                 SSL_OP_NO_RENEGOTIATION);
        SSL_CTX_clear_options(ctx, SSL_OP_IGNORE_UNEXPECTED_EOF);
        SSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF);
        // NO_TICKET alone still allows stateful TLS 1.3 tickets.
        configured(SSL_CTX_set_num_tickets(ctx, 0), "ticket configuration failed");
        configured(SSL_CTX_set_max_early_data(ctx, 0), "early-data configuration failed");
        configured(SSL_CTX_set_recv_max_early_data(ctx, 0), "early-data receive configuration failed");
        configured(static_cast<int>(SSL_CTX_set_max_send_fragment(ctx, fragment_bytes)),
                   "fragment configuration failed");
        SSL_CTX_set_mode(ctx, SSL_MODE_AUTO_RETRY);
        SSL_CTX_clear_mode(ctx, SSL_MODE_ENABLE_PARTIAL_WRITE | SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER);
        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER |
            (server ? SSL_VERIFY_FAIL_IF_NO_PEER_CERT : 0), nullptr);
        SSL_CTX_set_default_passwd_cb(ctx, refuse_password);
        configured(SSL_CTX_load_verify_locations(ctx, ca_file.c_str(), nullptr), "CA loading failed");
        configured(SSL_CTX_use_certificate_chain_file(ctx, certificate_file.c_str()),
                   "certificate loading failed");
        configured(SSL_CTX_use_PrivateKey_file(ctx, private_key_file.c_str(), SSL_FILETYPE_PEM),
                   "private key loading failed");
        configured(SSL_CTX_check_private_key(ctx), "certificate/private key mismatch");
    }
};

TlsContext::TlsContext(std::shared_ptr<Impl> impl) : impl_(std::move(impl)) {}

TlsContext TlsContext::client(const std::string& ca_file, const std::string& certificate_file,
                              const std::string& private_key_file) {
    return TlsContext(std::make_shared<Impl>(false, ca_file, certificate_file, private_key_file));
}

TlsContext TlsContext::server(const std::string& ca_file, const std::string& certificate_file,
                              const std::string& private_key_file) {
    return TlsContext(std::make_shared<Impl>(true, ca_file, certificate_file, private_key_file));
}

struct TlsFrameChannel::Impl {
    enum class State { request, response, complete, closed, failed };
    std::shared_ptr<TlsContext::Impl> context;
    int socket;
    ClientFrameSizes sizes;
    std::unique_ptr<SSL, decltype(&SSL_free)> ssl{nullptr, SSL_free};
    State state = State::request;

    Impl(std::shared_ptr<TlsContext::Impl> tls, int connected_socket,
         const ClientContext& expected, const std::string& server_name)
        : context(std::move(tls)), socket(connected_socket), sizes(client_frame_sizes(expected)) {
        if (!context) throw std::invalid_argument("MPT TLS context was moved from");
        if (context->server) {
            if (!server_name.empty())
                throw std::invalid_argument("MPT TLS server does not accept a server_name");
        } else {
            check_server_name(server_name);
        }
        check_socket(socket);
        ERR_clear_error();
        ssl.reset(SSL_new(context->context.get()));
        if (!ssl) throw std::runtime_error(error_message("connection allocation failed"));
        auto* bio = BIO_new(socket_method());
        if (!bio) throw std::runtime_error(error_message("socket BIO allocation failed"));
        BIO_set_data(bio, &socket);
        BIO_set_init(bio, 1);
        SSL_set_bio(ssl.get(), bio, bio);  // SSL now owns the BIO, never the socket.
        if (!context->server) {
            SSL_set_hostflags(ssl.get(), X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS |
                                        X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
            configured(SSL_set1_host(ssl.get(), server_name.c_str()), "hostname configuration failed");
            configured(SSL_set_tlsext_host_name(ssl.get(), server_name.c_str()), "SNI configuration failed");
        }
        ERR_clear_error();
        errno = 0;
        const auto result = context->server ? SSL_accept(ssl.get()) : SSL_connect(ssl.get());
        if (result != 1) fail("handshake failed", result);
        if (SSL_version(ssl.get()) != TLS1_3_VERSION || SSL_session_reused(ssl.get()) ||
            SSL_get_verify_result(ssl.get()) != X509_V_OK ||
            SSL_get0_peer_certificate(ssl.get()) == nullptr)
            fail("peer authentication failed");
    }

    [[noreturn]] void fail(const char* operation, int result) {
        const auto socket_error = errno;
        const auto ssl_error = SSL_get_error(ssl.get(), result);
        state = State::failed;
        auto message = error_message(operation);
        message += " (SSL error " + std::to_string(ssl_error) + ")";
        if (ssl_error == SSL_ERROR_SYSCALL && socket_error != 0)
            message += std::string(": ") + std::strerror(socket_error);
        throw std::runtime_error(message);
    }

    [[noreturn]] void fail(const char* operation) {
        state = State::failed;
        throw std::runtime_error(error_message(operation));
    }

    void require(bool server, State wanted) const {
        if (state == State::failed)
            throw std::runtime_error("MPT TLS channel is unusable after failure");
        if (context->server != server || state != wanted)
            throw std::logic_error("MPT TLS operation has the wrong role or exchange order");
    }

    void write(const Bytes& frame, std::size_t bytes) {
        if (frame.size() != bytes)
            throw std::invalid_argument("MPT TLS frame has the wrong public width");
        // No status, proof length, padding or other plaintext byte is inspected.
        for (std::size_t offset = 0; offset < bytes;) {
            const auto count = std::min(fragment_bytes, bytes - offset);
            std::size_t written = 0;
            ERR_clear_error();
            errno = 0;
            const auto result = SSL_write_ex(ssl.get(), frame.data() + offset, count, &written);
            if (result != 1) fail("frame write failed", result);
            if (written != count) fail("incomplete fixed-fragment write");
            offset += count;
        }
    }

    Bytes read(std::size_t bytes) {
        Bytes frame(bytes);
        for (std::size_t offset = 0; offset < bytes;) {
            const auto count = std::min(fragment_bytes, bytes - offset);
            std::size_t received = 0;
            ERR_clear_error();
            errno = 0;
            const auto result = SSL_read_ex(ssl.get(), frame.data() + offset, count, &received);
            if (result != 1) fail("frame read failed or truncated", result);
            if (received == 0 || received > count) fail("invalid frame read count");
            offset += received;
        }
        return frame;
    }
};

TlsFrameChannel::TlsFrameChannel(const TlsContext& tls, int connected_socket,
                                 const ClientContext& context, const std::string& server_name)
    : impl_(std::make_unique<Impl>(tls.impl_, connected_socket, context, server_name)) {}

TlsFrameChannel::~TlsFrameChannel() = default;

void TlsFrameChannel::send_request(const Bytes& frame) {
    impl_->require(false, Impl::State::request);
    impl_->write(frame, impl_->sizes.request_bytes);
    impl_->state = Impl::State::response;
}

Bytes TlsFrameChannel::receive_request() {
    impl_->require(true, Impl::State::request);
    auto frame = impl_->read(impl_->sizes.request_bytes);
    impl_->state = Impl::State::response;
    return frame;
}

void TlsFrameChannel::send_response(const Bytes& frame) {
    impl_->require(true, Impl::State::response);
    impl_->write(frame, impl_->sizes.response_bytes);
    impl_->state = Impl::State::complete;
}

Bytes TlsFrameChannel::receive_response() {
    impl_->require(false, Impl::State::response);
    auto frame = impl_->read(impl_->sizes.response_bytes);
    impl_->state = Impl::State::complete;
    return frame;
}

void TlsFrameChannel::close() {
    if (impl_->state == Impl::State::closed) return;
    impl_->require(impl_->context->server, Impl::State::complete);
    ERR_clear_error();
    errno = 0;
    const auto result = SSL_shutdown(impl_->ssl.get());
    if (result < 0) impl_->fail("shutdown failed", result);
    if (result == 0) {
        // Read one byte only to distinguish an authenticated end-of-stream from
        // forbidden trailing application data. Nothing is silently discarded.
        std::uint8_t trailing = 0;
        std::size_t received = 0;
        ERR_clear_error();
        errno = 0;
        const auto read_result = SSL_read_ex(impl_->ssl.get(), &trailing, 1, &received);
        if (read_result == 1) impl_->fail("unexpected application data after fixed frame");
        if (SSL_get_error(impl_->ssl.get(), read_result) != SSL_ERROR_ZERO_RETURN)
            impl_->fail("unauthenticated or truncated shutdown", read_result);
    }
    const auto shutdown = SSL_get_shutdown(impl_->ssl.get());
    if ((shutdown & (SSL_SENT_SHUTDOWN | SSL_RECEIVED_SHUTDOWN)) !=
        (SSL_SENT_SHUTDOWN | SSL_RECEIVED_SHUTDOWN))
        impl_->fail("incomplete authenticated shutdown");
    impl_->state = Impl::State::closed;
}

}  // namespace ethereum_mpt
