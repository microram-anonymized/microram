// Optional mutually authenticated TLS 1.3 envelope for complete client frames.

#pragma once

#include "client.hpp"

#include <memory>
#include <string>

namespace ethereum_mpt {

// Optional OpenSSL 3 transport. Each context trusts only the explicit CA file
// and presents its own certificate chain and unencrypted PEM private key.
// Servers authorize any client certificate valid for TLS client authentication
// under that CA. Applications needing finer authorization must add that policy.
class TlsContext {
 public:
    static TlsContext client(const std::string& ca_file,
                             const std::string& certificate_file,
                             const std::string& private_key_file);
    static TlsContext server(const std::string& ca_file,
                             const std::string& certificate_file,
                             const std::string& private_key_file);

 private:
    struct Impl;
    explicit TlsContext(std::shared_ptr<Impl> impl);
    std::shared_ptr<Impl> impl_;
    friend class TlsFrameChannel;
};

// One request and one response on a fresh mutually authenticated TLS 1.3
// connection. Session resumption, tickets, compression and early data are off.
// The connected, blocking POSIX stream socket is borrowed: the caller owns its
// lifetime and sets I/O deadlines before construction. Construction handshakes.
// Client server_name is a mandatory DNS name verified against certificate SANs
// and sent as SNI; server server_name must be empty. Socket writes suppress
// SIGPIPE locally. A channel has one caller and cannot be copied or moved.
//
// Widths are admitted from trusted public context before any I/O. These methods
// transport already encoded complete frames without inspecting their plaintext.
// Call decode_request_frame / verify_response_frame separately to bind the
// header, trusted root and original requests and to verify Ethereum proofs.
// Fixed 16 KiB writes (plus a public final remainder) conceal result lengths,
// not query arrivals, the public profile, or response completion timing.
class TlsFrameChannel {
 public:
    TlsFrameChannel(const TlsContext& tls, int connected_socket,
                    const ClientContext& context,
                    const std::string& server_name = {});
    ~TlsFrameChannel();
    TlsFrameChannel(const TlsFrameChannel&) = delete;
    TlsFrameChannel& operator=(const TlsFrameChannel&) = delete;
    TlsFrameChannel(TlsFrameChannel&&) = delete;
    TlsFrameChannel& operator=(TlsFrameChannel&&) = delete;

    void send_request(const Bytes& frame);
    Bytes receive_request();
    void send_response(const Bytes& frame);
    Bytes receive_response();

    // Both peers call after the complete exchange. Waits for authenticated
    // bidirectional close_notify and rejects trailing data or truncation.
    // Destructor only frees TLS state; it neither blocks nor closes the socket.
    void close();

    // Invalid setup/width throws invalid_argument; wrong role/order throws
    // logic_error. TLS/I/O errors throw runtime_error and poison the connection:
    // no retry, shutdown or further application I/O is allowed afterward.
 private:
    struct Impl;
    std::unique_ptr<Impl> impl_;
};

}  // namespace ethereum_mpt
