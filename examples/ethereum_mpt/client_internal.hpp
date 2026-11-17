// Internal declaration shared by client.cpp and client_verify.cpp: structural
// response decoding, kept out of the public client API.

#pragma once

#include "client.hpp"

namespace ethereum_mpt::client_detail {

// Client-only structural decoding. Checks exact width, expected public header
// and echoed addresses/slots. Only verify_response_frame should expose results.
BatchResult decode_response_frame(const ClientContext& expected,
                                  const std::vector<ClientRequest>& requests,
                                  const Bytes& frame);

}  // namespace ethereum_mpt::client_detail
