# Cryptographic primitives

See [DESIGN.md](DESIGN.md) for the routing and key-normalization argument.

`hash_primitives.hpp` exposes `AesRoundKeys`, `SecretKeySeed`,
`DeriveRoutingAesRoundKeys`, `DeriveStoredKeyAesRoundKeys`, the `AesCtrTag*Host`
helpers, and `AesHashKey128`. `DeriveAesRoundKeys` is raw key expansion for
standalone fixtures and the separately seeded tree; the hierarchy uses the
two labeled derivations.
The `AesCtrTag*Host` helpers evaluate the fixed two-block CBC routing function:
the labeled packed identity is block zero and the full stored key is block one.
(The `AesCtr` prefix refers to the packed counter/nonce identity in block zero;
the mode is CBC-MAC, not CTR.)
The scalar helpers here are the reference; the table layer's VAES and AES-NI
kernels compute the same function.
Production callers must pass their per-instance round keys explicitly; the
standalone helpers' fixed-key defaults are for reproducible kernel fixtures.

This folder owns cryptographic mechanism only. The hierarchy's nonce-family
coordinates belong to [`../oram/levelarena/`](../oram/levelarena/DESIGN.md);
the tag-to-bucket mapping belongs to [`../oram/table/`](../oram/table/DESIGN.md).
Callers should use the ORAM's seed and nonce interfaces rather than
instantiating routing policy here.
Validate the fixed-label known answers and derived scalar/vector schedules in
[`cpu_byteslice_key_derivation_test.cpp`](../../tests/oram/cpu_byteslice_key_derivation_test.cpp),
and the scalar/vector tag equivalence and wide-key cases in
[`cpu_byteslice_routing_tag_test.cpp`](../../tests/oram/cpu_byteslice_routing_tag_test.cpp)
and [`cpu_byteslice_oram_map_test.cpp`](../../tests/oram/cpu_byteslice_oram_map_test.cpp).
