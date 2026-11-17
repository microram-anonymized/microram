# Cryptography for routing and stored keys

The hierarchy reveals which bucket it probes. A public routing function would
let an observer test candidate keys against that bucket, even if the surrounding
scan had fixed control flow. The implementation therefore derives routing tags
under a per-instance secret AES key. Rebuild identities are public and change
the routing function without requiring a new secret key schedule for each
table.

## Separate a secret key from a public routing identity

[`hash_primitives.hpp`](hash_primitives.hpp) represents an AES-128 schedule with
eleven 16-byte round keys, or 176 bytes of key material. The hierarchy passes
its routing schedule explicitly to tag generation. `SecretKeySeed::Random()`
draws the 16 master seed bytes from the kernel's generator with `getrandom(2)`,
retrying when a signal interrupts it. That call blocks only until the kernel's
pool is first initialized, and it carries the kernel's workarounds for faulty
CPU generators. Only where the call is unavailable (not Linux, a kernel without
it, or a sandbox that refuses it) does it fall back to `std::random_device`.
It refuses an all-zero seed with `std::runtime_error`: that seed would be the
all-zero AES master key, which a failing hardware generator can produce. It
runs once per map, at construction. The security reduction requires an
independent uniform secret 128-bit seed, so deployment entropy is an explicit
assumption. `Fixed(seed)` and `FixedAesRoundKeys()` provide reproducibility,
not a production secret.

The hierarchy derives two AES keys by encrypting two distinct public blocks
under that master, then expanding each resulting 128-bit block as a key:

| Role | Exact 16-byte input to master AES | Entry point |
| --- | --- | --- |
| Routing, including real and dummy tags | ASCII `oram-routing-v1` followed by one zero byte | `DeriveRoutingAesRoundKeys` |
| Stored-key normalization | ASCII `oram-stored-v1` followed by two zero bytes | `DeriveStoredKeyAesRoundKeys` |

Labels are byte strings, with no integer packing. The master is used only for
these two evaluations; all request and rebuild work uses the derived schedules.
Both helpers expand the master locally, so construction costs two master key
expansions, two block encryptions and two subkey expansions. The derivation adds
no per-access work, cache, allocator or stored master schedule, and a fixed seed
still determines every placement and stored representation.

For a transcript distinguisher, a reduction can query its master AES oracle
at these two labels and simulate all subsequent work with the returned keys.
Replacing master AES by a uniform permutation costs that reduction's AES-PRP
advantage. The returned keys are then a uniform ordered pair of distinct
128-bit blocks. Its total variation distance from two independent uniform
keys is exactly `2^-128`: the latter pair coincides with that probability,
and conditioned on being distinct has the former law. Consequently the
key-separation contribution is at most
`Adv_AES-PRP(B, 2 queries) + 2^-128`. Reduction `B` includes the full downstream
simulation time; the two-query count does not make that time constant.
This is the two-query case of the
[PRP/PRF switch (Bellare–Rogaway, §4.9, Lemma 4.17)](https://web.cs.ucdavis.edu/~rogaway/classes/227/spring05/book/main.pdf#page=79).
No numerical AES advantage or standards-compliance claim is supplied.

This separates hierarchy keys without a related-key assumption. It does not
replace the routing or CBC outputs by independent words; their construction
advantages and query counts remain separate in
[the error ledger](../../analysis/bound_certification/ERROR_ACCOUNTING.md).
Do not charge this switch twice if a joint construction bound already includes
it. Independently seeded instances have separate costs. Reusing a master across
instances repeats the subkeys and requires joint accounting. Raw
`DeriveAesRoundKeys` remains a key expansion for standalone fixtures and the
separately seeded tree position generator. Reusing the hierarchy master in that
generator or any other primitive is outside this two-label contract; the tree
backend is not included in the hierarchy certification.

The hierarchy enforces separate normalization and routing allowances; their
[source-level derivation](../oram/levelarena/DESIGN.md#routing-budget) bounds
routing queries and physical block calls, including repeated work and padding.
Those counts do not bound the full simulation time or prove observation
correspondence. Exhausting the routing allowance stops the instance and may
interrupt accepted work.

## Route a complete key under an explicit identity

Every routing message has exactly two 16-byte blocks, for narrow and wide keys
and for real and dummy probes. Let `p = PackAesCtrHighWord(nonce_lo, nonce_hi)`.
The byte encoding is:

| Block | Bytes 0–7 | Bytes 8–15 |
| --- | --- | --- |
| `B0` | Little-endian `p` | ASCII `oram-rt1` |
| `B1` | Little-endian stored low word | Little-endian stored high word |

The label's high-word integer is `0x3174722d6d61726f`. A narrow key has zero
high word. A dummy uses its reserved counter as the low word and zero as the
high word. The packed identity contains a real/dummy domain bit, a 48-bit
family counter and a 15-bit level; the domain bit separates otherwise equal
real and dummy inputs. Width is fixed per instance, so no width tag is needed.
The [hierarchy](../oram/levelarena/DESIGN.md) supplies the family identities,
and the [table layer](../oram/table/DESIGN.md) maps the resulting word to a bucket.

Under the routing schedule `E`, the tag is fixed-length CBC-MAC projected to
64 bits:

```
prefix = E(B0)
tag = low64(E(prefix XOR B1))
```

This uses the same routing key for both blocks, with no further subkeys, key
expansions or retained family-prefix cache. A scalar evaluation costs two AES
encryptions. The common-family rebuild kernel shares one prefix encryption
across each group of 32 keys, then performs 32 second-block encryptions. This
reuse preserves the function exactly; prefix values remain secret internal
state. Online probes materialize four qwords per padded candidate in their
existing scratch and evaluate both blocks, keeping the publication plan public.
The construction has one message format, including when the stored key fits
eight bytes. Mixing one-block narrow tags with these two-block tags under the
same schedule is outside this contract.

Equality of encoded messages forces equality of the complete stored key and
packed identity. Wide keys therefore cannot alias structurally (as they could
if the two key words were XORed into one block), without relying on stored-key
randomness. Distinct logical keys may
still normalize to the same stored key. The packing function also masks its
fields: callers must prevent out-of-range counters, level truncation and
identity reuse before packing. These are separate lifetime/correspondence
obligations. Repeated real inputs still give repeated tags, so the hierarchy's
freshness and dummy protocol remain necessary.

After the key-separation hybrid, a conservative routing replacement bound is

```
delta_route <= min(1, Adv_AES-PRP(B_route, at most 2q queries)
                      + 8*q*q / 2^128).
```

Here `q` bounds distinct two-block routing messages in the complete execution.
This specializes [Bellare–Kilian–Rogaway, Theorem 3.2,
Eq. (11)](https://cseweb.ucsd.edu/~mihir/papers/cbc.pdf#page=18) to two blocks of
128 bits. The theorem allows adaptive messages; an oracle wrapper memoizes
repeats and projects each response to its low 64 bits. Restricting the input
format and projecting outputs cannot increase distinguishing advantage.
The reduction simulates the remaining execution, so its running time includes
that work. Its statistical term already includes the permutation/function
switch and internal CBC collisions; neither is charged again as an encoding
error. The bound is valid with clipping even when it is numerically vacuous.

This construction bound is not a native lifetime query count or a proof of
compiled execution. `q` includes initialization, rebuild routing, real probes,
dummy candidates and speculative work, rather than only accepted API requests.
Retries and repeated primitive calls still contribute to execution time and
the physical block-call inventory even when they add no distinct message.
At `q = 2^32`, the displayed statistical allowance is already `2^-61`, before
AES advantage, normalization and capacity error. Achieving a total native
`2^-64` target therefore needs a tighter justified analysis or changed
cryptographic parameters. This implementation claims neither that target nor
independent AES words without the stated reduction.

## Normalize wide keys without discarding their distinguishing bytes

The table layer stores user keys of at most 15 bytes verbatim, at their own
width. It maps keys of 16 bytes or more to a 16-byte result with
`AesHashKey128`, using the stored-key schedule derived above. The subkeys become independent only in the stated hybrid;
native keys are deterministic functions of one master seed.

For a fixed user-key width of sixteen bytes, one AES permutation produces the
stored key. Thus distinct keys of that width do not collide in this conversion,
and neither do the verbatim widths below it. For collisions, no random-function
replacement of normalization is needed at widths 1–16: after key separation,
the routing reduction can simulate this injective conversion with its own
independent normalization key. Segment matching of 16-byte stored keys
(`CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT`) uses their values as well. Its
false-match bound treats the one-block AES as an ideal permutation, at cost
`Adv_AES-PRP(B_normalize, Q)`; see
[ERROR_ACCOUNTING.md](../../analysis/bound_certification/ERROR_ACCOUNTING.md#stored-key-matching). For wider keys, the
implementation uses a length-prefixed CBC-MAC construction: one AES block for
the length followed by one per padded input block. The cost is therefore
`m = 1 + ceil(u/16)` AES block evaluations for a fixed `u`-byte key above sixteen bytes,
compared with one evaluation at sixteen bytes and none below.

The checked [byte-encoding argument](../../lean/RebuildBound/Spec/NativeKey.lean)
proves the short-key claim at fixed width, with verbatim keys below sixteen bytes
and injective block encryption used only at sixteen. It represents both stored
words as sixteen bytes, including the zero high word of keys of at most eight
bytes. The long-key statement proves message injectivity and the
exact block count, preserving the length and every input byte. It does not prove
digest injectivity or replace native AES/packing correspondence. All-width
OpenSSL vectors provide finite implementation evidence. Mixed-width trailing-zero
aliases are explicit negative regressions: nine versus fifteen verbatim bytes,
fifteen versus sixteen bytes, and nine versus sixteen in the generic helper's
one-block branch.

For native widths `17 <= u <= 64`, `m` is fixed at 3, 4 or 5 for the instance.
The length block followed by the zero-padded key is injective at that fixed
width. The same fixed-length CBC theorem cited above therefore gives

```
delta_normalize <= min(1, Adv_AES-PRP(B_normalize, at most m*Q queries)
                          + 2*m*m*Q*Q / 2^128).
```

Here `Q` bounds distinct user keys submitted to normalization, including
initialization, misses and processing before a refused access. The reduction
simulates routing with the independent routing key and replaces normalization
by a uniform 128-bit random function; repeated keys are memoized. Its running
time includes the complete simulation. This bound includes the primitive
switch, so no additional switch is charged for these calls. Fixed width and
exclusive use of the normalization schedule are part of the contract; the
generic helper's ability to process other lengths does not extend this result
to mixed-width calls under the same key.

Compression still permits collisions in the random-function hybrid. Their
unconditional probability is at most `min(1, Q*(Q-1)/2^129)`, even for adaptive
keys: each new answer meets at most the preceding distinct answers. This is
charged separately from `delta_normalize`, without conditioning the capacity
experiment on collision-free normalization. At `Q = 2^32`, the collision term
is below `2^-65`, but the construction allowance is larger and the native `Q`
need not equal the access horizon. The hierarchy's
[normalization budget](../oram/levelarena/DESIGN.md#normalization-budget) bounds
distinct inputs and actual conversions by its checked reservation limit `B`,
including failed initialization and standalone conversion calls. Thus `Q = B`
is valid conservatively, with at most `m*B` normalization block encryptions.
Routing and running-time budgets remain separate. Neither arithmetic statement
supplies a total native security certificate.

Normalization bounds subsequent comparison and routing state by sixteen key
bytes, independent of the original width. AES round operations also avoid
secret-indexed software lookup tables in this implementation. Neither use
encrypts stored values: data-at-rest encryption and authentication are outside
this layer's implemented role.

The [README](README.md) identifies engineering entry points. Follow the
[maintenance rule](../../DESIGN.md#documentation-maintenance) when revising this
document.
