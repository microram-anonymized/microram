# Ethereum MPT implementation boundary

This document describes how the example is built: the public canonical
reference and packing, the fixed-round account/storage traversal over real ORAM
batches, deterministic mock updates with replacement generations or
incremental page uploads, durable retained-window public checkpoints, local
client framing with proof verification, an optional TLS transport, and the
read/update measurement harnesses. [README.md](README.md) explains how to build
and run each part.
The reference trie/codec/packing routines operate on public data or disclosed
local correctness queries. They allocate, branch and index normally and must
not be called inside a protected private traversal.

## Security boundary

The example inherits the library's
[security boundary](../../DESIGN.md#security-boundary-and-limitations): the
observer sees memory addresses and control flow, while private memory contents
and per-instance keys are protected. The goal is to hide which account and
storage path a batch selects from that observer and, with the optional TLS
channel, from a network observer. It does not hide queries from the trusted
code processing them and is not a PIR protocol. The library does not encrypt or
authenticate stored buckets, so the pages need the same protected-memory
boundary as the library.

| Public for one service configuration | Private during a query |
|---|---|
| Entire MPT, account/storage contents, updates and canonical layout | Which account and storage slots are queried |
| Block/root, generation, capacities, page width and tier cutoffs | Selected child, page, offset and node length |
| Backend, worker budgets, query arrivals, `Q`, `K` and fixed schedule | Selected path length, reference kinds and results |
| Public update/retention policy and response width | Query errors and real proof lengths, until disclosed to the client |

Fixed ORAM call counts alone do not protect the application: selected offsets,
parsing, comparisons, hashing, result writes and dummy selection must also have
secret-independent addresses and control flow (see
[Fixed-round traversal](#fixed-round-traversal)). The target is
indistinguishable traces under the ORAM assumptions, not identical physical
addresses or a bound on wall-clock latency. To hide how many slots a client
wants, configure a public maximum `K` and mark unused slots with private masks.

Public maintenance must not leak earlier reads. Live ORAM buckets, stash and
position map have been rearranged by private reads, so maintenance never scans
or exports them; it uses ordinary map writes or builds fresh maps from public
state with fresh randomness. Compaction, tier policy, retention and page
allocation depend only on public chain contents, configuration and operation
counts, never on hit rates, visited records or lane activity.

## Canonical reference

`build_trie` sorts complete 256-bit paths, rejects duplicates, and constructs
canonical compressed branches, extensions and leaves. Branch value slots are
empty because every key has exactly 64 nibbles. Extensions lead to branches;
their nonempty paths strictly advance depth. Account payloads are bounded by
an eight-byte nonce, a 32-byte balance and two 32-byte hashes. Nonzero storage
scalars are RLP encoded before becoming leaf byte-string values.

Children shorter than 32 encoded bytes are embedded lists. Other children are
32-byte hash references; every nonempty root is identified by its hash even
when short. The Keccak implementation uses the original `0x01` suffix and a
136-byte rate. It is a variable-length reference implementation. The traversal
uses the separate four-permutation helper in `fixed.cpp`.

The complete graph validator checks canonical forms, child bindings, cached
hashes, role-specific values and depth. The proof verifier checks the selected
authenticated path, consumes inline descendants locally, and distinguishes
missing data from authenticated absence. It does not establish that unrelated
hash-referenced subtrees in a proof are available; complete snapshot validation
provides that guarantee before packing.

## Incremental canonical construction

`update_trie` accepts unique already-hashed key mutations with canonical encoded
values, or `nullopt` deletions. It applies batches through shared prefixes and
returns an immutable graph, sharing untouched nodes with the input. Changed
branches and compact paths are normalized before encoding: branches with one
child collapse, adjacent short paths merge, empty subtries disappear, and child
references follow the original 32-byte encoding threshold. There is no alternate
commitment or node encoding. No-op mutations preserve the root pointer.

The updater and `lookup_trie` operate on public data and require canonical
immutable graphs produced by `build_trie`, prior updates or full `validate_trie`.
They validate new values and duplicate mutation keys but do not rescan unrelated
subtrees; they are not untrusted graph importers or private query functions.
`TrieUpdateStats` counts distinct existing node objects inspected and new node
encodings/hashes, and is assigned only on success. These counters describe the
mutator, not copying, sorting, packing or complete service work.

`CanonicalState` owns the public logical state, canonical snapshot and nonempty
storage-root reference counts. `apply` stages a new value, updates each changed
storage trie and then the union of account paths, and verifies the advertised
root before returning. Root removal is delayed until all account mutations have
been considered so shared storage, root swaps and convergence remain valid.
Storage resets start from empty, while absent deletions and no-op fields preserve
existing nodes. Failed validation cannot modify the parent state or its graph.
`CanonicalUpdateStats` aggregates account/storage mutation counters and counts
storage processing calls, including explicit no-ops.

`IncrementalService` uses this construction even when its page update needs a
compaction or capacity replacement. `ReplacementService` retains `apply_delta`
and full canonical rebuilding as a reference baseline. Public-state and metadata
maps are still copied per prepared version, and packing/closure validation still
scans complete images. This does not claim delta-proportional total work or a
fully incremental persistent canonical database.

## Public packed snapshot

The packer validates the account trie and all referenced storage tries before
publication of a returned value. Stored records are deduplicated by
`(role, incoming nibble depth, hash)`. Nonempty roots are always stored;
ordinary embedded descendants stay inside canonical RLP. Account records carry
a storage-root locator, including a zero locator for empty storage.

Records are ordered deterministically and next-fit packed separately by public
tier. The default has account-top depths `[0,3)` and bulk for everything else.
A configured storage-top tier pools all storage roots. Disabled top maps have
no pages; each configured map has a permanent all-zero page zero. The bulk map
always exists, including for an empty snapshot.

Each record is an eight-byte header, the unchanged canonical RLP, then
twelve-byte locators:

```text
RecordHeader (8 bytes): rlp_bytes u16, kind u8 (branch/extension/leaf),
    trie_kind u8 (account/storage), link_count u8,
    nibble_depth u8 (incoming consumed-key depth, 0..64), reserved u8[2] = 0
Locator (12 bytes): page_id u64, offset u16, record_bytes u16
```

A branch carries one locator per hashed child in child-index order, an
extension one if its child is hashed, and an account leaf exactly one for its
storage root (zero for empty storage). Embedded children need none: a hash
reference alone (33 bytes) exceeds an embedded node's 31-byte limit, so an
inline subtree has no hashed descendants. The maximum record sizes are
`8 + 532 + 16*12 = 732` bytes for a branch, 88 for an extension, 168 for an
account leaf and 78 for a storage leaf, so every record fits one page.
Integers are explicitly little endian and records never straddle a page.
Location assignment precedes link resolution. Only the canonical RLP is
hashed, so locators can change on repacking without changing any Ethereum hash;
a wrong locator yields a hash mismatch (an error), never valid absence.

The independent packed-image validator inventories every page, checks record
extents, metadata, zero tails and statistics, then follows canonical references
and auxiliary locators from all retained account roots. It rejects incorrect hashes,
roles, depths, tier placement, missing/unreachable records and incomplete
storage closures. This validator uses public dictionaries and is not a query
algorithm.

`PackedSnapshot` holds a single root. `PackedGeneration` packs the union
of retained snapshot closures with one shared dummy per configured tier and
deduplication by the same role/depth/hash identity. Roots preserve input order,
including empty and duplicate state roots. Every input snapshot must supply its
complete storage closure even if another root shares those records. Validation
requires every physical record to be reachable from at least one root in the
packed image. Incremental images retain historical root locators until
compaction even after their queryable public manifests have been pruned.

`append_generation` validates its confirmed-loaded base and all new snapshot
closures, reuses exact role/depth/hash identities, and assigns new records only
to fresh page IDs. Published page tails are never filled later. Explicit public
packing-run boundaries let validation check cumulative run counts and next-fit
packing without treating a sealed old tail as reusable space. Unchanged roots
add no records or pages. Compaction repacks the union of retained snapshots.

## Upper-trie tiers and the padded schedule

With public cutoffs `h_A` and `h_S` fixed per generation, a node at incoming
nibble depth `d` is stored in the account-top map if it is an account node with
`d < h_A`, in the storage-top map if it is a storage node with `d < h_S`, and in
bulk otherwise. All storage tries share the same storage-top and bulk maps;
choosing a per-account map would reveal the account. Maps are never divided by
nibble value, which would reveal a key prefix.

Every lane runs all depths `0..64` and processes its next node only when its
private cursor equals the public depth. An extension from depth 0 to depth 5
with `h_A = 3` therefore reads at depth 0 in the account-top map, dummy-reads
at depths 1 and 2 (account top) and 3 and 4 (bulk), and reads its child at
depth 5 in bulk. Calling the lower map as soon as an extension is found, ending
early on absence, dropping a finished lane, or skipping an inline round would
each reveal path shape. Using consumed-nibble depth also keeps a record's
placement stable when a Patricia split adds a node above an unchanged subtree.

## Public updates and publication

`mock_chain` applies validated final-state deltas to a copy of public state.
Upsert/delete sets must be unique and disjoint; slot keys must be unique within
an upsert. Account fields replace old fields, storage patches existing state
unless explicitly reset, and absent/recreated accounts always start with empty
storage. Zero deletes a slot. Every resulting root must match the supplied
expected root before loading starts. Independent eight-block fixtures exercise
these transitions and two branches using pinned `py-trie` roots.

Both services share `VersionService` coordination and follow explicitly
supplied latest heads. `ReplacementService` validates
parent availability and consecutive block numbers, resolves a retained common
ancestor for forks, and packs all retained roots into a fresh generation. The
loader must return only after all maps have loaded successfully; the real
adapter uses fresh library randomness and normal batch writes. No live ORAM
layout, position map, stash or random seed is exported or reused.

The coordinator is serialized, with one caller and at most one complete proof
batch active. Its admission guard spans account and storage phases. A staged
generation is separate from the current one; `publish()` returns false during
an active batch or preparation. At the next full boundary a no-throw pointer
swap publishes the complete root table, profile and maps together. Old maps
are then retired. This is atomic under the serialized API contract, not a
thread-safe publication primitive. Preparation can run at public read
boundaries while the admitted batch keeps its original generation; the demo
injects preparation before the first storage round without changing traversal.

Root/parent failures publish nothing. A throwing loader destroys its partial
generation and preserves the current one. A fatal traversal exception makes
the current generation unavailable; fresh replacement from public state is the
recovery path. The loader interface is trusted to implement its completion and
snapshot-binding contract. Tests inject loader and reader failures separately.
Block identity fingerprints cover sorted complete delta contents. Validated
identities survive discarded staging and failed loading; identical unpublished
blocks may retry, identical published blocks are idempotent, and conflicting
reuse throws. Invalid root candidates never become validated identities.

The public retention policy is FIFO by distinct publication, across all branches;
reads, duplicate delivery and ancestor republication do not reorder it. Pruned
states/manifests are unavailable to service callers. If a reorg's common ancestor was pruned, even
with both heads retained, reload a public checkpoint before claiming the head
is served. Fingerprint tombstones persist for the session and consume growing
public metadata, separate from the bounded full-state window. Public checkpoint
files restore the retained window into fresh maps; tombstones outside that
window are not persisted. Observed and served identifiers remain
separate, including when a validated update fails to load.

Counters report the peak sum of the current and staged ORAM arenas and packed
page values after successful loading. They exclude public object/container
overhead, scratch and failed-load peaks. The integration demo also reports
Linux process peak RSS, which includes that overhead and transient allocations.
This is a tiny correctness workload and provides no production memory or update
throughput claim. Concurrent ingestion is not implemented.

## Durable public restart material

`checkpoint.hpp/.cpp` persist a `PublicHistoryCheckpoint`: the selected published
head and a vector of `PublicCheckpoint` entries in oldest-to-newest publication
order. Each entry contains the block header, delta fingerprint and complete
public account/storage state. Exporting during a staged update still selects
only published versions. No generation ID, locator, tier profile, page image,
backend state or query information enters the file. Replacement and incremental
services rebuild canonical tries and fresh ORAM maps for all saved roots on
restart. The saved head need not be the last entry, because reorg republication
does not reorder retention. Observed head resets to served head; pending updates
and identity tombstones outside the saved window are not restored. A
single-head `PublicCheckpoint` API is also provided.

Version 1 uses an explicit big-endian binary encoding, independent of struct
padding or the build's page width. Its 176-byte header contains the eight-byte
magic `EMPTCPT\0`, 32-bit version and zero reserved field, 64-bit total file
length, block ID, parent ID, state root, 64-bit block number, delta fingerprint,
and 64-bit account and total-slot counts. Each sorted account carries its
20-byte address, 64-bit nonce, 32-byte balance, 32-byte code hash and 64-bit
storage count, followed by sorted 64-byte slot/value pairs. The 32-byte trailer
is Keccak-256 of all preceding bytes. An empty checkpoint occupies 208 bytes.

Version 2 retains the common first 24 bytes with version set to 2. Its 80-byte
header adds the selected head ID at offset 24 and three 64-bit counts at offsets
56, 64 and 72: versions, cumulative accounts and cumulative slots. Each version
starts with 152 bytes: block ID, parent ID, state root, 64-bit number, fingerprint,
and 64-bit account/slot counts. Version-local account and storage records use the
same layout as version 1. One final 32-byte Keccak checksum covers the entire
file; there are no nested checksums. Full states are repeated per version.
History decoders accept version 1 as a one-entry history, while single-head
decoders reject version 2 to avoid losing retained roots silently.

Decode checks cumulative byte/count admission limits and exact extent before
canonical trie construction, rejects duplicate or out-of-order keys and zero
storage, and recomputes every state root. It accepts no trailing bytes. Block
IDs are nonzero and unique and the selected head must exist. A parent present
in the window must precede its child and have exactly the previous block number,
with overflow rejected. Absent parents are allowed as pruned ancestry; standalone
anchors retain version 1's metadata acceptance. Restore rejects a saved window
larger than the service's configured retention count before loading maps.
Limits bound serialized bytes and cumulative version/account/slot counts;
public map/trie construction needs additional memory. Encoding validates limits
before rebuilding tries or touching a file. This is public variable-time work
outside the private traversal.

Saving uses a mode-0600 temporary sibling, complete writes, file `fsync`, atomic
`rename`, and parent-directory `fsync`. Pre-rename failures remove the temporary
file and leave an existing target intact. A post-rename directory-sync failure
reports uncertain durability; it cannot roll back the visible replacement.
Loading requires a bounded regular file and a complete checksum-valid encoding.
Durability depends on the POSIX filesystem honoring synchronization calls;
tests exercise file errors and replacement semantics, not simulated power loss.

The checksum detects accidental corruption, not malicious replacement. State
root validation binds public state to the recorded root, but does not establish
trusted block identity, consensus or freshness. Callers must validate expected
metadata independently. The CLI uses committed independent fixture headers and
delta fingerprints and rejects unavailable continuation ancestors before map
loading or file writes. This remains a local mock restart demonstration.

## Incremental publication and failure

`IncrementalService` prepares public copy-on-write records without mutating its
current backend. It preflights all tier capacities, including dummy pages and
headroom, before choosing between append staging and a fresh compacted
generation. A configurable public append-count interval and explicit compaction
also rebuild from retained public states. Neither query contents nor privately
visited records influence these decisions.

Two optional per-tier thresholds apply to the proposed append before any shared
backend writes: `compact_at_fullness_percent` compares allocated pages (including
the dummy) with capacity, and `compact_at_dead_bytes_percent` compares unreachable
record bytes with total record bytes. Both accept `0..100` with zero disabled,
and trigger on equality. Fullness applies only to tiers that gain pages, so an
unchanged image does not rebuild solely because it is full. Dead-byte liveness
uses the post-update retained-root union, follows public storage links, and
deduplicates physical records by tier/page/offset. Embedded nodes are already
inside their containing record and have no external descendants. Dummy pages
and packing slack are excluded. Even a block with no new records can drop the
last retained reference to old records and cross the dead-byte threshold.
Selecting a retained head leaves reachability unchanged and skips these checks.
The percentage comparison uses exact integer arithmetic without overflowing
large capacity values. Any triggered policy loads a separate complete retained
closure, retaining the existing failure and full-batch publication rules.

An append stages a new manifest table sharing the current backend and generation
ID. `publish()` refuses to run during either proof phase. At a full batch boundary
it reserves the complete staged page closure, uploads nonempty tiers through
ordinary batch writes with no requested old values, and completes pending work.
Only then does a no-throw table swap admit the new root. New locators are never
used as a deduplication base until this completion. Reentrant reads, preparation
and publication during uploads are refused under the serialized caller contract.

An upload or completion exception clears staging, preserves the previously
published manifest table, counts reserved pages and marks the shared backend
unavailable. This includes every old root using that backend. Identical retry
builds a fresh generation; no uncertain locator is reused. If a read fails
after append preparation, publication first rebuilds the staged retained roots
into fresh maps. Failure of an independent fresh loader leaves the current
backend unchanged. Discarding an unuploaded append consumes no page IDs.

Retained-ancestor publication needs no writes and preserves generation IDs and
locators. Public retention bounds full states and queryable manifests; packed
images retain allocated historical records and their root locators until a
rebuild. Thus retired roots can still share allocated pages with live roots,
and all unreclaimed bytes count toward capacity. Compaction drops that historical
closure and recovers dead records and sealed-run tails. Memory accounting counts
shared ORAM arenas once and includes failed reservations; it does not count
duplicate public image copies as extra ORAM page storage.

Canonical construction shares unchanged nodes, while page allocation/upload
reuses unchanged packed records. Public-state copies, dictionary reconstruction,
image copying and closure validation still do whole-image work. There is no
claim of total update work proportional to changed records or of a production
ingestion rate. Dead-byte policy evaluation scans the public reachable closure;
it does not provide an incremental liveness index. Combined peak-memory admission
is not implemented.

## ORAM integration

The demo creates fresh maps only after packed validation, loads each complete
image using ordinary batch writes, and finishes pending work. Construction
failure exposes no usable partially loaded adapter. Eight-byte keys encode the
public page IDs exactly. Appends preflight their complete extent, reserve IDs
before tiled writes, and reject attempts to rewrite dummy, loaded or reserved
pages. Logical capacity remains distinct from the backend's rounded capacity.
Read batches prepare every descriptor before a single
`access_batch` call and preserve duplicate lanes. There is no scalar lookup
loop hidden in the batch adapter.

Map calls remain serialized. The example explicitly disables worker pools in
all tiers so it uses one caller budget. Public capacity includes the dummy
page; the library may round it up. Logical packing bytes and ORAM arena bytes
are reported separately. This small fixture is not a performance result or a
memory estimate for an Ethereum snapshot.

`TieredPageMaps` validates and loads all configured maps together and allocates
descriptor/key scratch for a public maximum lane count. Each read prepares all
keys and outputs, then issues one actual `access_batch` call. It retains no
canonical node or locator dictionary. Its diagnostic access/call counters
depend only on public batch sizes. Backend exceptions propagate; a fatal ORAM
failure cannot be turned into a successful absence or a promised dummy drain.

## Fixed-round traversal

`BatchTraversal` pins one root, locator and tier profile for the entire run.
Public admission checks reject zero/overflowing lane counts, proof-buffer limits,
mismatched `Q`/`K` and a reader with fewer than `max(Q, Q*K)` lanes
(`PageReader::max_lanes`) before any map read. All buffers are allocated before the
first round. The proof limit bounds proof slots; result fields and scratch are
additional proportional allocations. The caller must bind the reader to that
same validated immutable snapshot and serialize its use.

Account lanes run at public depths `0..64`, then `Q*K` storage lanes run at those
same depths when `K > 0`. Each round selects its map from phase and public depth.
Every lane submits a page request, including dummy page zero for completed,
failed, inline or waiting states. Extensions retain pending state across gaps.
Children of one node are never consumed recursively in that round. Storage
roots and their locators are selected only from authenticated account leaves.
An account error is inherited by all its storage lanes.

`fixed.hpp` supplies full-width selection with compiler value barriers and
fixed-stage rotation networks. Extraction checks record extents and zeroes
invalid or unused output without using selected offsets as addresses. Parsing
opens exactly 17 candidate outer RLP items, scans all 16 child positions and
locator candidates, and bounds malformed cursor arithmetic. The public role
selects the account or storage value parser. Inline subtrees are authenticated
by their parent and opened in later depth rounds; complete canonical closure
validation remains a precondition of loading a snapshot.

`fixed.cpp` constructs original Keccak padding and performs four complete
Keccak-f[1600] permutations every round, including idle lanes. It mask-saves the
digest at the true final block so later blocks cannot change it. Tests compare
every supported input length with the reference, including altered unused tails.

The transition step checks hashes, roles, kinds, link counts, storage-root
sentinels, depth and canonical extension targets. It compares paths over a
fixed 64-position scan and selects children/links without a private index.
Missing data, including a missing dummy page, latches an error. Failed lanes
continue their public schedule and finish with cleared fields and proof slots;
an active lane after depth 64 is also an error.

Proof slots are explicitly encoded as 65 arrays of 536 bytes. External nodes
are included at their public depth; inline and skipped depths remain empty.
Each slot writes all 532 payload bytes, including zero padding. The client-side
`decode_proof` rejects invalid headers/padding and returns canonical proof nodes
for `verify_proof`. This decoder and the demo's printed results are disclosed,
variable-work output. The default demos use plaintext frames; the optional
transport encrypts and authenticates those complete frames with TLS 1.3.

## Local client framing

`client.cpp` encodes complete plaintext request/response buffers in a versioned
example-local format. Every integer is explicitly little endian; hashes,
addresses and big-endian 256-bit words retain their byte order. No ABI padding
is serialized. Both frames start with the same 128-byte header:

| Offset | Bytes | Field |
|---:|---:|---|
| 0 | 8 | ASCII `MPTFRM01` |
| 8 | 1 | Frame kind: 1 request, 2 response |
| 9 | 1 | Account top depth `h_A` |
| 10 | 1 | Storage top depth `h_S` |
| 11 | 1 | Reserved, zero |
| 12 | 2 | Build-wide page width: 768, 1024 (default), or 2048 |
| 14 | 2 | Proof rounds, 65 |
| 16 | 8 | Public request count `Q` |
| 24 | 8 | Public storage slots per request `K` |
| 32 | 32 | Request ID |
| 64 | 32 | Block ID |
| 96 | 32 | Expected state root |

The request body contains `Q` records, each with a 20-byte address followed by
`K` 32-byte storage positions. The response body contains `Q` groups in request
order. Each group has the following account record, then `K` storage records
in requested slot order:

```text
AccountRecord:
    address[20], error_u64, present_u64, nonce_u64,
    balance[32], storage_root[32], code_hash[32], proof[34840]
    // 34,980 bytes
StorageRecord:
    slot[32], error_u64, present_u64, value[32], proof[34840]
    // 34,920 bytes

request_bytes  = 128 + Q * (20 + 32*K)
response_bytes = 128 + Q * (34980 + 34920*K)
```

The proof uses the existing 65 slots of 536 bytes each, with no node compaction
inside the service. Status masks are zero or all ones, exactly as in traversal
results. Successful absence retains its authenticated proof, clears nonce and
balance, uses the empty storage root and clears the local account code-hash
field. Failed lanes have cleared fields/proofs; account errors require errors
in every associated storage lane. A storage-only error can coexist with a
successfully verified account.

`client_frame_sizes` checks public counts and overflow, the existing aggregate
proof-buffer limit and a separate maximum complete-frame width, both 64 MiB by
default. Limits are local policy and are not wire fields. Decoders require an
exact width and byte-for-byte expected header before allocating lane buffers.
Wire counts, roots and profiles never determine admission or the client's
trusted root. Request decoding copies fixed addresses/positions; path hashing
uses their fixed lengths. Encoding visits every result field and every proof
byte at addresses determined by public `Q`/`K`, without branching on masks,
node lengths or values. Public shape validation precedes those copies.

`client_verify.cpp` runs only on the client, outside the protected traversal.
It checks echoed request addresses/positions, canonical masks and padding,
then authenticates account proofs against the caller's trusted state root.
Only the authenticated account supplies the storage root. Proven account
absence implies empty storage, while service errors remain explicit failures.
Convenience fields must match authenticated values. Malformed proofs/frames
throw; correctly cleared error records are returned as errors rather than
absence. JSON conversion accepts successful results, strips padding, emits
minimal quantities, and normalizes an absent account's code hash to the
canonical empty-code hash. It emits an EIP-1186 result without a JSON-RPC wrapper.

The snapshot demo checks frames against its known synthetic snapshot. Both
version demos build response context from the completed `VersionedBatch`
manifest, so preparation of a new head cannot relabel the admitted batch.
Their client root expectation comes from the independent public fixture state,
and every retained-root query goes through the same framed verification path.

Header equality is a local context check, not cryptographic authentication.
MPT proofs authenticate successful values against the chosen root; they do not
authenticate error/status bits, block freshness or request identifiers. Frames
are plaintext, with no channel or replay state. The optional channel below
encrypts and authenticates the whole fixed-width request and response. Expected
block freshness remains an independent client responsibility.

## TLS envelope boundary

`transport.hpp/.cpp` is an opt-in OpenSSL 3 target. `TlsContext::client` and
`TlsContext::server` load explicit CA, certificate-chain and private-key PEM
files. Both require peer certificates and normal certificate verification;
the client sets SNI and verifies an explicit DNS server name with
[`SSL_set1_host`](https://docs.openssl.org/3.0/man3/SSL_set1_host/).
The server's trusted client CA defines its admission population; there is no
per-subject ACL. TLS version bounds both equal 1.3. Compression, session
caching/tickets and early data are disabled. The example uses OpenSSL's record
encryption/authentication and sequence numbers rather than a custom AEAD scheme.
Disabling [early data](https://docs.openssl.org/3.0/man3/SSL_read_early_data/)
avoids accepting replayable 0-RTT requests. Ordinary authenticated application
retries are distinct from record replay and are not deduplicated across connections.

`TlsFrameChannel` borrows a connected blocking POSIX socket on systems with
`MSG_NOSIGNAL` support, checked at configuration. The owner must
keep it open, configure I/O timeouts and serialize access; destruction does
not block or close the socket. Public `ClientContext` admission computes both
frame sizes before TLS I/O. A fresh channel performs its handshake before
accepting application data and enforces client/server roles and exactly one
request followed by one response. `close()` completes authenticated shutdown
after the exchange, rejecting trailing application data and unnotified EOF;
callers complete this step before accepting an exchange as successful.
Transport failures permanently invalidate the channel. Socket timeouts bound
individual blocked operations, not the total time of a peer that keeps sending.

`send_request` and `send_response` accept only the admitted complete widths.
They visit the buffer at public offsets and write successive chunks of at most
16,384 bytes, including the final public-size remainder. No content, presence
mask, proof length or padding byte chooses a write boundary. The matching read
fills its fixed buffer through
[`SSL_read_ex`](https://docs.openssl.org/3.0/man3/SSL_read/) calls; fragmentation
does not change allocation or message width. Partial input, unauthenticated EOF,
and TLS authentication errors cannot return a complete frame. These byte-stream
operations do not themselves parse context or verify MPT proofs. The caller must
use `decode_request_frame` and `verify_response_frame` with independently known
context; accepting a response from a trusted TLS peer alone is insufficient.

The stream demo keeps all ORAM calls on the service thread and uses a separate
client thread over `socketpair`. It creates the entire response only after both
traversal phases finish, then sends it once. Client-side proof comparison and
JSON conversion happen after authenticated reception. Public roots and profiles
are fixed from the validated synthetic snapshot before admission. The optional
target does not retrofit TLS into the plaintext update demos or benchmarks.

TLS adds protocol overhead to the fixed plaintext widths. The DNS server name
(SNI), public batch profiles, connection timing, transport fragmentation and
completion timing
remain visible; the adapter does not promise fixed packet sizes or release times.
Both endpoints inhabit one process in the demo, so this is envelope integration
testing, not a separate protected service or a certificate-management system.
Deployment must place the server TLS endpoint within the traversal's protected
boundary. Existing compiler review covers traversal/local framing, not OpenSSL
internals or an end-to-end side-channel audit of this new transport.

The transport tests force uneven TLS fragments, compare encrypted record
widths across membership/absence/error responses, reject tampered and repeated
records, and check truncation, trailing data, certificate failures, socket
admission and default-SIGPIPE broken-peer handling. The suite is also suitable
for AddressSanitizer/UndefinedBehaviorSanitizer builds. These are correctness
checks, not a proof of network or local trace privacy.

## Compiler-output review

The fixed helpers (`fixed.cpp`), parser (`fixed_node.cpp`) and traversal
(`traversal.cpp`) were inspected in GCC and Clang assembly at `-O3` without LTO,
and additionally with `-march=native` on an AVX-512 host. Value barriers are
placed at mask creation as well as at selection: without the first barrier,
Clang can split record extraction into separate paths based on extent validity.

In the reviewed output, branches depend only on fixed scans, public
role/depth/lane counts, public admission/allocation, and stack checks. Selected
lengths, child choices, offsets and status masks stay in arithmetic selection,
and there are no private-address gathers. Native Clang emits masked
inline-buffer loads whose masks depend on the public loop index versus the
fixed 31-byte bound; no private value controls those memory masks. Because
compilers inline differently (GCC inlines `phase`/`step` into
`BatchTraversal::run`; Clang inlines `step`/`finish` into `phase`), the review
covers callers and `start_lane`, `finish` and child selection as emitted.

`encode_response_frame` (`client.cpp`) was inspected the same way at
`-std=c++17 -O3` without LTO or native flags. Its branches depend on the public
profile and vector counts, fixed copy lengths, the 65-by-536 proof loops,
allocation and error paths. Result masks and nonce are shifted/stored and proof
bytes are loaded/stored; no branch or address target derives from private result
masks, proof lengths or RLP contents.

The optional TLS send wrappers and socket BIO callback (`transport.cpp`) were
inspected with `-std=c++17 -O3 -DNDEBUG -DETHEREUM_MPT_PAGE_BYTES=1024 -S`,
without native flags or LTO. The send wrappers never load payload bytes: they
inspect vector width, public role/state and offsets, and TLS results. The 16 KiB
fragment selection and input pointer depend on public sizes. The BIO callback
forwards ciphertext to `send` and branches on length, syscall result and
`EINTR`. OpenSSL internals, syscalls and elapsed-time behavior are outside this
wrapper review.

For the non-default widths, `fixed::extract_record` and its
`window<768,732>` and `window<2048,732>` callees were compared with the
default-width object (GCC, `-O3 -DNDEBUG`, `objdump -drwC -Mintel`, no native
flags or LTO). Selected offsets, lengths, page IDs and need masks remain
arithmetic masks; candidate loads use public stage/index addresses; branches
cover fixed loops and stack checks. The 768-byte input uses ten 1024-byte
network stages, while 2048 uses eleven 2048-byte stages. This covers extraction
only, not every alternate-width caller.

To regenerate inspection output from the repository root, repeat for each
translation unit `fixed`, `fixed_node`, `traversal`, `client` and (with TLS)
`transport`, and for both compilers:

```sh
c++ -std=c++17 -O3 -g -fverbose-asm -I examples/ethereum_mpt \
  -S examples/ethereum_mpt/traversal.cpp -o /tmp/mpt-traversal-gcc.s
clang++ --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/15 \
  -std=c++17 -O3 -g -fverbose-asm -I examples/ethereum_mpt \
  -S examples/ethereum_mpt/traversal.cpp -o /tmp/mpt-traversal-clang.s
```

The Clang GCC-install path is host-specific. Repeat with the actual deployment
flags and inspect inlined callers, branch conditions and every address derived
from private input; counting conditional jumps alone is insufficient. This is a
source/object review, not a formal trace proof, a timing guarantee, or a
certification of other toolchains, LTO, sanitizer builds, ORAM internals or a
complete service. The library's protected-memory and capacity assumptions still
apply. Correctness and sanitizer tests supplement this review; they do not
establish obliviousness.

## Measurement boundary

The read benchmark adds public scalar-call and true-batch comparisons, tier
cutoffs, compile-time page widths and explicit top-tier backends. One caller
owns all maps and all worker counts are zero. Bulk remains tree-backed.
Normal traversal still submits one genuine batch per round; only the benchmark
scalar wrapper splits it into one-lane calls, after all independent input keys
for that round have been prepared. Every lane, including dummies, is retained.

Timers surround public rounds and complete service intervals. The benchmark
checks the expected tier/lane schedule and counts, verifies all client frames,
and compares canonical proof bytes outside service timing. It reports adapter
time separately from the remaining local traversal work; the latter includes
allocation and proof-buffer work and does not isolate parsing or hashing.
Throughput divides requests by service time with no queue or verification time.
After all iterations, a separately timed final barrier completes pending ORAM
work and catches failures before reporting success; service percentiles and
throughput exclude that drain.
Logical value traffic is not a measurement of physical ORAM traffic.
The sweep runner creates a fresh process for each configuration so that the
reported process high-water RSS belongs to that configuration.

The update benchmark serializes preparation, a configurable number of old-head
proof batches, and publication. Fresh replacement/compaction loading occurs in
preparation; shared-map append writes occur only in publication. Update pause
is the sum of those two intervals. Its `canonical_builder` field distinguishes
incremental `path_copy` construction from the replacement `full_rebuild` reference;
mode comparisons include both construction and page-loading differences.
Scheduled service time adds measured read
service and is the denominator for throughput and compaction duty cycle.
Per-block inclusive harness arrival-to-publication wall lag also includes framing,
verification and builder-accounting traversals; scheduled lag excludes that overhead. Arrival
starts immediately before preparation, after constructing the synthetic oracle.
Mandatory probes of all retained roots after publication are counted separately
and excluded from throughput, lag and duty cycle. These real ORAM reads still
change backend state and may leave deferred work for later completion barriers,
even with zero measured read batches. Every measured/probe proof is
verified, but oracle roots come from the local canonical builder; independent
fixture tests remain the separate external Ethereum correctness check.

`public_builder_memory()` measures live logical payload at observation points:
state fields/slots and distinct node RLP across shared retained versions, packed
page vectors for both current/pending images, upload vectors and identity
tombstones. Distinct node allocations with equal RLP still count separately.
Container/allocator overhead, unused capacity, decoded node fields, other
metadata and temporary construction buffers are excluded. The sampled peak
does not measure transient allocation peaks. ORAM arena counters and Linux
peak RSS are separate; RSS also includes benchmark oracle/proof allocations.
`packing_stats()` describes the published image, including unreclaimed historical
records until compaction. `occupancy()` walks that public image for all retained
roots and separates live/dead record bytes, published pages and capacities per
tier. Its page counts exclude pending uploads and uncertain failed reservations;
backend memory accounting includes the latter. The update benchmark samples
occupancy after publication outside service and lag, while configured policy
checks count toward preparation time. Read/update sweeps do not introduce arrival queues,
physical-traffic instrumentation, worker threads or concurrent ingestion.

Page width is a CMake setting propagated across every example target and
validated in client headers. The same generic fixed-address extraction network
handles 768, 1024 and 2048 bytes; records remain whole and retain their
732-byte bound. Correctness tests cover every supported width. The compiler
review above covers the default width end to end and extraction at the other
widths; other width/toolchain combinations need their own review.

## Scope and limitations

The TLS stream demo tests encrypted envelopes; a remote service, deployment
isolation, certificate management and public release timing are outside its
scope. Durable public checkpoints preserve the retained history window and
accept version-1 single-head files. Whole-state copying and packing scans still
bound the cost of incremental preparation. Queueing measurements, physical ORAM
traffic, isolated parsing/hash profiles, worker-budget sweeps, combined
peak-memory admission and concurrent ingestion are not implemented. The read
and serialized update benchmarks provide reproducible comparisons; their
synthetic workloads and small smoke runs do not establish a production
performance profile.
