# Ethereum MPT example

This example uses the library as the private storage layer of an Ethereum
state-proof service. The Merkle Patricia Trie (MPT), its contents and its
updates are public; which accounts and storage slots a client asks about is
private. The service returns standard Ethereum account and storage proofs
(EIP-1186 style) that a client verifies against an independently trusted state
root, while the memory accesses of the service reveal only public batch
dimensions.

The construction keeps canonical Ethereum node encodings and hashes, but packs
many nodes into each fixed-width ORAM value (a *page*) and adds physical child
*locators* (page ID, offset, length) outside the hashed bytes, so traversal
needs no online hash-to-location directory. A batch of `Q` account lookups,
each with `K` storage slots, runs 65 public nibble-depth rounds per phase; in
every round each lane reads exactly one page with one ORAM batch call (a dummy
page when it has nothing real to read), and all node parsing, hashing and
child selection use fixed-work masked code. Small ORAMs hold the top trie
depths (*tiers*); a bulk ORAM holds the rest. [DESIGN.md](DESIGN.md) gives the
security boundary, record format, schedule and update protocol.

The example builds a deterministic account/storage snapshot, verifies
membership and absence proofs, packs the snapshot into 1,024-byte pages, and
serves proof batches through real `TreeByteMap::access_batch` operations on a
fixed depth schedule.
The update demo applies deterministic public blocks, retains historical roots,
and publishes versions only between complete proof batches. The incremental
demo copies changed canonical paths while sharing untouched nodes, reuses stable
records, appends sealed pages through normal ORAM writes, and compacts retained
roots into fresh generations.
All three demos round-trip fixed-size requests and responses and verify the
decoded account/storage proofs against independently known roots.

**These are local correctness demos.** The default executables use plaintext
frames; the optional TLS demo encrypts complete frames over authenticated local
streams. Neither is a deployed network service. The traversal
uses isolated fixed-work helpers and padded proof slots. A review of their
compiler output is described in [DESIGN.md](DESIGN.md#compiler-output-review);
it is not a security certification.
The public codec, proof verifier, builder and diagnostic output still use
variable-time accesses and run outside the protected traversal.

## Build and run

The examples are external consumers of the installed library. From the
repository root, on a machine meeting the library's CPU requirements:

```sh
cmake -S . -B build-mpt-library -DCPU_BYTESLICE_ORAM_BUILD=library
cmake --install build-mpt-library --prefix /tmp/ethereum-mpt-install
cmake -S examples -B build-mpt-examples \
  -DCMAKE_PREFIX_PATH=/tmp/ethereum-mpt-install -DCMAKE_BUILD_TYPE=Release
cmake --build build-mpt-examples -j2
ctest --test-dir build-mpt-examples --output-on-failure
./build-mpt-examples/ethereum_mpt/ethereum_mpt_example
./build-mpt-examples/ethereum_mpt/ethereum_mpt_updates
./build-mpt-examples/ethereum_mpt/ethereum_mpt_incremental
```

The demo uses 48 accounts, a shared eight-slot storage trie, account top depths
`[0,3)`, and one bulk map. Page zero exists in both maps. Both backends are
explicitly `TreeByteMap<>`, with one shared caller and no background workers;
the benchmark also supports hierarchical top-tier backends. It checks all loaded pages,
duplicate real/dummy IDs, and a missing page in a batch. It then runs `Q = 19`,
`K = 2`, including duplicate requests, present/absent accounts and storage slots,
and accounts with empty storage. The 19 account lanes and 38 storage lanes
exercise batches larger than 16 lanes.

Every phase runs depths `0..64`, including extension gaps, inline nodes and
finished lanes. With `K > 0`, there are exactly 130 application batch calls,
`65*Q*(1+K)` logical page reads and four Keccak permutations per lane/round.
For the demo these are 3,705 reads and 14,820 node-hash permutations. Proof
slots occupy 34,840 bytes per account or storage traversal (1,985,880 bytes for
this batch), separately from convenience fields and scratch. `K = 0` runs
only the 65 account calls. Slot counts and admission limits are public.

The `Q = 19, K = 2` request and response frames occupy 1,724 and 1,991,708 bytes;
the `Q = 1, K = 0` frames occupy 148 and 35,108 bytes. These fixed sizes include
context, echoed keys, result fields and all proof padding, regardless of
membership, absence or a service error.

The output reports `S` canonical bytes, `N` stored records, `E` ordinary hash
links, `A` account leaves, `R` record bytes, `P` real pages, packing runs and
utilization per tier. Logical page-value bytes, rounded ORAM capacity and
ORAM arena bytes are separate measurements. Arena bytes are not total resident
memory: builder objects, container overhead, stacks and test scratch are extra.

The 1,024-byte value is a packed page containing variable-length records, not
one padded node. The maximum canonical branch is 532 bytes; its stored record
is 732 bytes after the eight-byte header and sixteen twelve-byte child locators.
The 1,024-byte default fits the largest record, packs many small nodes per
read, and keeps a power-of-two extraction network; it is not a tuned optimum.
Set the example CMake cache variable to
`-DETHEREUM_MPT_PAGE_BYTES=768`, `1024` (default), or `2048` to build the complete
example, tests and benchmark at that width. Each build uses one public width
throughout packing, maps, fixed-work extraction and client context validation.
A smaller page does not automatically save memory: with whole records, more
of each 768-byte page can be left as unusable tail than with 1,024 bytes, so
total page bytes can grow. The 532-byte proof payload bound and the four Keccak
permutations per round do not change with page width.

Widths below 732 bytes cannot hold the largest record whole and would require
splitting records into fragments, which is not implemented. With `F = ceil(732/B)` fragments per record, every lane would
read `F` consecutive page IDs in every round (dummies included) and reconstruct
the complete canonical node before authenticating it: reading only the chosen
child's fragment cannot verify a branch hash, which commits to all siblings.
A record would be placed only where `offset + record_bytes <= F*B`, so `F`
reads always suffice. Fragmentation can improve storage density but multiplies
logical reads to `F * 65 * Q * (1+K)`; the validator, extraction network and
capacity accounting would all need fragment-aware versions.

## Mock blocks and replacement generations

`ethereum_mpt_updates` follows the explicitly supplied mock latest heads from
`fixtures/mock_blocks.txt`. All eight state roots come independently from
`py-trie==3.1.0`. The fixture exercises complete account-field replacement,
storage insert/overwrite/zero-delete, account deletion/recreation, storage reset,
shared storage roots, an empty state and a fork with two replacement branches.
These are final-state mutations; the example does not execute transactions or
validate Ethereum consensus/fork choice.

The demo injects each update between the account and storage phases of a
`Q = 2, K = 1` batch. It builds and loads new maps, confirms that publication is
refused while the batch is active, and verifies that both phases still return
proofs for the original block. After publication it verifies proofs against
every retained root. Each returned `VersionedBatch` carries its block ID, parent,
number, root, generation, root locator and tier profile.
The response frame takes its block/root/profile from that pinned manifest;
client expectations come from the original request and independently constructed
fixture root. Every retained-root query also passes client verification. At
`Q = 2, K = 1`, each request is 232 bytes and each response is 139,928 bytes.

`ReplacementService` uses one serialized caller. Preparation may be interleaved
at a public read boundary; the example does not provide a background ingestion
thread. Publishing swaps the complete manifest table and all tier maps together.
Failed root checks or partial generation loading leave the current maps intact.
A fatal read exception marks that generation unavailable until a fresh one is
published. Observed and served heads remain separate during preparation/failure.

Retention keeps the last configured number of distinct published blocks in
publication order, including abandoned branches (eight in the demo). Duplicate
delivery and reads do not extend retention. A reorg can therefore prune a common
ancestor while retaining both branch heads; that reorg requires a public
checkpoint reload. Identical deliveries are idempotent, conflicting block IDs
are rejected even after failed loading/discard, and identity fingerprints remain
as session-long public tombstones after full states are pruned. `checkpoint()`
exports the published head's public state; `history_checkpoint()` exports the
whole retained window and selected head for a fresh service. The checkpoint
file API persists both forms; the demos save the full window by default.

The output separates peak overlapping ORAM arena bytes, packed page-value bytes,
and Linux process peak RSS. RSS includes public states, builder temporaries,
allocator overhead and proof buffers; arena/page counters alone are not total
memory. Full rebuilds per block are a correctness baseline, not an Ethereum
ingestion throughput claim.

## Durable public checkpoints

Both update demos accept `--checkpoint-out PATH`, `--checkpoint-in PATH`, and
`--through-index N` (the inclusive fixture index, from 0 to 7). They save after
verifying every retained root at startup and after each subsequent publication.
This example stops after fixture index 4, then restarts in a separate process
and follows both forks using saved ancestors:

```sh
./build-mpt-examples/ethereum_mpt/ethereum_mpt_incremental \
  --through-index 4 --checkpoint-out /tmp/mpt-public.checkpoint
./build-mpt-examples/ethereum_mpt/ethereum_mpt_incremental \
  --checkpoint-in /tmp/mpt-public.checkpoint \
  --checkpoint-out /tmp/mpt-public.checkpoint
```

Replacement and incremental services share the format, so either executable
can resume the other's file. The file is independent of page width, tier profile
and backend. On restart the service validates every canonical root and rebuilds
fresh ORAM maps with fresh randomness. It restores publication order, selected
head and retained block identities, then verifies account/storage proofs for
every restored root before processing more blocks. Service constructors reject a
saved window larger than the configured retention count instead of pruning it.

`checkpoint.hpp` provides `encode_public_history_checkpoint`,
`decode_public_history_checkpoint`, `save_public_history_checkpoint` and
`load_public_history_checkpoint`. Version 2 stores an explicit served-head ID and
ordered versions, each with block identity, parent, number, state root, delta
fingerprint, public account fields and nonzero storage slots. A single Keccak
checksum covers the complete file. Decoding rejects malformed lengths/counts,
duplicate blocks, missing heads, inconsistent retained parent ordering/numbers,
noncanonical account/slot order, zero storage, root mismatches and trailing data.
An absent parent is allowed because retention can prune ancestors.

The single-head `*_public_checkpoint` APIs encode/decode one version-1 head.
History loaders also accept version-1 files and promote them to a one-entry
window; the single-head loaders reject version 2 instead of silently discarding history.
Default admission limits are 256 MiB per file, 1,024 versions, 1,000,000 cumulative
account records and 4,000,000 cumulative storage slots. Repeated states count
once per saved version. Callers can supply `CheckpointLimits` explicitly; the
demos cap versions at eight. Limits bound serialized data and counts, not total
memory used to reconstruct canonical tries. The format stores complete states
per version and does not deduplicate them on disk.

On POSIX systems, saving writes a private temporary sibling file, syncs it,
atomically renames it over the destination, then syncs the parent directory.
Failures before rename preserve an existing destination and clean up the
temporary file. If the directory sync fails after rename, saving reports that
durability is uncertain; the destination may already contain the new checkpoint.
Successful saves rely on the filesystem honoring these synchronization calls.

The checksum and state-root reconstruction do not authenticate block metadata
or prevent rollback. A caller must obtain its expected block/root from a trusted
source. The demos check every restored header field and fingerprint against the
independently generated fixture before loading maps. Checkpoints contain public
state only, with no ORAM layout, position map, stash, randomness or query data.

Pending updates and identity tombstones outside the retained window are excluded.
A reorg needing a pruned ancestor still requires an earlier checkpoint or a
complete public state source. The demos preflight the requested fixture
continuation and reject missing ancestors before loading maps or replacing the
output file. Version-2 checkpoints at indices 2 or 4 retain the ancestors needed
to finish both forks. A version-1 single-head checkpoint at index 4 lacks
index 1 and cannot follow the next fork.

## Incremental updates and compaction

`ethereum_mpt_incremental` runs the same eight independent mock roots and
retained account/storage proof checks. `IncrementalService` shares the version
coordinator with `ReplacementService`. Preparation validates the public delta
and packs only new `(role, incoming depth, hash)` record identities. Existing
page bytes and locators remain unchanged, including their unused tails. Each
nonempty append is a separately recorded next-fit packing run.

`prepare()` performs no writes to the current maps. `publish()` first requires
a complete batch boundary, uploads every staged tier with ordinary `kWrite`
batches, finishes pending work, then publishes the entire manifest table.
The demo stages updates between account and storage phases and confirms that
the admitted batch keeps its original root. Unchanged roots need no page writes;
switching to a retained ancestor also reuses the same generation.

Capacities include dummy pages and configurable public headroom per enabled
tier. All tiers are preflighted before any upload. If an append cannot fit,
preparation loads a fresh compacted generation containing the retained roots.
A public append-count interval and `prepare_compaction()` also trigger rebuilds.
The demo uses eight spare pages per enabled tier and compacts after three
append publications, then performs a final explicit compaction. Output reports
uploaded pages, append/replacement publication counts and compaction savings.

`IncrementalOptions::compact_at_fullness_percent` and
`compact_at_dead_bytes_percent` accept `0..100`; zero disables each threshold
(the default). Before uploading, fullness compares the proposed page count,
including the dummy, with each tier's capacity. It applies only to tiers gaining
pages. Dead-byte pressure compares unreachable record bytes with all record
bytes per tier after applying retention; it excludes page slack and dummies.
Every retained root and shared storage trie counts as live, regardless of which
roots were queried. Reaching either threshold stages fresh maps. Even an
unchanged-root block can trigger dead-byte compaction by pruning old history;
a retained-head switch does not change the live closure or trigger these checks.
Small headroom or low fullness thresholds can cause frequent rebuilds.

Upload failure publishes nothing and conservatively invalidates the shared
backend, including the old root's instance. Reserved/uncertain pages remain
counted, and retries rebuild fresh maps from public state. Failures while
loading a separate replacement leave the current maps usable. Discarding an
unuploaded append leaves no reserved pages. Tests inject partial multi-tier
uploads and completion failures and verify these distinctions.

Retention prunes public manifests and full states; physical records and root
locators remain in the cumulative packed image until compaction. This permits
exact accounting and reuse of confirmed-loaded pages, including pages shared
by live and retired roots. Compaction reconstructs only retained closures.
Backend memory counters count a shared backend once and include uncertain
reservations. `public_builder_memory()` separately reports retained logical
state, canonical RLP, packed-image copies, upload copies and identity payloads;
container storage and scratch are extra.
`occupancy()` reports per-tier published page counts/capacities and live/dead
record bytes. It walks public packed links and counts shared records once,
including records sharing pages with dead records. Pending uploads and uncertain
failed reservations are excluded from this published-image view; backend memory
counters continue to include uncertain reservations. This scan reads no ORAM
pages and does not inspect query history.

`CanonicalState` builds the initial canonical snapshot once, then applies a
block by copying only changed account/storage trie paths. `update_trie` groups
mutations by shared prefixes, splits and merges compact paths, collapses branches,
and preserves the canonical embedded-versus-hashed child rule. Unchanged nodes
retain their `NodePtr`; no-op updates retain the root pointer. Shared storage
roots remain live until their last account reference disappears. Reset/deletion,
fork preparation and rejected roots leave the parent snapshot unchanged.

The incremental service uses this path even when an ORAM capacity limit forces
a fresh generation. The replacement service retains the full-state canonical
rebuild as a comparison baseline. Unit tests compare mutation roots and proof
bytes with full rebuilds and independent fixtures, and check node sharing and
split/merge/child-width boundary cases.

Public-state and dictionary copies, packing validation and packed-image staging
still do whole-state work. This is incremental canonical construction and page
uploading, not a fully incremental database. Concurrent ingestion and combined
peak-memory admission are not implemented. The
update benchmark below measures the complete serialized preparation/publication
path, including the remaining scans and copies.

## Local client frames

`client.hpp` provides `encode_request_frame`, `decode_request_frame` and
`make_path_requests` for admission, followed by `encode_response_frame` and
`verify_response_frame` for the completed batch. A caller supplies the expected
request ID, block ID, trusted state root, tier profile and public `Q`/`K`.
`client_frame_sizes` checks arithmetic, the proof-buffer limit and a separate
complete-frame limit before buffers are allocated. The default for both byte
limits is 64 MiB; decoded results and other scratch are additional allocations.
The exact versioned layout is specified in [DESIGN.md](DESIGN.md#local-client-framing).

The response encoder writes every field and all 65 proof slots for each lane;
it does not choose work or output size from presence/error masks or node lengths.
The variable-work client decoder rejects mismatched context, echoed addresses
or slots, incorrect widths, noncanonical masks/padding and inconsistent fields.
It verifies the account against the caller's root, then verifies storage against
the storage root committed by that account. Valid service errors remain explicit
errors, and are never treated as proven absence. A verified absent account yields
empty storage proofs and zero values.

`to_eip1186_json` exports one successfully verified account as an EIP-1186 result
object with account and storage proof arrays. It omits the JSON-RPC wrapper,
uses minimal hexadecimal quantities and refuses any account/storage error.
For an absent account it supplies zero nonce/balance and the canonical empty
storage root and code hash. JSON formatting belongs on the client because its
length and work disclose the proof shape; the default demos print only summaries.

The frames are plaintext and provide no network privacy, channel authentication
or replay protection. Matching header fields checks the local request context;
only MPT proofs authenticate successful values against the trusted root. Status
bits and request IDs are authenticated when these frames use the optional TLS
channel below. Block freshness still comes from the client's trusted root.
The snapshot demo uses a zero block ID for its synthetic
snapshot; the update demos use the committed mock block IDs.

## Optional authenticated TLS transport

Enable OpenSSL 3 and POSIX socket support with `MSG_NOSIGNAL` (such as Linux)
explicitly; the default build does not need OpenSSL. Starting from the
installed-library setup above:

```sh
cmake -S examples -B build-mpt-tls \
  -DCMAKE_PREFIX_PATH=/tmp/ethereum-mpt-install -DCMAKE_BUILD_TYPE=Release \
  -DETHEREUM_MPT_ENABLE_TLS=ON
cmake --build build-mpt-tls -j2
ctest --test-dir build-mpt-tls --output-on-failure
python3 examples/ethereum_mpt/transport_test.py --demo-only \
  build-mpt-tls/ethereum_mpt/ethereum_mpt_tls_demo openssl
```

The runner creates a temporary test CA and separate server/client credentials,
runs the demo, and removes those files. No private keys are committed. To use
existing PEM credentials, invoke the executable directly:

```sh
./build-mpt-tls/ethereum_mpt/ethereum_mpt_tls_demo \
  --ca ca.pem --server-cert server.pem --server-key server-key.pem \
  --client-cert client.pem --client-key client-key.pem --server-name localhost
```

`transport.hpp` wraps the existing complete frames in OpenSSL TLS 1.3. Both
peers verify certificate chains against explicitly configured trust files;
the client also verifies the server DNS name. The server admits client
certificates issued by its configured CA; finer per-client authorization is
outside this example. Compression, early data, session resumption and tickets
are disabled. TLS supplies record authentication, encryption and replay
protection; no application cipher or nonce format is added.

The channel admits public frame sizes before its handshake, then permits one
request and one response per connection. Reads fill the exact admitted buffer;
writes send a completed frame in fixed chunks of at most 16 KiB. It never reads
wire counts to choose allocation sizes or strips proof padding. Truncation and
TLS errors invalidate the channel. Callers still decode requests against the
server's expected context and verify responses against the client's original
request and trusted state root. A new authenticated application request can
repeat an earlier request ID; there is no persistent application deduplication.

The demo uses a local socket pair and a client thread, with one serialized ORAM
caller. It verifies `Q=1,K=0`, `Q=4,K=2` and `Q=19,K=2`, including membership,
absence, duplicate accounts and empty storage. All 65 account rounds and, when
enabled, 65 storage rounds finish before response transmission. The client
checks canonical proof bytes and EIP-1186 conversion after decryption.
The transport accepts caller-owned connected sockets, including TCP sockets;
the caller configures timeouts and closes the sockets. The demo sets 30-second
I/O timeouts and opens no listening port.

This exercises the encrypted envelope, not deployment isolation: both endpoints
and the disclosed fixture live in one process. A deployment must keep TLS and
traversal inside the same protected-memory boundary and obtain expected roots
independently. Public profiles, the server name (SNI), arrivals, TLS overhead and
completion timing remain observable. There is no fixed release schedule, remote
service lifecycle, certificate provisioning/revocation workflow or TLS benchmark.
The default read/update benchmarks still measure plaintext local framing.

## Engineering entry points

| File | Responsibility |
|---|---|
| `codec.hpp/.cpp` | Ethereum Keccak-256, strict RLP, compact paths, account and storage scalar codecs |
| `trie.hpp/.cpp` | Canonical fixed-key trie construction, immutable batch mutations, graph validation and proofs |
| `packing.hpp/.cpp` | Public closure validation, stable append packing, sealed-run accounting and link validation |
| `fixed.hpp/.cpp` | Masked selection, bounded fixed-address extraction and four-permutation Keccak |
| `fixed_node.hpp/.cpp` | Fixed-work RLP, compact-path, scalar and record parsing |
| `traversal.hpp/.cpp` | Public depth rounds, masked lane transitions, account/storage handoff and padded proofs |
| `client.hpp`, `client.cpp`, `client_verify.cpp` | Fixed-size local framing, checked admission, client proof verification and EIP-1186 JSON |
| `transport.hpp/.cpp`, `transport_main.cpp` | Optional mutually authenticated TLS 1.3 fixed-frame channel and real-ORAM stream demo |
| `transport_test.cpp`, `transport_test.py` | TLS protocol/failure tests and temporary test credential generation |
| `page_store.hpp`, `page_map.hpp` | Capacity-bounded immutable page appends and preallocated reads through the public tree byte-map API |
| `mock_chain.hpp/.cpp` | Public final-state deltas, incremental canonical state, identities, fixture loading and reference snapshots |
| `version.hpp/.cpp` | Retention, append/replacement publication, capacity preflight, compaction, reorgs and public checkpoints |
| `checkpoint.hpp/.cpp` | Bounded public checkpoint codec and atomic durable file replacement |
| `fixture.hpp`, `main.cpp` | Complete deterministic public snapshot and runnable integration example |
| `update_main.cpp` | Replacement and incremental mock chain demos through real ORAM maps |
| `update_benchmark.cpp`, `update_benchmark_sweep.py` | Serialized read/update measurements and matching replacement/incremental sweeps |
| `*_test.cpp` | Codec, structural, corruption, packing and external-fixture tests |
| `fixtures/generate.py`, `fixtures/generate_blocks.py` | Independent Ethereum `py-trie` golden fixture generators |

The trie API accepts already-hashed 32-byte paths. The demo hashes the 20-byte
account address and the actual 32-byte big-endian storage position separately.
Zero storage is represented by omission from the entry list. Duplicate paths,
noncanonical values and incomplete storage closures are rejected. Snapshot
building is from complete entries. `apply_delta` and `snapshot_from_state` retain
the full rebuild reference; `CanonicalState::apply` shares unchanged trie nodes
and verifies the new root without reconstructing every account/storage trie.
`update_trie` and `lookup_trie` are public variable-time helpers requiring an
immutable canonical graph from the builder, updater or `validate_trie`; they do
not validate unrelated subtrees on every call.

`make_path_request` hashes an address and its storage positions with fixed-length
work. `BatchTraversal` also accepts already-hashed paths for structural fixtures.
It pins its root, root locator and tier profile across both phases.
Both version services pin the containing generation. `TieredPageMaps` loads a validated immutable image
and owns preallocated request scratch. Calls remain serialized. A custom
`PageReader` must preserve the batch contract and the same snapshot binding;
the ordinary reader used in unit tests is deliberately public instrumentation.

Results have zero/all-ones `present` and `error` masks. Malformed nodes, wrong
hashes, bad locators and missing pages (including dummy pages) latch errors;
failed lanes keep their full schedule and return cleared fields/proof slots.
Account errors propagate to every associated storage lane. Fatal backend
exceptions propagate: the demo does not assume a failed ORAM can keep reading.
`verify_response_frame` checks framing and fields, removes proof padding with
`decode_proof`, and authenticates account/storage values with `verify_proof`.
Only the optional TLS channel encrypts these frames; plaintext callers have no
network-privacy claim.

`verify_proof` returns an optional encoded value: absence is `nullopt`, while
malformed, missing or tampered nodes throw. Proofs are ordered root plus hashed
descendants; inline children remain inside their parent. Extra proof nodes are
rejected. This deliberately narrow reference API is not an arbitrary Ethereum
proof-database importer.

## Independent fixtures

Normal tests need no Python packages or network access. Committed golden data
comes from Ethereum `py-trie==3.1.0`, with pinned RLP and Keccak dependencies in
`fixtures/requirements.txt`. The C++ tests compare roots and generated proof
bytes exactly, and verify the externally generated proofs and expected values.
The generator also verifies its minimal proofs using `HexaryTrie.get_from_proof`.

To reproduce the fixtures in an isolated environment:

```sh
python3 -m venv /tmp/mpt-fixtures
/tmp/mpt-fixtures/bin/pip install -r examples/ethereum_mpt/fixtures/requirements.txt
/tmp/mpt-fixtures/bin/python examples/ethereum_mpt/fixtures/generate.py \
  > /tmp/mpt-oracle-vectors.txt
diff -u examples/ethereum_mpt/fixtures/oracle_vectors.txt /tmp/mpt-oracle-vectors.txt
/tmp/mpt-fixtures/bin/python examples/ethereum_mpt/fixtures/generate_blocks.py \
  > /tmp/mpt-mock-blocks.txt
diff -u examples/ethereum_mpt/fixtures/mock_blocks.txt /tmp/mpt-mock-blocks.txt
```

Fixtures include secure account/storage paths and separate synthetic paths for
deep extensions, inline subtrees, the child-size threshold, and a 65-node path.
The synthetic cases do not claim known address or slot Keccak preimages.

The traversal suite additionally checks exact map/lane schedules across tier
cutoffs, 65-node account and storage paths, inline transitions, maximum nodes,
corrupt metadata and missing pages. The fixed helpers are compared with the
reference for every node-hash length from 0 through 532, including all Keccak
rate boundaries. Version tests cover phase-boundary publication, retained
proofs, duplicate/conflicting deliveries, failed roots and partial loading,
fatal reader recovery, retention, reorgs and fresh restart. Incremental tests
compare every fixture root/proof with the replacement baseline and exercise
stable pages, upload failures, capacity rebuilds and periodic/explicit compaction.
Public policy tests cover fullness/dead-byte triggers, retained closures and
shared storage, pruning without new pages, and failed replacement loading.
Canonical mutation tests cover batched path unions, randomized full-rebuild
comparisons, no-op node sharing, retained-parent immutability, storage-root
sharing/reset/deletion and invalid deltas. Client tests cover fixed frame sizes,
context/request binding, malformed frames,
status/padding consistency, tampered proofs and client JSON conversion.
Checkpoint tests cover strict decoding, corruption, cumulative resource limits,
atomic file replacement, pending-update exclusion, retained-history restore and
restart into fresh maps. CLI tests resume across both update modes and fixture
forks with real ORAM proofs, accept version-1 files and reject unavailable history.
`fixtures/checkpoint_v1.hex` freezes a version-1 single-head checkpoint at
fixture index 4 for compatibility testing; it is not an independent Ethereum oracle.
The optional TLS suite additionally checks certificate/hostname rejection,
fragmented reads, ciphertext tampering/replay, truncation, authenticated shutdown,
socket admission and broken-peer writes. It compares encrypted record widths
across membership, absence and service errors at the same public profile.

## Read benchmark

`ethereum_mpt_benchmark` runs disclosed synthetic queries through real ORAM maps
and emits one JSON object. It checks every warmup and measured response with the
client verifier and compares proof bytes with the canonical reference outside
the measured service interval.

```sh
./build-mpt-examples/ethereum_mpt/ethereum_mpt_benchmark \
  --accounts 256 --storage-entries 64 --q 19 --k 2 \
  --account-top 3 --storage-top 3 --top-backend hierarchical \
  --mode batch --warmup 2 --samples 20

python3 examples/ethereum_mpt/benchmark_sweep.py \
  --binary build-mpt-examples/ethereum_mpt/ethereum_mpt_benchmark \
  --q 1,8,19 --k 0,1,2 --account-top 1,2,3,4 --storage-top 0,3 \
  --top-backend tree,hierarchical --samples 20 --output /tmp/mpt-reads.jsonl
```

The sweep always includes scalar calls and genuine batches with both cutoffs
zero, then tiered batches. Scalar mode splits each public depth round into
one-lane ORAM calls; it retains the same complete lane set, dummy reads, parser
and proof generation. All variants use one caller and zero background workers.
Bulk stays explicitly on `TreeByteMap`; enabled top tiers use the selected
`TreeByteMap` or hierarchical `ByteMap`. The adapter also supports choosing
different engines for the two top tiers in C++.

Repeat `--binary` for executables from separate page-width builds to sweep
768/1024/2048-byte pages. The runner starts a fresh process per configuration,
flushes each complete JSON row, refuses an existing output file, and stops at
the first failure. Use `--dry-run` to inspect the command matrix. No Python
packages are needed.

The dataset contains sequential 64-bit IDs encoded as account addresses and
storage positions, then Keccak-hashed as usual. Odd accounts share one storage
trie and even accounts have empty storage. Queries repeat a fixed pattern of
present and absent accounts, duplicate addresses, and present/absent slots.
This is a synthetic workload, not a measured Ethereum state distribution;
shared storage roots deliberately exercise deduplication.

Each JSON row records public configuration, state root, raw samples, packing
statistics, capacities and these measurements:

| Measurement | Meaning |
|---|---|
| Batch service p50/p95/p99 | Nearest-rank percentiles from request decoding/path hashing through response encoding; every request completes at the batch boundary |
| Requests per service second | Measured request count divided by total service time, excluding setup, client verification and final drain |
| Final drain time | Completion of pending ORAM work after all iterations, checked before emitting a successful result |
| Page-read time by tier | Timed adapter calls, including key preparation, scratch setup and scalar splitting where selected |
| Local traversal time | Traversal minus page-read time; includes parsing/hashing, lane/proof work, allocations and timing overhead |
| Round calls / ORAM calls / page reads | Separate per-tier counts per batch, excluding initialization and warmups |
| Logical page-read bytes | Full page width times logical reads; physical ORAM traffic is unmeasured |
| Packing slack / ORAM arena ratio | Unused real-page bytes separately from arena bytes divided by all packed page values |
| Process peak RSS | Linux high-water mark including public builder, ORAM, scratch and verification allocations |

Queue-fill latency and physical ORAM traffic are explicitly null. There is no
arrival queue, transport or update traffic in this benchmark. Local traversal
time does not isolate parser or hash costs. Verification between iterations
can affect caches; throughput is normalized to service time rather than full
process wall time, and small sample counts do not estimate tail latency well.
The separately reported final drain can include deferred work from warmups;
short runs do not establish sustained throughput. Initial load time includes
public validation and adapter allocation. Destruction
of returned results and frames happens outside service timing. The synthetic snapshot
and all dummy pages are loaded before timing; reads are checked against each
tier's fixed schedule and the configured request horizon includes warmups and
initial writes. Tiny states may round to the same minimum ORAM capacity, so
smoke runs establish harness correctness only.

The update benchmark adds delta sweeps, served-head lag, compaction duty cycle
and public-builder payload accounting. Arrival queues, physical traffic,
isolated parser/hash costs and deployment-specific worker budgets remain
unmeasured. The compiler-output review in DESIGN.md covers the default page
width (plus extraction at 768 and 2048 bytes); repeat it for other widths and
deployment compiler flags before making privacy claims about those builds.

## Read/update benchmark

`ethereum_mpt_update_benchmark` emits one JSON object for a synthetic linear
chain through real ORAM maps, with one caller and zero workers. Each block
prepares an update, serves the configured complete batches against the old
head while the update is pending, then publishes at the next batch boundary.
It compares incremental appends with replacement loading on identical deltas.
The JSON `canonical_builder` field reports `path_copy` for incremental mode and
`full_rebuild` for replacement mode. This comparison therefore includes canonical
construction differences as well as page publication; capacity/periodic rebuilds
in incremental mode still use path-copy construction. There is no warmup; fresh
generations and compaction replacements start cold.

```sh
./build-mpt-examples/ethereum_mpt/ethereum_mpt_update_benchmark \
  --accounts 64 --storage-entries 8 --q 4 --k 1 --blocks 8 \
  --read-batches-per-block 2 --delta-accounts 2 --storage-changes 1 \
  --retained-blocks 2 --page-headroom 32 --compact-after-updates 3 \
  --compact-at-fullness-percent 80 --compact-at-dead-bytes-percent 40 \
  --update-mode incremental

python3 examples/ethereum_mpt/update_benchmark_sweep.py \
  --binary build-mpt-examples/ethereum_mpt/ethereum_mpt_update_benchmark \
  --q 1,4 --k 0,1 --read-batches-per-block 0,2 \
  --delta-accounts 0,1,4 --storage-changes 0,2 --blocks 8 \
  --update-mode incremental,replacement --output /tmp/mpt-updates.jsonl
```

The sweep starts a fresh process for each configuration, flushes JSONL rows,
refuses existing output files and stops on failure. Repeat `--binary` for
different page-width builds; use `--dry-run` to inspect its command matrix.
Tier cutoffs and top backends are configurable; bulk stays tree-backed.
Both public compaction percentages are configurable in the benchmark and sweep;
their defaults are zero. Each sample reports published page counts, capacities
and live/dead record bytes per tier. Final tier summaries also separate live
and dead records from packing slack. Occupancy reporting runs after publication,
outside measured service and lag; policy checks themselves count in preparation.
Zero changed accounts exercises distinct blocks with an unchanged root.
Other deltas rotate through accounts and insert, overwrite or zero-delete slots.
Expected states are mutated separately from the service, but their roots and
proofs use the local canonical builder. Independent `py-trie` coverage belongs
to the committed fixture tests, not these synthetic benchmark roots.

| Measurement | Meaning |
|---|---|
| Update pause | `prepare_ns + publish_ns`; includes fresh loading during preparation or append writes/completion during publication |
| Scheduled service time | Update pauses plus measured old-head read service; throughput and compaction duty cycle use this denominator |
| Scheduled service lag | Per-block preparation, measured reads and publication; observed head is one block ahead until publication |
| Harness arrival-to-publish wall lag | Inclusive wall interval starting just before preparation; includes pending-read framing/verification and builder-accounting traversals |
| Logical update writes | Appended and freshly reloaded pages, excluding initial setup; physical ORAM traffic remains unmeasured |

Every measured response is verified outside read service timing. After each
publication, compulsory probes verify the new and every retained root; these
probes are counted separately and excluded from throughput, lag and compaction
duty cycle. Setup, oracle construction and final drain are also reported
separately; generation completion barriers during updates count toward update
pause. This is a serialized schedule, without an arrival queue or concurrent
ingestion. Probe and verification work can still affect caches and deferred work.
Probes issue real ORAM reads, so `--read-batches-per-block 0` removes the measured
old-head workload but still includes validation traffic between updates.

Builder payload is sampled after setup, preparation and publication. It counts
distinct retained states/nodes once, both current/pending packed-image copies,
upload copies and identity tombstones. It excludes unused capacity, containers,
decoded node fields, other metadata and temporary construction work; the sampled
peak is not allocator usage or a transient peak. Linux process peak RSS includes
ORAMs, oracle snapshots, proof buffers, temporaries and allocator overhead.
Packing slack and overlapping ORAM arenas are reported separately. Small runs
validate the harness; they do not establish sustained ingestion performance.

## Scope and limitations

- The MPT is public; only the queried accounts and slots are protected, from an
  observer of memory addresses and control flow (the library's
  [security boundary](../../DESIGN.md#security-boundary-and-limitations)).
  This is not PIR against a server that can read its own plaintext memory.
- Blocks are mock final-state deltas with independently generated roots; there
  is no transaction execution, consensus or fork-choice validation, and no
  transaction/receipt proofs or bytecode retrieval.
- The service has one serialized caller. Concurrent ingestion, arrival queues,
  combined peak-memory admission and a remote service lifecycle are not
  implemented. The TLS demo runs both endpoints in one process.
- Public-state copies, packing validation and dead-byte scans do whole-image
  work; updates are not delta-proportional end to end.
- The benchmarks use small synthetic workloads. Their output validates the
  harness and exposes cost components; it is not an Ethereum performance claim.
