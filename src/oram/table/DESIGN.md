# Byte-sliced table design

The table layer gives routing and probing the same representation. A bucket
contains 64 slots, and byte position `b` of every slot occupies one contiguous
64-byte line. A routing decision therefore becomes a register permutation
reused across all byte positions. An online lookup compares key lines and
extracts value bytes with register indices, without addressing memory by a
secret slot number. Hierarchy geometry and publication belong to the engines;
see the [ORAM design](../DESIGN.md).

Terms used below: a **dense** table is scanned in full on every access (the
online stash, where each access inserts one entry, and frozen stashes awaiting
a rebuild); a **hashed** table is probed at one bucket chosen by the key's
routing tag. A **tier** (or residual stash) holds a rebuilt table's
**residuals**, entries that overflowed their routed main bucket. A **carry**
is the full table a level hands to the level above, and a **nonce family** is
the set of tables published under one routing nonce. The
[arena design](../levelarena/DESIGN.md) defines the hierarchy-specific terms.

## Representation and its cost

[Layout](cpu_byteslice_layout.hpp) stores key, value, and routing-tag lines,
plus a separate 64-bit occupancy mask. Engine metadata occupies one byte of
the value field. If the stored key has `k` bytes, the application value has
`v` bytes, and routing uses `t` tag bytes, an engine bucket's backing data is
`64(k + v + 1 + t)` bytes, plus 8 bytes for occupancy. This excludes allocation
rounding and engine descriptors. The byte-sliced representation itself adds no
per-field padding. At the hashed-table load of one half, 64 physical slots
represent a capacity of 32 entries; residual storage is additional.

Keeping the actual width of keys up to eight bytes removes unnecessary key
lines from both storage and probes. Relative to storing every narrow key in
eight bytes, a `k`-byte key saves exactly `64(8-k)` bytes per bucket. Four-byte
keys thus save 256 bytes per bucket, or 8 bytes per logical entry at load one
half. These are byte counts, not execution-time predictions.

[Stored-key encoding](cpu_byteslice_stored_key.hpp) stores user keys up to
15 bytes verbatim, so a key costs exactly its own width, and hashes keys of 16
bytes or more into 16 bytes under a secret, domain-separated key. Equality for
wide user keys therefore depends on the stored-hash collision assumption only
above 16 user bytes. For a fixed width of 16 bytes, one AES permutation is
injective; see the [cryptographic argument](../../crypto/DESIGN.md).
Compressing a user key of width `u > 16` saves `64(u-16)` bytes per bucket
relative to storing it verbatim. Routing tags are recomputed under the
engine's routing identity and are not persistent key identity. The arena
engine deliberately shares a nonce family between a carry and its consuming
merge. Its [family protocol](../levelarena/DESIGN.md#carries-and-preparation)
defines when a fresh identity is required.

Routing uses fixed two-block CBC-MAC over a labeled packed identity and the
complete stored key. The scalar path and both SIMD paths implement the same
message. Bulk re-tagging shares the first CBC state across each 32-key group.
Online scalar and batch probes assemble four qwords per candidate, padding to
four candidates, so their public templates and message scratch hold two AES
blocks per candidate. These buffers participate in the engine's byte bill.
The address pass computes both real and dummy candidates before secret
selection. There is no per-family key schedule or persistent prefix cache. The
[cryptographic design](../../crypto/DESIGN.md) owns the encoding and reduction.

The least significant routing-tag bytes occupy the last lines. Once routing
has consumed bits `0..l`, the bucket position encodes those bits, so
`RoutedLines(l)` omits `floor((l+1)/8)` tag lines from subsequent movement.
The [routing map](cpu_byteslice_routing_map.hpp) also packs a mixed-radix digit
into spare high bits when the geometry permits. Saving one tag byte saves
64 bytes per bucket. These savings apply to rebuild storage or traffic;
probes already omit all tag lines.

## Probing without revealing the matching slot

A dense table is scanned in full. A hashed table contributes one bucket per
request, selected from the key's pseudorandom routing tag until a fresher copy
has been found, then from an independent dummy target. The dummy target is
the routing PRF evaluated on a fresh counter in a dummy identity domain that is
separate from real routing messages. Counters are reserved per lane and plan
position before any address is computed and are never reused
(`ReserveDummyCounters` in the
[level-arena engine](../levelarena/cpu_byteslice_level_arena_engine.hpp)), so a
dummy address is pseudorandom and independent of every real tag and of every
other dummy. Because a key is real-probed at most once per nonce family
(the invariant the [probe plan](cpu_byteslice_probe_plan.hpp) audits), a real
and a dummy probe of one table are therefore indistinguishable to the
observer. The
[probe-address pass](cpu_byteslice_probe_addresses.hpp) resolves addresses
before the [probe kernels](cpu_byteslice_probe.hpp) extract values. It computes
both real and dummy candidate addresses for every hashed table unconditionally,
batching their AES evaluations and index arithmetic. The dependent cascade
then selects between two prepared pointers after each match. This moves AES
and index mapping off the match-to-next-load chain; it does not eliminate
those computations or probe both candidates. Publication-time geometry
precomputes table bases and map shapes shared by all accesses. Both paths
load complete required byte lines; occupancy and match masks affect register
selection, not a secret-indexed memory load. Correctness relies on the
engine's freshness order and on removing or suppressing stale copies before
they can become observable answers.

The generic byte-wise matcher uses register-only `obliCmpEqMask8`
comparisons before intersecting their results with occupancy. The XOR/OR
matcher similarly uses `obliTestNMask8` after its XOR/OR reduction. These
compiler boundaries prevent a key-line load from folding into a comparison
masked by an earlier mismatch or an empty occupancy word. Protected-page
regression tests check that empty occupancy and mismatching keys still access every required key line.

The [probe plan](cpu_byteslice_probe_plan.hpp) orders tables by window end
descending and tier ascending. Its published suffix is immutable; the
request thread refreshes its reserved dense prefix from the stash ring
inside the reader epoch. Validation checks every interval
and tier group, then tracks active containing windows with a bounded stack
to detect crossings between nonadjacent windows. Each window is pushed and
popped once, giving linear work without allocation for supported engine
geometries; deeper hand-built plans use an exhaustive fallback. The engines
own the lifetime of that plan and its table views. Sharing the plan format
does not make a view safe to overwrite while another thread probes it.

[Batch probing](cpu_byteslice_batch_probe.hpp) amortizes address and layout
work across requests while serving independent requests in lane order. All
inputs must be available before execution and cannot depend on another lane's
outputs, so this is not equivalence to an arbitrary sequential program. Conflict
sets identify repeated requests, and a forwarding chain carries earlier
results and writes to later lanes. The
[parallel-batch metadata](cpu_byteslice_parallel_batch.hpp) extends those
relations across tiles. A tile boundary cannot reset deduplication or
freshness. All eligible lanes and public buckets still take part in the
memory-access schedule.

## Share extraction and dense scans across lanes

The [batch result layout](cpu_byteslice_batch_layout.hpp) accumulates one
64-byte line per value byte, with request lane `j` in column `j`. A dense
bucket supplies all lanes through one byte permutation per value line.
Hashed extraction places its result directly into the requesting lane's
column, so dense and hashed answers need no intermediate row conversion.
For `n <= 64` lanes and `v` value bytes, the row reference's merge performs
`nv` scalar byte selections. The sliced path removes this conversion phase
and merges by value line. Reading or returning `nv` output bytes is still
necessary; the representation does not remove the output-size lower bound.

The arena's [bucket-owned scan](../levelarena/cpu_byteslice_level_arena_batch.hpp)
partitions the initial dense region into contiguous bucket ranges and gives
each worker all public query groups of up to 64 lanes. Each bucket is visited
once per global query group, rather than once per balanced request-owner
tile. With `D` initial dense buckets and `n` requests, that is
`D ceil(n/64)` bucket visits. If request ownership would create `p` smaller
tiles, independent tile scans instead require `Dp` visits. There is no visit
count reduction when both partitions already have the same number of groups.
Later dense tiers remain part of the ordinary cascade.

Each worker writes private partial results. Scanning buckets oldest to newest
and merging contiguous worker ranges in the same order preserves freshness
without per-answer rank storage. Whole-job conflict metadata and forwarding
still span all query groups. Bucket ownership changes where shared scans run;
it does not permit skipping a bucket because every current query has hit.

## Scalar value columns

[value-plane primitives](cpu_byteslice_value_plane.hpp) extract a public
`[begin,end)` column range without occupancy or key reads. The permutation
index is a secret slot used only in vector registers. `ValueAccumulator<N>`
loads every column unconditionally, then applies the take mask with the core's
register-only `obliMaskMov8`; this prevents a compiler from suppressing a
nonwinner's load. Pairs of accumulated columns are permuted into two output
bytes at the end; odd widths use one full-line permutation. Explicit unrolling
before scalar replacement lets GCC retain accumulators in registers. Empty
ranges load and write nothing. Meta extraction similarly loads its entire line
even on a miss. Range writes scatter owned
bytes to a public stash slot. These primitives support the arena's synchronous
split executor and persistent workers without changing bucket layout.

## Dense direct-slot matching

For sufficiently large public batches and dense scans,
[dense matching](cpu_byteslice_dense_match.hpp) derives a slot directly from
row and column membership. Exact four- and eight-byte fields identify the
unique live key's row and column. This requires within-bucket uniqueness;
the generic byte-sliced matcher remains the duplicate-preserving fallback.
Direct recovery avoids constructing a full match mask only to convert it
back into an extraction index. Query preparation uses 2 KiB of transient
scratch and introduces no persistent per-bucket index. The arena's batch path
selects this matcher only where VP2INTERSECT is compiled in
(`kNativeDenseCrossMatch`); without it, as on Granite Rapids, dense scans use
the generic byte-sliced matcher.

The 16-byte path compares both 64-bit halves against the same partner in each
row or column. Synchronized rotations and an unsigned minimum of the OR of
the two XOR differences give exact subset membership. Complete zero-key repair
excludes zeroed dummy lanes. Thus a match in a different partner's half cannot
displace a true hit. The selected slot is still verified against all 128 bits
and occupancy using fixed-address loads. Within-bucket full-key uniqueness
remains required for direct row/column recovery; no random-key assumption is
needed for equality. Stored-hash collisions and cryptographic routing errors
remain separate. Under the build option `CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT`
(default ON, VP2INTERSECT hosts only), the two halves instead match with
VP2INTERSECTQ independently and are ANDed, which is faster on a host with
native VP2INTERSECT. A false candidate built from two different partners'
halves can then displace a true hit; final verification still prevents false
acceptance, so the effect is a lookup false negative. That event has
negligible probability for secret-keyed 16-byte stored hashes and is charged
in the certified bounds; see
[segment configuration](../../../analysis/bound_certification/ERROR_ACCOUNTING.md#segment-configuration).

These mechanisms assume the repository's
[observation and security model](../../../DESIGN.md); secret-dependent audit
checks are diagnostic code, not production oblivious execution.

Maintain this document by editing the relevant explanation directly, following
[documentation maintenance](../../../DESIGN.md#documentation-maintenance).
