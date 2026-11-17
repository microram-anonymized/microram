# Rebuild kernel design

Rebuilds route records by secret destinations through public networks.
Byte-sliced permutations move every field together; occupancy masks select
records in registers. Fixed-capacity residual stashes retain records that do
not fit. The [level arena](../levelarena/DESIGN.md) supplies source freshness,
geometry and storage ownership, while the [scheduler](../scheduler/DESIGN.md)
preserves kernel order across execution pieces.

Terms used below. A rebuild's *sources* are its input tables, each with a
public freshness rank; the *carry* is the incoming table a smaller level hands
up to be merged. A *residual* is a record that a routing stage could not
place; it is *shed* into that stage's fixed-capacity *stash*. A *tier* is the
small fixed-capacity residual table published beside each main table and
probed with it. A residual pass's *pool* is the set of stashes and tiers it
recovers from; its *range table* is the pool partitioned by destination range
so that a linear sweep can offer each residual back to its main bucket (the
*second chance*); whatever remains is *drained* (packed) into the output
tier. Digits, fanout, inboxes and the dense prefix are defined in the
[level arena design](../levelarena/DESIGN.md).

## Route decisions once, move every byte the same way

A binary [MergeSplit](cpu_byteslice_mergesplit.hpp) partitions two 64-slot
buckets by one routing bit. Each output keeps the first bucket's applicable
lanes and fills its free slots from the second in slot order. A pair of
128-to-64 permutation indices implements that placement for every live byte
line. Records from the second bucket that cannot fit go to the stage's
[residual stash](cpu_byteslice_residual_stash.hpp).

The [stash-aware quad](cpu_byteslice_mergesplit_stash.hpp) executes two binary
levels over four buckets while each byte line is in registers. It loads and
stores four lines per byte position rather than loading and storing those
lines separately for each level. The [butterfly](cpu_byteslice_butterfly_stash.hpp)
combines quads with one pair pass for an odd depth. Its recursive split keeps
the low half even. Recursive cache grouping does not add register fusion.
Consumed low tag bytes are omitted from subsequent movement according to
[the table layout](../table/DESIGN.md#representation-and-its-cost).

For `m * 2^k` buckets, write `m = r * 2^e` with odd `r`.
[Mixed-radix routing](cpu_byteslice_radix_stash.hpp) routes `k+e` low bits in
`r` power-of-two blocks and then performs one terminal `r`-way split across
corresponding buckets. Supported odd radices are 1, 3, 5 and 7. At `r = 1`
there is no terminal split. This avoids padding the whole main table to the
next power of two, at the cost of a terminal kernel with quadratic work in
`r`.

## Deduplicate at source joins

The [deduplication network](cpu_byteslice_dedup_network.hpp) gives equal keys
the same routing tag. After bits `0..b-1` have been routed, equal keys occupy
corresponding buckets in their respective source blocks. At a source join,
comparison clears the older copy before MergeSplit moves the records. A
source that is already unique needs no comparisons inside its own route.

At level-arena digit `j = r * 2^e`, block 0 contains the carry of `U` buckets,
followed by older spans of `U, 2U, ..., 2^(e-1)U`. These spans double the
prefix, so `e` binary cross-source levels join them without a gather. Other
blocks contain only older data and route independently; the terminal radix
pass compares those blocks against the fresher block 0.

The [key comparison kernels](cpu_byteslice_dedup_masks.hpp) use exact stored-key
equality for widths 1 through 16. Wide keys keep both qwords tied to the same
partner through synchronized rotations. The OR of their XOR differences is
zero exactly when the complete keys agree; an unsigned minimum reduces those
scores to membership. Cross-bucket, retained-source destination, class-marked
offer and earlier-slot self comparisons all use this rule. Dummy lanes are
zeroed in registers and only complete zero keys need explicit repair. Self
comparison admits only earlier partners, keeping the lowest real copy.

On a VP2INTERSECT host, the build option `CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT`
(default ON) replaces this rule at stored width 16 with four 32-bit segment
matches, ANDed. A slot then matches when each segment occurs in some partner,
not necessarily the same one, so two different secret-hashed keys collide with
probability at most `64^4 / 2^128 = 2^-104` per compared slot. The segment
form uses native VP2INTERSECT, which is cheaper than the exact rule's
synchronized-rotation kernels where VP2INTERSECT is implemented in hardware; on
hosts without it the exact rule is used and the option has no effect.

Loads and loop counts depend on public widths, bucket addresses and indices.
There is no match-dependent early exit. Exact stored equality has no false
matches, including for caller-controlled keys; normalization collisions
(distinct user keys that map to one stored key) and cryptographic routing
assumptions are separate concerns. The Lean module
[NativeMatch](../../../lean/RebuildBound/Spec/NativeMatch.lean)
bounds the segment form's false matches; the
[Lean claims](../../../analysis/bound_certification/LEAN_CLAIMS.md) state the
premises under which that bound applies.

## Recover residuals without revealing their homes

A half-full main table reserves two physical slots per logical entry, but
individual destinations can still overflow. Per-stage stashes have public
capacities selected by the [generated capacity table](cpu_byteslice_stash_capacity_table.hpp).
Its Poisson-excess Chernoff model supports at most eight stash buckets per
stage. Applying a model to a rebuild requires the source-distribution and
failure-budget premises for that rebuild; occupancy alone does not establish
independence across stages. The arena also checks final tier capacity and
[DFS geometry](cpu_byteslice_dfs_residual.hpp) before accepting a configuration.
See the [capacity analysis](../../../analysis/bound_certification/README.md)
for its stated scope and assumptions.

Residual recovery first deduplicates sources by public freshness rank.
Equal-rank sources must already be disjoint. Sources retain their records
while a private copy is gathered and retagged for the destination table.
The [range plan](cpu_byteslice_residual_range.hpp) either copies the pool
directly for a small main table or partitions it into public coarse ranges
using DFS. An empty pool still has one padding bucket, whose occupancy is
cleared even when the scratch is reused.

The [second-chance sweep](cpu_byteslice_second_chance.hpp) visits main buckets
at public indices. For each main bucket it visits every page of the associated
range in order, comparing destination bits in registers. The deduplication
rule says which copy wins: main, residual, or a class bit selecting between
the two. Every candidate and main key must be unique within its own source,
and equal keys must agree on their destination.

A class-marked offer allocates stale candidates only into slots free before
any duplicate clearing. Fresher candidates then use the remaining free slots
and the slots freed by their duplicate clears. Each clear has a corresponding
fresh candidate, so bucket occupancy never decreases. This keeps a stale
copy of a record shed by the final routing stage in residual storage, where
it can still be deduplicated against that fresher shed. Pages are processed
in order; earlier pages are not revisited.

Offers can run immediately after the final routing operation for each
bucket. [Chained offers](cpu_byteslice_second_chance.hpp) plan several pages
against updated scratch key lines and apply their permutations during one
payload pass. The radix and fixed-merge kernels also fold offers into their
own output loops. The sequence of key comparisons and allocations remains
the same as the corresponding per-bucket offers.

At the top fixed merge, `ResolveTopDestination` resolves every candidate
page before any allocation for that destination. It clears older copies
shadowed by the incoming main or tier and removes winning tombstones. The
subsequent merge and offers operate on distinct live winners. The engine
must guarantee that the merge consumes every older source before tombstones
can be forgotten.

Late sheds from a fused routing stage belong to a drain-only source prefix:
they are produced after gathering and cannot be part of the swept copy.
After routing, pool deduplication compares those sheds with the original
sources, including candidates already absorbed into main. Range leftovers
are packed into the destination tier. Where ranks require it, the packed
leftovers are deduplicated against the drain-only sheds before those sheds
are appended. Every drain checks capacity; failure prevents publication.
Only the pass's owned source masks are reset.

## Public-capacity DFS distribution

A DFS pass with a pool of `P` physical slots, `2^D` coarse ranges and `S`
slots per range uses node capacity `C(h) = min(P, S * 2^h)` at height `h`.
If every leaf fits, every ancestor fits, so one coarse-range capacity event
covers all internal nodes. Capacities, selected tag-bit positions, traversal
and buffer addresses depend only on public geometry.

The [workspace](cpu_byteslice_dfs_residual.hpp) gathers a private copy of the
sources. It compacts directly from that pool into each node at the first
height whose capacity is below `P`, avoiding intermediate full-capacity
splits. Below that height, a unit stably compacts both children: the left
into its workspace, the right into the parent's buffer, which preserves the
pending right sibling while the left subtree runs. Leaf children write
directly into stacked pages at `page * 2^D + leaf`. Public padding ranges
outside a mixed-radix main table are skipped and their masks are cleared.

Compaction uses a fixed network over whole buckets. Per-bucket occupancy
prefixes determine register compressions, rotations and blend masks.
Networks of up to eight buckets execute one byte line at a time in registers;
larger networks execute their tiles before the remaining cross-bucket
passes. Every record byte follows the same permutation, including class and
tombstone bits. Selected records retain input order. Stable partitioning
preserves supplied freshness order; it does not create or validate it.

`Configure` builds a public list of units without growing storage. `Run`
accepts only the next contiguous interval of units, allowing the scheduler
to stop between units and resume on another thread. A direct compaction or
a split's child compactions are indivisible. Capacity failure returns false
and prohibits resuming that pass; no partial result may be published. The
gathered pool and original sources remain available independently of the
leaf masks that offers clear.

Storage consists of the gathered pool, a pool-sized direct-child buffer,
one left workspace per lower height, masks, selection arrays, per-bucket
prefix counts, buffer descriptors and the unit list. `Planned` predicts
requested backing bytes and `Allocated` counts the corresponding vector
capacities. Aligned-allocation rounding is applied by the caller's byte bill;
workspace objects, allocator bookkeeping and consumer storage are separate.
[Distributor tests](../../../tests/oram/cpu_byteslice_dfs_residual_test.cpp)
compare ordered full records with a scalar filter across public geometry,
capacity boundaries, dirty reuse and execution-piece widths.

## Initialize directly into the final table

[Direct initialization](cpu_byteslice_initialization.hpp) scatters a public
record count by input ordinal into the arena's final largest-level region,
at its normal initial load. It tags records under one fresh nonce and runs
the existing routing and residual-recovery kernels. A partial input still
processes the full public table geometry. The iterator may reuse storage for
one record, because scattering consumes each record before advancing it.

The arena supports the distinct-key policy: stored keys must not repeat.
First-wins and last-wins enum values are rejected. The initializer does not
implement a general duplicate-resolution policy through these rebuild kernels.
The [tree map](../tree/DESIGN.md) has no bulk initializer and is filled by
ordinary insertions.

All loop extents, capacities and freshness ranks are public. Secret masks
may control register selection but cannot suppress normal observable work.
Checked overflow is a declared failure path. Publication, source pinning and
synchronization remain engine responsibilities; see the
[system security model](../../../DESIGN.md).
