# Byte-sliced oblivious maps

This library implements fixed-capacity maps whose memory-access patterns are
intended to hide the requested keys and lookup outcomes. Its main construction
combines a byte-sliced hierarchical ORAM with fixed storage owned by each
level. A second construction keeps large values in a tree and uses the
hierarchy as a position map. The design concentrates on reducing data movement
and storage while preserving the routing, freshness, and lifetime invariants
that make those transformations valid.

This document explains the system-level choices. The
[source design index](src/DESIGN.md) and component documents below give the
algorithms and derivations. [README.md](README.md) covers the public API,
configuration, building, and benchmarks. Project terms (level, prefix,
carry, tier, residual, owner, helper) are defined in the
[ORAM overview](src/oram/DESIGN.md#components-and-reading-order) and in the
term lists that open the [table](src/oram/table/DESIGN.md),
[rebuild](src/oram/rebuild/DESIGN.md) and [arena](src/oram/levelarena/DESIGN.md)
designs. Two terms recur here: an *inbox* is a fixed buffer of a receiving
level into which the level below builds its carry, and a *nonce family* is
the set of tables published under one routing nonce, at most one of which is
live at a time.

## Design contributions

**Routing decisions are shared across all bytes of a record.** Hierarchical
buckets contain 64 slots in byte-sliced form: a line holds the same byte
position from every slot. A routing operation constructs permutation indices
from metadata once, then applies them to every key, value, and required tag
line. This separates the cost of deciding where a record moves from the cost
of moving its bytes. Register fusion reuses loaded lines across consecutive
routing stages. The [table](src/oram/table/DESIGN.md) and
[rebuild](src/oram/rebuild/DESIGN.md) designs derive the resulting byte and
instruction counts.

**A carry is built where its next consumer will use it.** Each hierarchical
level owns fixed main regions and dedicated residual tiers. The incremental
engine packs tier payload in one separate pool while preserving unified slot
lifetimes and the main arenas' standalone spacing. A producer leases an inbox in the receiving level
and builds its full carry directly there. The receiver can adopt the table
without relocating it. Alternating partial tables between local banks and
leased inboxes also removes private intermediate banks. These choices turn
storage accounting into an enumeration of fixed slots and eliminate specific
copies; they do not eliminate the routing work itself. The
[arena design](src/oram/levelarena/DESIGN.md) derives the exact allocation for
uniform and mixed fanouts.

**Residual recovery makes denser main tables usable.** Routing can temporarily
concentrate more entries in a bucket than it can hold. Fixed-capacity residual
stashes retain those entries, and a public sweep gives them another opportunity
to enter their intended main buckets. Freshness-aware deduplication ensures
that an overflowed old value cannot supersede a newer value or deletion
([why rebuilds preserve freshness](src/oram/DESIGN.md#rebuilds-preserve-both-destination-and-freshness)).
This permits the main-table design to target load one half. Main-table space,
residual space, and failure assumptions are accounted for separately in the
[rebuild design](src/oram/rebuild/DESIGN.md).

**Batching reuses scans and exposes independent memory work.** Candidate
addresses are prepared before the dependent probe cascade. Dense scans reuse
loaded key and value lines across requests, and equal-key requests forward
state in request order. Parallel workers operate under one requester snapshot.
Optional scalar value workers partition fixed user-value columns beneath the
same winner/tombstone cascade. The requester retains metadata and a public tail,
joins every read before releasing its epoch, and drains owned pending insertion
bytes before publishing or reusing storage. The default count is zero; the
[arena design](src/oram/levelarena/DESIGN.md) specifies the ownership protocol.
Batching preserves the map's ordered key effects but still pays a probe and
insertion schedule for every request. The
[table design](src/oram/table/DESIGN.md) explains the matching, accumulation,
and forwarding algorithms.

**Large values reuse a metadata-only eviction plan.** The tree construction
computes one placement plan from identifiers and leaf positions, then applies
it across all payload byte columns. Each access reads one path, evicts along
that same path, and writes it back. Payload workers own disjoint columns and
reuse that plan. The hierarchy continues to rebuild small position records;
large values move only along accessed paths. The
[tree design](src/oram/tree/DESIGN.md) explains this separation and the tradeoff
between tree geometry, stash width, storage, and path traffic.

These are implementation contributions and their causal cost arguments.
They are not claims of priority over the literature or universal throughput
improvements. Instruction counts and logical byte traffic describe work for
a stated configuration; cache behavior, core count, and scheduling determine
how that work translates into elapsed time.

## How an access composes with rebuilding

The hierarchical map buffers recent accesses in a dense online stash and
organizes older records into geometrically growing hashed tables. A lookup
scans the dense region and probes published tables in freshness order. After
finding the newest version, later hashed tables receive pseudorandom dummy
probes. Every operation advances the insertion schedule, so rebuild demand
depends on the public request count rather than on whether a lookup succeeds.

In the arena engine, published tables stay immutable while a rebuild reads
them. Accesses create newer versions instead of removing the older ones.
A completed rebuild atomically replaces its source tables in the probe plan,
and reader retirement controls when those sources may be overwritten. A
miss creates a tombstone so repeated absent-key accesses do not repeatedly
probe the same older routing identity. Deletion uses the same freshness
mechanism. The [arena design](src/oram/levelarena/DESIGN.md) owns the lifetime,
nonce-family, tombstone, and capacity arguments.

The arena engine's synchronous storage mode (`ByteMap<false>`) runs the same
geometry planner, merge jobs, and residual routing, so it shares the same
conditional capacity-failure analysis and online path, tombstones on misses
included. The difference is who pays: the access that completes a dense
prefix runs every merge it triggers. Because no reader sees a table while it
is rebuilt, each level's table grows in place in one region, which takes
about half the arena's main storage. The
[mode's header](src/oram/levelarena/cpu_byteslice_level_arena_synchronous.hpp)
derives the layout and lists what differs from the arena.

Concurrency changes when rebuilding is paid. Owner threads may prepare a
merge before its carry arrives, but finite buffers eventually impose
backpressure if owners or readers lag. The implementation supports one
requester per map instance; batch participants share that requester's reader
interval. Neither concurrent execution nor the subtask representation implies
a worst-case wall-clock bound. The
[scheduler design](src/oram/scheduler/DESIGN.md) distinguishes kernel plans
from engine scheduling, and the
[measurement design](src/oram/support/DESIGN.md) separates service from queueing.

## Security boundary and limitations

The intended observer sees memory addresses and control flow, including
accessed buckets or tree paths. Configuration, key and value widths, operation
count, the operation kind, batch dimensions and descriptors, and scheduling
are public. The operation kind is visible because a hierarchical blind write
(`write`, `insert_or_assign`, or a `BatchOp::kWrite` lane without outputs)
skips the probe cascade, whereas `find`, `contains`, `exchange`, `erase` and
the callback forms probe every published table. Applications that must hide
whether a request is a write should issue `exchange` or
`BatchOp::kReadThenWrite`. Secret internal contents
and per-instance cryptographic keys must remain protected. Hashed addresses
and assigned leaves depend on secret state; the goal is indistinguishability
of observable traces under the stated assumptions, not literal equality of
addresses for every logical request sequence.

The construction relies on unpredictable secret AES keys, disciplined routing
identities, bounded public work schedules, and compiled primitives that keep
secret selection in registers. The [cryptographic design](src/crypto/DESIGN.md)
explains tag and stored-key assumptions. The [core design](src/core/DESIGN.md)
explains why source-level branchlessness alone does not establish the memory
access contract. Diagnostic audits that branch on secret state are outside
production oblivious execution.

The implementation has material limits that must accompany paper claims:

- Buckets are not encrypted or authenticated at rest. An observer who reads
  their contents is outside the access-pattern protection described here.
- The hierarchy targets capacity failure at most `2^-64` over `2^32`
  requests. The [capacity analysis](analysis/bound_certification/README.md)
  composes routing, residual, initialization and output terms for covered
  configurations. Its bounds depend on undischarged reference-history,
  component and inventory premises; the unconditional bound remains one.
  `certification()` reports coverage and the conditional bound for an exact
  geometry and request horizon. This is not an end-to-end security certificate:
  wide-key hashing and matching assumptions, scheduler liveness, and memory
  safety also require their own arguments.
- The tree's stash width rests on simulated and extrapolated stash tails for
  the default rule's geometries at load one half (the procedure is in the
  [tree design](src/oram/tree/DESIGN.md#stash-size)), not on a proved lifetime
  bound. Tree composition also inherits the chosen position map's assumptions
  and limits.
- Overflow is observable and treated as failure. Automatic retry with a fresh
  routing identity is not implemented. Source invariants and correctness tests
  do not establish resistance to every speculative or physical side channel.

## Where each argument lives

| Topic | Authoritative document |
|---|---|
| Public API, configuration and threading contract | [README.md](README.md), [include/cpu_byteslice_oram/CONFIGURATION.md](include/cpu_byteslice_oram/CONFIGURATION.md) |
| Source index, reading order and glossary | [src/DESIGN.md](src/DESIGN.md), [src/oram/DESIGN.md](src/oram/DESIGN.md) |
| Register-only secret selection | [src/core/DESIGN.md](src/core/DESIGN.md) |
| Routing tags, stored keys and their reductions | [src/crypto/DESIGN.md](src/crypto/DESIGN.md) |
| Byte-sliced representation, probing, batching | [src/oram/table/DESIGN.md](src/oram/table/DESIGN.md) |
| Routing networks, deduplication, residual recovery | [src/oram/rebuild/DESIGN.md](src/oram/rebuild/DESIGN.md) |
| Rebuild phase plans and resumption | [src/oram/scheduler/DESIGN.md](src/oram/scheduler/DESIGN.md) |
| Level-arena geometry, carries, publication, budgets | [src/oram/levelarena/DESIGN.md](src/oram/levelarena/DESIGN.md) |
| Tree ORAM eviction, stash size, payload workers | [src/oram/tree/DESIGN.md](src/oram/tree/DESIGN.md) |
| Timing semantics of the benchmarks | [src/oram/support/DESIGN.md](src/oram/support/DESIGN.md) |
| Capacity-failure certification and proofs | [analysis/bound_certification/README.md](analysis/bound_certification/README.md) |
| Constant-time instruction evidence | [tests/timing/README.md](tests/timing/README.md) |

## Documentation maintenance

Each directory under `src/`, including recursively nested directories, keeps a
`DESIGN.md` explaining its current mechanisms, motivation, correctness and
security assumptions, and analytical costs, and a `README.md` that is the
engineering guide to its entry points, editing constraints and validation
tests. Each derivation lives in one authoritative component document; other
documents link to it rather than repeating it. Root design material stays at
the system level.

Documents describe the current implementation. They explain the problem and
mechanism before the saving, define units and assumptions beside formulas,
keep claims traceable to code or a stated derivation, and distinguish
eliminated work from work deferred or executed concurrently. Runtime
measurements are not recorded in the documents; they are regenerated by the
benchmark harness ([benchmarks/campaigns/README.md](benchmarks/campaigns/README.md)).
