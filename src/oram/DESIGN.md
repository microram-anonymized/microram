# Composing the ORAM engines

The hierarchical engines turn map operations into a scan of recent records and
a sequence of hashed probes, followed by one insertion into a small online
stash. Rebuilds periodically combine those records into larger tables. The
central design problem is to preserve freshness and hide lookup outcomes while
the physical representation changes.

## Components and reading order

| Folder | Role |
|---|---|
| [table](table/DESIGN.md) | Byte-sliced buckets, stored keys, routing tags, metadata, and the oblivious probe and batch-matching kernels. |
| [rebuild](rebuild/DESIGN.md) | MergeSplit routing networks, deduplication at source joins, residual (overflow) recovery, and direct initialization. |
| [scheduler](scheduler/DESIGN.md) | Ordered rebuild task plans with resumable cursors, lane division, and residual-pass validation. |
| [levelarena](levelarena/DESIGN.md) | The hierarchical engine: per-level storage, carries, publication and reader retirement, owner threads, value workers, and the certified capacity report. |
| [tree](tree/DESIGN.md) | The tree ORAM for large values over a hierarchical position map, with read-path eviction and payload workers. |
| [support](support/DESIGN.md) | Benchmark measurement utilities; no engine depends on them. |

Read this page first, then `table`, `rebuild`, `scheduler` and `levelarena`
in that order for the hierarchy; `tree` builds on the hierarchy's public
`ByteMap` and can be read after `table`. Terms used throughout: a *level* is
one size class of hashed tables; a *carry* is the merged table one level
hands to the next; the *online stash* and the *dense prefix* are the small
regions every access scans in full; a *residual* is a record that overflowed
its main bucket during a rebuild and sits in a level's fixed-width *tier*;
an *owner* is a background thread that runs a group of levels' rebuilds, and
a *helper* widens one group's routing lanes. The
[arena design](levelarena/DESIGN.md) defines these precisely.

## A common representation, two rebuild lifetimes

The [table layer](table/DESIGN.md) defines byte-sliced buckets, routing
identities, metadata, and probes. A probe searches tables in freshness order and
returns the newest matching record, including an erased record called a
*tombstone*. Hashed tables receive either a real or a dummy bucket probe.
Dense tables are scanned in full. The scan's public shape does not stop when a
match is found.

The security invariant of the cascade is that a key is probed for real at most
once per *nonce family* (the public coordinate that, with the instance's secret
AES key, fixes a hashed table's routing) over that family's lifetime; every
other hashed-table probe is a dummy. Three mechanisms establish it. (1) Every
access inserts the key into the online stash afterwards, whatever it found: a
read re-inserts the value, and a miss or erase inserts a tombstone. A later
access to the same key therefore finds a fresher copy above every table already
probed for real and probes dummies below it. (2) Publication admits at most one
live member of a family to the probe plan (`PlanHasAtMostOneMemberPerFamily`),
so a carry and the merge that shares its nonce are never both probeable. (3)
A family is named by the publication its bytes end at, a unique coordinate
([CanonicalFamily](levelarena/cpu_byteslice_level_arena_family.hpp)), so every
rebuild output is hashed under a family not used before and its records become
probeable again only under a family in which they have not been probed. Dummy targets
are PRF outputs of a never-reused counter in an identity domain separate from
real tags, so real and dummy addresses are identically distributed. Builds with
`MICRORAM_BYTESLICE_PROBE_AUDIT` check (family, key) uniqueness at run time.

The [arena engine](levelarena/DESIGN.md) keeps published table contents immutable
while background rebuilds read them. New accesses create fresher records in the
online stash, so several physical versions of one key may coexist. Publication
replaces a set of source tables with completed outputs atomically, and storage
is reused only after readers of the old tables have finished. Consequently,
deduplication and memory ownership are parts of the algorithm's correctness.

The arena engine also has a synchronous storage mode, behind `ByteMap<false>`.
It runs the same jobs at the same points, so its records follow the same
lifecycle, but the request that completes a prefix runs every merge before it
continues, and each level's table is rebuilt in place in one region.

## Rebuilds preserve both destination and freshness

The [rebuild layer](rebuild/DESIGN.md) maps entries into bucket destinations
through fixed routing networks. Its MergeSplit primitive constructs a routing
permutation once and applies it to all byte lines. Overflow records enter a
bounded residual stash and receive a second opportunity to enter their intended
main bucket. Freshness ordering must survive both paths: a newer tombstone
must suppress an older value even if the two records temporarily occupy
different main and residual structures.

The [scheduler layer](scheduler/DESIGN.md) expresses these transformations as
ordered tasks with explicit scratch and residual-pass contracts. It supplies
execution plans rather than deciding which published table an access can see.
Arena owners run each phase's task list in pieces and stop between two pieces
when a level with a nearer deadline becomes runnable, earliest deadline first;
the inline executor runs one bounded share of that work per flush. This bounds
how long a runnable level waits behind another level's phase, not the time a
request may wait for a worker or a reusable buffer, which still depends on the
rebuild keeping up and on the host scheduling its threads.

## Batch requests without changing key semantics

Batching exposes independent candidate addresses and reuses dense bucket loads
across requests. Requests with equal keys require ordered forwarding: only the
first occurrence probes the old state for real, and later occurrences obtain
the state left by the preceding equal-key request. Each request still advances
the logical access count and online-stash insertion schedule. The
[table design](table/DESIGN.md) owns the matching and forwarding mechanisms;
the arena design owns the snapshot lifetime and worker coordination.

## Keep large values outside hierarchical rebuilds

The [tree engine](tree/DESIGN.md) stores large values on random root-to-leaf
paths and stores their locations in a small position map. The production
position map itself uses the hierarchical byte map. Each access reads one
path and evicts along that same path: the eviction computes a placement plan
from compact metadata, then reuses it across payload byte columns. Thus the
hierarchy rebuilds only the small position records; the full value is never
rebuilt through the levels.

[Measurement support](support/DESIGN.md) is separate from these protocols. It
distinguishes the work charged to an operation from the delay imposed on later
requests, which is necessary when evaluating concurrent rebuilding or batching.

The [system design](../../DESIGN.md) defines the shared security boundary.
The [README](README.md) defines internal include and namespace conventions.
Maintain these explanations by
[editing them directly](../../DESIGN.md#documentation-maintenance).
