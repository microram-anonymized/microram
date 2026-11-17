# Tree ORAM design

The tree stores large values while a hierarchical map stores their positions.
This separation keeps payload bytes out of the hierarchy's rebuilds: a value
moves only when its tree path is accessed. The position map still pays the
hierarchy's access and rebuild costs, but its value is only a leaf position
and, when needed, an identifier. The [ORAM overview](../DESIGN.md) places this
construction alongside the hierarchical engines. This document explains the
implementation; the [README](README.md) covers editing and validation.

The tree is Path ORAM [Stefanov et al., "Path ORAM: An Extremely Simple
Oblivious RAM Protocol", CCS 2013] over a binary tree of four-slot buckets (`Z = 4`) at a
load of one half. Every access makes one pass over one path: it reads the
path and the stash, takes the requested entry out, evicts the other entries
along the same path, and writes the path back. The stash is `A` AVX-512
registers of 64 lanes, where a *lane* is one entry's slot in a register.
The top `fold` levels of the tree are not stored; their entries live in the
stash. [CpuReadPathOram](cpu_tree_read_path_oram.hpp) is the engine.
Throughout, `N` is the capacity, `L` the number of leaf bits, `P` the number
of stored buckets on a path, `V` the value width and `E = 16 + V` the entry
width in bytes.

## Remapping makes the path independent of the key

A live entry has an assigned leaf and resides either on that leaf's path or in
the stash. An access obtains the old leaf from the position map, reads that
path together with the stash, and gives the entry a fresh leaf. The entry then
lands in the stash, and later accesses whose paths share a bucket with its
new path move it down. Eviction places an entry only in a bucket that lies on
both the read path and the entry's own path, so the old path is always
sufficient to find it.

[CpuTreeMap](cpu_tree_map.hpp) combines one position-map operation with one
tree access for each lookup, insertion, exchange, or deletion. A read also
updates the position map because leaving a key on its old leaf would make
repeated reads recognizable. An exchange extracts the previous value and
writes the new one in the same pass. A deletion removes the position-map entry
and lands nothing, so the found entry leaves the working set.

The map draws two leaves on every operation from a per-instance AES PRF over
a counter: a new assignment and a path for a miss. A constant-time selection
chooses the old assignment on a hit and the random path on a miss. Making both
draws unconditionally keeps the PRF counter's use independent of membership.
The leaf mask is unbiased because the number of leaves is a power of two.
The PRF is the two-block AES CBC function of
[src/crypto](../../crypto/DESIGN.md#route-a-complete-key-under-an-explicit-identity)
under the tree's own key, expanded from a fresh `SecretKeySeed::Random()`
that is independent of the position map's seed (`CpuTreeMap::FreshPosition`).
The message is a fixed public identity followed by a 64-bit counter that
increments on every draw, so no message repeats within an instance. The leaf
is the tag's low `L` bits.

[HierarchicalPositionMap](cpu_tree_position_map.hpp) implements the lookup and
remapping with one `ByteMap::exchange`, or `erase` for deletion. Its
`Deamortize` template parameter chooses the arena engine's deamortized or
synchronous storage mode. If a key fits in eight bytes, its zero-extended
bytes can serve as the entry identifier (`uid_from_key`). The position map
then stores only `max(1, ceil(L / 8))` bytes. Wider keys use a fresh counter
identifier and add eight bytes to that value. The counter must not wrap
during the instance's lifetime. `UnorderedPositionMap` is a non-oblivious
test and benchmark backend; composing it with an oblivious tree does not make
the resulting map oblivious.

`access_batch` batches position-map remapping and then executes tree accesses
in request order. Repeated keys observe earlier requests in the batch.
Request inputs must be independent of other requests' outputs; an exchange
may overlap its own input and output, which is handled by an input copy.
The tree reports one batch participant because its shared stash and metadata
remain serial. Position-map batching uses that map's own options.

## Read-path eviction

**The working set.** One access works on the stash and on the `P` buckets of
the path it reads. Both are held as *byte lines*: a byte line is one 64-byte
register holding the same entry byte from 64 lanes. The path's `4P` lanes are
ordered *leaf first*: path position `m` is the bucket `m` levels above the
leaf, in lanes `4m .. 4m + 3`. A path of at most 16 buckets fits one register
(`B = 1` path registers); a longer one takes two (`B = 2`, positions 16..31
in the second). For each entry byte the working set is therefore `B + A`
64-lane words, in the priority order [path 0, path 1, stash 0, ...,
stash `A - 1`].

**The plan.** [PlanReadPath](cpu_tree_read_path_eviction.hpp) reads only the
16 metadata lines: an eight-byte identifier (*uid*) and an eight-byte stored
position. For every lane it computes whether the lane holds an entry, whether
that entry is the requested one, and the deepest level its own path shares
with the read path: `L` minus the bit length of its leaf XOR the path's leaf.
Position `m` is level `L - m` and admits the entry when that shared level is
at least `L - m`. Then, leaf first, step `m` takes the first four lanes in
priority order that are eligible at position `m` and not yet placed. The
requested entry is excluded from this pool. The stash entries that are not placed stay where they are; the lane the
requested entry lands in is the lowest lane not kept. The lane sets are
64-bit words, and every step on them is PDEP, POPCNT, TZCNT or a hardened
select. VPCOMPRESSB turns each bucket's selected lanes into its four source
indices.

The rule has three properties, and the data pass and the overflow check rely
on all of them:

1. *Every path entry is placed, at its own position or deeper.* When step `m`
   runs, the entries from positions below `m` are already placed (by
   induction), so the at most four entries that sat at position `m` are the
   highest-priority candidates and are eligible there. A path entry therefore
   moves toward the leaf or stays, never into the stash, and the second path
   register never takes a source from the first.
2. *The stash is never permuted.* A stash entry the plan cannot place keeps
   its lane. A stash line changes only where an entry left for the path,
   where the requested entry left, and in the one lane the accessed entry
   lands in.
3. *It places as many entries as any greedy eviction.* Eligibility is nested:
   an entry eligible at a position is eligible at every shallower one. So any
   leaf-first greedy that fills each bucket as far as it can is a maximum
   placement, whatever its priority, and the number of entries left in the
   stash does not depend on the priority. This is the argument of the Path
   ORAM paper (its reduction to an infinite-bucket ORAM post-processed by
   greedy eviction) that the stash count equals that of an infinite-bucket ORAM post-processed by
   a greedy eviction, which covers any leaf-first greedy whichever eligible
   entries it chooses. Keeping stash entries in place therefore leaves the
   same count on every operation as a planner that compacts the stash, so
   stash-size analyses of compacting Path ORAM planners carry over.

**Overflow** is a pass that keeps more than `64A - 1` stash entries, leaving
no lane for the accessed entry. The plan is computed from chunk 0 alone, and
the engine throws `StashOverflowError` before it stores anything.

**The data pass.** Each destination path register lists the source words
that can feed it, in priority order: all `B + A` for the first, and all but
the first path register for the second, which takes nothing from it. The list
is grouped into consecutive pairs from its start, which is what VPERMT2B
takes, and the destination is the OR of one zero-masked VPERMT2B per pair,
with one seven-bit index vector per destination. An odd list leaves its last
word, the last stash register, alone; one merge-masked VPERMT2B whose first
table is the accumulator folds it in (index `64 +` lane, under that word's
mask), overwriting the accumulator in place with no copy and no OR. Every
destination lane has at most one source, so the accumulator is zero under
that mask beforehand. A destination with no source is in no mask and comes
out zero, a dummy. The accessed entry's byte is *gathered* the same way over
all `B + A` words, with a broadcast index under all-or-nothing pair masks; it
is zero when nothing was found. One masked move per stash register lands the
new entry's byte: its new uid and position on the metadata lines, `value_in`
on a write, else the gathered byte. The landing lane is secret, so every
stash line of every stash register is rewritten whole. On the metadata lines,
lanes whose entries left the stash are zeroed and read as dummies; value lines
keep stale bytes there, which the cleared metadata marks invalid. No payload
comparison or payload-dependent routing is needed.

Permutes and ORs per value byte line (a list of `n` words costs
`ceil(n / 2)` permutes and `floor(n / 2) - 1` ORs):

| Path registers `B` | `A` | Routing | Gather | Total | ORs | Landing moves |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 2 | 2 | 4 | 2 | 3 |
| 1 | 4 | 3 | 3 | 6 | 2 | 4 |
| 2 | 3 | 3 + 2 | 3 | 8 | 3 | 3 |

The gather runs only when the access reads the value out or lands the old
value; a write that returns nothing skips it. Metadata lines are routed but
not gathered.

**One access, in order.** The engine computes the path's bucket addresses,
leaf first, and prefetches them. It loads chunk 0 of every bucket, which is
exactly the metadata, and transposes it into byte lines. It plans and checks
overflow. It routes the metadata lines, transposes them back and stores them.
Then it loads, transposes, routes, gathers into `value_out`, transposes back
and stores each value chunk in turn. There is no second path: an access
evicts only the path it read.

## Stash size

The quantity that fails is the *leftover count*: the stash entries a pass
keeps, not counting the one it lands. The engine fails when it exceeds
`64A - 1`, so `A` is the smallest register count with `k* <= 64A - 1`, where
`k*` is the count whose per-access exceedance probability is the target
`2^-96`. Three registers hold 191 lanes beside the accessed entry, four hold
255.

The measurement does not run the engine. The plan is a function of the
metadata and the leaf alone, so the scalar simulator
[cpu_tree_stash_sim.hpp](../../../benchmarks/oram/cpu_tree_stash_sim.hpp) runs
the same rule over metadata with an unbounded stash, and the
[engine test](../../../tests/oram/cpu_tree_read_path_oram_test.cpp) holds the
engine to it slot for slot and stash lane for stash lane. The tooling that
produces the requirement is:

- `cpu_tree_bucket_shape_benchmark`
  ([source](../../../benchmarks/oram/cpu_tree_bucket_shape_benchmark.cpp))
  runs the simulator for one *row* (a geometry: `N`, fold, `A` and load,
  with a read workload) over many independent seeds (each seed is hashed
  first; raw consecutive seeds would be shifted copies of one random
  stream), pools their histograms of the leftover count, fits the log-tail
  `log2 P[k' >= k]`, which is linear in `k` for Path ORAM, and reports the
  count at the target with a jackknife standard error over seeds (successive
  accesses are correlated; independent seeds are not).
- [analysis/run_stash_tail_long.py](../../../analysis/run_stash_tail_long.py)
  runs a set of rows as one resumable process per seed, deep enough to fit
  the tail far below `2^-30`.
- [analysis/stash_requirement.py](../../../analysis/stash_requirement.py)
  takes `k*` as the larger of the fitted count plus two jackknife standard
  errors and the deepest fitted point carried to the target at the shallower
  of the fit's slope and its deep half's slope, a guard against a tail that
  flattens.
- [analysis/plot_stash_vs_n.py](../../../analysis/plot_stash_vs_n.py) draws
  the measured and extrapolated stash size against `N` for several
  security parameters.
- [analysis/plot_stash_tail.py](../../../analysis/plot_stash_tail.py) draws
  the paper's stash-tail figure and prints its numbers from the same export;
  [analysis/stash_rows/paper.json](../../../analysis/stash_rows/paper.json)
  lists the paper's rows and seeds ([REPRODUCE.md](../../../REPRODUCE.md)).

The default rule's stash width comes from this procedure, run at load one
half with round-robin reads (every key in a fixed cyclic order) and uniformly
random reads, at representative capacities of every fold the rule produces
(fold 1 over a range of capacities, fold 2 by a shallower screen at several
capacities, and folds 3 to 5 at `2^20` to `2^22`): every fold 1 to 4 row needs at most three
registers and every fold 5 row needs four. A fold costs fewer stash lanes than it moves out of the
tree, but the tail flattens as the fold deepens. Fold 1's requirement passes
three registers at `2^27`, so the rule takes four from `L = 25` (`2^27`) on.

These numbers have limits that apply to every use of them:

- **Every `k*` is an extrapolation.** Simulation reaches tails of roughly
  `2^-35`, not `2^-96`. A high-stash episode lasts many consecutive
  operations, so the deepest fitted points rest on few seeds; the jackknife
  and the slope guard charge for that.
- **Not every configuration has its own row.** A capacity without a row takes
  the nearest measured row with the same fold; `2^19` (fold 2), for
  example, takes the nearest fold-2 screen row. At fold 1 the deep tail can
  rest on a rare burst in a single seed. Fold 1 was measured at every power
  of two from `2^12` to `2^27`: it fits three registers up to `2^26` and
  needs four at `2^27`, through one such burst. So the rule takes four from
  `L = 25`, which holds `2^27` at load one half; larger trees take four
  without a row of their own.
- **A custom load or `leaf_scale` needs its own measurement.** Every row is at
  load one half.
- **It is not a bound.** If a per-access probability `p` is justified for a
  deployment, `T` accesses fail with probability at most `T p` by a union
  bound.

`max_stash_occupancy()` and `stash_capacity()` report the secret maximum
occupancy and the lanes it is measured against, for tests and measurement.

## Geometry and the default rule

[TreeGeometry::ForCapacity](cpu_tree_layout.hpp) solves for `L`: the
smallest depth whose slots, times the load, hold `N`. The slots are every
slot of the tree, folded levels included, plus the stash's `64A` lanes:
`4 (2^(L+1) - 1) + 64A`. At the default load of one half, `N` fits `L` leaf
bits exactly when `N <= 2^(L+2) - 2 + 32A`, so `L` is about `log2 N - 2`.
The load is halved once per unit of `leaf_scale`.

**The rule.** For a tree of `L` leaf bits, the fold is `L - 15` while that is
2 to 5, else 1. The path then has `P = L + 1 - fold` buckets: 16 for `L = 16`
to 20, at most 15 below. From `L = 21` the tree takes fold 1 and a path of `L`
buckets in two registers. The stash has `A = 3` registers up to fold 4 and
`A = 4` at fold 5 and from `L = 25` on (`kWideStashLeafBits`), the fewest that
hold the requirement in [Stash size](#stash-size). Because the stash's lanes
count toward the load and `A` depends on the depth and the fold,
`ForCapacity` sets the fold and `A` for each candidate depth before it counts
that depth's slots. So `L = 24` with three registers holds up to
`2^26 + 94` entries, and four registers start one entry later.

| `N` | `L` | fold | `P` | path registers | `A` |
|---|---:|---:|---:|---:|---:|
| `2^10` | 8 | 1 | 8 | 1 | 3 |
| `2^14` | 12 | 1 | 12 | 1 | 3 |
| `2^18` | 16 | 1 | 16 | 1 | 3 |
| `2^19` | 17 | 2 | 16 | 1 | 3 |
| `2^20` | 18 | 3 | 16 | 1 | 3 |
| `2^21` | 19 | 4 | 16 | 1 | 3 |
| `2^22` | 20 | 5 | 16 | 1 | 4 |
| `2^23`..`2^26` | 21..24 | 1 | 21..24 | 2 | 3 |
| `2^27`..`2^34` | 25..32 | 1 | 25..32 | 2 | 4 |

The fold keeps the path in one register as long as the stash can pay for it.
A one-register path needs fewer permutes per byte line (4 instead of 8 at
`A = 3`, 6 instead of 9 at `A = 4`), keeps its whole tile in registers, and
lets short payload slices gather first (see
[Parallel payload](#parallel-payload)). Folding `f` levels
moves their `4 (2^f - 1)` slots into the stash: 4, 12, 28, 60 and 124 lanes for
folds 1 to 5. Fold 6 would spend 252 lanes, nearly four registers before any
stash tail, and the stash-size procedure puts it at five or six registers, so
deeper trees return to fold 1. Where both fit, the rule takes the fewer
registers: each stash register adds permutes per byte line (see the table in
[Read-path eviction](#read-path-eviction)) and a full rewrite of its `E` stash
lines on every access.

**Capacity is a power-of-two staircase.** One bucket per leaf means the
tree's slots double from one depth to the next. A request just past a power
of two takes the next depth and twice the arena, so storage per entry varies
by up to a factor of two between consecutive powers of two. `capacity()`
reports the requested capacity, not the slots; the public map raises a
request below 128 to 128 (`kTreeMinimumCapacity`). There is no leaf-bit
floor: a small request is built as shallow as its capacity allows.

**Explicit values.** `fold` 0 and `stash_registers` 0 ask for the rule. An
explicit fold is 1 to 5 and must leave a path of at most 32 buckets, at
most 16 at fold 5, whose stash was measured only behind one register. An
explicit `stash_registers` is 3 or 4 and at least the rule's for the depth
and fold built, so fold 5 and `L >= 25` need 4.
`max_folded_slots` 0 admits whatever the fold costs; an explicit value is at
most `64A - 1`, lowers the rule's fold to one it pays for, and refuses an
explicit fold that costs more. `max_load` is zero (one half) or in `(0, 1)`;
the resolver refuses loads above one half. The public map writes the fold and
`A` it built back into the engine's knobs, and the resolver reports them as
the derived choices `tree.fold` and `tree.stash_registers`, with
`tree.leaf_bits` and `tree.path_slots`.

## Storage formats

An entry is its uid (8 bytes), its stored position (8 bytes) and its value.
Validity lives in bit 63 of the stored position, not in the uid. Leaf
addresses use at most 36 bits, so that bit is free, any 64-bit value
(including zero, and including the key) is a legal uid, and an all-zero arena
is empty. Every comparison of a stored position against a path sets the bit
in the path's word too, or it would not cancel.

A bucket is `C = ceil(E / 16)` chunks of 64 bytes. Chunk `t` holds entry bytes
`16t .. 16t + 15` of the four slots, interleaved: byte `k` of slot `z` is at
offset `4k + z` of the bucket, across chunk boundaries. Chunk 0 is therefore
exactly the metadata, later chunks are value only, and the last chunk's
columns past `E` are padding.

The [transposition](cpu_tree_transpose.hpp) turns chunk `t` of 16 buckets,
one per register, into 16 byte lines of 64 lanes, lane `4i + z` holding slot
`z` of path position `i`. The interleaved layout is the first two stages of a
64 x 64 byte transpose done once at rest; the remaining four stages are one
VPERMT2B per output register each, from eight constant index vectors. Each
stage is an involution, so the same tables transpose back for the
write-back. The network is pruned exactly to the path's length: forward and
inverse together cost 72 shuffles per chunk at `P = 8`, 101 at `P = 9` and
128 at `P = 16` (`ExactNetworkShuffles`). A two-register path transposes its
second tile at `P - 16`. The stash is stored as byte lines already, line `i`
holding byte `i` of all `64A` lanes with register `a` at offset `64a`, and is
never transposed.

The stored tree holds levels `fold` to `L`, level `j` having `2^j` buckets,
level by level. Within a level, bucket `b` is stored at the bit reversal of
`b`, and level `j` starts `64 (j - fold)` bytes later than packing would put
it. Both suit an eviction schedule that walks a fixed leaf sequence: the
bit-reversed order makes such a sweep visit each level linearly, and the
64-byte skew keeps a path's `P` addresses out of one cache set. The read path
reads uniformly random paths, which need neither; the layout costs one bit
reversal per pass and 64 bytes per level. [PathAddressing](cpu_tree_layout.hpp) turns a leaf into its `P`
bucket addresses with one bit reversal and a mask per level; every address
depends only on the geometry and the leaf.

**Exact storage.** With `Q = 2^(L+1) - 2^fold` stored buckets, the
[allocation](cpu_tree_layout.hpp) requests `64 C Q + 64 P + 64 A E` bytes for
an unsliced tree: padded buckets, level skew, and stash lines. A tree split
into `R` planes (see [Parallel payload](#parallel-payload)) requests
`64 C Q + 64 P R + 64 A E`, since each plane has its own skew. These counts
exclude the position map, allocator overhead, object state, worker stacks and
job buffers. `TreeGeometry::slots()` counts logical slots, not chunk padding
or skew; multiplying it by the entry width is not the arena. The composed
map's footprint is larger than the logical bytes by the load factor of one
half, the chunk padding, and the position map; `arena_bytes()` reports the
tree's own allocation.

**Movement per access.** The pass loads and stores `P C` bucket chunks,
`128 P C` bytes, and loads and rewrites every stash line, `128 A E` bytes. A
two-register path also stages its first tile through L1 once each way per
chunk, because the two tiles do not fit the register file together. These are
kernel byte counts, not DRAM traffic: caching and prefetching decide what
reaches memory. The composed map adds one position-map access.

## Parallel payload

The plan is a function of the metadata lines and the leaf alone, so the value
chunks are independent of each other given the plan. A chunk range of every
bucket, with the stash lines those chunks carry, is a self-contained storage
with the same layout: a *plane*. The synchronous engine is one plane. The
threaded engine splits the entry by byte columns into a metadata plane, chunk
0, which the calling thread owns, and one payload plane per worker owning a
contiguous chunk range, divided by quotient and remainder
([SliceLayout](cpu_tree_layout.hpp)). Every plane has its own arena, so no
writable tree byte is shared, and every plane applies the same plan to its
own chunks. Reassembling the planes gives the synchronous engine's bytes under
identical requests.

**Worker count.** One worker per started 32 value bytes
(`payload_threshold`), none below 32; 32 value bytes are two chunks, a
128-byte run of every bucket. The count is capped by `payload_max_threads`,
which the public options leave uncapped, by the physical cores the caller and
the position map's threads leave, and by the `C - 1` payload chunks. At 96-byte
values a tree has six payload chunks and three workers. The granularity is a
tuning constant chosen from worker-count sweeps over value widths; a finer
slice puts more chunks in flight per access. Measure the crossover for a
different machine or workload. With several cache
domains the resolver keeps the workers in the caller's domain below
`kTreePayloadSpreadBytes` (2048) value bytes, because one worker in another
domain adds its cross-domain round trip to every access, and spreads them
over all domains from there on, where the additional cores' bandwidth
outweighs that round trip.
Width and the core budget are public, so the worker count reveals no data.

**One threaded access.** The [worker protocol](cpu_tree_payload_workers.hpp)
publishes each job in two steps, each a release store to a sequence word on
its own cache line. The first carries the leaf and a copy of the caller's
input value; the workers compute their addresses and start their loads while
the caller transposes chunk 0 and plans. The second carries the plan. The
caller routes and stores chunk 0 and then waits until every worker has
signalled that its slice of `value_out` is written. Each worker answers with
two words of its own: *value ready* and *done*. An ordinary payload pass
signals value ready after routing its last chunk, before that chunk's
transposition back and write-back. A short slice behind a one-register path,
at most four chunks (`ReadPathStagesSlice`), gathers first: the worker loads
and transposes its whole slice while it waits for the plan, then gathers the
accessed entry's bytes, writes `value_out` and signals before it routes.
Staging takes the slice's loads and transpositions off the response path,
which pays when the slice is short; a long staged slice holds more
transposed lines than the register file and adds memory traffic, which costs
more than it saves, hence the four-chunk limit (a tuning constant). Either way the caller returns while the
workers' write-back runs on; the write-back is deferred past the response,
not removed.

**The job ring has two slots.** A worker publishes value ready for job `t`
only after done for job `t - 1`, so once the caller has collected value ready
for job `t` from every worker, the slot job `t - 1` used is free, and
publishing job `t + 1` needs no extra wait. Each worker spins on the word it
wants for `payload_spin_micros` (200 by default, 2,000 in the hybrid map),
then parks, or with `payload_monitor_wait` sleeps on the word's cache line
where the CPU offers it.

**Lifetime and failure.** The input value is copied into the job before
publication, so no caller memory is referenced after the access returns.
The caller's `value_out` is released only after every worker has signalled,
on an exception path too. An overflow is found on the caller before the plan
is published; the job is published cancelled, every worker retires it, and
nothing is written. A worker that throws latches the pool's failure and
retires every job, present and future, so no wait hangs; the access rethrows,
and later accesses are refused. An init hook that throws, or a thread that
cannot be created, fails construction after the started workers are joined.
Readers of raw storage must drain the tree first, and an explicit drain waits
for every published job.

## Security

The intended protection is the memory-address and control-flow trace of map
operations, assuming secret internal data and a secret per-instance PRF key.
Every access reads and writes exactly one path, `P` buckets with every chunk
of each in a fixed order, and every line of the stash. The leaf is the only
input to those addresses. It is a fresh pseudorandom leaf, uniform over the
leaves, drawn when the entry was last accessed; a miss reads a fresh random
path as well. The geometry (`N`, key and value widths, `L`, fold, `A`, `P`),
the operation kind, batch dimensions and the payload worker count are public.
Which lane held the entry, where every entry moves, whether the entry existed
and which stash lane it lands in are register data under masks and permute
indices. The position map must itself be oblivious. The implementation does
not encrypt or authenticate the arena, so it does not hide keys or values from
an adversary who can read its contents.

Within a pass, fixed-address loads and stores and register permutations hide
matching and placement. Every compare of secret data uses the register-only
forms in [src/core/mov_intrinsics.hpp](../../core/mov_intrinsics.hpp), every
secret select is a hardened conditional move, and a secret mask selects
between registers only, never which memory is read or written. The property
depends on the emitted machine code as well as the C++: written plainly, GCC
fuses a broadcast and a masked move into a load under a secret mask, so the
planner pins its broadcasts in registers.
The [instruction census](../../../tests/timing/README.md) disassembles the
built tests and benchmarks and must find no uncovered instruction (it matches
the mnemonic and its masking) and no unreviewed masked memory operation, and
`avx512_constant_time_test` measures, for one operand form of each such
instruction, whether it takes operand-dependent time. No claim of
constant wall-clock time follows from these source-level invariants.

Overflow is the one secret-dependent branch the construction permits. It is
an observable, fatal failure event, thrown before the pass writes anything.
The position map has already changed by then, so `CpuTreeMap` latches failure
on an exception from its access or either background-work drain and rejects
later operations; recovery requires discarding the instance and rebuilding
from an independent copy. How rarely the event occurs is the extrapolated
measurement in [Stash size](#stash-size), not a proof.

The capacity certification in
[analysis/bound_certification](../../../analysis/bound_certification/README.md)
covers the position map, a hierarchy, but not the tree's stash. A tree plan's
`certification()` is therefore `not_covered`, and only
`hierarchy_certification()` reports the position map's bound (see
[CONFIGURATION.md](../../../include/cpu_byteslice_oram/CONFIGURATION.md#certification-report)).

The hierarchy's public access horizon and, when it rehashes keys, its key
normalization budget (one normalization per position-map access) are checked
before position remapping. A scalar tree operation requires one position-map
access; a valid batched operation checks the entire batch because all its
positions change before tree execution begins. Callback adapters check two
accesses, or three when the key can change, before invoking the callback.
Insufficient budget raises `std::overflow_error` without changing either map
or latching failure; a smaller operation can use the remainder. These checks
concern the position map's declared budgets, not the tree stash's
probabilistic analysis. A position map that has failed (a rebuild failure on
an owner thread, or its routing budget) refuses at the same check; that
refusal latches the tree map's failure, and `failed()` also reports the
position map's own state.

Maintain this document by revising the affected explanation and derivation,
following the repository's [documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).
