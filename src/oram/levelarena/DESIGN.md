# Per-level arena design

The arena engine is the hierarchical ORAM behind `ByteMap`. Accesses scan a dense prefix and probe hashed levels `1..L`, while owner threads rebuild those levels in the background; each level combines incoming carries into partial tables until it forwards a full carry upward. Every buffer is a fixed physical slot allocated at construction, so rebuilding overlaps accesses within a fixed storage bound. Its central choice is to build each full carry directly in the receiving level's inbox. A receiver can adopt that table in place, and the producer can reuse the same inbox for its even partials before forwarding, so a carry is never relocated after it is built and even partials need no level-private buffer. This does not remove rebuilding or guarantee a bound on request latency when workers or readers stop making progress.

**Terms.** A *level* `l` is one size class of hashed tables; levels are `1..L`, and `L` is the *top*. A *carry* is the full table a level forwards to the next. A non-top level `l` (fanout `b_l`) absorbs `b_l` carries per cycle (the top absorbs `D`, defined below); after the `j`-th it holds the *partial* table `P_j` built from `j` carries, and `j` is its *digit*. `P_(b_l)` is the level's outgoing carry. In a merge, *A* is the older operand (the level's current partial, or the top's whole table) and *B* is the incoming carry; elsewhere `B` also names the geometry's maximum fanout, and context distinguishes the two. A digit is *sparse* when its carry is a hashed table rather than level one's dense prefix. Odd partials are built in the level's own *odd bank*; even partials go to an *inbox*, a buffer owned by the level above that the producer *leases* by holding a *credit* (exactly one credit exists per free buffer occupancy). A *Ready* message tells the receiver that a carry is published. A *nonce family* is the public coordinate (level, ordinal) that names the AES nonce a table is hashed under; a carry and the merge that consumes it share a family. A record's *home* is its destination bucket. A routing stage *sheds* a record that does not fit its home into a fixed-depth stash; a *residual* is such a record, and a *tier* is the fixed-width residual table published beside a main table. The *online stash* is the unit of `s` buckets that receives each access's insertion; the *dense prefix* is a frozen run of `r0` online-stash units, kept in the requester's ring and scanned in full by every access. *Owners* are rebuild threads that each drive a group of levels; *helpers* share an owner's routing *lanes* (independent slices of one stage). A *lease* is exclusive write ownership of one slot occupancy.

This document describes the current implementation. The [ORAM overview](../DESIGN.md) explains the shared online and rebuild primitives; [README.md](README.md) maps local engineering tasks to files and tests. Changes should replace the affected explanation directly, following the [documentation maintenance rule](../../../DESIGN.md#documentation-maintenance).

## Geometry and storage bound

A bucket contains 64 physical slots. Let `s` be the online insertion unit in buckets, `r0` the number of units per dense prefix, `q` the number of completed prefixes permitted in flight, and `L >= 2` the number of hashed levels. The geometry rejects smaller `L`; levels are numbered `1..L`. A non-top level has fanout `b_l` in `{2,4,8}`, bounded by configured maximum `B`. The top digit `D` is in `{1,2,4,8}` and at most `B`: per access the top moves `2D/(B+1)` times what a fanout-`B` level moves, so `D <= B` keeps that below two. The capacity ladder's default lower bound `B/2+1` selects `D=B`; callers can lower that bound to permit smaller binary digits. Define

```
Z   = 2 r0 s
U_l = Z product(i=1..l-1) b_i
T   = D U_L
C   = 32 T
```

`U_l` counts buckets in an incoming hashed carry, `T` counts top-table buckets, and `C` is the nominal logical entry capacity at load one half. A dense prefix holds `64 r0 s` access positions in `r0 s = Z/2` buckets. Its hashed representation doubles the bucket count. The requester owns a ring of `q+1` dense prefix slots, including the one being assembled.

[Geometry::BuildStorage](cpu_byteslice_level_arena_geometry.hpp) allocates two inboxes of `U_l` buckets at every receiving level `l >= 2`, two top banks of `T` buckets, and an odd bank of `(b_l-1)U_l` wherever an odd partial must be built. The default reserves the odd bank at every non-top level, including fanout two. At a binary level above level 1, digit 1 installs the carry into that bank through the ordinary partial-merge pipeline. Publishing the replacement retires the source inbox, making it reusable after reader retirement. This leaves both inboxes available while the current table is live.

Let `J = {1, ..., L-1}` in the default layout. The exact main allocation is

```
M = 2T + 2 sum(l=2..L) U_l + sum(l in J) (b_l-1) U_l.
```

For a uniform fanout this becomes

```
B in {2,4,8}: M/T = 2 + (3B-1)/((B-1)D) * (1 - B^(-(L-1))).
```

Counting each non-top level's odd bank and its two output inboxes at the next level gives `(3b_l-1)U_l`, or `3-1/b_l` full-slot equivalents. At fanout two this is 2.5.

These are **main buckets per top bucket**. Physical main slots per nominal logical entry equal `64M/C = 2M/T`. For example, uniform `B=8,D=8` approaches `M/T=135/56`, or `135/28` physical slots per entry. Neither ratio is a total byte overhead. Every table-storage slot also has a fixed-width residual tier, and the engine allocates masks, dense prefixes, job scratch, planning buffers and queues. [BufferByteBill](cpu_byteslice_level_arena_capacity.hpp) prices those modeled buffers; it excludes component objects, some wiring containers, callbacks, allocator overhead and thread runtime storage. Requested bytes and allocator-reserved bytes are separate quantities.

`Params::bank_first` (public option `deamortized_bank_first`, default `kNoClone`; see the next section) adds one tier per level with a bank-first run, as a second slot over its odd bank's buckets. `M` is unchanged.

The incremental engine owns one compact residual-tier payload pool through
`LevelArenaSet`. In level and physical-slot order, each slot gets a permanent,
disjoint slice of `slot.tier_buckets * layout.BucketBytes()` bytes. This includes
both inboxes, both top banks, and the run-bank slot even though it shares a main
with the odd bank. Inboxes keep the producing level's tier width. Slices are
consecutive and 64-byte aligned, with no per-tier padding or page alignment;
multi-bucket tiers keep their contiguous stride and key/value/meta/tag layout.
The ordinary aligned allocator does not round a pool smaller than 2 MiB to a
huge page. The online dense-prefix ring remains a separate allocation.

Main arenas keep the region layout, offsets and allocation alignment of a
standalone `LevelArena`, which embeds a tier payload region and tier mask words
next to each slot's main. In the engine those embedded tier regions are unused
holes and the embedded tier mask words are unused, so hashed-main spacing is
the standalone layout's while residual payload lives in the pool. If
`R = sum(physical slots) tier_buckets` and `w` is the stored entry width
including metadata and routing tags, the pool's requested payload is `64 w R`
bytes. The unused embedded holes cost another `64 w R` bytes inside the arena
allocations. They are reported as `retained tier holes`, not as a second live
tier copy; mask storage is reported under `masks`. The allocator's rounding
applies once to the pool and independently to each main arena. The capacity
planner prices the pool and the holes with the same selection policy as every
other buffer. `main_arena_bytes()` includes arenas, holes, masks and the pool;
the geometry's internal `ArenaBytes()` describes only the arenas themselves.
Keeping the standalone layout lets the engine, the synchronous mode and the
standalone `LevelArena` share one region and offset computation, and keeps
main-table addresses independent of tier sizing; the holes are a stated storage
cost, reported separately.

Storage separation does not separate lifetime ownership. Each slot's
`ResidualStash::data` permanently names its assigned slice, while its inline
masks remain in the slot runtime. Leases, generations, publication and reader
epochs protect main and tier together; neither can be reused until the slot
retires. Published views use that stash's payload and masks, and rebuilds write
the same slice without an extra publication copy. The pool outlives every
arena, job, plan and worker that references it. Standalone `LevelArena` users
retain their embedded tier storage, and synchronous storage is unchanged.
There is no request-path allocation, live relocation or dynamic compaction.
Probes visit the same active tiers in the same logical cascade order; sharing
an allocation does not cause inactive slices to be scanned.

The pool places tier payload consecutively rather than at page-aligned offsets
after each main region, which avoids mapping every tier to the same cache sets
when arenas are aligned and main sizes are powers of two. Placement changes
neither overflow probabilities nor certification.

The [Python model](../../../analysis/level_arena_model.py) checks the uniform closed forms against slot enumeration. All bank and inbox extents are determined by public geometry; scheduling changes their reuse times, not their allocation.

## Carries and preparation

An incoming carry with one-based ordinal `v` installs digit `j = 1 + ((v-1) mod b_l)`. For `j < b_l`, the output has `j U_l` buckets. Odd partials use the local bank; even partials use an inbox leased from level `l+1`. At digit `b_l`, the output exactly fills that inbox and becomes the next level's carry. Source and destination remain disjoint because odd and even outputs alternate locations. Reusing either location still requires reader retirement. The inbox lease is one slot occupancy that holds `P_2, P_4, ..., P_(b_l)` in turn, and a slot's tier is emptied by the slot only when an occupancy begins, so every merge empties its destination tier when it is bound. Otherwise a table would be published with its predecessor's leftovers, and a merge consuming it as a carry would rank those stale copies freshest.

**The bank-first run** (`Params::bank_first`) starts each cycle in the odd bank, which is idle then. Its last occupant `P_(b-1)` left when the full table published, while the inbox the next even digit needs may still hold the previous full table that the level above is absorbing. So digits `2..r` are built in the bank, and the forwarding lease is first taken at digit `r+1` rather than 2 (`LevelArenaGeometry::ForwardingLeaseDigit`).

- **Placement.** Each partial is written while the one before it is still live. So the run's last partial sits at the bank's top, and those before it alternate base, top, and so on (`BankOffset`). Two consecutive tables then take `(2j-1)U <= (b-1)U` buckets, which bounds the run at `r <= b/2`.
- **Parity decides the run's end.** An odd last digit is followed by an even one, which goes to the lease with no copy, while an even last digit would be followed by an odd one that does not fit beside it. So the run (`BankFirst::kNoClone`) ends at the largest odd digit `<= b/2`: none at `b = 2, 4`, digits 2..3 at `b = 8`.
- **Two lifecycles, one bank.** Coexisting tables need separate lifecycles and tiers, so a level with a run has a second slot over the odd bank's buckets (`SlotKind::kRunBank`, which holds the run's even partials). Neither slot machine knows about the other. The level therefore waits while the other occupancy is retired before it leases one (`LevelState::BankSiblingBlock`). A retired table may lie anywhere a new one is about to be written.
- **The default is `kNoClone`.** It runs the same merges on the same bytes, only in the bank, at the cost of one additional tier per participating level. It widens the window in which the level above must hand back an inbox from `(b+2)` to `(b+4)` producer periods at B=8. `kOff` uses the forwarding inbox from digit 2.
- **Placement is checked at construction and at run time.** The geometry verifies that consecutive tables are disjoint and in different occupancies, and that the lease digit is the first digit that uses the lease. At run time a lease refuses to overlap the live partial beside it, and a merge job refuses an older operand that overlaps its output.

At digit 1 above level 1, fanouts above two adopt the carry without copying bytes or changing the probe plan. Binary levels instead use the odd-bank installation described above, preserving the nonce family across one publication that replaces the inbox table. Two inboxes are necessary: an adopted first carry can occupy one while the producer builds the carry needed to replace it in the other. A single inbox would create a dependency cycle.

A merge separates work on the older table from work requiring the incoming carry. [LevelMergeJob](cpu_byteslice_level_arena_job.hpp) retains destination views, private masks, residual descriptors and the nonce across these phases; its level owns the destination lease and keeps all borrowed sources and range scratch valid until the job completes. An owner may prepare the older table while waiting for the carry. Preparation remains paid work, but can leave the request's dependency path. The [merge planners](cpu_byteslice_level_arena_merge.hpp) use the shared routing, deduplication and residual-offer primitives.

The residual routing is determined by each pass's public shape ("How each pass builds its range table" in [the pass shapes](cpu_byteslice_level_arena_pass_shape.hpp)). A *one-page DFS* is the [rebuild layer's DFS distribution](../rebuild/DESIGN.md#public-capacity-dfs-distribution) of a residual pool with one page per coarse range; the *retained carry* is the stash holding the A records that preparation shed, kept for the finish. Level 1 builds B directly and then finishes with separated sources (below); a sparse digit greater than one has separated sources, below; a sparse digit one drains its carry's tier; the top prepares through a one-page DFS and finishes with separated sources like a sparse ordinary digit: a one-page DFS leaf of its retained carry, with the incoming carry's tier offered directly. Coarse ranges use eight ranges per pool bucket, capped at `2^kDfsMaxRangeIndexBits = 2^18` homes per range. A pool whose shape selects direct offers uses that deterministic plan. [Bound certification](../../../analysis/bound_certification/README.md) analyzes this routing subject to the premises described below.

Separated sources apply to every ordinary digit greater than one. Preparation routes A through the complete binary/mixed-radix network and retains every A shed. The public carry region `[0,U)` is not cleared: the one pass that reads it (the first continuation at an even digit, the radix pass at an odd one) is planned with `Subtask::blank_first`, never reads its stale masks, and writes all of them. Install performs no copy. Finish uses `PlanFixedCarryInsertion`, shared with the top, to split B by its final home and insert it directly from the published carry. Ordinary contexts preserve tombstones; only top contexts enable `drop_unshadowed` and top resolution. Digit-one and top routing keep their separate contracts.

At the first added binary continuation, `2^bit == upper_offset == U`: each pair contains one empty bucket and at most 64 A records. Neither output can overflow, so the planner marks the task `blank_first` and the runner uses the blank-first `MergeSplitPair`, which reads only the A bucket and no stash, and the stage declares no stash writer. At an odd digit the radix pass is marked the same way and skips the permutes that would take from block 0. Earlier preparation spans may have shed into the same stage stash; those records remain readable and are still swept. Later continuation levels use `MergeSplitPairStash`. The selection is determined by public geometry and is unchanged when a task is sliced or resumed.

The separated residual allocation contains one A page per padded coarse range followed by one private retagged copy of B's `t_B` tier pages. Combined source dedup precedes gathering; each destination sees its A page before B's full-home offers. Private masks and lane folds cover both parts, and the single drain reads original sources through shed dedup. For `M` padded leaves and `N` main buckets this uses `M+t_B` pages and `N(1+t_B)` page offers. Here `t_B` is the producer level's tier width, separate from the online insertion width `s`. Main dedup visits `dU` buckets, and B's main is inserted directly from its published storage. The [completed-A bound](../../../analysis/bound_certification/REPORT.pdf) includes all A losses; the generated certification table reports which exact native shapes and horizons it covers.

### Directly built level one

Level one builds every carry directly from the dense prefix; there is no butterfly backend at level one. Install keeps the chronological prefix deduplication on private masks. It then hashes each of the `M = r0 s` prefix buckets once into a cache of low `log2 U_1` tag bits, called B's homes. Every home `h` then scans all `M` buckets in public order and takes the first `min(X_h, 64)` winners into `B[h]` ([`cpu_byteslice_dense_select.hpp`](../rebuild/cpu_byteslice_dense_select.hpp)). The rejected winners drain in bucket and lane order. Digit one drains into its configured output tier; above digit one, they drain into one standalone 64-slot B tier. The residual occupancy is exactly `sum_h (X_h - 64)_+`, and overflowing the selected tier is the install's declared failure (`dense-drain`). No butterfly runs and no bounded intermediate stash exists. Because the merge's map keeps the low `K + e >= K` raw bits, `final_home mod U_1` is B's home. Correctness rests on these invariants: prefix deduplication yields exactly the newest occurrence of each key, tombstones included; B's main and tier partition those winners exactly once; and every A record is routed to its final home or a stash before B is inserted, so no B-dependent filtering happens during preparation. A producer tier can overflow even when the final split by digit would not (129 distinct records at one B home leave 65 leftovers); that is a separate, accounted failure event, not a fallback trigger.

At digit 1, B is built straight into the output and its tier, and no finish pass runs. Above digit 1 the job builds B into its own `U_1` buckets and tier. Its finish is then the separated one (`SeparatedSources` includes this case): A is routed completely in preparation, B is inserted by the fixed sweep with its ways recomputed, and A's residuals go through a one-page DFS leaf, exactly as at a sparse digit: its only range event is A's complete-home excess on a coarse range, which does not depend on B. B's tier is offered directly, and the leftover dedup resolves a B-main shed against an older A residual. B-main sheds are distinct survivors at permanently full homes, so they number at most the final excess. The merge slot is therefore made at least as wide as the output tier (`MergeStashBuckets`), so it cannot overflow before the tier does; the route stashes keep their certified depth. Automatic sizing gives one bucket of each, so this only widens a pinned tier's merge slot.

The build is one ordered stage: dedup, homes, `U_1 * M` home visits, drain. Its cost (`DenseSelectHomeTouches`) and storage (`AddDenseDirectBytes`) are priced like every other phase. The certification lookup requires matching regenerated evidence and fails closed on missing or stale shapes. Above digit one the build adds one capacity event, the producer tier; digit one has only its output-tier event; the A leaf is the separated pass's own event at level one's shapes, and the merge stash is dominated by the output tier.

A phase is resumable. When it starts, the job plans it at the whole budget into a task list reserved at construction: one task per range and one per butterfly block, at most a few thousand at the top. A [phase cursor](../scheduler/cpu_byteslice_subtask_cursor.hpp) then runs that list in pieces cut at the executing group's budget, and may stop after any piece; a later call resumes from the stored position. A piece is a sub-range of a range task, or a leaf of the butterfly's own recursion, run in order, so the output is byte-identical at every budget and every stopping point. The position lives in the job rather than on the executing thread's stack, which is what lets an owner leave a phase half done and run another level first. For the same reason each level has its own residual range table: a stopped phase keeps its table attached while another level's phase runs.

A phase's tasks form stages, and the planners mark each one: a routing half of a butterfly root, a copy, a cross level, a radix pass, the fixed merge, or an ordered run of residual work. A level whose public table size reaches `lanes.min_buckets` divides each divisible stage into up to `lanes.lanes` lanes; this includes level 1. Each lane owns a contiguous run of public work units and a private stash array of the configured depth. Offer stages additionally copy their range occupancy words into private masks, which are folded back by bitwise AND after all lanes finish. The payload stays shared and read-only. At stage end, lane stashes fold into the job's own in lane order with the checked stash merge, which bounds their combined occupancy. Stash insertion appends to the lowest free slots and nothing leaves a stash during routing, so this ordered fold preserves the one-lane result.

A job with lanes can share its phases with helper threads: `top_helpers` serve the group containing the top, and `bottom_helpers` serve the group containing level 1 when it is a different group. Any thread claims a lane of the running stage through one compare-and-swap on a word that packs the stage's sequence number, lane count and next unclaimed lane. A lane stopped by preemption is put back, and any thread may resume it from its stored position. The thread that finishes a stage's last lane folds it and opens the next stage. Only the owner crosses a phase boundary. When helpers hold every remaining lane, the owner reports `kHelpersBusy` and runs its other levels, and a helper that opens the next stage or finishes the phase signals it; an owner that opens a stage itself does not signal its own event, which would stop the phase it is in. A group waiting on its helpers does not acknowledge a drain round. Which thread runs a lane does not change the result.

A carry and its consuming merge must use the same raw hash. [CanonicalFamily](cpu_byteslice_level_arena_family.hpp) follows public forwarding ordinals to the terminal publication and names the nonce by that coordinate. Producer and consumer therefore agree before either runs. The coordinate is public; the AES key is an instance secret and must also agree. Retagging changes the routing interpretation without moving the already routed carry under a different hash. Only one logical member of a family may occur in a live probe plan; family history spans successive identities of the same physical carry.

Sharing a nonce between a carry and its consumer is safe because the merge that consumes a carry removes it from the probe plan in the same publication that adds the merge output (one plan transaction), so two members of a family are never probeable at once, and publication refuses any plan that would hold two. A key that received a real probe in the carry was then reinserted into the online stash, after the carry's window ended; that fresher copy is not in the merge output, so every later access finds it first and sends the output a dummy probe. Each key therefore receives at most one real probe per family, which is the invariant the [online cascade](#online-security-and-capacity) relies on. *Retagging* recomputes a record's stored routing tag under the destination's index map without moving its payload; the *terminal publication* is where a carry's forwarding chain stops: a carry with ordinal `v` at level `l` whose digit completes the level (`v` a multiple of `b_l`) yields a full table that arrives at level `l+1` as ordinal `v/b_l`, and the family is the (level, ordinal) at which this stops. All members of a family end at the same window end, so a member and its successor occupy the same place in the probe cascade.

## Top compaction and residuals

Top preparation, including direct initialization, distributes through a one-page DFS. It preserves the production coarse partition, fused final-stage offers and drain order. The top finish is a separated pass, the same range rule as every finish below the top (`FinishPassRange`): the preparation's retained carry, A's class alone, goes through a one-page DFS leaf, and the incoming carry's tier is offered directly after it. The top's resolution (`ResolveTopDestination`) treats the direct set as the fresher class, so every version is still resolved before the first capacity decision. Scratch sizing, byte accounting and residual work estimates use the same per-pass ranges (`TopPreparePassRange`, `FinishPassRange`).

The top always compacts into a bank of `T` buckets. It consumes its old table and an incoming carry, resolves newer copies against older ones, and publishes the result with its tier. `D` is a power of two (1, 2, 4 or 8, at most `B`); the geometry, the capacity ladder and the public options reject other digits. Preparation routes one binary butterfly over all `T` buckets, so a top digit of eight needs no radix-eight routing kernel.

For `D > 1`, the incoming carry's stored tags do not encode its position among the top's `D` blocks. The sweep recomputes its way line in registers from the key and the shared hash instead of copying and retagging a whole table. At `D=1` there is only one way and no way recomputation is needed. For a carry of `U_L` buckets and `w` payload bytes per physical slot, this eliminates a full temporary payload copy of `64 U_L w` bytes written, together with its corresponding reads; hash and way computation still occur.

Residual handling resolves B's main and tier keys against the prepared main and A's residual candidates before allocating any output slots. The top then merges and offers those distinct live winners without further deduplication. This order preserves freshness and makes overflow depend on the resolved live set. The [top tests](../../../tests/oram/cpu_byteslice_level_arena_top_test.cpp) exercise full-bucket replacements, tombstones and forced residual cases.

The [stash sizing code](cpu_byteslice_level_arena_stash.hpp) feeds public rebuild counts, routing widths and stage counts into the shared overflow-capacity table. It uses the caller's `max_accesses` horizon, default `2^32`, and additionally reserves one top preparation for direct initialization while conservatively rounding partial periods upward. Stage stashes receive one quarter of the `2^-64` sizing budget; tiers receive a separate quarter. Automatic tier sizing selects a width per producing level, with a nondecreasing floor below the top; the top uses its own requirement. Inboxes retain their producer's tier width, including after adoption. Engine and capacity options use zero for automatic sizing; an insufficient positive shared-width or per-level pin rejects. These resolved widths feed allocation, pass shapes and range scratch planning. The separate certification lookup composes the analyzed capacity events at matching native shapes; its bounds are conditional on undischarged proof premises. Overflow is a declared failure, and automatic retry under a fresh nonce is not implemented.

## Publication, readers and progress

One requester owns online insertion. Rebuild owners drive disjoint levels or adjacent groups of levels. A batch's workers participate in that requester's single reader interval; they do not create independent concurrent requesters. Setting owner threads to zero makes the requester drive the same state machines at flush boundaries. The synchronous storage mode, below, runs the same jobs without the state machines.

[Slots](cpu_byteslice_level_arena_slots.hpp) and [boundary credits](cpu_byteslice_level_arena_boundary.hpp) establish exclusive write ownership. Each free occupancy has exactly one credit, either queued or held by its producer. A credit identifies a generation and extent; writable views require a valid lease. Cancellation replaces the abandoned lease's credit exactly once. A leased inbox can remain occupied by a published even partial until its replacement and reader retirement permit reuse.

[Publication](cpu_byteslice_level_arena_publication.hpp) takes a mutex, applies the operation's remove/add set to the latest live state, validates a new immutable probe plan, then installs it with a sequentially consistent store. Preparing the ready notification occurs before installation and may fail. Committing the prepared notification occurs afterward and must not throw. Readers do not acquire the publication mutex.

A requester enters its [reader epoch](cpu_byteslice_level_arena_epoch.hpp) before loading the plan. After replacement, the publisher samples epoch `e` and retires removed storage at threshold `e + (e & 1)`. Reclamation requires observed reader progress to reach that threshold. Publishing a replacement does not authorize immediate reuse of the source's payload, tier or masks. Merge jobs may borrow published payload only while using private mutable masks.

Owners poll dependencies and park through [generation-counted events](cpu_byteslice_level_arena_event.hpp): read the generation, poll, then wait for a change. Signalers expose work before incrementing the generation. An event may have several waiters (a group's helpers share one), so it counts the waiters registered to park rather than keeping one flag that the first to leave would clear for the rest. Backpressure follows outgoing credits toward the top, and requester waits occur with its epoch closed. Eventual worker scheduling and reader quiescence permit progress. Finite buffers cannot hide an indefinitely paused owner or reader, so this design supplies bounded storage and overlapping work, not a worst-case wall-clock latency guarantee. The requester's wait limit is a deadlock detector, not a deadline: it bounds one backpressure wait, each spin and park included, and in a drain only a stretch in which no owner is seen to move (a progressing poll, a phase answering the drain's signal between two pieces, a helper finishing a lane), because a drain waits out every phase in flight, a speculative top preparation included.

A group visits its members earliest deadline first, on the requester's prefix clock, and cuts their phases into pieces. Between pieces a phase checks the group's event generation. A change causes it to stop when an earlier-deadline member can merge, when it is preparing speculatively and another member can merge, or when a member owes a credit that its next step can return. Otherwise it re-arms on the observed generation and continues. The next round orders members by deadline again. Publication is one transaction and has no intermediate pause.

A group's slice limit is half its tightest buffer window. With `P(l)` the prefix product and `f` the lower level's forwarding-lease digit, the windows are `q` prefixes at level 1, `f P(l-1)` at a receiving non-top level, and `(b+f) P(l-1)` at the top. The configured request rate converts that window to time; the cost model's line cost converts time to bucket touches. The default request rate is the model's estimate for a saturated sequential requester. These are work budgets, not wall-clock guarantees. Explicit rates must be finite and nonnegative, and computed touch budgets must fit a 64-bit count. Without owner threads the requester runs a share at each flush, sized by a finite positive multiple of the modeled work per flush; a stopped phase resumes on a later flush. `FlushPolicy::kSettle` instead drives each flush to quiescence.

[The rebuild parameters](cpu_byteslice_level_arena_rebuild_params.hpp) choose how the levels are divided among owner threads, how many helper threads and lanes the top's group gets, the piece rate and the inline share, as one value. A heuristic chooses them from public sizes and a thread budget: a static per-level cost model counted from the routing planners, contiguous groups that minimise the largest group's demand with a penalty for bursty middle levels, and helper threads for the top once it is the bottleneck. The cost model's defaults are calibration constants fitted on one host; `python -m analysis.oram_bench fit-rebuild` refits them on a target and writes them as a `rebuild_cost_*` override block for a preset, and an explicit division (`Options::groups`) bypasses the heuristic. The division never changes the stored bytes, only which thread runs which level.

Retired storage is immediately reclaimable when publication observes a quiescent requester; otherwise it waits for the current reader epoch to close. A group blocked on that retirement registers as an epoch waiter before parking. Every epoch close (an access, a batch, a plan diagnostic, or an exception exit) wakes registered groups. A group registers when a member is blocked on retirement or the plan pool, and also whenever a member holds a retired inbox. The producer waiting for that inbox's credit reports only `kNoOutputCredit`, while the receiver may itself be parked on `kNoCarry`, so the receiver registers to be awakened for reclamation.

An access removes before it inserts: its probe clears the key from the current online-stash unit, and a batch clears every lane's key before inserting any. Everything that can refuse therefore runs first. With owner threads the requester's wait for a free prefix slot is bounded by the wait limit, so it runs before any removal: a scalar access whose insert will complete a prefix waits for that slot before it probes, a batch job waits for the slot its inserts will complete, and a key-changing callback secures the slots of both its accesses before the source is removed. A slot, once free, stays free until the requester takes it, so the freeze after the insert never waits. Every probing batch job ends at the current unit's boundary, so it completes at most one prefix and its commit never waits. A refusal therefore leaves the engine unchanged and usable. The inline flush has no wall-clock limit (it drives the levels itself), so it still waits after the insert, in the order the replay oracles model. What can throw after an insert is a failure: a batch that fails after its removals, any step of the inline executor, and a flush after an insert that throws (no level can progress, a settle that stalls) latch a failure that every later call re-raises, as an owner thread's failure is re-raised with owner threads.

### Threading rules

The source refers to these rules by number ("threading rule 7"). Rules 4 to 7 also bind the inline executor, which is every actor at once; rules 1, 2, 3 and 8 matter once owner threads give a slot two threads.

1. **One requester.** The odd/even reader-epoch word admits one active request snapshot. Public calls on one engine (accesses, batches, drain, initialization) are serialized by the caller; batch participants share the requester's interval rather than opening their own.
2. **One actor per role.** Only the upstream owner consumes inbox credits and takes, writes, publishes or abandons a lease. Only the receiving owner issues credits, accepts Ready, retires and reclaims its inbox slots, and only a level's owner touches its banks. Grouping keeps these logical roles and never runs two steps of one level concurrently. A publisher may update the global plan under its mutex but never reclaims another owner's slots there.
3. **Exactly one credit per free occupancy.** Initial credits are issued once, at construction, and then one per successful reclamation; free slots are never rescanned to mint credits. A cancelled lease returns exactly one replacement credit when execution continues.
4. **Ready follows plan installation.** A receiver learns of a carry only from the Ready channel, never by scanning slot state. Everything fallible (generation, source identities, ordinal, family, window, extent, the destination tier, plan and message reservations) is checked and reserved before the commit. Under the mutex the delta is applied to the latest plan, validated and installed; afterwards only nonthrowing handoff and the release-enqueue of Ready remain. Nothing allocates or validates after installation.
5. **Epochs are not publication counters.** A reader enters its epoch (seq_cst) before loading the plan. After the seq_cst replacement store the publisher samples epoch `e` and gives the removed storage threshold `e + (e & 1)`. Reclamation compares an acquire observation of reader progress against that threshold, never a publication id or a predicted value.
6. **Preparation pins its source.** A level has at most one pending ordinal and job. A prepared job retains its source generation, destination lease, family and sheds; nothing else at that level can advance the ordinal or replace that source while it is pending, and a mismatched Ready is refused rather than renonced.
7. **Dense retirement crosses back to the requester.** Level 1 publishes a prefix's replacement and returns the prefix's identity and retirement threshold to the requester; only the requester reclaims prefix slots. That notification storage is bounded by the prefix ring, and the requester never waits with its reader epoch open.
8. **Wakeups and failure are part of the protocol.** Work, credits and retirements are made visible before their event is signalled. Epoch waiters register before the final predicate recheck, and messages are drained and the event generation rechecked before parking. No owner waits inside a grouped step or while holding the publication mutex. A failure wakes every wait; shutdown joins all threads and closes reader snapshots before releasing storage, and a prepared lease is abandoned only after every task referring to it has stopped.

### Direct initialization

`Initialize` builds an engine from a batch of records by publishing one full top of `T` buckets under family `(L, D)` and nothing else. The engine then continues as if ordinary insertion had reached that state: with `H = D U_L / Z` synthetic completed prefixes, level `l` has accepted `H / (b_1 ... b_(l-1))` carries (the top `D`), the stash-flush counter is `r0 H`, and the access-position offset is `64 s r0 H = 32 T`. Every non-top digit is then zero, inboxes and dense prefixes are empty, and every later family has a later window end, so `(L, D)` is never reused. Nothing is published until every record is valid, and owner threads must not have started. The initialized contents equal those of ordinary insertion in logical values and windows, not in nonce-dependent byte layout.

### Batches and near/far placement

A batch serves independent requests in lane order; a write is visible to a later lane's read of the same key. It deduplicates the whole job, probes one plan under one reader epoch, and leaves that epoch before any insertion can reach a blocking flush. The dense prefix's key lines are loaded once per chunk and matched against every lane from registers, which is why a batch tolerates a longer dense prefix than a scalar access. Two execution shapes differ only in who runs the cascade: chunked execution runs one tile on the calling thread, and parallel tiles run one tile per participant and commit in lane order on the requester.

On a host with several cache domains, `Options::near_max_level` names the largest level whose rebuild is near the requester. Owner groups never straddle that boundary, and batch participants are always near. The assignment of CPUs is a pure function of public numbers and is applied through the caller's thread-init hooks; the library does not pin threads itself.

## The synchronous storage mode

`Options::synchronous` (the public `ByteMap<false>`) keeps everything above except overlap. The request that completes a dense prefix merges it through every level it carries into, the top included, before it returns. No reader is inside the hierarchy while that happens, so no table has to stay probeable while its replacement is written, and each level needs one region instead of an odd bank, two inboxes and the forwarding lease. [SynchronousLevels](cpu_byteslice_level_arena_synchronous.hpp) owns those regions.

- **Layout.** Level `l < L` has a region of `b_l U_l` buckets, and its digit-`j` table occupies the top `j U_l` of it. A merge writes `P_j = [carry's U | P_(j-1)]`, and the job already copies its older operand to offset `U` of its output (offset 0 at the top), so the binding is in place (`LevelMergeBinding::in_place`). The job's copies are then the identity: `CopyAndRetagRange` sees source and destination alias and only re-tags. At digit `b_l` the region is full and is the next level's carry, read where it lies. The top compacts in place in its `T` buckets. Each level alternates between two tier stashes, so a merge's output tier is never its older operand's.
- **Storage.** `M = T + sum(l=2..L) U_l`, which for a uniform fanout is `M/T = 1 + B/((B-1)D) (1 - B^-(L-1))`, approaching `8/7` at `B = D = 8`, versus `135/56` for the overlapping arena layout. The capacity ladder prices this bill when asked (`LevelArenaCapacityRequest::synchronous`), so its choice can differ from the arena's for the same request, but it searches the same geometries by the same rules.
- **What is shared.** The geometry, the stash and tier sizing, the canonical families, every job and its residual routing, the publisher, the dense ring, the probe cascade, batching and direct initialization are the arena's own code, run at the same `(level, ordinal)` in the same order. The tables are therefore byte for byte the arena's: the [synchronous test](../../../tests/oram/cpu_byteslice_level_arena_synchronous_test.cpp) runs both with one secret and compares every live table's occupied entries. The certification report applies unchanged. Two things differ, and neither is a job. An adopted first carry (digit 1 above level 1 at fanout above two) is copied, main, masks and tier, from the level below's region into this level's. And a forwarded table is published by its producer and then removed by the publication of the merge that consumes it, rather than living in an inbox.
- **What it costs.** No overlap: the request that completes a prefix pays for every merge it triggers, a top compaction included. The mode takes no owner threads, helpers or lanes and refuses `FlushPolicy::kHandOver`.

## Online security and capacity

The online cascade scans the dense prefix and probes the published tables in freshness order. Secret matches select between real and domain-separated dummy addresses without changing the public plan traversal. Read misses and erases insert real tombstones, so repeated absent-key requests can find a recent entry instead of repeating an older family's real probe. A batch forwards repeated-key results in lane order and uses dummy probes for later occurrences; batch inputs must not depend on another lane's output buffer. The invariant this preserves is that each key receives at most one real probe per nonce family: after a real probe the key is reinserted into the online stash, and that fresher copy precedes every member of the family in freshness order from then on (see the family rule in [Carries and preparation](#carries-and-preparation)). Each real probe therefore lands at a fresh pseudorandom position under the family's secret hash and each dummy probe at a domain-separated pseudorandom position, while the traversal order and probe count are fixed by the public plan.

Top consumption is the point at which older versions can cease to be protected by a tombstone. Below the top, tombstones survive rebuilding. The online path marks a tombstone unshadowed when no older live copy of its key can exist: its probe found nothing, or found a tombstone that was itself unshadowed (the found entry is the key's freshest copy, so everything older is that tombstone or older still). The batch path gets the same mark from its forwarding chain, which gives each lane the qualifier the serial access would, so a repeated key inherits it lane by lane and an earlier lane's write clears it. Top compaction omits unshadowed tombstones as it reads them, leaving published source bytes unchanged.

The top's sweep resolves every version before any capacity decision, as required by the [capacity proof](../../../analysis/bound_certification/REPORT.pdf). For each destination bucket, `ResolveTopDestination` visits every public offer group of the merge pass's private range table. It drops older-class candidates (the preparation's retained carry) superseded by B's keys, clears the prepared table's copies of fresher-class candidates (B's tier), and drops resolved tombstones. Main dedup has already cleared the prepared table's copies of B's main keys, and pool dedup has cleared retained copies of B's tier keys. FIFO consumption leaves nothing older than the two operands, so resolved tombstones need no output slot. The merge and offers place only distinct live winners; any leftover targets a full bucket, and the tier holds the live set's complete-home excess. The trailing drop over the output and its tier finds no tombstones (asserted in checked builds) and remains fixed public work. An unfused merge may omit shadowing tombstones only if no later pass can hold a staler copy; the dispatcher determines this from public context.

The nominal capacity is `C=32T` for every supported `D`, including one, and the public contract counts the live key set. The fixed sweep omits every carry tombstone, from its main and its tier, after resolving their older copies in both the prepared table and the residual range table. Thus neither erases nor absent-key traffic adds a logical-capacity term. The [job setup](cpu_byteslice_level_arena_job.hpp) enables the omission unconditionally at the top. The [top fixtures](../../../tests/oram/cpu_byteslice_level_arena_top_test.cpp) cover the narrow `D=1` case, a carry that erases keys only the retained carry holds, and a carry tier that erases a full bucket's keys, and check every case's output tier against the complete-home excess of the live set; the [resolution test](../../../tests/oram/cpu_byteslice_top_resolution_test.cpp) checks the sweep and its epilogue against a scalar resolve-then-compress oracle, append prefixes included. The [map tests](../../../tests/oram/cpu_byteslice_oram_map_test.cpp) run full-capacity churn, write-then-erase, and repeated miss and erase histories at `D=1`. Logical capacity does not guarantee that every hashed placement fits: a rebuild can still report overflow, subject to the conditional bound for a covered geometry and horizon. [Geometry selection](cpu_byteslice_level_arena_capacity.hpp) enumerates supported capacities and prices modeled buffers, so a byte-slack setting constrains that model rather than process memory.

### Scalar value workers

Value workers are a performance option: they partition the same public column traversal across threads and do not change which records win.

A worker's progress word names the winning bucket of a dense run in 12 bits, so value workers need a dense prefix of at most 4,096 buckets (`r0 s`, where `s` is the online stash in buckets). The engine refuses value workers with a longer prefix at construction (`std::invalid_argument`), and the configuration resolver refuses such a plan.

Scalar accesses may assign fixed contiguous user-value columns to persistent
[value workers](cpu_byteslice_level_arena_value_workers.hpp). With the default
count zero, the ordinary single-thread value cascade runs and no job buffers or threads are
allocated. The split cascade is a compile-time policy of the same winner and
tombstone loop: first matching entry, last matching bucket of a dense run,
lowest matching slot. The requester owns keys, occupancy and the meta column.
It retains a public tail of oldest entries and extracts their values itself.
The tail is clamped so entry zero, the mutable unit, remains worker-owned.

Each worker receives its own start line and resolves both address candidates
from the immutable plan and original nonce/counter offsets, including the
requester-owned tail. Start records carry the full stored key; forwarded
values live in a separate pool-owned buffer. A separate release
progress word records completed entries and the winner. Sparse stores precede
hashed entries and close the worker boundary, each as soon as its entry's hit
is known. Its newest contents subsume all older stores. A job does not reset
it: a worker reads a word tagged by another job as no progress. A worker
selects permitted candidate pointers in registers, prefetches at most two
entries past its blend cursor (moving the window after every blend; dense
entries go ahead of progress) and blends all available entries before polling
again. Up to 24 columns use explicitly unrolled accumulation followed by a
final permutation; wider ranges extract and blend each bucket. The public
range selects the kernel, with a per-bucket override for comparisons. Empty
ranges issue no value loads, writes or forwarding prefetches but still
participate in every job and completion. Replies up to 56 bytes share a line
with their full-width release completion counter; wider replies use owned overflow buffers. The
requester acquires every completion, assembles bytes without a winner branch,
and only then leaves the reader epoch. A 16-bit progress tag cannot cause ABA:
only one job is outstanding, all completions precede reuse, the requester
rewrites the word before its tag could name a later job (2^16 jobs since its
last store), and full-width sequence exhaustion is refused before publication.

After the operation's formula chooses the inserted bytes, the engine
stages them in the pool's forwarding buffer and writes only key/meta/occupancy
at the public stash slot. Staging right after the join lets that shared line's
invalidations finish before the next start stores, which commit in order
behind them. Every scalar insertion is forwarded, including misses, erases,
writes and tail winners. Each worker of the next job commits its columns
after its address pass, before it blends entry zero and before any
cancellation can return. The requester never reads those columns in
the prefix. Before a full unit freezes, a batch or unprobed write starts, an
explicit executor step/drain runs, or storage is destroyed, an insertion-only
job commits pending bytes and joins. This closes the ownership chain from
worker stores through completion acquisition to prefix publication. Idle
workers alone do not establish committed insertion visibility.

Workers spin for a configurable window, then park. With monitor wait enabled
on a host that has it, a worker monitor-waits instead of parking: it re-arms
and sleeps one OS-capped quantum at a time until a job or shutdown arrives, so
an idle worker never blocks in the kernel and stays runnable. Start stores are
release stores; the requester's side of
the park handshake is one fence and a check of every parked flag per job, in
the join. The worker sets its parked flag and rechecks the start counter
with sequentially consistent operations while holding the sleep mutex. Either
it sees the published job or the requester sees it parked and notifies under
that mutex. No requester operation before the join waits for worker progress.
Requester-written and worker-written state never share a 128-byte line pair (the L2 spatial
prefetcher's unit); worker scratch uses line-aligned allocations. The requester
polls all completion words together, reading the timeout clock only after
4,096 unsuccessful polls. Optional CLDEMOTE hints apply to start and reply
lines; progress is never demoted. Startup failures join created threads;
a worker failure retires the maximum sequence and prevents later accesses.
Cancellation joins every accepted reader before the epoch can close. Workers
allocate no storage on the access path and never retain caller pointers.

Per-thread traces partition the single-thread public column traversal: each worker
loads its entire range from every permitted bucket irrespective of the winner,
and writes its range at every forwarded public slot. The requester publishes
at public entry boundaries and drains at public operation/storage transitions.
Secret winner fields enter only register selects, masks and permutation
indices. Protected-page and instruction-census tests check unconditional loads
and register-only masking; model checks establish logical payload correctness.
Probe audits stay inline and are diagnostic execution. Poll counts depend on
scheduling and memory latency, within the repository's observation model.

Worker storage is allocated at construction. Forwarded bytes, each AES and
candidate array, selected pointers, temporary extraction bytes and overflow
replies are rounded separately to 128-byte pairs. The buffer bill retains
logical sizes as requested bytes and includes that padding in reserved bytes;
start and reply records each reserve a separate pair. As elsewhere, the bill
excludes component-object overhead and thread stacks. Per access, workers
repeat the address pass and split value-line traffic across cores; they do not
reduce the total required loads. Unit freezes and public path transitions add
an insertion-only job when pending bytes exist.

### Access horizon and counter limits

The engine enforces `max_accesses` against online insertion positions, including
blind writes, misses and suppressed batch lanes. Synthetic initialization
positions are excluded. Before a scalar request or complete internal batch
chunk probes or removes records, a subtraction-based check rejects an excess
with `std::overflow_error`. Chunks retain their public lowering widths; an
over-budget chunk is refused intact, with earlier chunks and their replies
committed. A smaller retry may use the remainder. Composed callbacks check all
their accesses before invoking user code. Exhaustion does not mark the state
corrupt or prevent draining accepted work; pending payload bytes can finish
before a new request is refused.

Scalar and batch probes share a checked dummy-counter reservation. It reserves
one counter per lane and absolute plan-table position, including unused dense
positions, before address generation or output writes. Division checks the
remaining range before multiplication or addition; a refusal leaves the counter
unchanged. Successful reservations are never refunded, even if later work
throws. Active lane/table offsets therefore stay in their reserved, disjoint
64-bit ranges. This is an input-counter guarantee, separate from wide routing's
encoding and cryptographic assumptions. The access guard also checks addition
to the physical position counter.

Before table allocation, `RequireLifetimeFits` checks a physical-position bound
`P = initialization_offset + max_accesses`, reserving direct initialization even
for an empty start. For each level with carry span `C`, the next possible
preparation has ordinal `v = floor(P/C) + 1`. Both `v` and its complete window
end `v*C` must fit the 48-bit family field and 64-bit position field,
respectively. Canonical forwarding preserves the window end and decreases the
ordinal. The check therefore covers speculative preparation without adding a
runtime allocator or changing family assignment.

The same bound covers dense windows and IDs. At level one, write `C = r*u`,
where `u` is the unit size and `r = prefix_flushes <= 8`. The largest flush
count `f = floor(P/u)` satisfies `f < r*v < 2^51`; flush and prefix counters
therefore fit the 55 bits available before their eight-bit ID shift. The
padded current-unit end `(f+1)*u <= v*r*u` fits the checked window, including
the next empty unit exposed by draining the last full unit. The publisher
separately refuses to allocate a hashed-table ID pair reaching bit 63, which
belongs to dense IDs. Unsupported lifetimes throw before table storage is
allocated. These arithmetic guards do not bound normalization or primitive
calls, or establish native execution correspondence.

### Normalization budget

Access positions cannot count every use of the normalization key: callers can
convert a key with `StoredKey`, and initialization or an access can fail after
conversion. The engine therefore keeps one separate, nonrefundable reservation
counter. `max_key_normalizations` sets its limit `B`; when unset, the limit is
`Capacity() + max_accesses`, checked for overflow. One full initialization and
an ordinary run fit that default. Additional conversions and failed attempts
consume the same allowance; deployments needing retries can select a larger
limit at construction. No rekey or automatic reset is performed.

Widths below sixteen are stored verbatim, use no AES normalization and consume
zero reservations. At widths of sixteen or more, `StoredKey`, including a
standalone const call, reserves one input before AES. Scalar byte APIs first
check the access horizon, so an already exhausted horizon spends no
normalization budget. Initialization reserves its complete count before reading
the iterator; even an iterator exception retains that reservation while rolling
back the logical state.
Each probing batch chunk reserves all its lanes on the requester before
dispatch. Workers only convert those admitted inputs and never update the
counter. Blind batch writes use scalar admission. A callback checks its full
one- or two-conversion cost before looking up the source or invoking user code;
a thrown callback restores the source with the already stored key.

The single-requester/no-reentry contract also applies to `StoredKey` and budget
inspection. A check compares the requested count with `B - used` before adding,
so refusal leaves the counter unchanged and a successful reservation cannot
wrap. Every normalization belongs to exactly one reservation, with at most the
reserved number of conversions performed. Induction over reservations gives
`Q <= A <= R <= B`, where `Q` counts distinct inputs, `A` actual conversions,
and `R = KeyNormalizationCount()` reserved inputs. Repeated keys are charged
again; no per-key set is stored. Unused reservations can make both inequalities
strict. `MaxKeyNormalizations()` exposes the resolved limit.

The checked `NativeNormalizeTrace` interface ([Spec/NativeNormalize.lean](../../../lean/RebuildBound/Spec/NativeNormalize.lean)) consumes a compact list of actual
conversions in the random-function hybrid (the proof game in which encryption
under the normalization key is replaced by a random function). The source has three calls to
`EncodeReservedKey`: `StoredKey` after reserving one input, the initialization
scatter after reserving `count`, and byte-key `LoadBatchLane` after reserving
the chunk's `m` lanes. Include every computed key/fingerprint pair, even when
initialization rolls back or a later operation fails. Unused reservations add
no entries; retries append their conversions. Parallel batch lanes may be
enumerated in lane order for the proof because their input keys are already
chosen before conversion results are available. This order need not be their
wall-clock completion order.

The theorem in [Proofs/NativeNormalize/Trace.lean](../../../lean/RebuildBound/Proofs/NativeNormalize/Trace.lean) (premises in [LEAN_CLAIMS.md](../../../analysis/bound_certification/LEAN_CLAIMS.md)) identifies such a list with the Lean collision proof's causal replay (finite causal query recursion) from a
local next-conversion equation and its length bound `A <= B`. Unused conversion
slots form a suffix; repeated keys keep the proof's fresh-padding treatment.
This gives the collision bound at `Q = B` without counting internal execution
steps. Constructing this native trace and its measurable
causal chooser, with an independent environment in the cryptographic hybrid,
remains an execution-correspondence obligation. This source inventory does not
establish those premises or a native collision bound on its own.

For fixed key width `u`, actual AES block encryptions under the normalization
key are at most `B` for `u = 16`, and at most `m*B` for `17 <= u <= 64`,
where `m = 1 + ceil(u/16)`. These are mathematical integer bounds, not wrapped
64-bit products. Both initialization and failed attempts are included. The
[cryptographic reductions](../../crypto/DESIGN.md) can therefore use `Q = B`
as a conservative normalization query bound. They still require their entropy,
exclusive key-use and observation premises. Routing has the separate allowance
below; elapsed time and concrete execution refinement remain separate obligations.

### Routing budget

`max_routing_evaluations` caps complete routing-message evaluations at `R`,
including repeated messages and SIMD padding. Its default, `UINT64_MAX`, is an
arithmetic ceiling, not a recommended cryptographic budget or a promise that the
declared access horizon will complete. A deployment can choose a smaller limit
at construction. No reset, retry allowance or automatic rekey is provided.

One `RoutingEvaluationBudget` belongs to the engine. Its routing schedule lends
that same counter to every requester, value worker, batch participant, rebuild
owner and helper. The two leaf tag routines reserve before any encryption:
`AesBatch32Regs` reserves 32 evaluations and executes 33 AES blocks (one shared
prefix and 32 second blocks); `AesTagsInterleaved` reserves its message count
rounded up to four and executes two AES blocks per reserved message. Both VAES
and AES-NI paths use these rules. A full bucket calls the former twice, reserving
64 evaluations for 66 AES blocks. There is no extra charge at a delegating wrapper.

This placement includes all stored slots, dirty dummy slots, real/dummy probe
candidates, padding, speculative rebuilds, repeated value-worker computations
and initialization routes, even when initialization fails. Counters are not
part of initialization rollback. Standalone tag fixtures without a hierarchy
schedule have no allowance; the separately seeded tree position generator is
outside this hierarchy contract.

Each successful atomic compare/exchange adds at most `R - used`; a failed
comparison retries with the current count. Thus the counter never wraps or
exceeds `R`, even with concurrent workers. With the default `R = UINT64_MAX`,
reservations of at most `2^32` evaluations cannot approach the limit, so each
thread adds them to its own cache-line counter instead of contending for the
shared one; `RoutingEvaluationCount()` sums these counters and stays exact. A
larger reservation switches the budget to the single exact counter for good,
and a sequentially consistent flag orders the switch against every per-thread
addition, so none is lost (`cpu_byteslice_routing_budget.hpp`). No reservation is refunded. Every
executed routing message belongs to a reservation, so
`distinct messages <= evaluations <= RoutingEvaluationCount() <= R`, and
physical routing AES block encryptions are at most `2R` (a mathematical integer
product). The two master derivation calls and normalization blocks are separate.
`MaxRoutingEvaluations()` exposes `R`. The same conservative `q = R` is available
to the CBC reduction, which memoizes repeated messages; the actual repeated
work still contributes to its simulation time. No elapsed-time bound follows
from the counter: scheduling, waits and client callbacks remain separate.

A refused reservation leaves the count unchanged and latches a permanent stop.
It throws `std::overflow_error`; `Failed()` reports the stop, and subsequent
access, initialization, batch, owner-start and drain calls reject. The engine's
worker exception handling joins participants and propagates failure. Operations
already in flight may finish or be interrupted; their reservations remain
charged. In particular, exhaustion during a rebuild or value-worker operation
may leave accepted work incomplete. The instance must then be discarded; there
is no smaller retry, rollback or drain guarantee. Reaching the limit exactly
does not itself stop the engine until another positive reservation is refused.

This is source-level admission accounting, not a proof of C++ execution or
observable-trace correspondence. The allowance bounds the query argument in
the cryptographic reduction; it neither supplies AES advantages nor
meets the total native error target. In particular `R = 2^32` already gives the
conservative routing statistical term `2^-61`.

### Certification report

The capacity planner chooses a geometry by bytes and stated rules; it does not consult the failure-probability analysis in `analysis/bound_certification`. [The certification lookup](cpu_byteslice_level_arena_certification.hpp) reports what that analysis says about the geometry a plan or a map was built with, and never refuses one. `CertifyLevelArenaGeometry(params, max_accesses)` returns `kCertified` when a covered record matches and its composed conditional bound is at most 2^-64, `kAboveTarget` when a record matches but its bound is above the target (this certifies nothing, and does not show that failures are frequent), and `kNotCovered` otherwise. It also returns the bound as `ceil(1000 log2 bound)` (rounded up from the exact rational), the record's horizon, and a reason naming the first requirement that failed, such as an unsupported capacity, an excessive horizon, or differing stash or tier widths.

A record applies when B, s, q, L, r0, D, the fanout ladder, the per-level tier widths and the per-level stash depths that `LevelArenaStashSizing` gives at the caller's horizon all equal the record's, and the caller's horizon is at most the record's. `bank_first` must be `kNoClone`. With identical sizing, a shorter horizon runs the same jobs with the same per-job bounds no more often, so the recorded lifetime bound still holds. A shorter horizon whose sizing differs is a different shape and is not covered. The value width, the key width and the scheduling knobs (threads, groups, helpers, lanes, batching) do not enter any job's shape.

Every bound is conditional on the certification checker's undischarged premises. With those premises undischarged, the unconditional bound is still 1.

The records live in a generated file, `cpu_byteslice_level_arena_certified_bounds.inc`, written by `analysis/bound_certification/code/export_certified_bounds.py` from every `configuration_space_2p*.json`. The script refuses inputs whose recorded source hashes no longer match the tree. `--allow-stale` writes a development table that marks every reason. `--check` fails if the file is out of date. The certification artifacts record the hashes of the engine headers that decide job shapes and stash sizes ([source_scope.py](../../../analysis/bound_certification/code/source_scope.py)), so an edit to any other header stales nothing; `regenerate.py` there recomputes only stale artifacts. No probe may compile against the lookup header and its table, which are generated from those artifacts: only `include/cpu_byteslice_oram/byte_map.hpp` includes them. The export script (`g++ -MM` for each probe) and `cpu_byteslice_level_arena_certification_test` (a lexical include scan) both fail if a probe reaches either file. `ResolvedPlan::certification()` and `hierarchy_certification()`, the plan choices `certification`, `failure_bound_log2` and their `hierarchy.` or `position_map.` twins, and `ByteMap<true>::certification()` expose the report. The choices are left out of the configuration key.

Observable dimensions include public geometry, request count, batch size, publications and worker scheduling. Security depends on secret hash keys, nonce-family discipline, fixed public work bounds and correct compiled masked kernels. The implementation does not encrypt bucket contents at rest. Probe audits and correctness tests provide evidence for particular invariants, not a complete trace-noninterference proof.
