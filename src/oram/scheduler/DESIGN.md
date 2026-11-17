# Rebuild planning design

The scheduler layer translates rebuild phases into kernel invocations while
preserving routing order and residual freshness. It does not decide when a
level owns a worker, how publication occurs, or when requests wait. Those
policies belong to the [engines](../DESIGN.md). The arena plans each phase
at saturated widths and runs it through a resumable cursor at the executing
group's widths. Widths bound work between stopping points; indivisible
kernels and differing per-unit costs prevent a hard wall-clock bound.

The kernels and their vocabulary are defined in the
[rebuild design](../rebuild/DESIGN.md): a *residual* is a record that a
routing stage could not place in its bucket and *sheds* into a fixed-capacity
residual stash; *DFS distribution* partitions the pooled residuals into
public-capacity coarse ranges
([Public-capacity DFS distribution](../rebuild/DESIGN.md#public-capacity-dfs-distribution));
and an *offer* (second-chance sweep) gives each range's records the free
slots of the main buckets that range covers
([Recover residuals without revealing their homes](../rebuild/DESIGN.md#recover-residuals-without-revealing-their-homes)).
A *phase* is one rebuild step over a level (a copy, a route, an absorb or a
merge), and a *lane* is one independently runnable share of a stage.

## Preserve the algorithm while separating execution

[Subtasks](cpu_byteslice_subtask.hpp) describe public ranges and kernel
parameters. The [phase planners](cpu_byteslice_subtask_plan.hpp) emit them in
the same order as the monolithic kernels, and the
[dispatcher](cpu_byteslice_subtask_run.hpp) supplies the corresponding views,
nonces, and scratch. The level-arena engine uses these kernels while retaining
its own publication and worker-ownership policy.

Order is part of correctness. Butterfly recursion determines which routing
bits have already been consumed, and residual insertion can depend on which
source reaches a shared stash first. A planner therefore mirrors the kernel's
recursive split and leaf rule. An indivisible leaf can exceed a requested
slice width. Widths describe scheduling units, not a hard time bound.
Planning saturates the widths and the cursor below cuts pieces at the
executing group's; cutting moves work between invocations without removing
any routing work.

## Resume a phase from a stored position

A phase that must stop partway cannot be a planner recursing on the
executing thread's stack, because the thread has to return and a later call,
possibly on another thread, has to continue. So the arena plans a phase once
at saturated widths into a list sized when its job is built. That list holds
coarse descriptors for public ranges, copy tiles and butterfly blocks. It
does not materialize one descriptor per execution piece.

A [phase cursor](cpu_byteslice_subtask_cursor.hpp) runs the list in pieces.
A range piece is a sub-range at the width the planners would use at the
executing budget (`PieceUnits`). A butterfly piece is a leaf of
`SubnetworkWalk`, an explicit-stack walk of the planner's own recursion with
the same split and leaf rules and the same order. The cursor stores the task
index and, inside a butterfly block, O(depth) recursion frames. After every
piece that leaves work behind it asks its caller whether to stop. Running
the pieces in order issues the kernel calls the whole phase would, so the
output does not depend on the budget or on where the phase stopped.

## Divide a stage into lanes

The planners also mark stages (`MarkStage`, `MarkLaneUnit`) for sinks that
keep them; other sinks ignore the marks. A stage says whether lanes may
divide it and how. By task, each unit is a run of tasks, such as a copy tile
with the sub-networks that route it. By range, the stage is one task whose
public range is divided into contiguous intervals. The mark also
names the stash slots the stage sheds into and the offer passes whose range
masks require private lane copies. Offers only clear masks and each candidate names one main
bucket, so ANDing those private masks at the stage boundary combines
consumption by disjoint lanes. The untiled copy-then-route
spells out its root's first split for the same reason: one butterfly task per
block could not be divided.

A lane runs its units in order against a private shed stash array, and the
stage ends with a checked fold of every lane's stash into the phase's, in
lane order. Stash insertion appends to the lowest free slots, so the fold
reproduces the stash a one-lane stage builds. `StageLanes` chooses the lane
count from the plan and the configured maximum, never from the thread count.
The one-thread cursor runs a stage's lanes back to back, and the level arena
job runs the same lanes on several threads (`LaneCursor`, claimed through an
atomic word).

## Units must match the kernel

The [budget helpers](cpu_byteslice_subtask_cost.hpp) distinguish copy buckets,
retag buckets, cross-source pairs, radix tuples, and residual scatter groups.
These are not interchangeable units. A scatter group with fanout `f` writes
`f` buckets, so a bucket budget must divide by `f` before becoming a group
count. Likewise, an `r`-way radix tuple uses work quadratic in `r`; the helper
charges `ceil(r^2/2)` binary bucket-touch units, giving 5, 13, and 25 at
`r = 3, 5, 7`. This is an analytical scheduling currency, not a measurement
of elapsed time or an admission control mechanism.

Copy/retag fusion and residual-offer fusion change the work within a unit.
Their planners retain the geometry and order required by the kernels while
using the corresponding combined unit. The eliminated traffic and tag work
are derived in the [rebuild design](../rebuild/DESIGN.md). Scheduling those
kernels does not independently multiply their savings.

## Validate residual ownership before execution

A residual pass combines sources of different freshness and may clear their
occupancy during deduplication. The
[residual-pass builder](cpu_byteslice_residual_pass.hpp) therefore accepts a
declarative source list, ranks, owned prefix, drain-only prefix, deduplication
rule, and optional fusion site. It validates those relationships centrally.
The caller supplies the predicate identifying published mask arrays because
only the engine knows what a request thread can currently read.

Ownership here means mutable occupancy, not necessarily private payload.
A descriptor with private masks may borrow pinned immutable payload, but
cannot serve as a writable drain. Sources that deduplication can clear must
not alias occupancy exposed to readers. Equal-rank sources must be disjoint,
and class-marked sources must satisfy the required suffix ordering. These
constraints prevent silent loss or resurrection of records.

Range sizing and attachment are separate operations: the builder computes
required scratch geometry, then attachment rejects a view of the wrong size.
When offers run inside a final routing phase, that phase can shed records
after the range table has been built. Those late sheds must occupy the
validated drain-only prefix; treating them as swept sources would reset
records that the sweep never saw. Only one active pass may fuse at a given
site, and its leading drain-only source must be that site's shed stash. Successive sites may reuse scratch
after the preceding pass has drained and reset it.

The pass shape depends only on public capacities and freshness ranks.
Occupancy, key matches, and overflow counts cannot choose the task sequence.
The engine must additionally enforce source pinning, publication, and worker
ownership. It also binds a DFS workspace for every distributing range plan; direct and
empty plans require no distributor. The public DFS unit list is executed in
order, with no allocation or occupancy-dependent choice of pieces.

Maintain this document by editing the relevant explanation directly, following
[documentation maintenance](../../../DESIGN.md#documentation-maintenance).
