# Direct-job reference contract

The Core-only direct-job models execute all supported digits through
`runJob`, which validates geometry and original inputs before execution.
`runDigitOne` remains the digit-one API and rejects later digits with
`requiresLaterPhases`; `buildB`, A preparation/distribution and finish are
internal phase functions with explicit contracts. `DirectJobPublication` and
`DirectJobFailure` prove whole-job publication and failure behavior. This
mapping records native correspondence targets, not completed native proofs.

## Geometry and input boundary

`U = 2^K` is positive by construction; supported digits are 1 through 8.
Output main has exactly `digit * U` homes, each of capacity 64. Capacities in
this reference are record counts, including zero for boundary controls. Native
output tiers instead have 1 through 8 whole 64-record pages. Below-64 fixtures
are reference controls, not claims of native fixture coverage. Native arena
prefix shape also requires `U = 2*r0*s`, `r0 ∈ {2,4,8}`, and power-of-two `s`;
that additional restriction is a native source-layout adapter obligation.

A main has `(digit-1)*U` buckets of exactly 64 lanes. Main and old tier jointly
have unique keys; the tier fits `aTierCapacity`. Main records have their previous
digit homes under the separately supplied old word family. At digit one A is
absent, including its tier and route pool. Current routing is the existing
`digitHome`, including the odd-radix mapping. `DirectJobHome` proves its modulo-U
law for all words. There is one current word function per key, shared across
all versions; no randomness or finite-word uniformity premise is used.

Prefix units are chronological logical flush units, possibly empty, cleared,
holed or multi-bucket. Each unit has unique keys; `Inputs.Valid` rejects a
unit with a repeated key. The native dense builder does not check this and
relies on the requester
(`levelarena/cpu_byteslice_level_arena_dense.hpp:279-290`), so it is a native
obligation next to exact comparison. All B units are newer than A.
Ranks and surviving occurrence indices are derived from list order, never
trusted from a fixture. Full `Rec` values carry key, value identity and tombstone.
`DirectJobBIndices` proves restored winner indices are in range; no successful
proof relies on the default record used by the total-lookup API.

Insertion capacity must be at least output capacity.
`copyCapacity` occurs only in `Geometry.Valid`; no model function reads it, so
the lane-copy premise is native scope. `LaneFold` proves separately that lane
copies at least as wide as their phase stash add no failure (W10).
At later digits the B tier is exactly 64 regardless of output capacity. Route
and radix capacities remain separate. The A pool bound counts bit stashes,
optional radix stash and old tier; digit one has no A pool. A direct range plan
is allowed only at at most 8 output homes or zero public pool capacity. A DFS
plan requires more than 8 homes, coverage by its padded range tree, and its
exact public A pool capacity. DFS operations use one-page leaves.
Exact native range-bit selection, finite index/word widths and the bound on
index bits remain adapter obligations. The A-phase implementation executes
direct and DFS plans with these exact record capacities and proves stable distribution and full-record conservation.

## Observable order and checks

The complete job order is prepare complete A with blank B region,
produce B, distribute operational A, finish B-main insertion and ordered offers,
resolve leftovers, drain, publish. Digit one executes only production and
publication. Preparing A may not inspect B. The B adapter reuses chronological
mask deduplication, the stable home scan and source-order remainder
drain; it does not replace the complete job with final-home redistribution.

A logical event has phase, site, zero-based ordinal, attempted occupancy and
capacity. B uses `.produceB/.outputTier` at digit one and `.produceB/.bTier`
otherwise. Its ordinal counts logical chronological units, including empty and
cleared units. The first failed append returns an event and no table. Analytical
execution uses the same update/event, keeps overflowing records and continues.
It is a separate type from publishable storage. The registered simulation proves
exact logical first-event identity and equality of successful states. Pauses
are covered by the whole-job cursors of `DirectJobResume`.

B main uses compact occupied records with implicit trailing holes, stable within
each home; tier uses original source order (`DirectRecordsTierOrder`,
`DirectJobBTierOrder`). `bLanes` restores trailing holes for the implemented
finish. Routed A lanes retain their actual holes and publish through the
separate lane-preserving `LaneResult` representation.

## Native check mapping (correspondence targets)

The table is a correspondence target, not an existing native theorem.
Paths below are relative to `src/oram/`; line anchors refer to the revision
the table was read from and may have shifted.

| Native operation | Logical phase/site | Identity and order restriction |
| --- | --- | --- |
| `kDenseDrain` (`scheduler/cpu_byteslice_subtask_run.hpp:407`) | produce B / output tier or B tier | Native source-bucket appends versus reference unit appends require chunk/batching normalization; first failing class is the comparison boundary until then |
| Butterfly/subnetwork and route continuation (`subtask_run.hpp:412,524`) | prepare A / route bit and continuation flag | Retain the native ordered A schedule; fused pair checks need batching correspondence |
| `kRadixRouteRange` (`subtask_run.hpp:643`) | prepare A / radix | Ordered tuple stream; normalize fused range tasks |
| `kResidualDfsPartition` (`subtask_run.hpp:726`) | distribute A / DFS | Reference node identity only; native preorder and paired-child checks require a traversal adapter |
| `kFixedMergeOffers` / `kFixedMergeRange` | finish / insertion | Fused path checks at last way; fallback checks every way; normalize to source-bucket check class before comparing |
| `kResidualDrain`, range prefix (`subtask_run.hpp:741`) | drain / output tier | Range-leftover order; padding/scratch contents are not output |
| `kResidualDrain`, drain-only suffix (`subtask_run.hpp:760`) | drain / output tier | Insertion-leftover order after ranked duplicate resolution |

A native bridge must not infer an exact native DFS node or instruction index
from equal failure verdicts. Failed jobs may leave private scratch writes;
publication is unavailable until every required check passes.

Source anchors: `levelarena/cpu_byteslice_level_arena_merge.hpp:141,748`
(geometry and phase order), `cpu_byteslice_level_arena_pass_shape.hpp:94,342`
(ordered pool and widened insertion/copy stores),
`cpu_byteslice_level_arena_geometry.hpp:766,779` (prefix/tier restrictions),
`rebuild/cpu_byteslice_residual_range.hpp:174` (direct branch),
`cpu_byteslice_dfs_residual.hpp:76,819,927` (range plan, traversal, paired checks),
`cpu_byteslice_second_chance.hpp:932,1055` (insertion batching), and
`levelarena/cpu_byteslice_level_arena_job.hpp:1026,1941` (lifecycle).

## A preparation and distribution

Preparation's arguments contain only geometry, current words and A main. It
executes ordered pair operations from `engineOps`, then ascending radix tuples.
Logical ordinals count this combined operation stream; radix ordinals do not
restart. Each pair checks its bit stash against `routeCapacity`, each radix
tuple checks the radix stash against `radixCapacity`. The first blank
continuation has a guaranteed-passing logical zero-occupancy event; native code
can omit its stash access, so accounting for it is a native ordinal adapter
obligation. Bounded execution stops before executing the next operation after failure.

Analytical state is retained after overflow and is not a publishable table.
Main plus stage sheds, radix sheds and old tier is a permutation of original A.
The residual order is stage stashes by bit, radix stash, old tier. Filtering B-tier
keys occurs only after preparation/production. B-main keys are retained for the
finish's original-source freshness handling, including shed tombstones.

Direct distribution yields `[pool]` without capacity events; finish selects
this sole list for every home. DFS yields stable coarse-range leaves and
reference-local depth-major padded node checks, with ordinal across all nodes.
It tests `min(poolCapacity, 64 * 2^height)`. The public range plan, not
`aTopology.I` or `.rangeBits`, controls distribution. Distribution failure returns
only an event, while analytical leaves remain separately available for witnesses.

The proved count domination is operational pool to completed unfiltered A,
for any Boolean record predicate and any B tier. `DirectJobExposure` proves
ordered-prefix read-mark dependence. `DirectJobABounds` connects these witnesses
to the S4a/ST4a, ST5/ST6 and SG2 results with their original capacity,
geometry and early-truncation premises. Native source/history applicability
remains separate.

## Separated finish execution

`DirectJobFinish.lean` defines `runJob` for all supported digits, with
structural validation before execution and a separate `LaneResult` publication
type. `runDigitOne` and the phase oracles keep their own interfaces.
`finishTopology` changes only the range fields of `aTopology`: direct plans use
one leaf covering every home, and DFS plans use their declared index/range bits.
The adapter's validity, home equality and exact agreement with distributed leaves
are proved. Producer main records acquire trailing empty lanes; routed main
lanes are never compacted. The immutable B table remains an argument throughout
insertion, independently of where its records subsequently reside.

Each logical finish transition inserts one B source bucket with `sInsertBucket`:
clear A-main copies of its keys across all destinations, then process ascending
ways, inserting B, offering A, and offering the standalone B tier. Sheds append
in way order. Its event is `.finish/.insertion`, ordinal equal to the ascending
source index, occupancy equal to cumulative insertion length, and capacity equal
to `insertionCapacity`. Offers do not modify that occupancy. This is an atomic
source-bucket observation: on failure private final-way offer writes can have
occurred, but no later source bucket executes and no output publishes. It is not
a claim of instruction-level stopping before native last-way offers. Native
fallback per-way and fused last-way checks still require the stated normalization.

Drain first checks each A leaf in range order, then the B-tier list, including
empty chunks. All events use `.drain/.outputTier` and `outputCapacity`. Ordinals
restart at zero for drain. A-class leftovers matching insertion keys are then
cleared in place, B-class leftovers remain unchanged, and insertion records
matching B-class leftovers are removed. The final append fills the cleared holes
before extending the tier; its ordinal is the number of preceding logical drain
chunks. Native bucket-level appends still need chunk normalization. The model
preserves tombstones throughout. Trailing output lanes are padded only after
successful drain; analytical tiers may exceed the capacity and are never passed
to publication by the bounded runner.

Registered proofs establish exact insertion refinement to the existing ordered
scalar separated operations, bounded/analytical agreement and logical first
failure, failure class/capacity and B lane padding. The
analytical finish takes its tier and drain events from the separated `sDrain`
(the drain refinement is definitional), and `DirectJobFinishDrainSimulation`
states that the bounded drain is `sDrain` stopped at its first failing event.
The `DirectJobBridge`, `DirectJobFinishCorrectness` and
`DirectJobFinishBounds` packages construct the producer-to-separated input
adapter and prove newest full-record conservation, uniqueness,
placement/saturation, exact excess and every insertion/drain bound from
original valid inputs and successful B production. The analytical results
allow A and finish overflows. `DirectJobPublication` transfers correctness to
all-digit successful publication, including exact main and output-tier widths.
`aTopology` sets B page metadata to one (no model function reads it), so
`finishTopology` is the comparison topology; proved exact operation equality
preserves the direct runner's slot capacities and range-plan semantics.
`DirectJobFailure` also proves unconditional whole-job analytical simulation,
first failure, no publication on failure and witness containment;
`DirectJobExposure` proves ordered transcript dependence. Public atomic theorem
assembly, the shared probability adapters and whole-job cursor/resume
(`DirectJobResume`) are proved. Native correspondence and
source/history applicability are separate open refinements; they do not require
reimplementing the phase algorithms.
