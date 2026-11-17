# Lean claims

This page maps each claim of the Lean formalization (`lean/` at the repository root) to its theorem,
premises and supporting evidence. Build and audit instructions are in
[lean/README.md](../../lean/README.md); the mathematics is in [REPORT.pdf](REPORT.pdf);
terms (level, digit, carry, A/B, family, tier, window, start) are defined in
[README.md](README.md#terms).

Summary. For all 94 standard `D=8` planner geometries at capacities
`2^11..2^31`, from initialized and empty starts, capacity failure and simulator
distance are at most `h * 2^-64` across `h ≥ 1` windows of `2^32` accesses. The
canonical engine model uses exact byte-string keys. `IdealApiFamily`,
`IdealCapacity` and `IdealApiOblivious` establish this from legal adaptive
requests and logical live capacity, with no key universe or encoding bound.
Independent countable client seeds are covered by `IdealApiSeedExact`,
`IdealSeedCapacity` and `IdealSeedOblivious`. `IdealApiBounded` and
`IdealSeedBounded` bound incorrect actual API results under explicit adapter
agreement off reference capacity failure.

The `NativeMatch*`, `NativeRouting*`, `NativeNormalize*` and `NativeKey*`
packages (18 refinement packages) connect a finite operational model of the
native matcher, routing encoding and stored-key normalization to these ideal
endpoints. Cryptographic substitution, normalization lifetime allowances,
completion stops and compiled native correspondence remain explicit
premises. The hierarchy derives routing and normalization keys from two
distinct master-AES labels; the [key-separation reduction](../../src/crypto/DESIGN.md)
costs a two-query AES-PRP advantage plus `2^-128`. Routing uses an unambiguous
fixed two-block CBC message for the full stored key and labeled identity, with
an explicit CBC PRF reduction that also applies to fixed-width normalization
above sixteen bytes. These reductions are stated in
[ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md); they are not Lean theorems, and
they do not by themselves establish a total native `2^-64` target.

Besides the canonical endpoints, the library exports fixed-geometry `*31`
statements, fixed-universe `Generic*31` statements and fixed-universe family
interfaces. They keep their own (stronger) premises and are listed below for
completeness; the canonical endpoints do not depend on their restrictions.
The model's design choices are explained in
[The model and the engine (P8)](#the-model-and-the-engine-p8) and
[Adaptivity and obliviousness](#adaptivity-and-obliviousness).

## Configuration-family capacity and privacy

The [public inventory](../../lean/RebuildBound/Spec/ConfigurationFamilyData.lean)
contains 94 compact parameter records. One constructor derives all direct,
separated, preparation, initialization and finish shapes. The numerical
family fixes bucket capacity 64, load 32, `D=8`, automatic tier/stash sizing,
and the standard `B=8, s=1, q=2` candidate domain; arbitrary top-digit or tier
pins are outside this claim.

| Export | Claim and explicit boundary |
| --- | --- |
| `IdealApiFamily` | Canonical arbitrary-byte-key reference correctness, exact probe simulation and `h * 2^-64` capacity failure, from valid initialization, public geometry/schedule and logical capacity on every legal observation branch. |
| `IdealApiOblivious`, `IdealSeedOblivious` | The same eventwise simulator error for observations explicitly agreeing with the reference off failure; independent countable seeds can have unbounded support and seed-dependent initialization. Native agreement is a separate hypothesis. |
| `IdealApiBounded`, `IdealSeedBounded` | Incorrect actual API results have outer measure at most `h * 2^-64` over `h ≥ 1` windows of `2^32` accesses, under explicit agreement of actual history, issued requests and selected results off reference failure. Correctness includes public request count, all logical prefixes, scalar/batch replies and probing addresses. |
| `ConfigurationFamilyStructural` | The decidable structural contract holds for every member from either start. Generic lookup, API and exact-law exports then apply. Empty-start lookup requires `run.init = []`. |
| `ConfigurationFamilyAnalytic` | Causal first-failure probability is at most the horizon multiplier times the exposure sum of actual direct, separated and top analytic bounds. No numerical matrices enter this proof. |
| `ConfigurationFamilyNumerics` | Every initialized member's exact class-weighted budget is at most `2^-64`. Full geometry equality and coverage are checked; missing rows or certificates default to one. |
| `ConfigurationFamilyCausal` | For either start and every `h ≥ 1`, the causal reference failure probability is at most `h * 2^-64`, under the trace, unshadowed, causal exposure and joint ideal-tape premises. |
| `ConfigurationFamilyWindows` | The same bound for fixed runs and adaptive clients. The fixed run is independent of the words; adaptive clients satisfy the public shape/schedule and admissibility requirements on every branch. |
| `ConfigurationFamilyOblivious` | Scalar, batch and adaptive simulator distance is at most `h * 2^-64`, with one fixed run-wide key universe and explicit observation agreement off failure. |

The `Ideal*` exports are the API claims. `ConfigurationFamilyCausal`,
`ConfigurationFamilyWindows` and `ConfigurationFamilyOblivious` are
fixed-universe interfaces; their supplied-law premises do not constrain the
canonical endpoints. The structural and numerical family certificates are
shared support for both.

[Statements](../../lean/RebuildBound/Spec/ConfigurationFamilyCertification.lean) and
[proofs](../../lean/RebuildBound/Proofs/ConfigurationFamilyBound.lean) share the same
local bounds. The empty-start identity removes exactly initialization, so no
second numerical certificate is needed. Direct nonempty A pools retain route
and radix events and have no range event. Source populations use their actual
128/256/512-record loads, with exact finite-word density factors and no
conditioning on previous success.

The 220 native role keys reduce to 24 direct, 133 separated, 21 finish and
23 complete preparation/initialization shapes (some role keys share a shape).
The final rational checks use conservative dyadic budgets; they do not assert
equality with Python's tighter conditional estimates. Fresh field comparisons
and mutation tests link the native fixtures to the public member list. They
provide finite implementation evidence, not a proof of the planner search,
native execution refinement, AES security, or unrestricted key churn.

## Generic semantics and fixed-universe exports

The arbitrary-key path uses
[ApiLegalStructural](../../lean/RebuildBound/Spec/ApiLegal.lean) for deterministic
request correctness and [IdealApiExact and IdealApiSeedExact](../../lean/RebuildBound/Spec/IdealProbe.lean)
for exact simulation. These use the smaller structural/initialization premises,
without logical live capacity or a numerical certificate. The
[IdealGeometry exports](../../lean/RebuildBound/Spec/IdealGeometry.lean) add generic
analytic capacity, window scaling and observation transfer under explicit
arithmetic and exposure certificates. The fixed-universe interfaces below keep
their own restrictions.

[HierarchySemantics](../../lean/RebuildBound/Proofs/HierarchySemantics.lean) is a
semantic root with no numerical-certificate or finite-family inventory
imports. Its [trusted statements](../../lean/RebuildBound/Spec/HierarchySemantics.lean)
quantify over any geometry satisfying the decidable
[structural contract](../../lean/RebuildBound/Spec/HierarchyStructure.lean).

| Export | Claim and premises |
| --- | --- |
| `HierarchyLookup` | Scalar and batch latest-supplied-value correctness and address agreement for arbitrary tapes; the run/schedule conditions plus `cfg.initialized = false → run.init = []`. |
| `HierarchyUniverseLookup` | The same lookup guarantee for keys with `key.toNat < 2^64` in one fixed run-wide universe bounded by the geometry's key capacity. |
| `HierarchyFixedSemantics` | Fixed-run scalar/batch pattern independence, freshness, exact simulator law under the joint ideal tapes, and observation transfer with error equal to actual failure probability. |
| `HierarchyUniverseSemantics` | Fixed-universe key transport of the exact laws and actual-failure observation transfer. |
| `HierarchyAdaptiveSemantics` | Exact measurable adaptive transcript law and actual-failure observation transfer; one fixed universe across every branch, public shape/schedule and joint tape premises. |

The contract checks actual direct/separated/top geometry and finite arithmetic;
it assumes none of these conclusions. Both starts are supported. All 94
manifest members and a capacity-1024, `D=4` geometry outside the numerical
family instantiate these exports. These are reference-model statements;
observation transfer still requires explicit agreement off failure. They
supply no family failure-probability bound or universal native refinement.
[HierarchyApi](../../lean/RebuildBound/Proofs/HierarchyApi.lean) adds six semantic
exports under the same contract, with [separate trusted statements](../../lean/RebuildBound/Spec/HierarchyApi.lean):

| Export | Claim and premises |
| --- | --- |
| `HierarchyBatchFound` | The complete selected record, including tombstone and flag bits, is independent of routing/dummy words under the fixed-universe batch setting. |
| `HierarchyFlagSoundness` | The local flag rule under any one word tape implies the unshadowed promise; structural trace/schedule premises and consistent empty history are explicit. |
| `HierarchyBatchApiCorrectness` | Local API post-record construction and the batch setting imply all-prefix maps, replies and address agreement, for either start. |
| `HierarchyApiAdmissible` | Structural caller premises and local API construction derive the batch setting, including its unshadowed promise. |
| `HierarchyAdaptiveFlagAdmissible` | One fixed universe, public shape/schedule and the flag rule on every replay branch derive the adaptive setting. |
| `HierarchyAdaptiveApiCorrectness` | The adaptive setting and local API construction on the realized run imply its all-prefix map, reply and address correctness under arbitrary tapes. |

The flag/API exports require consistent empty history for empty starts.
All 94 family members instantiate them from both starts. The capacity-1024,
`D=4` API witness derives its own setting and exercises a flagged erase,
duplicate-key forwarding and a realized adaptive chunk, including schedules
with no table or the empty top. Both roots have no numerical imports.

[ApiBounded](../../lean/RebuildBound/Spec/ApiBounded.lean) exports the direct
arbitrary-key `ApiBoundedTransfer`. Legal API requests derive reference
correctness from structural geometry, actual initialization size and public
schedule premises. If the actual run, issued requests and selected probe results
agree off reference capacity failure, every actual logical prefix, scalar/batch
reply and probing address is correct there. The address list must have exactly
one entry per scheduled table for a probing slot and be empty otherwise;
pointwise default-valued lookup alone cannot establish this count.
The actual request count must equal both the public slot count and the actual
slot count, rejecting truncated runs.
The incorrect-result event has outer measure at most the reference failure
event under any measure. No live-capacity premise, common dictionary, numerical
budget or adapter measurability assumption is needed for this transfer. Concrete
native agreement is a premise.

[HierarchyBounded](../../lean/RebuildBound/Proofs/HierarchyBounded.lean)
exports conditional supplied-record probe-correctness transfer, with
[explicit agreement premises](../../lean/RebuildBound/Spec/HierarchyBounded.lean):

| Export | Claim and premises |
| --- | --- |
| `HierarchyBoundedOnline`, `HierarchyBoundedBatch` | Actual probe results agree with the reference off failure. Under the structural contract, fixed-universe setting and consistent initial history, decoded values and addresses are correct there; the event of any incorrect probing result in the prefix has measure at most the reference failure event. |
| `HierarchyBoundedAdaptive` | The same conclusion for adaptive executions, requiring agreement of the actual issued history as well as probe results off adaptive reference failure; all branches use one fixed universe. |

These transfers need no tape law or numerical certificate and also hold for
outer measures. Both starts are exercised outside the numerical family.
Agreement covers every position in the prefix; correctness constrains its
probing operations and the indexed addresses. Native agreement,
termination and physical trace lengths are not established. This third
semantic root has no numerical imports. The generic trusted Spec closures
also exclude the concrete `*31` modules: shared definitions live in semantic
child modules that the `*31` modules re-export, and generic hierarchy
probability interfaces are separate from their `*31` instances.

[Local family probability adapters](../../lean/RebuildBound/Spec/DirectJobARoute.lean)
cover direct routing with a nonempty A pool. `DirectJobARouteWitnessBound`
uses six topology/storage equalities and the input-shape premise;
`DirectJobARouteWitnessProbability` applies the unconditional `SInputLaw`.
`DirectJobADirectWitnessProbability` eliminates the range event for `.direct`
while retaining stage/radix terms. It requires no DFS `I < K` or successful-tier
condition. The eight-home shape used by 33 family members is checked explicitly.
[Exposure accounting](../../lean/RebuildBound/Spec/HierarchyExposure.lean) proves
that empty starts remove precisely the initialization class and budget term
for arbitrary horizons and class bounds.

[Generic direct-history laws](../../lean/RebuildBound/Spec/DirectJobHistoryGeometry.lean)
derive `SInputLaw` from fixed complete source populations, normalized base
weights, actual source loads and five predecessor/input shape equalities. The
previous and current word-width premises are separate, and the exact joint
old-home density is retained without conditioning on success. Prefix accounting
derives chronology and cumulative loads.
[Level-one tape projections](../../lean/RebuildBound/Spec/HierarchyLevelOneGeometry.lean)
use `cfg.load * cfg.carry1`; all 94 members instantiate them at both starts and
arbitrary horizons, with source caps 128/256/512.
[Generic cycle coupling](../../lean/RebuildBound/Spec/DirectJobCycleGeometry.lean)
constructs those histories from arbitrary actual-geometry cycle prefixes
and a uniform cycle-tape projection. `DirectJobUniformCycleHistory` requires
fixed fresh units, their actual source load, the current digit and word agreement
on complete key unions. `DirectJobCycleHistoryTransport` bounds a reached
capacity failure by its unconditional local history-law probability; it does
not condition the law on earlier publication. Digit-one and whole-cycle bounds,
rejection-freedom and adaptive causal applicability use the same generic
construction. The family exports above compose these results with the checked
numerical inventory.

## Fixed-geometry capacity-2^31 claims (C1–C6)

C1–C6 are the fixed-geometry statements at `geometry31` (the capacity-`2^31`
instance described in the next section). They are independent of the
canonical arbitrary-key claims above and do not restrict them.

| # | Claim | Lean | Scope |
| --- | --- | --- | --- |
| C1 | In the serialised hierarchy model on the ideal hash tape, for any logical trace fixed independently of the hash words and meeting the premises below, the probability that some job triggered within the first `2^32` accesses fails a capacity test is at most `2^-64`. | `HierarchyUniform31` ([statement](../../lean/RebuildBound/Spec/HierarchyUniform31.lean), [proof](../../lean/RebuildBound/Proofs/HierarchyUniform31.lean)) | `geometry31`, fanouts `[4,4,8,8,8,8,8]`, `U_1=16`, `D=8`, `T=2^26`, capacity `2^31`; direct initialization |
| C2 | Under the same premises at horizon `(k+1)·2^32`, for every `k ≥ 0`, the probability that the run's *first* capacity failure is a job triggered in the `k`-th window of `2^32` accesses is at most `2^-64`. For every `h ≥ 1`, with premises at horizon `h·2^32`, failure within the first `h` windows has probability at most `h·2^-64`. | `HierarchyChunk31`, `HierarchyWindows31` ([statements](../../lean/RebuildBound/Spec/HierarchyChunk31.lean), [proofs](../../lean/RebuildBound/Proofs/HierarchyChunk31.lean)) | `geometry31`; every fixed window `k`, every `h ≥ 1`; unconditional first-failure bounds |
| C3 | Non-adaptive obliviousness: fix an operation sequence of at most `h·2^32` accesses (`h ≥ 1`) and a public plan schedule independently of the tapes, meeting the structural and schedule premises. The bucket/publication view on the joint ideal tapes has exactly the public simulator's law on every outcome, including the reference continuation after failure. Any observation agreeing with that view off capacity failure is within `h·2^-64` of the simulator on every measurable event. | `OnlineOblivious31`, `BatchOblivious31`; `OnlineExact31`, `BatchExact31`, `OnlineFailure31`, `BatchFailure31` ([statements](../../lean/RebuildBound/Spec/Oblivious31.lean), [scalar model](../../lean/RebuildBound/Spec/Model/Online.lean), [batch model](../../lean/RebuildBound/Spec/Model/OnlineBatch.lean)) | `geometry31`; scalar operations and batch chunks, counted in lanes; probe kind and chunk widths public; rebuild memory traces assumed public |
| C4 | Deterministic reference probe correctness: every scalar probe returns the latest preceding supplied value, and every probing batch lane includes earlier lanes of its chunk; a winning tombstone denotes absence. The record-based cascade selects exactly the online view's bucket addresses. | `OnlineCorrectness31`, `BatchCorrectness31` ([statements](../../lean/RebuildBound/Spec/Oblivious31.lean), [model](../../lean/RebuildBound/Spec/Model/Probe.lean)) | `geometry31`, every positive chunk horizon; structural settings including `UnshPromise`; arbitrary word and dummy tapes; no capacity-success or uniformity premise |
| C5 | Adaptive obliviousness at capacity `2^31`: a client chooses the keys and values of each operation from every bucket it has observed so far, while the program fixes the public shape (which operations probe, the chunk widths) and the plan schedule. On every possible transcript the client's keys lie in one universe of at most `2^31` keys with `key.toNat < 2^64` fixed before the tapes. On the ideal joint tapes the transcript is measurable and has exactly the simulator's law; the realized run fails within `h ≥ 1` windows of `2^32` accesses with probability at most `h·2^-64`; any observation that agrees with the transcript off that failure is within `h·2^-64` of the simulator on every measurable event. | `AdaptiveExact31`, `AdaptiveWindows31`, `AdaptiveOblivious31` ([statements](../../lean/RebuildBound/Spec/Adaptive.lean), [model](../../lean/RebuildBound/Spec/Model/Adaptive.lean), [proof](../../lean/RebuildBound/Proofs/Adaptive.lean)); `AdaptiveConstant` (a client that ignores its rows is a fixed run) | `geometry31` only; scalar operations and batch chunks; deterministic clients; rebuild memory traces assumed public |
| C6 | Reference API correctness: Read, Write, Erase, Exchange (with either insertion policy), and WriteWithoutProbe implement their logical-map transitions. Every prefix, final map, and scalar/batch prior-value response agrees, including duplicate batch lanes and present zero values. | `BatchApiCorrectness31`, `AdaptiveApiCorrectness31`; `ApiReferenceCorrectness` (sequential construction); `ApiFlagRule` and `ApiAdmissible31` (generated flags and structural admissibility) ([statements](../../lean/RebuildBound/Spec/ApiCorrectness.lean), [adaptive lift](../../lean/RebuildBound/Spec/AdaptiveApi.lean), [model](../../lean/RebuildBound/Spec/Model/Api.lean)) | `geometry31`, fixed or realized adaptive runs; arbitrary routing/dummy tapes; structural setting and local post-record construction from the effective selected entry; abstract payload/metadata codec; no capacity-success or probability premise |

"Overflow" is the event `Fails`: some potential job within the horizon whose
bounded execution on its reference inputs does not publish (level one, the
separated merges, the top preparation and finish, the initialization). The
model's tables after a failure follow a failure-free reference continuation,
so the key sets of every later job are fixed by the trace; the chunk claim
counts only first failures (see [the chunk form](#model-decisions)).

C4 concerns the supplied record history. C6 supplies the API transition
and response argument from an explicit local post-record construction rule.
The rule uses the effective selected record after batch forwarding, with
payload and metadata kept separate. The reference continuation retains overflow
records; transfer to bounded native execution still requires publication and
local execution correspondence.

How to read the numbers:

- Each number is a statement about the serialised model on the ideal tape.
  `Fails` counts the five modelled job kinds; lane copies, pauses, the online
  stash's unit discipline and helper threads are separate obligations, not
  composed into C1–C3.
- A window is measured by the level-one ordinal whose completion *triggers*
  the failing job (one speculative ordinal included), not by when the job
  executes natively: window `k`'s ordinals cover roughly accesses
  `k·2^32 + 513 … (k+1)·2^32 + 512` after the initialization. "Within the
  first `K·2^32` accesses" in C2 is meant the same way.
- The per-window bound of C2 is a first-failure bound, not a bound over all
  windows at once; over `K` windows use `HierarchyWindows31`. The windows
  partition `Fails` at horizon `K·2^32` for `K ≥ 1`, by the generic
  `HierarchyChunkPartitionProof.chunks_partition` used in
  [HierarchyWindows](../../lean/RebuildBound/Proofs/HierarchyWindows.lean).
- C3's `h` counts windows of `2^32` operations; with batch chunks every lane
  takes one access position, so it counts lanes. Both obliviousness
  statements use `HierarchyWindows31` to bound their failure term by `h·2^-64`.

## The capacity-2^31 geometry

`HierarchyUniform31`, `HierarchyChunk31` and `HierarchyWindows31` prove the
corresponding capacity claims at `2^-64`, `2^-64` per fixed first-failure
chunk, and `h * 2^-64` over the first `h ≥ 1` chunks. Their statements are in
[HierarchyUniform31](../../lean/RebuildBound/Spec/HierarchyUniform31.lean) and
[HierarchyChunk31](../../lean/RebuildBound/Spec/HierarchyChunk31.lean).

This instance has non-top fanouts `[4,4,8,8,8,8,8]`, `D=8`, `U_1=16`,
`T=2^26`, capacity `32 T=2^31`, bucket capacity 64 and load 32. Published
tier widths are `[1,1,1,1,2,2,2,3]`; stage stash widths are
`[1,1,1,1,2,2,2,4]`. Preparation drains four buckets; initialization drains
three. All 38 separated rows, the four reused direct shapes and the distinct
top/preparation/initialization bounds are certified in Lean.

The premises are P1–P7, including P4's key bound `N ≤ 2^31`; P8 is a native
applicability obligation. Each chunk uses premises at horizon
`(k+1) * 2^32`, and the window bound uses premises at `h * 2^32`.
This is an unconditional first-failure bound for a fixed chunk, not a
conditional-on-survival or arbitrary sliding-window guarantee. The proof
assumes no independence between jobs and derives the local laws and covering.

`OnlineOblivious31` and `BatchOblivious31` establish C3 with
error at most `h * 2^-64` on every measurable event, for `h ≥ 1`. Their exact
simulator laws, pattern independence, freshness and failure transfer are also
exported. The batch horizon counts slots, and the simulator sees the public
chunk widths. Both require the joint ideal family/dummy tapes and the same
observation agreement off capacity failure; `SyncSchedule31` supplies a valid
public synchronous schedule.

`OnlineCorrectness31` and `BatchCorrectness31` establish C4 at this geometry and
every positive chunk horizon. They return the latest preceding supplied value,
include earlier batch lanes, interpret winning tombstones as absence, and agree
with the online bucket-address view. They quantify over arbitrary routing and
dummy words without a capacity-success premise. Statements are in
[Oblivious31](../../lean/RebuildBound/Spec/Oblivious31.lean); the shared interfaces
use `HierarchyGeometry`, its actual initialization/preparation shapes and an
explicit error budget.

The bounded-key endpoints, the generic-key forms below and C5–C6 share
`geometry31`. A workload with fewer distinct keys runs on the same geometry
and is covered by these statements. Native execution correspondence, the
AES-to-ideal distance and the online stash are outside these endpoints.

## Compatibility: encoded keys in one fixed run-wide universe

The `Generic*31` endpoints replace the numeric bound by one universe `U`,
fixed independently of the tapes, containing at most `2^31` distinct keys with
`key.toNat < 2^64` used anywhere in the entire run. This includes
initialization, all queries and supplied operation/slot records, tombstones and duplicate
lanes. It is a total distinct-key bound, not a bound only on simultaneously
live keys. The canonical `IdealCapacity` theorem covers live-capacity-preserving
churn without it. All non-key premises of the corresponding bounded-key
endpoints are kept.

| Interface | Claim |
| --- | --- |
| [Spec.KeyUniverse](../../lean/RebuildBound/Spec/KeyUniverse.lean) | Actual-key family tape, its joint uniform law with the dummy tape, universe membership and the structural/schedule premises |
| [Spec.KeyRelabel](../../lean/RebuildBound/Spec/KeyRelabel.lean) and [Spec.KeyRelabelStructure](../../lean/RebuildBound/Spec/KeyRelabelStructure.lean) | Exact statements of all 14 `Generic*31` endpoints |
| [Proofs.KeyRelabel](../../lean/RebuildBound/Proofs/KeyRelabel.lean) | Assemble the transported capacity, view and correctness results |
| `GenericHierarchyChunk31`, `GenericHierarchyWindows31` | At most `2^-64` for first failure in any fixed chunk, and `h * 2^-64` within `h ≥ 1` chunks; the latter includes the first horizon at `h=1` |
| `GenericOnlinePattern31`, `GenericBatchPattern31`; `GenericOnlineFresh31`, `GenericBatchFresh31` | Word-independent real/dummy patterns and freshness of real family/key probes under the run-wide settings |
| `GenericOnlineExact31`, `GenericBatchExact31`; `GenericOnlineFailure31`, `GenericBatchFailure31` | Exact public simulator laws and transfer through the capacity-failure event |
| `GenericOnlineOblivious31`, `GenericBatchOblivious31` | Simulator distance at most `h * 2^-64`, with the same joint ideal tapes and observation agreement off failure |
| `GenericOnlineCorrectness31`, `GenericBatchCorrectness31` | Latest preceding supplied-value lookup, tombstone decoding, batch forwarding and exact probe-address agreement for arbitrary routing/dummy words |

The proof extends a bijection from `U` to `KeyIndex.range |U|` to a
permutation `e : LogicalKey ≃ LogicalKey`. The finite view `KeyIndex N` is
equivalent to `Fin N`; its bound applies only to this finite view,
not the canonical key domain or a native storage width. It maps
record keys by `e`, every family word by `w' = w ∘ e.symm`, and the unshadowed
predicate by `unsh' = unsh ∘ rec e.symm`. One such permutation is used for
the whole run and every failure outcome. Exact lane/state execution, failure
tests and identities, and probe addresses commute with it. Reindexing every
family tape coordinate by this bijection, while fixing the dummy tape,
preserves the joint uniform law and independence. No AES correspondence or
native execution conclusion is added.

## Adaptive clients

C5 adds two trusted modules: the interaction model
([Spec/Model/Adaptive.lean](../../lean/RebuildBound/Spec/Model/Adaptive.lean)) and
the statements ([Spec/Adaptive.lean](../../lean/RebuildBound/Spec/Adaptive.lean)).
The client is a function from the rows it has observed (the bucket each
earlier slot touched, per plan entry) to the records of the next operation's
lanes; it has no other input, so it reads no word of either tape. Each
operation's rows are `touched` on the run issued so far.

- **Setting.** `AdaptiveSetting` replaces P1: every run the client can issue,
  whatever rows it reads, meets the fixed-run setting `UniverseBatchSetting`,
  so P2–P7 hold on every branch; the transcript covers every slot of the
  public shape. `AdaptiveAdmissible` proves it for every client whose records
  have keys in `U`, with no unshadowed flag, an initialization of distinct
  keys in `U`, a shape within the horizon and a schedule meeting the
  premises. `AdaptiveFlagAdmissible31` extends it to clients whose unshadowed
  flags follow the engine's rule on every branch (`FlagRule`, at the
  all-zero words), the unshadowed promise included (`FlagSoundness31`). The
  witness [AdaptiveWitness](../../lean/spec_tests/AdaptiveWitness.lean) applies all
  three theorems to a client whose keys depend on the first observed bucket;
  [AdaptiveFlagWitness](../../lean/spec_tests/AdaptiveFlagWitness.lean) shows the
  setting for such a client that also erases an absent key with the flag
  set.
- **Scope.** One universe for all branches, fixed before the tapes: a client
  that uses `2^31` keys per branch but more across branches is not covered
  (the canonical `IdealCapacity` removes this restriction). The run's length
  is fixed by the shape (adaptive stopping is modelled by any continuation).
  Randomized clients with coins independent of the tapes are mixtures of
  deterministic ones; the canonical `IdealSeed*` exports state this for
  countable seeds.
- **Native premises.** The observation agreement off failure (P9) is a
  hypothesis of `AdaptiveOblivious31`, as in C3. The theorem accepts any
  measurable `ι`, including encodings with no security meaning. Natively the
  premise must hold in a causal, public form: maps `ι_j`, fixed
  before the tapes and the same for every compared secret, with the native
  observation before operation `j + 1` equal to `ι_j` of the rows through
  operation `j`, and the final observation equal to `ι` of the transcript,
  on every outcome outside `AdaptiveFails`. It also needs the engine's
  effective selected entry after batch forwarding (tombstone and unshadowed
  bits included) to be the model's `Probe.batch` result until the first failure (P8). Only then is the
  adversary a `Client`: rows ↦ the program's records for its choice from
  `ι_j(rows)`, with the records' flags and re-inserted values justified by
  `BatchFound31`, `BatchFoundCausal` and `AdaptiveFlagAdmissible31`
  ([AdaptiveNative](../../lean/RebuildBound/Spec/AdaptiveNative.lean)). Two
  clients observed through one encoding are within `2·h·2^-64` of each other
  (`AdaptiveTwoClients31`). The schedule and the public shape are decided by
  the program (P10). Native comparisons must also fix the public API operation
  kinds, including Read/Write/ReadThenWrite/Erase/Exchange batch lanes,
  Exchange's insert flag, and value/presence output descriptors; the bucket view alone
  does not identify instruction traces for different kinds. The rebuild
  memory traces are a premise of the
  capacity claim too (see [Adaptivity](#adaptivity-and-obliviousness)).
- **Method.** The capacity proof bounds every job's first-failure event on any
  trace drawn from the joint tape that is causal for exposure (a family's
  words cannot influence the units issued before its tables can appear in a
  plan), with one cutoff per population and the shared class budgets, then
  composes per chunk. The realized trace is such a trace. Fixed runs
  are the special case of a client that ignores its rows (`AdaptiveConstant`).

## API semantics and the conditional native adapter

The independent map in `Model.Api` preserves other keys and applies one request
at a time, in lane order. Read preserves the previous value, Write and blind
Write replace it, Erase removes it, and Exchange replaces it only if present or
its public insertion flag is set. A batch Write can return the previous value;
scalar Write and WriteWithoutProbe return no value. `none` records absence,
separately from a present zero payload. Tombstones constructed by the API have
zero payloads, and their unshadowed bit follows `NoOlderLiveCopy`.

The internal `Api.Action.write` denotes `ReadThenWrite`, a probed replacement.
Default scalar `Write`, `write` and `insert_or_assign` use
`Api.Action.blindWrite`; `WriteWithoutProbe`/`insert_without_probe` are
aliases. In a public batch, `kWrite` is blind only when its value output and
the batch presence output are both omitted. Blind lanes split the call into
scalar blind writes and contiguous probed chunks bounded by both width and the
next requester unit. Output-bearing Write and every `kReadThenWrite` are
probed. The primitive theorem statements apply to these lowered runs; the
operation name alone does not determine the probe shape.

**Lowering and grouping.** `ApiLoweringStructure` takes public unit size,
starting position, width and descriptors. It proves lane order and
multiplicity, bounded all-probing chunks, a `GroupsFit` bound at every
requester-unit boundary, and shape independence from keys and payloads.
`ApiLoweringMap` equates internal request transitions with an independent
public map. `PublicBatchApiCorrectness` and `PublicBatchApiCorrectness31` then
derive every prefix map and requested value/presence output from local
construction equations. Logical correctness allows any compatible grouping; the
structural partition and its equality to native grouping are separate. See
[ApiLowering](../../lean/RebuildBound/Spec/ApiLowering.lean). `ApiGroupedChoices`
proves that an adapter invoked after each internal group chooses exactly the
batch selected at the original public decision point, provided each invocation
retains that observation prefix. Lane indices, public shape, requester-unit
bounds and the induced slot schedule agree with the lowering.
`ApiGroupedReference` proves that chronological reference execution across
these groups preserves the entire record sequence, including encoded flags.
See [ApiGrouped](../../lean/RebuildBound/Spec/ApiGrouped.lean).

**Physical construction.** `ApiExecution` constructs physical postrecords from
chosen request groups, probing a provisional run before each insertion.
`ApiExecutionImplements` derives the local selection and construction
equations at zero tapes from public geometry and schedule premises alone;
`ApiExecutionFlags` derives the local flag rule. `ApiExecutionLowered` composes
fresh, unit-aligned public lowering with that constructor.
`ApiExecutionCorrectness` derives the setting, actual-tape construction
equations and every logical prefix/reply under fixed-universe premises;
`ApiStructural` supplies the universe-free endpoints described below.
Physical selections include tombstone metadata and need not equal chronological
reference selections. See [ApiExecution](../../lean/RebuildBound/Spec/ApiExecution.lean).
`ApiAdaptiveFrames` derives causal, nonempty, unit-aligned groups from public
batches. `ApiAdaptiveReplay` and `ApiAdaptiveInteraction` identify reconstructed
API requests with the supplied-record replay and actual interaction, without
a key-universe or capacity-success premise. Generated frames give every internal
group of a public batch the same original observation prefix.
`ApiAdaptiveCorrectness` derives the adaptive setting and actual-tape
implementation, prefix-map and reply correctness from explicit universe,
initialization and schedule premises. It assumes neither its own flag rule nor
its implementation equations. See [the adaptive request contract](../../lean/RebuildBound/Spec/ApiAdaptiveCorrectness.lean).

**Byte keys and populations.** [Key](../../lean/RebuildBound/Spec/Key.lean) proves
exact byte-string/natural-number roundtrips with no length bound.
[IdealKeyLaw](../../lean/RebuildBound/Spec/IdealKeyLaw.lean) proves a canonical
product law on tagged routing/dummy coordinates, finite uniform restrictions,
repeated reads, independent blocks, measurable dynamic reads and sectionwise
bounds, including the actual outside/fresh split. The canonical engine uses
`LogicalKey` in records, requests, requester lookup and clearing, hierarchy
jobs, API state and choices, routing inputs and finite local-law key sets.
Empty, zero-prefixed and long strings keep exact identity. Numeric fixture
conversions and finite tape views are explicit; no implicit numeric key
coercion or fixed key width enters the engine.
[RequesterCuts](../../lean/RebuildBound/Spec/RequesterCuts.lean) identifies every
completed frozen-unit and grouped trace cut with its exact lane prefix.
[HierarchyStructural](../../lean/RebuildBound/Spec/HierarchyStructural.lean) gives
range-free top history, uniqueness, placement, live-only publications and
finish permutations under explicit initial length, input-rate and flag premises.
A finite internal encoding restriction reuses the bounded-key induction;
no bound on the original trace's key identities or distinct-key count appears
in the public statements.
[ApiCapacity](../../lean/RebuildBound/Spec/ApiCapacity.lean) counts the independent
logical map at every lane prefix: exact support, initialization,
resolved-history and snapshot counts, symbolic misses/churn, and a
capacity-preserving logical idle extension.
[HierarchyLive](../../lean/RebuildBound/Spec/HierarchyLive.lean) then derives the four
top-job population bounds for every modeled top ordinal, without a supplied-cut
premise. The total finite-run trace has an empty tail, so cuts beyond its frozen
units represent the last complete-unit logical prefix.
The [ApiStructural package](../../lean/RebuildBound/Spec/ApiStructural.lean) derives
API prefix correspondence and the local flag promise from the physical
constructor for fixed and adaptive requests. Deterministic correctness requires
only actual initialization size; live populations additionally require
lane-prefix capacity and public cut alignment. Adaptive branches need no
shared dictionary.
The [ApiContinuation package](../../lean/RebuildBound/Spec/ApiContinuation.lean)
proves public singleton-read padding, exact
operation/slot/requester-prefix preservation, arbitrary-tape selected-record and
bucket-observation preservation, completed trace snapshots equal to the original
final logical map, and capacity-derived top populations. The same configuration
and schedule must accommodate the extended endpoint. Completion is a
trace-history result, not a claim that a top publication has already occurred.
The [ApiLegal package](../../lean/RebuildBound/Spec/ApiLegal.lean) types public
observations. Legal cell ranges use the internal chunk's start
schedule; blind and absent-table cells have only zero. Every legal prefix extends
to a full legal transcript. The total numeric adapter is the identity on actual
observations and preserves each public batch's original decision point. Its live
endpoint quantifies capacity only over legal typed branches and derives flags,
logical correctness and all top populations through the constructor.

**Canonical tape and local laws.** The
[IdealHierarchy package](../../lean/RebuildBound/Spec/IdealHierarchy.lean) connects
the canonical tape to actual hierarchy routing and dummy words, preserving
adopted-family identity and horizon coherence. Arbitrary finite byte key
selections have their exact word law; sectionwise event bounds may choose keys
from the complete outside environment. The
[IdealMeasurable](../../lean/RebuildBound/Spec/IdealMeasurable.lean) and
[IdealFailure](../../lean/RebuildBound/Spec/IdealFailure.lean) packages prove finite
local dependence and measurability of actual hierarchy tables, fixed/adaptive
transcripts, bounded job tests and adaptive capacity failure events on the
canonical product tape, without geometry, capacity, key-universe or
successful-execution premises. They do not equip the infinite tape with a
discrete sigma algebra or assume a measurable choice of finite witnesses.
[IdealSeed](../../lean/RebuildBound/Spec/IdealSeed.lean) and
[ApiSeed](../../lean/RebuildBound/Spec/ApiSeed.lean) handle independent client
coins. Seedwise budgets integrate, and one fixed seedwise simulator gives
both the mixed transcript law and its independence from the private seed.
Unconditional coupling transfers agreement outside a bad event. General seed
spaces require joint measurability; the actual API derives it for
countable seeds, including seed-dependent initialization and arbitrary legal
request choices. Regressions include positive-probability seeds selecting
keys of unbounded byte length, capacity-one churn in both starts and actual
reference overflow.
[IdealExposure](../../lean/RebuildBound/Spec/IdealExposure.lean) and
[IdealFreshness](../../lean/RebuildBound/Spec/IdealFreshness.lean) prove actual
adaptive input-prefix causality and independence from a whole fresh family,
from public geometry and schedule premises only. Earlier tables determine
real/dummy choices; resampling the cutoff family cannot change its completed
trace inputs. Input-prefix independence does not make routed intermediate
layouts independent of their routing words; the local laws below account for
that dependence.
[IdealInitialization](../../lean/RebuildBound/Spec/IdealInitialization.lean) proves
initialization's actual analytic failure bound by selecting only the supplied
input keys and applying the finite job theorem; a regression proves a real
overflow has positive probability under the same experiment.

**First-failure bounds per job class.**
[IdealDirectFresh](../../lean/RebuildBound/Spec/IdealDirectFresh.lean),
[IdealDirectLocal](../../lean/RebuildBound/Spec/IdealDirectLocal.lean),
[IdealDirect](../../lean/RebuildBound/Spec/IdealDirect.lean) and
[IdealDirectA](../../lean/RebuildBound/Spec/IdealDirectA.lean) bound the actual
adaptive direct jobs: B overflow, complete first-digit failure, union overflow
and the two-family old-home density for A, handling reference fallback without
assuming prior success. `IdealDirectFirstFailure` combines them for every
direct job in all 94 geometries and both starts, using the analytic
`directBound`. [IdealSepUnion](../../lean/RebuildBound/Spec/IdealSepUnion.lean) and
[IdealSepA](../../lean/RebuildBound/Spec/IdealSepA.lean) bound the separated union
witness and the adjacent-family A route and range witnesses;
`IdealSepFirstFailure` combines them, deriving input shape from lower
reference history and tier fit from the first-failure event.
[IdealTopPrep](../../lean/RebuildBound/Spec/IdealTopPrep.lean) derives the
top-preparation contribution from legal adaptive API clients and logical live
capacity: the early outside section fixes the completed input prefix while the
previous top's layout varies with its old family, and a finite two-family
projection proves the exact binary old-home density.
`IdealTopPreparationFirstFailure` discharges the word-width, DFS and analytic
cutoff conditions for all 94 geometries and both starts at cutoff 576.
[IdealTopFinish](../../lean/RebuildBound/Spec/IdealTopFinish.lean) derives the
finish bound: the late outside section fixes complete record sets while
preparation and the completing carry share the current family; shared A/B keys
reuse one word, and live capacity bounds both A and the resolved live winners.
`IdealTopFinishFirstFailure` applies the analytic budget at cutoff 576. None
of these uses a key universe, a supplied job population or a prior-success
premise; tier fit belongs to the event, so the reference execution remains
unconditional after earlier overflow.

**Composition.** [IdealProbe](../../lean/RebuildBound/Spec/IdealProbe.lean) proves
exact fixed-run, adaptive and legal API probe simulation on the canonical tape;
each replay fibre uses its own finite restriction.

[IdealFresh](../../lean/RebuildBound/Spec/IdealFresh.lean) states the freshness
behind that law for request runs. `IdealApiFresh` covers every structural
geometry, every adaptive API client with arbitrary byte keys, and every choice
of the words and the dummy tape: two different real probes never have the same
hash family and the same key. Its premises are those of
`ApiAdaptiveStructural`. The earlier forms, in `HierarchyFixedSemantics` and
`GenericBatchFresh31`, cover a fixed run whose keys are numbers below a bound,
or one fixed key universe at the `2^31` geometry. The
[spec test](../../lean/spec_tests/IdealFresh.lean) discharges the premises on a
concrete adaptive run and exhibits two real probes.

[IdealCapacity](../../lean/RebuildBound/Spec/IdealCapacity.lean) composes all actual
first-failure classes with the exposure counts. Its analytic proof
imports no numerical certificates; the numerical endpoint uses the checked
family budgets to obtain `h * 2^-64` over `h ≥ 1` windows of `2^32` accesses.
Live capacity is required at every legal request prefix, not on the union of
keys across time or seeds.

[TightOverflow](../../lean/RebuildBound/Spec/NativeMatch/TightOverflow.lean) puts a
number on the overflow bound alone. `IdealCapacityTight` has exactly the
premises of `IdealCapacity` (at most `h * 2^32` accesses, initial records not
counted) and bounds the overflow probability by `h` times
`NativeMatchTightBudget.exposureBudget`. That budget is an exact rational: the
sum of the member's per-class overflow bounds, each multiplied by its exposure
count. `NativeMatchTightOverflow` shows that it is below `2^-65.5` for all 94
members, stated as `0 ≤ x` and `x * x < 2^-131`. The largest budget is about
`0.3418 * 2^-64`.

The budget behind `IdealCapacity` is larger for two reasons. It rounds every
local bound up to a power of two, and the theorem then rounds the sum (at most
`0.6101 * 2^-64`) up to `2^-64`. The refined budget keeps the sum and replaces
three local bounds by the rationals that their certificates support: one
top-finish shape (`2^-70` becomes `0.53 * 2^-70`) and two range shapes
(`2^-76` and `2^-72` become `0.54` times as much). At capacity `2^31` these
three account for `0.58` of the `0.61`. The model and the overflow event are
the same; false matches and key normalization are not part of either budget.
The [spec test](../../lean/spec_tests/NativeMatchTightOverflow.lean) combines the two
theorems into the single bound `h * 2^-65.5`, also for runs with
`init.length + n ≤ h * 2^31`, and applies it to a concrete adaptive run from
both starts.

[IdealOblivious](../../lean/RebuildBound/Spec/IdealOblivious.lean) exports the combined
`IdealApiFamily` result and deterministic/seeded eventwise observation transfer.
[IdealBounded](../../lean/RebuildBound/Spec/IdealBounded.lean) composes
`ApiBoundedTransfer` with family capacity (`IdealApiBounded`,
`IdealSeedBounded`).
[IdealGeometry](../../lean/RebuildBound/Spec/IdealGeometry.lean) provides the
generic canonical analytic chain. Capacity uses an explicit public exposure
inequality; window scaling also requires divisibility and ordinal-count
arithmetic. Geometry keeps load 32, 64-lane buckets, fanouts 2..8, depth at
most 14, lower cutoff 256, and compatible direct/DFS shapes; top cutoffs are
explicit parameters.
[IdealGeometryFamily](../../lean/RebuildBound/Spec/IdealGeometryFamily.lean) verifies
all 94 geometries and both starts with exactly the family class budgets, and
`IdealCapacityAnalytic` specializes the generic window proof. This does not
extend the numerical family or establish a native error target.

**Native error composition.** [NativeError](../../lean/RebuildBound/Spec/NativeError.lean)
has two conditional endpoints. `NativeFailureBound` combines an outcome-event
hybrid with containment in normalization, matching, encoding, resource-refusal
and capacity events. `NativeObservationBound` combines the same unconditional
event bounds with exact reference simulation, off-failure agreement and a
two-sided hybrid for the tested public event. Both clip probabilities at one;
no independence, collision-free conditioning or finite key dictionary is used.
Correctness needs its own outcome-event hybrid; public-view closeness does not
cover confidential API results. The theorems do not supply AES advantages,
native refinement or completion within query allowances. A refused routing
reservation can truncate an otherwise capacity-safe run and must be charged
under the full-run contract; an unknown refusal probability is conservatively
one.

[NativeNormalize](../../lean/RebuildBound/Spec/NativeNormalize.lean) proves the
normalization collision bound. `NativeNormalizeFresh` derives the joint uniform
law of fresh answers from injective branchwise replay keys and exact replay
fibres on an arbitrary-byte-key random function. `NativeNormalizeAdaptive`
derives measurability and those replay fibres from finite causal query
recursion, leaving only branchwise freshness as its premise.
`NativeNormalizeIndependent` extends the recursion to arbitrary independent
measurable environments (an infinite oracle tape included; a regression rejects
a correlated-tape coupling). `NativeNormalizeBirthday` proves the clipped
`Q.choose 2 / 2^bits` collision bound, and `NativeNormalizeBound` transfers it
to a key/fingerprint trace through explicit answer slots on the same
unconditional space. `NativeNormalizeConversions` constructs that padding and
slot correspondence for bounded-width conversion choosers: one slot per allowed
conversion, repetitions reuse cached answers, and repeated or unused slots
query fresh proof-only keys longer than the real-key width.
`NativeNormalizeTrace` is the interface for an external chronological trace
whose length is bounded by the conversion budget and whose next key and answer
are fixed by a local equation from the preceding history; unused reservations
add no trace entries. Native trace enumeration, the causal local equation, the
independent environment and CBC replacement are explicit obligations.

[NativeKey](../../lean/RebuildBound/Spec/NativeKey.lean) checks the deterministic
stored-key byte encoding: keys below sixteen bytes are stored verbatim and a
sixteen-byte key is one encrypted block. `NativeKeyShort` proves fixed-width
injectivity for widths 1–16 under explicit injective block encryption, which
only width 16 uses. `NativeKeyVerbatim` proves widths below 16 injective for
every block operation. `NativeKeyLong` proves that native 17–64-byte keys have
distinct length-prefixed padded input messages and exactly
`1 + ceil(width/16)` blocks. Long-key digest collisions, the fixed-width CBC
reduction, compiled AES/packing and native correspondence are separate.
Regressions exhibit mixed-width zero-filling aliases, including fifteen versus
sixteen bytes under an injective block operation, so the fixed-width premise
cannot be dropped.

[NativeMatch](../../lean/RebuildBound/Spec/NativeMatch.lean) checks the approximate
rule that the default VP2INTERSECT build applies to sixteen-byte stored keys.
Rebuild deduplication ANDs four 32-bit segment memberships, and dense lookup
ANDs two 64-bit half memberships. The statements prove that the rule has no
false negatives; that with one partner supplying every segment it is exactly
membership; and that a false match needs two different donors, with at most
`m^k` values passing. Off a comparison's false-match event, the rule agrees
with logical key membership. For a comparison inventory measurable in an
environment independent of the stored keys, false matches have probability at
most `min(1, sum m^k / 2^128)`, under the normalization random function above
sixteen bytes and under one ideal permutation at sixteen bytes. A relabeling
theorem shows that, at sixteen bytes, routing by the permuted stored key is
jointly distributed as routing independent of the permutation.

[NativeMatchLanes](../../lean/RebuildBound/Spec/NativeMatch/Lanes.lean) proves
finite instruction semantics for packed words, byte unpacks, the fixed PDEP/PEXT
maps, occupancy and per-segment zero repair, retained-source destinations, and
both class directions. Its explicit native masks agree with `segMatch` and,
off the corresponding false-match events, with `DirectMask64.duplicateMask`.
[NativeMatchDense](../../lean/RebuildBound/Spec/NativeMatch/Dense.lean) proves the
8-by-8 qword shuffle network, per-subset repair, last-index recovery and full-key
verification. Under live-key uniqueness, losing a present hit entails a false
match in one of fourteen other row/column subsets; their weight is at most
`14 * 8^2`. Verification never accepts a different stored key.
[NativeMatchTrace](../../lean/RebuildBound/Spec/NativeMatch/Trace.lean) constructs
pre-clear helper events and proves local replay agreement.
[NativeMatchDenseTrace](../../lean/RebuildBound/Spec/NativeMatch/DenseTrace.lean)
derives logical uniqueness, selected-result and deferred-removal agreement,
and coverage of divergence through subsequent real/dummy probes; its physical
observer proves the allocation-loop correspondence and 53-bucket envelope.
[NativeRoutingCoupling](../../lean/RebuildBound/Spec/NativeRouting/Coupling.lean)
proves unconditional finite-used-key routing coupling and complete-message
collision reflection. `NativeRoutingActual` instantiates its causal chooser
with the actual adaptive execution, initialization and all issued slots,
complete native messages, public family cones and physical dummy reservations.

`NativeMatchJobs` and `NativeMatchHierarchy` prove whole-job and recursive
hierarchy agreement and actual inventory provenance. `NativeMatchHierarchyCounts`
and `NativeMatchOrdinals` derive comparison counts from actual jobs and
seed-preserving carry ordinals over finite prefixes. `NativeMatchAllocation`
checks `S_min` against the Lean capacity allocation for all 94 members
and both starts. `NativeMatchProduction` derives inventory independence and
bounds capacity union matching by `h * 2^-64`, before any normalization,
cryptographic or stop charge. No script-supplied execution count is a premise.
`NativeMatchApi` proves the full native adaptive continuation and first
divergence, including actual postrecords and later request choices.
`NativeMatchMemo` connects its exact inventory and capacity predicate to the
actual finite read memo. `NativeMatchRoutingBudget` proves the complete-message
routing error bound with one birthday charge above sixteen bytes and none at
sixteen. `NativeMatchEndpoint` instantiates the failure and observation
bounds in the canonical logical-routing experiment; the crypto/compiled hybrid,
encoding and completion-stop bounds are explicit inputs.

[NativeMatchCoded](../../lean/RebuildBound/Spec/NativeMatch/Coded.lean) exports
`NativeMatchCodedFailure` and `NativeMatchCodedObservation`. These endpoints
use an independent ideal RF64 oracle on the actual complete native messages,
with ideal permutation normalization at width 16 or ideal RF128 normalization
at a fixed width 17–64. For the certified family, both starts, `h ≥ 1`, a valid
execution context, a fixed width for initialization and all issued inputs,
`FieldsFit` and `CounterFit`, set
`epsilon = h * 2^-64 + canonical ringCost`, adding
`birthday128(init.length + accesses)` once at widths 17–64. Failure is at most
`min 1 epsilon`. For each measurable public-view event, its native probability
is at most `min 1 (simulator probability + epsilon)` and conversely; each
direction uses the same single charge. The public view is the optional
address-row transcript, with `none` on error or stop; confidential replies and
additional compiled leakage are excluded. Native outcomes after a bad event
are unrestricted and need not be determined by the exact-reference memo.

The [linear/best endpoints](../../lean/RebuildBound/Spec/NativeMatch/LinearCoded.lean)
keep the smaller of `birthday128(init.length + accesses)` and the proved
geometry-dependent affine normalization allowance, on those same events
([ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md#stored-key-normalization) gives the
formula). The [public-check endpoints](../../lean/RebuildBound/Spec/NativeMatch/Public.lean)
replace the family/counter assumptions by a finite Boolean check and remove
the canonical ring term when it passes. `NativeMatchPublicChecks` derives
`FieldsFit`, `CounterFit` and zero ring cost; `NativeMatchPublicFailure` and
`NativeMatchPublicObservation` use the best normalization allowance with
the same valid-context and fixed-width contracts.
`NativeMatchRingPublic` equates ring readiness with a public shape/snapshot
check for every adaptive client and every oracle outcome, and
`NativeMatchRingCost` proves the ring cost is exactly zero or one accordingly.
This is a proved public condition, not an assumption that arbitrary schedules
make progress. The arithmetic checks cover speculative dependency cones and
conservatively reserve a main and tier for every physical slot on every charged
lane.

The [tight allocation endpoints](../../lean/RebuildBound/Spec/NativeMatch/TightPublic.lean)
use the same native failure and observation events, validity, fixed-width,
public-check and dispatch-policy premises. `NativeMatchTightAdaptiveCapacity`
uses the unconditional adaptive exposure theorem with three sharper rational
local certificates; no request sequence is fixed in advance and no survival
condition is added. `NativeMatchTightPublicFailure` and
`NativeMatchTightPublicObservation` use `h * allocation + normalizeCost`, where
`allocation` is the exact checked overflow-plus-matching reserve.
`NativeMatchTightWindowError` proves a strict `h * 2^-64` bound when
`1 <= h <= 4` and `init.length + accesses <= h * 2^31` (initialization consumes
this allowance); `run32_error` shows a single allocation suffices for
`init.length + accesses <= 2^32`. This is not an indefinitely repeatable cycle
guarantee, and the normalization hash is not reset between windows. The
[per-member report](code/long_key_live_collision.json) and
[CSV](code/long_key_live_collision.csv) give all 188 member/start rows. In units
of `2^-64`, the worst `2^31`-input total is `0.622085842956571698`;
at the capacity-`2^31` default it is `0.601333027135829300`.

`NativeMatchSixteenWindowError`, in
[SixteenWindow](../../lean/RebuildBound/Spec/NativeMatch/SixteenWindow.lean), removes
the limit `h ≤ 4` for sixteen-byte keys. Their normalization cost is zero, so
the error term of `NativeMatchTightPublicFailure` and
`NativeMatchTightPublicObservation` is below `h * 2^-65`, and so below
`h * 2^-64`, for every `h ≥ 1`. The
[spec test](../../lean/spec_tests/NativeMatchSixteenWindow.lean) composes it with
both endpoints.

The [live-key endpoints](../../lean/RebuildBound/Spec/NativeMatch/LivePublic.lean)
prove the arbitrary-horizon route for widths 17–64. `NativeMatchLivePublicFailure`
bounds native semantic failure by
`min(1, h*allocation + pairBound128(choose(I,2)+n*N))`, with `I` initial
records, `n` accesses and capacity `N`. The
[semantic event](../../lean/RebuildBound/Spec/NativeMatch/Semantic.lean) covers
native stops, every logical prefix map, ordinary and scalar replies, and public
slot/address counts. `NativeMatchLivePublicObservation` bounds both directions
against the same exact simulator, using `h*allocation + pairBound128(choose(I,2))`;
there is no per-access collision charge for observation. The initial-only
charge is conservative, and vanishes for an empty start.
`NativeMatchLiveWindowError` proves, for every `h>=1`, `N<=2^31`, and
`I+n<=h*2^31`, that the semantic error is strictly below
`0.75*h*2^-64`, hence below `h*2^-64`. This is a cumulative-run guarantee,
including initialization once, and does not condition later windows on earlier
survival. The [per-member summary CSV](code/long_key_live_collision_summary.csv)
gives all 188 rows. The worst linear one-window total is
`0.747085843014779359 * 2^-64`; the default empty-start total is
`0.726333027194036961 * 2^-64`. At full initialization the default has `I=N=2^31`
and `n=0`, giving `0.601333027135829300 * 2^-64`. The birthday endpoint
can give a smaller bound for short runs.

For the live-key route, the complete native interpreter is coupled to the
canonical reference on 16-byte encodings of the stored-key classes. Local
uniqueness comes from the certified target tables; global injectivity of the
logical-key map is not assumed. The coupling covers direct, separated and top
jobs, retained lanes, tombstones, dense and fallback lookup, batch forwarding,
postrecords, and adaptive continuation. Initial winners give a valid collapsed
reference for every hash function, and its joint transcript law is independent
of that function. An independent permutation randomizes class labels without
changing the RF128 law. The actual complete-message RF64 routing law is then
transferred jointly with capacity/matching events and the reference transcript.
All bounds are unconditional; the fixed-request conditional Python ledger is
not used. [NativeMatchLivePairs](../../lean/RebuildBound/Spec/NativeMatch/LivePairs.lean)
uses `N`, rather than `N-1`, because a miss at a full map has `N` possible live
partners. [NativeNormalizeLiveApi](../../lean/RebuildBound/Spec/NativeNormalize/LiveApi.lean)
provides live-support contraction and pure API agreement. A dead/dead alias can
change real versus dummy addresses without changing replies, as the
[regression](../../lean/spec_tests/NativeDeadAliasWitness.lean) demonstrates, so this
correctness event separates logical results from address distribution.

What these endpoints leave open: stored-key secrecy, AES/PRP/CBC replacement,
normalization lifetime allowances, input entropy, schedule/publication
realization, other resource/completion stops, simulation time, C++ memory/byte
assembly, concurrency, compiler and machine execution. `StoredKey`, `*Stored`
and stored-key exposure or injection through `ByteMap::engine()` are outside
the secret-key claim. No total native error bound is claimed.

[NativeRouting](../../lean/RebuildBound/Spec/NativeRouting.lean) checks the masked
64-bit identity packing against its bounded arithmetic encoding and proves
complete two-block message injectivity in domain, counter, level and both stored
words. Field bounds are essential: regressions exhibit aliases when discarded
bits are allowed. Real/dummy domains and positive ordinary ordinals are
separated from the empty-top ordinal; positive levels separate it from dense
sentinel zero. The [lane submodule](../../lean/RebuildBound/Spec/NativeRouting/Lanes.lean)
checks the six native qword selector tables. `NativeRoutingSharedLanes` preserves
the full same-partner key; `NativeRoutingInterleavedLanes` preserves both input
blocks and checks the eight-tag gather and four-tag tail, including arbitrary
padding messages. Both hold for any operation on each pair of blocks. This
proves finite assembly and ordering, leaving byte packing, AES rounds, native
loop/memory behavior, compiled execution and family correspondence explicit.
The [family submodule](../../lean/RebuildBound/Spec/NativeRouting/Families.lean)
connects constructor guards to the canonical `familyOf` coordinates.
`NativeRoutingLifetime` bounds seeded and speculative model ordinals for both
starts, reserving initialization even for an empty start, and transfers the
separate full-window bound at each original level. `NativeRoutingFamilyBounds`
derives the canonical family's positive 15-bit level and 48-bit ordinal.
`NativeRoutingFamilyEncoding` identifies complete messages exactly by canonical
family, domain and stored key, allowing intentional producer/consumer sharing.
Native geometry mapping, counter progression and publication correspondence
are explicit.

**Callbacks and the native adapter.** `ApiAccessLowering` proves the
independent semantics of normalized callbacks: one probed upsert for a
value-only success, source Erase followed by destination blind Write for a
mutable-key success, and Read restoration for an exception.
`ApiAccessCorrectness` and `BatchApiAccessCorrectness31` prove callback-input,
response, and map correctness for a segment at any prefix. They derive the
callback input from the effective probe selection, rather than assuming it is
the logical prior value. See [ApiAccess](../../lean/RebuildBound/Spec/ApiAccess.lean).

`Api.Implements` is a local construction contract: request count, key/probe
alignment, and each supplied record equal to `postRecord` of that request and
its actual effective probe result. It assumes neither prefix-map equality nor
correct returned answers. `BatchApiCorrectness31` derives both; replay transfers
them to actual adaptive runs (`AdaptiveApiCorrectness31`). `ApiFlagRule` derives
the flag rule without lookup correctness or `UnshPromise`, even with arbitrary
dummy words. `ApiAdmissible31` then derives the full setting, including
`UnshPromise`, from ordinary geometry, universe, initialization and schedule
premises plus local construction and agreement with the codec's flag reader.

[NativeAdapter](../../lean/RebuildBound/Spec/NativeAdapter.lean) closes the causal
public-encoding reduction for a program that already issues postrecords.
`NativeLocalAgreement` relates the initial machine observation and each next
operation's observation to the current reference prefix through a state
invariant. Prefix induction proves equality of issued operations and the final
encoded transcript (`NativeAdapterAgreement`); it does not assume whole-run
agreement. Off capacity failure this gives `NativeAdapterOblivious31`, with
error `h·2^-64`, and `NativeAdapterTwoClients31`, with error `2h·2^-64`, for two
programs sharing the shape, full public metadata and encoding.
[NativeApi](../../lean/RebuildBound/Spec/NativeApi.lean) states separate local equations
for the selected entry after forwarding, the inserted record, and the actual
normalized response. `NativeApiCorrectness31` and
`NativeAdapterApiCorrectness31` derive complete prefix maps and returned answers
from them. Confidential API replies are separate from the attacker observation.
To claim full native obliviousness, the latter must contain the entire
accumulated observable trace, including events within an operation; a smaller
projection certifies only that projection.

These are conditional interface proofs. The C++/compiled machine, native byte
codec and initialization normalization, stored-key representation, optional
output buffers and alias behavior still require refinement. Constructing a
native API-aware adaptive program satisfying the local equations on every
candidate transcript is unproved. The fixed-universe endpoints above keep
their public schedule and shape, `geometry31`, and initialized-start
restrictions.

Callback application code and its side effects are outside the bucket-view
security claim. A value-only hierarchy callback completes one underlying
access; a successful mutable-key callback always completes two, even if its
key remains unchanged. An exception restores the source after the first
access and prevents the destination write. Consequently a secret-dependent
exception can shorten the public shape. API map correctness does not make
different completion shapes or callback instruction traces indistinguishable.
Tree/hybrid payload execution is outside the hierarchy proof.

## Premises and their evidence

| # | Premise (Lean name) | Status | Evidence |
| --- | --- | --- | --- |
| P1 | The logical trace (flush units, initialization input and the records' unshadowed bits) is fixed independently of the hash words (the trace is an input of the model) | **Assumption of the fixed-run claims** | Natively this needs a non-adaptive client and a rebuild schedule that does not depend on the words: the unshadowed bits depend on the schedule. That the inline executor's schedule is word-independent holds by reading ([ENGINE_ONLINE](../../lean/RebuildBound/Spec/Model/ENGINE_ONLINE.md) 1.3), with finite evidence from two-secret replay pairs, the engine default policy (`kAuto`, which resolves to `kShare`) included (P10). For adaptive clients P1 is replaced by admissibility on every branch (`AdaptiveSetting`; see [Adaptive clients](#adaptive-clients)); the canonical `Ideal*` endpoints derive it from legal API requests |
| P2 | Keys are distinct within each flush unit (`TracePremises.nodup`) | Proved for the requester model; native discipline audited | `RequesterUnique` proves it for every operation sequence of the modelled requester; the engine clears the current unit's copy of a key before every insert; no violation in any replay run |
| P3 | At most `32 U_1 = 512` records per level-one ordinal (`TracePremises.load`) | Engine fact | Every access inserts exactly one slot into the current flush unit, one ordinal consumes one prefix of `r0` units of `64 s` entries, and `U_1 = 2 r0 s`, so an ordinal holds at most `64 r0 s = 32 U_1` entries; never exceeded in any replay run |
| P4 | Bounded-key C1–C4: every `key.toNat` is below `N ≤ 2^31` (`TracePremises.keys`, `initKeys`; online settings' `keys`). Generic and adaptive forms: all keys lie in one fixed universe of at most `2^31` distinct keys with `key.toNat < 2^64` | **Restriction of those endpoints only** | Abstract operations accept arbitrary finite byte strings; native `Initialize` checks record count against `32 T`, and native key width is a separate contract. The fixed universe includes initialization, every query and supplied record, and tombstones; for C5 it covers every possible branch. The canonical `IdealCapacity` theorem does not need this premise; it uses legal API requests and live capacity |
| P5 | Initialization keys are distinct (`initNodup`) | Caller promise | `Initialize` input contract |
| P6 | Unshadowed-tombstone promise (`UnshPromise`): a flagged tombstone in a top finish's carry tier has no live copy in the prepared top table | **Stated premise**, derived for model runs satisfying `FlagRule` | `FlagSoundness31` ([AdaptiveNative](../../lean/RebuildBound/Spec/AdaptiveNative.lean)) proves that every batch run whose flags follow the engine's `NoOlderLiveCopy` rule meets `UnshPromise`. A flagged slot is a tombstone from a probing lane whose selected record is absent or a flagged tombstone. `ApiFlagRule` derives this rule from local API construction. Concrete agreement of native selected entries and records with the model is part of P8. Replay evidence checked every evaluated top finish with no violation |
| P7 | Ideal hash: one independent uniform 64-bit word per (family, key) (`TapePremises`) | **Idealisation** | Replaces the AES-keyed routing tags with a fresh nonce per family; the PRF distance is accounted outside Lean ([ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md)) |
| P8 | The engine executes the model | Finite evidence plus component proofs | See [The model and the engine (P8)](#the-model-and-the-engine-p8) |
| P9 | C3 and C5: the engine's observation equals (an image `ι` of) the model's view (for C5, the transcript of the adaptive interaction) on every outcome without a capacity failure (the hypothesis on `obs` in `OnlineFailure31`, `OnlineOblivious31`, the batch statements and `AdaptiveOblivious31`). For C5 natively: causally, with the observation before operation `j + 1` a fixed public function of the rows through operation `j`, on every outcome outside `AdaptiveFails`, with the maps fixed before the tapes and the same for every compared secret | **Hypothesis of the obliviousness claims** | The theorems take it as a hypothesis; it is part of P8 for the online layer. Evidence: the engine facts by reading ([ENGINE_ONLINE](../../lean/RebuildBound/Spec/Model/ENGINE_ONLINE.md)) and the view replay (below). The VP2INTERSECT batch matcher is not replayed |
| P10 | The native plan schedule does not depend on the words (the schedule is an input of the statements). For adaptive clients the schedule and the public shape (which operations probe, the chunk widths) are decided by the program, independently of the words and of the client's keys and values | Engine fact, by reading; finite evidence | ENGINE_ONLINE 1.3. Two-secret replay pairs run one operation sequence under two engine secrets (`kHandOver` eager and lazy, and the default `kAuto`, resolving to `kShare`, lazy, initialized and batched). The plans, dummy counters and real/dummy patterns, the units (unshadowed bits included), the outcome and the tables' record sets are identical, while the words and the touched buckets differ ([schema](../../lean/oracle/HIERARCHY_REPLAY_SCHEMA.md), "Two secrets"). The synchronous mode's schedule is `syncSchedule`, proved to meet `SchedulePremises` at `geometry31` (`SyncSchedule31`) |
| P11 | The dummy words are a uniform tape jointly independent of the family tape (`OnlineTapePremises`; `UniverseOnlineTapePremises` for generic/adaptive clients) | **Idealisation** | Replaces AES of the never-repeating dummy counter under the family's dummy nonce `H_F \| 2^63`; P7 covers only the family tape |

## The model and the engine (P8)

### Model decisions

The serialised hierarchy model ([Spec/Model/Hierarchy.lean](../../lean/RebuildBound/Spec/Model/Hierarchy.lean))
makes the following choices. Each is a premise or an abstraction that the
native engine must be shown to satisfy.

1. **Fixed logical trace.** The units written into level one per ordinal, and
   hence every level's key sets, are an input (`Trace`), not a function of the
   words. Adaptive clients are handled separately (C5 and the `Ideal*`
   endpoints) by causal exposure.
2. **One ideal word per (family, key).** The tape is one uniform 64-bit block
   per family, independent across keys and families. This idealises the AES
   tag; the cryptographic distance is accounted separately.
3. **Serialised job order.** Jobs run in dependency order: the level-`l`
   ordinal `v` after its own ordinal `v - 1` (A) and after the level-`(l - 1)`
   ordinal `v b_(l-1)` (B); at the top the preparation and then the finish.
   Natively jobs pause and interleave; identifying their logical inputs and
   outputs with this serial execution is a native obligation. Lanes, helpers,
   scheduling, paused-job cursors and byte layout are abstracted away.
4. **Carry pages.** A producer's tier is read by its consumer as sequential
   64-slot pages of the published tier's slot array, holes included; the
   model's last page takes every remaining slot so that no record is lost on
   overflowed outcomes.
5. **Binary levels.** For fanout 2 the engine plain-copies the first partial
   rather than adopting it, with no capacity test; in the model adoption and
   plain copy are the same table, so one rule serves every fanout.
6. **Top tombstone promise.** The unshadowed flag is set online, so the
   hierarchy model cannot derive it; it is the premise `UnshPromise` (P6).
7. **Load from the access rate.** The per-job load premises follow from at
   most `32 U_1` records per level-one ordinal (P3). Keys are distinct within
   a unit (P2); across the units of one ordinal a key may recur, which the
   chronological prefix deduplication resolves.
8. **Horizon.** The inventory counts one speculative ordinal per level. A
   speculative top finish that consumes a carry completing after the horizon
   performs no capacity test within it, so the failure event counts only jobs
   `WithinHorizon` (the job's level-one trigger time is at most level one's
   last potential ordinal).
9. **The chunk form.** "At most `2^-64` per window of `2^32` accesses" is
   read as: for every `k`, the probability that the run's *first* capacity
   failure lies in window `k` is at most `2^-64`. The window events partition
   `Fails`, so `h` windows cost `h * 2^-64`. The same trace from the start
   determines every window's start state, so no warm-start model is needed.
   Requiring instead that every job of window `k` succeeds on its reference
   inputs would also count failures caused by an overflowed tier from an
   earlier window, which per-job bounds alone do not control.

The model's tables after a failure follow the reference continuation (the
bounded job's analytical output with unlimited storage), so key sets are fixed
by the trace on every outcome.

### Proved refinements and finite evidence

Proved refinements of the native level-one B build to the model's producer
(scalar fixed-width semantics, not C++ semantics): `DirectCache64*`,
`DirectMaskBuckets*`, `DirectMaskSweep*`, `DirectMaskIndex*`, `DirectMask64*`,
`DirectSelect64*`, `DirectNativeCacheCandidate`, `DirectNativeCacheHomeMask`,
`DirectNativeDedup`, `DirectNativeBuild` (the native
flat-prefix build is exactly the model's `DirectMaskedRecords.build`). The
rest of the level-one job (`prepareA`, `distributeABounded`, `finishBounded`,
`finishOutput`) has no native refinement; its premises are packed
storage, SIMD lane-bit extraction, in-order slices, native tag = model word,
the byte-level permutes and the stash layout. Outside level one:
`RequesterUnique`/`RequesterShape` (the online stash's units) and
`LaneFoldExact` (the stage lanes). The `NativeMatch*` and `NativeRouting*`
packages above prove the finite semantics of the stored-key matchers and the
routing encoding.

In the exact matching configuration (stored widths 1–15, and width 16 without
VP2INTERSECT or with `CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT` off), rebuild
cross/self/destination/class masks and dense batch row/column lookup compare
complete stored keys against the same partner. The default VP2INTERSECT build
matches sixteen-byte AES stored keys by segments (rebuild) and halves (dense
lookup); its false-match event is the `matchKey` term of `NativeFailureBound`
and `NativeObservationBound`, bounded by `NativeMatch` (above). The native
engine enforces the request horizon and checked dummy reservations, and
construction checks initialized positions, speculative family ordinals and
complete windows over the declared horizon
([ERROR_ACCOUNTING.md](ERROR_ACCOUNTING.md#outstanding-native-obligations)).

Finite differential evidence, all against the real engine code
([lean/oracle/README.md](../../lean/oracle/README.md) describes the drivers,
fixtures and how to rerun them):

| Evidence | Scope | Result |
| --- | --- | --- |
| Whole-run replay (`lake exe oracle --hierarchy`, [schema](../../lean/oracle/HIERARCHY_REPLAY_SCHEMA.md)) | 64 public-engine runs: small runs (fanouts 2/4/8 and mixed, `L = 2, 3`, `D = 1…8`, `r0, s` variants, initialization, batches, eager and lazy rebuild schedules, forced failures at every job kind, erase- and read-miss-heavy traces), two-secret pairs, and two larger capacity-`2^27` configurations, scalar and batch | Every evaluated table equal lane for lane; trace premises checked on every run; the unshadowed promise on every run that evaluates the top; every forced failure named by the engine fails in the model with the same class. Missing evidence fails the replay, and mutated fixtures are all rejected. `hierarchy_battery_summary.py` summarizes a run's counts |
| Per-job oracles ([oracle/README.md](../../lean/oracle/README.md)) | `d = 2` merge, radix digits 2–8, top finish, top preparation and initialization, native direct job | All agree |
| Current API and `geometry31` replay ([`current_api_tests.py`](../../lean/oracle/current_api_tests.py)) | Scalar and batch runs on the actual `geometry31` allocation and public API runs (batch widths 1/5/16/64) | Public calls drive the API and requester models independently; every call's current unit and frozen prefix, every completed prefix and published table are compared lane by lane (keys, values, tombstones, unshadowed flags, occupancy); callback inputs, presence, exceptions, key changes and batch results are checked |
| Complete-cycle replay ([`complete_cycle_tests.py`](../../lean/oracle/complete_cycle_tests.py)) | Smaller configurations through full top rebuilds, empty and fully populated starts, scalar and batch | Complete dense table comparisons with the dense hierarchy evaluator |
| Wide-key fallback replay (`fallback_wide_tests.py`, `fallback_dispatch_tests.py`) | Every user key width 9–64 without VP2INTERSECT; empty/full starts, scalar/batch requests, shared low stored words below width 16 and shared 16-byte user prefixes above it | No state or view mismatch; corrupted-evidence controls rejected |

The `geometry31` runs rebuild only through the lower levels and initialize few
records; the complete-cycle runs on smaller configurations cover full top
rebuilds. There is no `geometry31` top replacement, near-capacity
initialization or top overflow in these runs. The default replay builds
disable VP2INTERSECT. The optional `ORACLE_VP2INTERSECT=1` builds
([oracle README](../../lean/oracle/README.md#with-vp2intersect)) reach the batch
dense cross-match only in additional lazy-drive `r0 = 8` runs that the scripted
corpus does not include; the dense cross-match is covered by the
`NativeMatchLanes`/`NativeMatchDense` proofs. The
library bounds the initialization record count, not numeric key values, so
replays with keys at or above capacity fail only the numeric-universe check
`trace_premises.N` (P4), which is expected.

The replay's evaluator is a memo over the model's defining equation. Proved
in Lean: its per-step equations and the soundness of each memo entry.
Argued, not proved: the loop invariants of `evaluate` and `checkView`, that
`tracePremises` decides `TracePremises`, and that each native table is
compared with the right memo entry. Evidence of this kind covers the runs
executed, not every trace.

The online engine evidence is the view replay, for the arena and the
synchronous engine: the engine's touched buckets and real/dummy flags equal
the model's at every plan entry, with no mismatch. The plans meet the schedule
premises, the synchronous plans equal `syncSchedule`, and no (family, key) is
real-probed twice. The batch real flags come from the dumper's re-coded
cascade: which of two same-key lanes made the real probe rests on that shadow
code and the engine fact `found = dup`.

## Out of scope

Owner threads and helper threads (the replay uses the inline executor; the
engine's synchronous test checks byte equality with the synchronous mode), the
AES-to-ideal distance, complete C++ refinement, configurations outside the
94-member family (the Python certification table covers others with its own
premises), and wall-clock or timing behaviour.

Runs without initialization. The `*31` statements use an initialized
configuration, even when its initial record list is empty. The family exports
also instantiate `initialized = false`: zero seeds, an empty base top and no
initialization job. Their capacity and privacy bounds cover that reference
start. Native correspondence is a separate obligation for either start.
Lookup from an empty start uses the explicit condition
`cfg.initialized = false → run.init = []`; a checked counterexample shows that
the run premises alone are insufficient. `AdaptiveAssembly.exactFor` applies
the replay proof at arbitrary geometry given its fixed-run pattern, freshness
and exact law; a capacity-1024, `D=4` regression discharges these structural
and joint-tape premises from both starts. It establishes an exact reference
law, not a numerical capacity or native-execution claim.

## Adaptivity and obliviousness

**What is observed.** The view is, per operation, the bucket touched in each
hashed main table of the probe plan, plus the publication events (the plan
sequence). The dense prefix and every tier are scanned completely, so they add
nothing. Bucket contents are not encrypted; the view is addresses only, and no
timing. Which operations probe (for example, `WriteWithoutProbe` touches no
hashed table), batch widths and the schedule are public inputs of the
simulator. A real probe uses the word of the table's family and the key (the
same word that placed the key); a dummy probe uses a separate uniform tape
(P11); the bucket is the table's digit map of the word, and the simulator
applies the same map to a fresh word, which also covers the slight bias of
mixed-radix maps.

**Why the view is simulatable.** In the model a failure is followed by the
reference continuation, so every table's key set is fixed by the run; hence
the real/dummy pattern (whether an earlier plan entry holds the key) does not
depend on the words (`OnlinePattern`). Every real probe reads a distinct
(family, key) word (`OnlineFresh`): after operation `j` real-probes key `k` in
a table of family `F`, it reinserts `k`, and every later copy of `k` is either
in the dense prefix or in a table whose window ends after `F`'s and so
precedes every member of `F` in the plan; below the top no key is lost, so a
member of `F` gets a dummy. The view is therefore a fixed map of distinct
coordinates of the uniform tapes and has exactly the simulator's law
(`OnlineExact`) on every outcome. Any observation equal to the view except on
failures is within the failure probability of it (`OnlineFailure`).

**Adaptive clients.** C1–C3 hold for every operation sequence fixed
independently of the hash words; C5 and the `Ideal*` endpoints cover adaptive
clients. A family's words become observable only when its tables enter a
plan, which happens after its window, and with it the population of every job
that reads that family, is complete. The one adaptive channel lies between the
two populations of a merge: A is complete before its old family is exposed, B
only after, so B may depend on observations of A's old homes. A's terms are
therefore bounded at A's cutoff and the union and B terms at B's, each within
the shared class budget; this suffices because the A witnesses do not read B,
and the union and B witnesses read only the new family on a fixed key set.

**Rebuild memory traces.** The rebuild jobs' memory traces are a premise of
the obliviousness claims and of the adaptive capacity claim: rebuild jobs
touch memory as a function of public geometry only (fixed work, masked
kernels), supported by the engine's instruction-census and protected-page
tests. The top preparation and the direct job route A under the new family
before B is complete, so a leak there would let a client choose B to collide
with A. C4 is a pointwise lookup result for arbitrary tapes under its
structural settings; it does not supply an adaptive-client obliviousness
reduction.

## Trusted base and validation

A reader must trust the Lean statements of the exported theorems (the `Spec`
tree: statement modules, the trusted model modules under `Spec/Model/`, the
configuration and family data), Lean's kernel and Mathlib. Proof modules
(`Proofs/`) need not be read. Mathlib supplies the measure theory.
[lean/README.md](../../lean/README.md) explains how to build the library, list the
dependency closure of the headline statements (`scripts/review_surface.py`),
and run the audits:

- every registered theorem's type is exactly its Spec statement constant;
- a from-scratch axiom walk over every Spec and Proofs constant reaches only
  `propext`, `Classical.choice` and `Quot.sound`;
- the library contains no `axiom`, `sorry`, `admit`, `native_decide`,
  `implemented_by`, `extern`, `unsafe`, `run_cmd` or `skipKernelTC`
  (`scripts/lean_forbidden.py`, `scripts/audit_spec.sh`);
- a whole-library `lake env leanchecker RebuildBound` replay re-checks every
  RebuildBound declaration in the kernel. Mathlib's and core's `.olean`s come
  from the pinned binary cache and are trusted with the toolchain.

Non-vacuity witnesses in `lean/spec_tests/` discharge every premise of the
headline statements on concrete runs (for example a full-rate trace with
tombstones after an initialization, with the canonical uniform tape) and show
that the failure events are nonempty. Remark: `UnshPromise` is stated on the model's internal tables; its
trace-level reduction (P6) is library code, not a registered statement.
