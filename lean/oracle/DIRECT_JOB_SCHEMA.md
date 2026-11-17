# Direct-job reference fixture schema (version 0)

`lake exe oracle --direct fixture.json ...` executes the Core-only
`DirectJob.runDigitOne` model and compares the complete result. Exit codes are
0 for exact matches, 1 for well-formed mismatches, and 2 for malformed inputs.
Multiple files produce one JSON line each, with the maximum exit code.

The three reference formats accept **hand/model reference regression** evidence. The
Python fixtures independently calculate expected results, but do not execute
the native scheduler. The native format described below additionally accepts independently exported
native observations; exact logical-unit/check adaptation is not established.
This runner is oracle engineering, not a proof package or a certification.

## Root object

Required fields:

| Field | Shape |
| --- | --- |
| `format` | Exactly `"direct-job-reference/0"` |
| `evidence` | Exactly `"reference-regression"` |
| `geometry` | Geometry object below |
| `inputs` | Original lane lists below |
| `words` | Array of per-key word assignments below |
| `expected` | Complete expected result below |

Numbers are JSON natural numbers of arbitrary precision; negatives, strings,
and fractional numbers are rejected. Booleans must be JSON booleans. Unknown
object fields are ignored, allowing fixture notes without affecting comparison.
The model's natural-number `value` represents the full abstract value identity;
the native format below specifies its complete byte encoding.

## Geometry

```json
{
  "K": 0,
  "digit": 1,
  "output_homes": 1,
  "output_capacity": 64,
  "a_tier_capacity": 0,
  "route_capacity": 64,
  "radix_capacity": 64,
  "insertion_capacity": 64,
  "copy_capacity": 64,
  "ranges": {"kind": "direct"}
}
```

Capacities count records. Geometry is accepted exactly when
`DirectJob.Geometry.Valid` holds: digit is 1 through 8; output homes equal
`digit * 2^K`; output capacity fits insertion and copy capacities; digit one has
zero A-tier capacity; range geometry satisfies its model condition.

`ranges` is either `{"kind":"direct"}` or
`{"kind":"dfs","index_bits":I,"range_bits":R,"pool_capacity":P}`.
A direct range requires at most eight output homes or a zero computed pool.
DFS requires more than eight output homes, at most `2^(I+R)`, positive `P`,
and `P` equal to the model's computed pool capacity. Digit one has zero pool
capacity and therefore uses direct ranges. See `DirectJobContract.lean` for
the remaining pool formula.
Invalid geometry is malformed (exit 2), regardless of the expected result.

## Original inputs and words

```json
{
  "inputs": {
    "a_main": [],
    "a_tier": [],
    "units": [
      [null, {"key": 7, "value": 10, "tombstone": false}],
      [],
      [{"key": 7, "value": 30, "tombstone": true}, null]
    ]
  },
  "words": [{"family": "current", "key": 7, "word": 0}]
}
```

`a_main` is an array of 64-lane buckets, each lane either `null` (hole) or a
record. Its bucket count is `(digit-1) * 2^K`. `a_tier` is an array of records
without holes, bounded by `a_tier_capacity`. A records have distinct keys across
main and tier. `units` is an oldest-to-newest array of logical flush units,
each an arbitrary-width lane array; empty and fully cleared units retain their
original ordinal. A unit may represent multiple native buckets. Keys must be
distinct within each unit; repeated keys across units are chronological
versions. Newest tombstones participate as records and remain in publication.
Ranks are derived from unit/lane order and are never fixture inputs.

A word assignment has `family` (`"current"` or `"old"`), `key`, and `word`.
Every key occurring anywhere in the original inputs requires a current word,
including versions that will be cleared. Every A key also requires an old word.
Repeated assignments to the same family/key are allowed only when equal.
Unused assignments are allowed. A main placement is validated against the old
family via the model's `digitHome K (digit-1)`; current words are shared by all
phases. These checks prevent a missing word from silently using the total
lookup's default zero. Malformed shapes, duplicate keys, missing/inconsistent
words, and invalid old placement are malformed (exit 2).

## Expected result

Digit one executes chronological exact-key dedup, stable per-home selection of
at most 64 winners, and source-order residual drain. Publication main homes
are in home order; records in each home retain source order. Tier records
retain source order across all homes and units. Main trailing holes are
implicit; explicit holes in expected publication are malformed.

A publication has exactly `output_homes` compact record arrays, each of length
at most 64, and a compact tier array:

```json
{
  "kind": "published",
  "main": [[{"key": 7, "value": 30, "tombstone": true}]],
  "tier": []
}
```

A first failed append has a normalized logical check event:

```json
{
  "kind": "failed",
  "event": {
    "phase": "produceB",
    "site": {"kind": "outputTier"},
    "ordinal": 3,
    "occupancy": 65,
    "capacity": 64
  }
}
```

The ordinal is zero-based in the **original logical units**, including empty
and cleared units. Occupancy is measured after the failing append. Failure has
no publishable table. The full event is compared, including phase, site,
ordinal, occupancy, and capacity; a valid but wrong field is exit 1.

Supported phase strings are `prepareA`, `produceB`, `distributeA`, `finish`,
`drain`, `publish`. Site objects have `kind` equal to `radix`, `bTier`,
`outputTier`, or `insertion`; `route` additionally requires natural `bit` and
boolean `continuation`; `dfs` additionally requires natural `depth` and `pre`.
These spellings allow wrong-site/phase controls without conflating a mismatch
with malformed JSON. They are reference identities, not native task indices.

A rejected result is `{"kind":"rejected","reason":"requiresLaterPhases"}`.
A structurally valid later-digit request explicitly returns this result; the
runner never publishes its partial B producer as a complete job. `geometry`
and `inputs` are also recognized rejection reason spellings, but their invalid
fixture inputs are caught as malformed before execution.

## Output and regression

Each accepted fixture produces `file`, `job` (`direct-digit-one`), `evidence`,
`comparison` (`pass`/`fail`), `actual`, and `expected`. Both results use the same
normalized JSON spelling. Complete records (key, value, tombstone), every main
home and lane position, tier order, verdict, and event fields are compared.
Malformed fixtures use the existing oracle `o1: malformed` error envelope.

Run `lake build oracle`, then `python3 oracle/direct_job_tests.py` from this
Lean project. The tests generate expected outputs using an independent Python
newest-occurrence map and chronological home/tier walk. They cover populations
below/equal/above 64, excess 64/65, configurable digit-one tier capacities
31/64/65 with exact/overflow boundaries, tombstone-to-value replacement,
distributed excess and tier order, holes/empty/cleared units, versions and
newest tombstones, failure ordinals, full-record/order/event/verdict mutations,
input/word/geometry rejection, arbitrary-precision values, later-digit
rejection, and valid/invalid DFS geometry. `--keep DIR` retains generated
fixtures for review. All are reference regressions; native fixtures are
produced by the exporter described in "Native direct-job fixtures" below.

## A-phase fixtures (`--direct-a`)

`direct-job-a-reference/0` shares the `evidence`, `geometry`, `inputs`, and
`words` fields above. It requires digit 2–8 and applies the same structural
checks before execution. `expected` is an exact observation object with fields:

- `a_main`: analytical routed main, each bucket exactly 64 record-or-null lanes.
- `a_stashes`, `a_radix`: analytical ordered stage sheds and radix shed.
- `a_trace`: all preparation events with the event object spelling above.
- `unfiltered_pool`: stage sheds, radix shed, then original A tier.
- `b_tier`: analytically continued chronological B residual records.
- `operational_pool`: unfiltered pool with B-tier keys removed.
- `leaves`, `distribution_trace`: stable operational lists and every DFS event;
  direct plans have one list and no distributor checks.
- `bounded`: either `{"kind":"failed","event":...}` or
  `{"kind":"phases-completed"}`. Failure priority is preparation, B production,
  then distribution. This result does not publish a complete later-digit job.

Preparation ordinals span pair and radix operations. DFS ordinals span the
padded depth-major node order; they are not native traversal identities.
Analytical snapshots remain comparable after overflow. They do not assert
native scratch contents after failure. Expected snapshots never define inputs
to the Lean reference; missing or changed observation fields fail comparison.

Run `python3 oracle/direct_job_a_tests.py` after building the oracle. Its separate
Python lane router, chronological producer and range partitioner generate 125
cases across digits 2–8, recursive routes, capacities and order/payload mutations.
The generator copies expected observations independently of fixture inputs so
expected-output mutations cannot silently change the reference inputs.

## Complete execution / finish reference mode

`oracle --direct-finish FILE...` accepts format `direct-job-finish-reference/0`.
The `evidence`, `geometry`, `inputs` and supplied `words` fields follow the same
original-input contract above. The mode accepts digits 1–8 and recomputes the
complete bounded job, preserving phase priority: A preparation, B production,
A distribution, insertion, drain, publication. Malformed structures remain exit
2; expected-result mismatches exit 1; matches exit 0. Mixed batches process all
files and return the greatest exit status.

`expected` is an object containing:

- `finish_main`: analytical main buckets as full arrays of records/null lanes.
- `insertion`: insertion records in source/way append order.
- `remaining_leaves`: A leaves remaining after offers, in range order.
- `remaining_b_tier`: B-tier pages remaining after offers (one logical page).
- `raw_tier`: analytical drained lanes, including holes left by ranked resolution,
  before trailing output-width padding.
- `finish_trace`: insertion events followed by preliminary and final drain events.
- `bounded`: `{ "kind": "published", "main": [...], "tier": [...] }`, or
  `{ "kind": "failed", "event": {...} }`. Published main and tier both preserve
  actual lane positions; the tier includes trailing padding to output capacity.

At digit one the analytical view has producer main lanes, producer tier as
`raw_tier`, and empty insertion, leaves, remaining B tier and finish trace.
B-production events still determine bounded failure. At later digits analytical
finish fields are present even after earlier A, B or distribution failure; they
are witnesses for regression, not publishable output. Bounded failure never
contains a table.

Insertion ordinals count source buckets; drain ordinals count A leaves, then the
single B-tier list, then the final insertion append. Empty units count. The
source-bucket transition is atomic at this logical boundary: native final-way
check/offer timing and physical drain bucket batching remain adapter obligations.
The independent generator additionally checks successful complete records against
a newest-key map, uniqueness, placement, saturation and exact excess. This is
regression evidence, not the still-open universal correctness proof or C++
correspondence. Run `python3 oracle/direct_job_finish_tests.py`; `--keep DIR`
retains generated fixtures.

The `--direct-finish` report also includes `analytical_result`, recomputed by
continuing the whole job analytically and then selecting its first failed
logical check (or padding its successful output). This must equal
`expected.bounded` in addition to the existing complete observation comparison.
The fixture schema is unchanged. This checks the newly proved whole-job
simulation on all valid regression fixtures, including earlier phase failures.


## Native direct-job fixtures (same `--direct-finish` mode)

`direct-job-native/0` sets `evidence` to `native-differential` and reuses the
original `geometry`, `inputs`, and supplied `words` contract above. The real
`LevelMergeJob` exporter is `direct_native_dump.cpp`. It calls
`Begin`, `PrepareOlder`, `InstallCarry`, and `FinishMerge` against native
storage and checks original main/prefix/tier bytes and masks remain unchanged.
It exports original snapshots before starting the job; no model result is used
to construct native expected observations.

Keys are the full native 8-byte stored key as an unsigned natural. Values are
all eight payload bytes, including the final metadata byte, encoded as a
little-endian unsigned natural. Only `kMetaResidualClass` (0x40 in the final
byte) is masked because it is scratch. Tombstone bit 0x80 and every other
payload bit are preserved. Null lanes represent native occupancy-mask holes;
main lanes and padded tier lanes are compared exactly, without sorting.
Wide keys/values, arbitrary dummy bytes, tags and post-failure scratch are
outside this exporter’s scope.

`expected` is either the native publication (`kind`, exact `main` and `tier`
lane arrays), or a normalized failure:

```json
{"kind":"failed","phase":"produceB","site":{"kind":"bTier"}}
```

Failure comparison projects both bounded and analytical reference results to
**phase and check class only**. Logical ordinal, failed occupancy, route bit,
continuation flag and DFS node are intentionally omitted. Native chunking and
DFS traversal have not been proved to identify those reference fields. A
failure exports no publication. Unknown native exceptions fail the exporter;
recognized overflow messages retain their native text under `native.message`.
This finite comparison is not the universal native failure/refinement proof.

`observations` is a required object with any of the following independently
read successful phase boundaries: `a_main`, `a_stashes`, `a_radix` after A
preparation; `b_tier` after B installation. Their spellings match the A-phase
schema above. Unknown boundary names are malformed. Omitted boundaries mean
unobserved, never an inferred match. No unavailable analytical continuation
state is invented after native failure. The oracle recomputes available
reference boundaries solely from original inputs and words, and compares every
exported boundary exactly. Reports expose `actual`, `analytical_result`,
`reference_boundaries`, and `snapshots` pass/fail.

From the Lean directory, run:

```sh
lake build oracle
python3 oracle/direct_native_tests.py --keep .lake/oracle/direct-native
```

The driver compiles an assertions-enabled native exporter, runs all eight
selected K=4 digit geometries with 64-record stores, and adds separate controls
for small direct A, spread excess, 128/512-record output tiers and DFS capacity
boundaries. Native below-64 output tiers are unavailable; those remain reference
controls. Full records, lane positions, tier order, failure class and publication
mutations must be detected; malformed original words/evidence/geometry and mixed
batch exit codes are checked. Native fixtures are finite regression evidence;
probability applicability, exact native check identities, whole-job resume and
universal C++ correspondence remain separate obligations.
