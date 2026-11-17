# Planner configuration space

This page summarizes the conditional numerical certificate over every
configuration the capacity planner can choose. The level-one adapter uses the
direct B producer and completed A-only preparation (see
[README.md](README.md#level-one-and-top-contracts)).

The target is a conditional capacity-failure bound of `2^-64` over `2^32`
accesses. These results assume the source laws and execution premises recorded
with each candidate: logical-history, ideal-family, imported-comparison, start
and inventory-rule premises are not discharged by the Python checker, which
therefore records an unconditional upper bound of one. (The Lean family
theorem in [LEAN_CLAIMS.md](LEAN_CLAIMS.md) proves the `s=1` standard subset
in the ideal reference model.) A candidate above the target
means these component bounds do not certify it; it does not estimate an actual
failure rate.

[REPORT.pdf](REPORT.pdf) gives the mathematics.
[code/bound_table.json](code/bound_table.json) contains exact bounds for public
job shapes. `code/configuration_space_2p{n}.json` contains the default `s=1`
space at capacity `2^n`; `code/configuration_space_s{s}_q2_2p{n}.json` contains
`s=2,4`. Each artifact records candidates, conditional bounds, coverage gaps,
planner defaults, excluded options and source hashes.

## Selected capacity `2^27`

Two reference ledgers at capacity `2^27` meet the conditional target with no
coverage gaps. Their logarithms below summarize exact rational comparisons.

| Geometry (`r0=8`, `D=8`, `s=1`, `q=2`) | Conditional lifetime bound, log2 |
|---|---:|
| [Uniform fanout eight](code/selected_configuration_check.json) | -69.678562 |
| [Default half-fanout ladder](code/selected_configuration_half_fanout_check.json) | -69.678190 |

Both retain status `unproved_applicability`, unconditional upper bound one,
and `complete_configuration_certified=false`. The numerical target result
therefore remains conditional.

## Full planner-space results

All 51 spaces (17 capacities times three stash settings) have complete
native/inventory coverage and no missing job keys. Every planner default meets
the conditional target at each capacity for each `s=1,2,4`, including larger
direct prefixes. All candidates at capacities through `2^30` meet the target. At
`2^31`, five `D=1` geometries in each setting exceed the target; all `D=8`
geometries still meet it.

Entries below are **candidates meeting the conditional target / candidates
considered**. Candidate names, exact bounds and planner defaults are recorded
in the corresponding linked artifact family described above.

| Capacity | `s=1` | `s=2` | `s=4` |
|---|---:|---:|---:|
| `2^15` | 19/19 | 18/18 | 16/16 |
| `2^16` | 20/20 | 19/19 | 18/18 |
| `2^17` | 20/20 | 20/20 | 19/19 |
| `2^18` | 20/20 | 20/20 | 20/20 |
| `2^19` | 20/20 | 20/20 | 20/20 |
| `2^20` | 20/20 | 20/20 | 20/20 |
| `2^21` | 20/20 | 20/20 | 20/20 |
| `2^22` | 20/20 | 20/20 | 20/20 |
| `2^23` | 20/20 | 20/20 | 20/20 |
| `2^24` | 20/20 | 20/20 | 20/20 |
| `2^25` | 20/20 | 20/20 | 20/20 |
| `2^26` | 20/20 | 20/20 | 20/20 |
| `2^27` | 20/20 | 20/20 | 20/20 |
| `2^28` | 20/20 | 20/20 | 20/20 |
| `2^29` | 20/20 | 20/20 | 20/20 |
| `2^30` | 20/20 | 20/20 | 20/20 |
| `2^31` | 15/20 | 15/20 | 15/20 |
| Total | 334/339 | 332/337 | 328/333 |

The shared bound table holds 413 distinct public shapes, comprising
40 direct level-one, 154 separated ordinary, and 73 each for top preparation,
initialization and top finish. Bounds are reused across configurations only for matching keys;
exposures and inventory coverage are recomputed for each configuration.

## Scope and exact keys

The enumeration fixes branching `B=8`, dense-prefix count `q=2`, horizon
`2^32`, automatic per-level tier widths and native stash sizing. It considers
capacities `2^15..2^31`, `s=1,2,4`, supported depths, prefix flush counts
`r0=2,4,8`, binary top digits and the planner's half-fanout and bottom-fanout
ladders. A candidate belongs to a capacity only when its rounded capacity is
exactly that capacity; feasible larger plans are listed separately.

A table key is the job role plus every field of the native configuration-probe
row except its level index. Roles are direct level one, separated ordinary,
top preparation, initialization and top finish. The key retains digit, stash,
output and operand tier widths, direct/DFS partition, and the direct-producer
mode and standalone B-tier capacity. The level index labels jobs; exposure
counts depend on the configuration and are applied when composing its ledger.
Missing keys and stale dependencies fail closed.

Value width affects the planner's memory bill and selected default. It does
not alter the capacity bound for a fixed public shape. The level-one planner
check validates public domains and aggregate source
capacities; actual task/site enumeration is performed by the deterministic
inventory audit. These checks are separate evidence and do not prove the
probability laws.

## Direct level-one obligations

Let `U=2 r0 s`. The chronological prefix is deduplicated before B is selected
by its current low-bit home. The temporary residual count is exactly
`sum_i max(X_i-64,0)`, including overflow spread across many homes. Digit one
writes directly to the configured output tier and has no narrower producer
check. At higher digits, the standalone one-bucket B tier has capacity 64;
its global positive-excess producer bound is charged once at production.

A completes its route with B's region blank. Its stage checks use completed-A
bounds. Its residuals use one-page DFS leaves, or a native direct plan with no
distributor event. The actual A coarse width must satisfy `0 <= I < k` when
the completed-A range theorem is used.

B production and final placement use the same current job family. B residuals
therefore cannot inherit the independent-family law of a published carry.
The A range event is bounded using unfiltered completed A; final insertion and
publication use the complete distinct-union excess. Freshness checks retain
newest records and remove shadowed copies, including B-main records that shed.
Insertion stash and lane capacities are at least the output-tier capacity, so
one output event covers both. These events are union-bounded without assuming
independence or conditioning their marginal laws on earlier success.

Higher ordinary levels retain completed-A separation; top preparation and
initialization retain binary one-page DFS bounds; top finish retains its
separated carry and resolved-live-set excess bounds.

## Reproduction and scope

[code/certify_configuration_space.py](code/certify_configuration_space.py)
enumerates and composes each space using
[code/bound_table.py](code/bound_table.py), native geometry checks and the
deterministic inventory audit. Acceptance compares exact rational bounds;
logarithms are display summaries. Regenerate affected producers after changing
geometry or mathematics; updating recorded hashes alone does not validate old
computations.

From the repository root:

```sh
python3 analysis/bound_certification/code/regenerate.py --dry-run
python3 analysis/bound_certification/code/regenerate.py
```

Other branching factors, horizons, prefix counts, pinned tiers, bank placement
and ladders outside the planner space require matching artifacts. These
numerical results alone do not establish native applicability.
