# Cryptographic and stored-key error accounting

This accounting is conditional. It does not discharge native cryptographic,
matching, history or placement obligations, and supplies no unconditional
`2^-64` certificate. Capacity estimates in the ideal reference experiment
must reserve room for these separate errors.

The canonical arbitrary-key theorem supplies `eta_capacity = h * 2^-64`
for the 94 certified geometries, both starts and legal clients preserving live
capacity over `h` windows of `2^32` accesses, including independent countable
client seeds. See [IdealCapacity](../../lean/RebuildBound/Spec/IdealCapacity.lean) and
[IdealOblivious](../../lean/RebuildBound/Spec/IdealOblivious.lean). This discharges the
ideal reference term only. Native normalization, matching, routing construction,
lifetime and execution/observation coupling still require their own bounds or
explicit hypotheses; the total native target does not follow from this term.

[IdealBounded](../../lean/RebuildBound/Spec/IdealBounded.lean) transfers the same ideal
budget to the outer measure of incorrect actual API results, including truncated
execution, under explicit agreement of actual history, issued requests and
selected results off reference capacity failure. Independent countable seeds
and seed-dependent initialization are supported. This adapter premise still
requires a concrete native proof; the transfer neither removes the native error
terms below nor conditions the capacity experiment on their absence.

[IdealGeometry](../../lean/RebuildBound/Spec/IdealGeometry.lean) supplies the same
canonical analytic chain beyond the numerical family when explicit geometry,
cutoff and exposure certificates are provided. The family theorem is its
instance with the same budgets. This generalization supplies no additional
native error allowance or numerical target for an uncertified geometry.

## Experiments and events

Let `N` be the native execution, `I` a precisely specified ideal replacement
of its secret keyed functions, and `R` the reference experiment used by the
capacity theorem. For the declared workload class and complete observable
transcript, require a hybrid advantage bound `delta_crypto` between `N` and
`I`. In `I`, define `BadNormalize` (distinct user keys have equal stored
keys), `BadMatch` (a comparison accepts a key absent from its partners; in
dense lookup, another row or column of a bucket holding the query's key accepts
it), and
`BadEncoding` (distinct stored-key/family routing inputs encode the same
complete routing message).
Also define `Stopped` for a resource refusal that prevents completion of the
advertised execution. Require a coupling from `I` to `R` that agrees through
the first divergence unless one of these bad events or reference capacity
failure occurs. With unconditional ideal bounds `eta_normalize`, `eta_match`,
`eta_encoding`, `eta_stop`, and `eta_capacity`,

```
Pr_N[failure] <= min(1, delta_crypto + eta_normalize + eta_match
                           + eta_encoding + eta_stop + eta_capacity).
```

This follows by the transcript hybrid inequality, the coupling containment
and the union bound. Independence of events or rebuilds is unnecessary.
Bounds apply before first failure, including initialization, speculative
work and pauses. Do not condition capacity laws on cryptographic, producer,
or publication success. A stopped bad-event analysis instead bounds its
first occurrence on the unconditional coupled space.

[NativeError](../../lean/RebuildBound/Spec/NativeError.lean) checks this composition.
`NativeFailureBound` takes a hybrid bound for the correctness/failure outcome
event and containment of the ideal failure event in the five-event union.
`NativeObservationBound` uses the existing off-failure observation transfer,
an exact reference simulator law, and a two-sided hybrid for the particular
tested public event. Both clip probabilities at one. Their assumptions remain
explicit: neither theorem proves AES security, native agreement or any of the
individual event bounds. In particular, a public-view hybrid alone does not
bound incorrect confidential API results. An eventwise cryptographic premise
can be justified for an admissible efficient test; these statements do not
assert a computational AES bound uniformly over all measurable events.

The stop term is necessary for the full-run contract in `ApiResultsCorrect`,
which requires the advertised request count even if execution is truncated.
For example, a zero routing allowance can stop a run with certainty while its
capacity, normalization, matching and encoding errors are all zero. Enforcing
query limits does not bound their refusal probability. Set `eta_stop = 0` only
with proved completion within the allowances, or an observation contract that
explicitly models the same stops in its reference and simulator. Otherwise an
unknown stop probability is conservatively one. The stopped reference needs
its own proved simulator law: adding a stop rule does not inherit the full-run
exact law, and does not establish full-run `ApiResultsCorrect`. Include horizon and
normalization refusals when they prevent an execution promised by the chosen
contract; requests excluded by that contract need not be charged. Public
observations include stops and the committed prefix, as well as the declared
address/timing leakage. No completion or leakage guarantee follows from the
admission counters alone.

`delta_crypto` may be the sum of explicitly justified hybrid advantages;
it is not automatically an AES single-key advantage. The hierarchy derives
routing and normalization keys as master AES outputs at two fixed distinct
labels. The [construction and reduction](../../src/crypto/DESIGN.md) give
`delta_separation <= Adv_AES-PRP(B, 2 queries) + 2^-128`, with `B` simulating
the complete subsequent execution. The statistical term couples a uniform
distinct pair to independent keys; it is charged once per independently seeded
instance, not once per request. The master must be an independent uniform
secret used only for those two labels. Fixed seeds and cross-instance or tree
master reuse are outside that contract. No numerical AES advantage is
asserted.

After separation, the downstream routing and normalization replacements require
their own advantages, full query budgets and admissible observation model.
Include `delta_separation` in `delta_crypto` once, or absorb it into a justified
joint bound. Routing and fixed-width normalization have the construction
reductions below; native query bounds and execution correspondence remain
separate. Normalization collisions and construction birthday costs remain.

## Stored-key normalization

Native sources: `src/oram/table/cpu_byteslice_stored_key.hpp` and
`src/crypto/hash_primitives.hpp`. User-key width is fixed per instance.

* Widths 1 through 15: the verbatim key, zero-filled in two words, is
  injective at fixed width. There is no normalization.
* Width 16: one AES permutation is injective. Normalization collision
  probability is zero; this establishes neither independent routing words nor
  uniform stored keys.
* Widths 17 through 64: length-prefixed CBC processing compresses keys to 128
  bits. At a fixed width `u`, every message has `m = 1 + ceil(u/16)` blocks,
  where `3 <= m <= 5`, and the padded input encoding is injective.

[NativeKey](../../lean/RebuildBound/Spec/NativeKey.lean) checks these deterministic
encoding facts at byte level. `NativeKeyShort`
proves injectivity for each fixed width 1–16 under explicit injective block
encryption, which only width 16 uses; `NativeKeyVerbatim` proves widths below
16 injective for every block operation. `NativeKeyLong` proves
injectivity of the long-key input messages, preserving all bytes and the length,
and their exact block count. It does not assert digest injectivity or extend
the fixed-width CBC reduction to mixed widths. Native AES and byte-packing
correspondence remain obligations; independent all-width vectors provide finite
implementation evidence. Mixed-width zero-filling aliases (nine versus fifteen
bytes, and fifteen versus sixteen even under an injective block operation) are
checked negative witnesses, so the fixed-width premise cannot be dropped.

Widths 1–15 perform no normalization. At width 16, collisions need no random
replacement: in the independent-subkey hybrid the routing reduction simulates
the injective normalization with its own independent key, so `eta_normalize = 0`.
Then `delta_normalize = 0` as well, unless another term uses the values of
width-16 stored keys. Segment matching does (see stored-key matching below): with
it on, replace the one-block AES by an ideal permutation, charging
`delta_normalize <= Adv_AES-PRP(B_normalize, Q)` with no statistical term.

For a fixed width above 16, the same CBC theorem used for routing gives

```
delta_normalize <= min(1, Adv_AES-PRP(B_normalize, at most m*Q queries)
                          + 2*m*m*Q*Q / 2^128).
```

The [normalization construction](../../src/crypto/DESIGN.md#normalize-wide-keys-without-discarding-their-distinguishing-bytes)
specifies the reduction. It replaces normalization by a 128-bit random function
under adaptive queries, with routing simulated using its independent key.
Memoization makes `Q` the number of distinct user-key inputs; simulation time
still includes repeated calls. The bound already includes the underlying
PRP/PRF switch. Fixed width and exclusive use of the normalization key are
required; this is not a mixed-width guarantee for the generic helper.

In an ideal random-function experiment with at most `Q` distinct user-key
inputs, even adaptively selected inputs obey
`eta_normalize <= min(1, Q*(Q-1)/2^129)` when each genuinely new input receives
an independent uniform 128-bit response conditional on the complete prior
transcript. Sum `(i-1)/2^128` at the `i`th fresh query. Repeated input queries
add no collision opportunities. Include keys supplied by initialization,
reads of absent keys, writes, erases and speculative input processing; an
access count alone is not a proved bound on `Q`. For several instances sum
per-instance terms unless a common function requires one shared query count.

For the modeled complete-message ideal execution, the checked
[linear endpoints](../../lean/RebuildBound/Spec/NativeMatch/LinearCoded.lean) use
a local collision event covered by a canonical pair inventory of exact
comparison sites and shared-family routing aliases. The inventory is chosen
independently of the normalization random function.
It retains past misses and deleted keys where their comparisons or
family exposure require them, without declaring every lifetime collision bad.

For fixed certified geometry and start `g`, let `q = ctx.accesses` count actual
charged lanes, including blind accesses, with `q <= h * 2^32` and `h >= 1`.
The explicit natural coefficients `A(g)` and `B(g)` are independent of `q`,
`h`, key identities and random outcomes. At widths 17–64, the checked allowances
are

```
eta_local = min(1, (A(g) + q * B(g)) / 2^128)
eta_best = min(birthday128(init.length + q), eta_local)
epsilon_best = h * 2^-64 + eta_best + canonical ringCost.
```

`NativeMatchLinearCodedFailure` and `NativeMatchLinearCodedObservation` use
`eta_local`; `NativeMatchBestCodedFailure` and `NativeMatchBestCodedObservation`
use `eta_best`. The latter compare certified bounds on the same complete-message
failure and public-observation events. Failure is at most
`min(1, epsilon_best)`. Each observation direction adds the same `epsilon_best`
to the other event probability and caps at one. Width 16 retains zero
normalization cost. There is one normalization charge, and the existing
capacity-plus-VP2 allocation remains `h * 2^-64`; the new allowance is additional,
not absorbed into that allocation. The proof uses unconditional routing
marginals and a guard decoded from sparse local diagnostics and recorded replies.

The [public-check endpoints](../../lean/RebuildBound/Spec/NativeMatch/Public.lean)
retain the valid-context and fixed-width premises, but derive `FieldsFit`,
`CounterFit` and zero canonical ring cost from `NativeMatchPublic.check ctx = true`.
The finite Boolean check tests each level's last potential-coordinate time below
`2^48`, `accesses * (4 + 2 * allocatedSlots.length) < 2^64`, and ring readiness
using only the public shape and consumed-prefix snapshots. The time bound covers
speculative dependency cones; certified membership supplies the 15-bit level
bound. The reservation bound includes blind accesses and all main/tier slots.
Both arithmetic checks are sufficient, conservative conditions.

`NativeMatchRingPublic` proves that the reference ring guard equals this public
shape check for every oracle outcome. `NativeMatchRingCost` therefore gives
cost zero when it passes and one otherwise. Public schedule validity alone does
not imply progress: a stalled consumed-prefix count can eventually fail the
guard. `NativeMatchPublicFailure` and `NativeMatchPublicObservation` use
`h * 2^-64 + eta_best` on the original complete-message events when the combined
check passes, with no separate ring probability premise. This is a model check,
not a new native admission check or a proof of scheduler progress.

These ideal execution bounds do not bound every collision among lifetime normalization
calls, model eager compiled startup, or discharge
compiled execution and resource/completion stops. The coefficient formulas are
in REPORT.pdf ("Lifetime accounting");
[code/linear_wide_key_components.py](code/linear_wide_key_components.py)
evaluates them for every certified geometry and start. The normalization CBC term
`2*m*m*Q*Q / 2^128` above and routing CBC term `8*Q_route*Q_route / 2^128` below
still use their lifetime input counts. Standalone, discarded and
speculative calls remain in those budgets. The local actual-`q` theorem does
not make the total deployed error linear.

[NativeNormalize](../../lean/RebuildBound/Spec/NativeNormalize.lean) checks this
analytic step. `NativeNormalizeFresh` derives the joint fresh-answer law on an
arbitrary-byte-key random-function tape from injective replay keys and exact
replay fibres. `NativeNormalizeAdaptive` constructs those fibres and proves
measurability for a chooser that receives only the preceding answers. It needs
only branchwise freshness, not a fixed key dictionary or an assumed answer law.
`NativeNormalizeIndependent` integrates measurable key choices depending on an
independent environment, including an entire infinite oracle tape. It derives
joint measurability and the product law of that environment and fresh answers;
the environment need not be countable. The product experiment is essential:
uniform marginal laws do not justify using a correlated environment.
`NativeNormalizeBirthday` bounds collisions among `Q` independent
`bits`-bit answers by `min(1, (Q.choose 2) / 2^bits)`.
`NativeNormalizeBound` transfers that bound to a returned key/fingerprint trace
using answer slots: every returned fingerprint equals its assigned answer,
and distinct keys have distinct slots. The trace can depend on the answers;
repeated entries can reuse slots. All laws and correspondence premises refer
to the same unconditional experiment. Uniform marginals alone are insufficient.

At 128 bits this is the displayed collision allowance, and it supplies the
normalization term of `NativeError`. `NativeNormalizeConversions` supplies
a generic bounded-width conversion adapter. Each replay slot either introduces
a real key, reuses a cached conversion, or returns nothing. Repeated and unused
slots query distinct proof-only keys longer than the real-key width; those
answers never reach the conversion chooser. Freshness, answer slots and exact
persistent-tape conversion steps are proved, so the same birthday bound follows
without assuming those correspondences.

Here `Q` bounds all replay slots. `NativeNormalizeTrace` transfers this
result directly to a chronological conversion trace of length at most `B`.
Its local equation identifies the next conversion and tape answer from the
preceding returned history, for every position below `B`. Positions beyond the
trace length must return `none`; repetitions still count as conversions. The
proof identifies each prefix with the existing replay; unused conversion slots
form a suffix, while repetitions retain the replay's fresh-padding treatment.
Thus unused reservations, waiting and failed attempts with no conversion
add no trace entries; computed conversions discarded by rollback remain in the
trace. The bound is `birthday bits B` on the same unconditional experiment.

The [native conversion inventory](../../src/oram/levelarena/DESIGN.md#normalization-budget)
identifies the scalar, initialization and batch sites. Establishing their compact
trace, length bound, causal local equation and independent environment still
requires execution correspondence; admission alone proves no causal equation.
The longer padding keys extend only the ideal random function; they are neither
native conversions nor AES calls. No second ORAM engine or cryptographic
replacement is introduced, and the capacity experiment remains unconditioned.

At `Q = 2^32`, the collision expression is strictly below `2^-65`. It is charged
separately from the normalization construction bound, which is larger. For
widths above 16, and at width 16 with segment matching on, one valid sequence
is key separation, normalization replacement, then routing replacement, yielding
`delta_crypto <= delta_separation + delta_normalize + delta_route`, clipped to
one. All reductions include the remaining execution in their running times.
The birthday term cannot be applied to a public hash or merely from uniform
output marginals. It bounds the unconditional collision event in the stated
random-function hybrid; the capacity experiment is never conditioned on its
absence. The hierarchy enforces a separate normalization reservation limit
`B = max_key_normalizations`, defaulting to actual capacity plus `max_accesses`.
The [native derivation](../../src/oram/levelarena/DESIGN.md#normalization-budget)
gives `Q <= actual conversions <= reserved inputs <= B`, including standalone
conversion calls, initialization, misses, repeated inputs and failed attempts.
Width 16 uses at most `B` normalization AES block calls, widths above sixteen
at most `m*B`, and widths below sixteen none. These products are mathematical
integer counts. Whole batches reserve on the requester before worker
conversion; initialization reservations survive rollback. Native observation/refinement and the other query budgets
remain open. This admission bound supplies no numerical AES advantage.

## Stored-key matching

### Exact configuration

This configuration covers stored widths 1–15 always, and width 16 when
VP2INTERSECT is absent or `CPU_BYTESLICE_ORAM_WIDE_KEY_VP2INTERSECT` is off.
All four rebuild entry paths use same-partner comparisons:
`CrossBucketDuplicateMaskAt`, `DedupBucketDestinationsWide`,
`CrossBucketClassDuplicateMasksAt`, and `BucketSelfDuplicateMask` in
`src/oram/rebuild/cpu_byteslice_dedup_masks.hpp`. Network joins, residual pools,
offers, drains and shed cleanup call these paths. In this configuration, wide
keys compare exactly, including partial high words and caller-selected keys.

For wide keys, synchronized rotations retain the same partner for both
64-bit halves. The OR of their XOR differences is zero exactly for full-key
equality. Unsigned minimum reduces those scores over partners. Complete-key
zero repair excludes dummy partners; self comparison admits only earlier
slots. No independence or segment-freshness premise is needed for these
predicates.

The dense direct-slot matcher exists only with VP2INTERSECT, at stored widths 4,
8 and 16. At width 16, `MatchUniqueDenseSlots<8, 2>` in
`src/oram/table/cpu_byteslice_dense_match.hpp` uses same-partner equality within
each row and column only with the option off. Full-key uniqueness within the
bucket remains the direct-slot matcher's contract. Other widths, and builds
without VP2INTERSECT, use the generic online byte-sliced matcher. That matcher
and batch duplicate forwarding compare complete keys in every configuration.

The XOR/OR, unsigned-minimum, rotation, dummy-repair and selected-partner laws
above are elementary; native scalar differential regressions exercise the C++
paths. Native packing, machine instructions and complete execution refinement
are not proved for this configuration.
Subject to that correspondence, exact stored equality contributes zero
`eta_match`; it still inherits `BadNormalize`. Equal routing tags or homes
are occupancy collisions, not key equality. The full native bound remains
conditional, including uniqueness and every other adapter obligation.

### Segment configuration

The default VP2INTERSECT build matches stored width 16 approximately. Through the key API only user keys of 16 bytes or more
reach that width, so the rule sees only secret-keyed AES outputs. The engine's
`*Stored` entry points are excluded below.

- **Rebuild.** `WideSegmentMatchMask` and the segment branches of
  `DedupBucketDestinationsWide` and `CrossBucketClassDuplicateMasksAt` AND four
  32-bit memberships. Each membership is exact over real partners, with
  per-segment zero repair, class separation, and (in the self branch) earlier
  slots only. The self branch is reached only from debug assertions.
- **Dense lookup.** `MatchUniqueDenseSlots<8, 2>` ANDs two 64-bit half
  memberships per row and column. It runs on full 64-lane groups when a plan
  has 16 to 65,536 dense buckets.

Each segment may come from a different partner. A rebuild false match silently
drops a live entry. A dense false candidate in a later row or column displaces a
present key's hit; final verification prevents only false acceptance. The
displaced lookup also skips a removable-unit clear and changes later
real/dummy probes. `BadMatch` must therefore be charged in both
`NativeFailureBound` and `NativeObservationBound`; it is in both statements'
bad-event union. The segment rule itself has no false negatives
(`NativeMatchSound`): a true member passes every segment. A dense displacement
is a lookup false negative caused by a false match in another row or column.

[NativeMatch](../../lean/RebuildBound/Spec/NativeMatch.lean) checks the rule and its
probability, independently of lanes and execution:

- `NativeMatchExact`, `NativeMatchSound`, `NativeMatchCover` and
  `NativeMatchCountBound`: one partner supplying every segment is exactly
  membership; there are no false negatives; a false match needs two different
  donors; and at most `m^k` stored values pass with `m` partners and `k`
  segments.
- `NativeMatchBridge`: off a comparison's false-match event, the rule agrees
  with logical key membership for any stored-key map.
- `NativeMatchIndependent` and `NativeMatchPermutation`: for a comparison
  inventory measurable in an environment independent of the stored keys, the
  false-match probability is at most `min(1, W / 2^128)`, where
  `W = sum over comparisons of m^k`. The first covers the normalization random
  function above sixteen bytes. The second covers one ideal permutation at
  sixteen bytes, with no normalization collisions.
- `NativeMatchRelabel`: at width 16, routing by the permuted stored key has the
  joint law of routing independent of the permutation.

The rates are:

- `64^4 / 2^128 = 2^-104` per compared rebuild slot with 64 partners;
- `2^-98` per directional bucket pair;
- at most `14 * 8^2 / 2^128` per dense query and a bucket holding its key. Each
  row or column subset is one comparison; in a bucket without the key, full-key
  verification rejects every candidate.

A comparison inventory that reads the stored keys is outside these theorems:
with one-bit words, a tape-adaptive choice exceeds the bound.

The ideal term is
`eta_match <= min(1, (W_rebuild + W_dense) / 2^128)`. The weights come from the
exact-matching reference's comparisons in the window. They are public functions
of the schedule and of the number of records each rebuild consumes; no native
counter enforces them.

**Rebuild comparisons.** A per-site model of the public rebuild schedule
computes them for every certified geometry. It covers eight production sites:

- level-one prefix deduplication;
- the fixed insertion of B into A at separated and top finishes;
- A-leaf offers and B-tier offers;
- the top's resolve step;
- residual-pool deduplication;
- class-marked leftover deduplication.

Initialization and top preparation compare nothing. The count per job does not
depend on timing: inline, threaded and synchronous executors run the same jobs,
there are no retries, and speculation runs only preparation. The per-window
model gives the same envelope for both starts; the registered finite-prefix
proof (`NativeMatchProduction`) instead follows each start's actual
seed-preserving ordinals and derives the tighter `S_min` counts.

A subject is a real element-side record. Every access inserts exactly one
entry, so a carry into level `l` holds at most `32 U_l` records. The top's older
table holds at most its live capacity. A call with `n` subjects and `p`
partners (both at most 64) has weight `n * p^4 <= 64^4 * min(n, p)`, so each
call can be charged `min(n, p)`. Some sites compare records of one source; for
example, A-leaf offers have A's own records among their partners. Any match
there is false, and these calls are counted.

| Charge per call | Comparisons per access | `eta_match` per `2^32`-access window |
| --- | --- | --- |
| real subjects | 104.3 | `2^-65.30` |
| `min(subjects, partners)` | 39.8 | `2^-66.69` |
| real subjects, top bounded only by its slots | 138.3 | `2^-64.89` |

Every row is the maximum over the certified geometries. The maximum occurs at
`L8_r2_D8_8.8.8.8.8.8.8` (`2^31`), which makes 5.09 bucket-pair calls per
access. The bounds hold for every routing outcome. Per access, the first row is
`2^-97.3`, below the `2^-96` per-access target that matches the capacity term
of `2^-64` per `2^32` accesses.

**Dense lookup.** A query can lose a hit only in a dense bucket holding its key.
A plan holds a key at most once per online unit and once per live table tier:
at most `3 * r0` plus the arena's slot count, between 11 and 53 buckets. With
at most `2^32` real query lanes, the term is at most `2^-80.5` per window. It
requires bucket uniqueness derived from the exact reference invariants; the
native audit-build check alone does not establish that production obligation.

Applying these bounds natively requires:

- compiled execution correspondence with the finite native model. The registered
  job/hierarchy traces derive actual `S_min` inventory counts and ordinal
  exposures. Exact Lean arithmetic and `NativeMatchProduction` combine matching
  with the actual capacity allocation for all 94 geometries and both starts;
- C++ byte/memory and compiled execution correspondence for the registered
  finite lane semantics. `NativeMatchLanes` proves the actual unpack/mask/zero
  repair operations and both class directions; `NativeMatchDense` proves
  verification soundness and lost-hit coverage by fourteen other subsets.
  The dense trace and `NativeMatchApi` derive logical uniqueness,
  selected-result/removal agreement and complete native adaptive continuation
  up to the first bad event;
- compiled correspondence with the finite native execution, whose agreement
  with the exact reference is proved off capacity, matching, normalization
  and ring-stop events;
- for width 16, the ideal-permutation replacement in `delta_crypto` and the
  relabeling (`NativeMatchRelabel`);
- above 16 bytes, re-indexing routing by stored key to routing by logical key
  over the actual routing reads, with aliases covered by the normalization
  event. `NativeRoutingCoupling` proves the unconditional finite-query lemma
  and message codecs. The sparse logged reader supplies both unconditional
  routing marginals, actual-prefix family coverage, and a decoded local guard
  for the existing native API. `NativeMatchLinearCodedFailure` and
  `NativeMatchLinearCodedObservation` transfer the actual-`q` local allowance
  above to the same complete-message ideal experiment as the unchanged
  `NativeMatchCodedFailure` and `NativeMatchCodedObservation` birthday endpoints.
  The checked `NativeMatchBestCodedFailure` and `NativeMatchBestCodedObservation`
  select the smaller normalization allowance, charging it once. Capacity plus
  matching remains `h * 2^-64`, and canonical ring cost remains additional.
  Native outcomes after a bad event are unrestricted. Public encoding/counter
  fit and cryptographic replacement/lifetime allowances remain explicit;
- that the client neither observes nor chooses stored keys.

The last point excludes the engine's `StoredKey` and `*Stored` entry points,
which are reachable through `ByteMap::engine()`. Through `*Stored` a client can
insert structured sixteen-byte stored keys and force multi-donor matches
outright. Through `StoredKey` a client that controls which keys share a
deduplication bucket can search for donor keys. VP2INTERSECT latency must also
be independent of the data. Disabling the option restores the exact
configuration.

## Routing replacement

Routing uses fixed two-block CBC-MAC under its separated AES schedule. The
first block is the packed identity followed by ASCII `oram-rt1`; the second
contains the complete stored low/high words. All integers are little-endian.
Real and dummy inputs use different packed domain bits; a dummy's key block
is its reserved counter followed by zero. Narrow keys also use two blocks.
The tag is `low64(E(E(B0) XOR B1))`. The exact format, cost and reduction are
specified in the [cryptographic design](../../src/crypto/DESIGN.md#route-a-complete-key-under-an-explicit-identity).

The message encoding is injective in stored key and packed identity, including
cross-domain inputs. The registered
[NativeRouting](../../lean/RebuildBound/Spec/NativeRouting.lean) proof identifies the
native mask/shift expression with bounded arithmetic packing and proves that
complete-message injectivity. Its bounds exclude the aliases produced by
discarded high counter/level bits. Thus structural `eta_encoding` is zero,
subject to native byte/compiled execution and allocated family/counter
correspondence. The registered [lane identities](../../lean/RebuildBound/Spec/NativeRouting/Lanes.lean)
check shared-key interleaving, variable-message loads and both output gathers
for an arbitrary operation on each block pair. They include arbitrary padded
messages; the tail guarantees only the four stored qwords. These finite
identities do not establish AES, loop/memory or compiled-code correctness.
The [family adapter](../../lean/RebuildBound/Spec/NativeRouting/Families.lean) derives
canonical-family field bounds from the constructor's conservative lifetime
allowance, including initialization and speculative ordinals for both starts.
It reuses the existing hierarchy forwarding and preserves intentional family
sharing. This discharges the model's field arithmetic, leaving native geometry
mapping, actual counter progression and publication correspondence explicit.
`BadNormalize` remains separate. Internal CBC block collisions are covered by the construction bound,
rather than treated as collisions of this message encoding.

For at most `q` distinct routing messages, the conservative replacement term is

```
delta_route <= min(1, Adv_AES-PRP(B_route, at most 2q queries)
                      + 8*q*q / 2^128).
```

This is the two-block specialization of
[Bellare–Kilian–Rogaway, Theorem 3.2, Eq. (11)](https://cseweb.ucsd.edu/~mihir/papers/cbc.pdf#page=18).
The reduction permits adaptive inputs, memoizes repeated messages and projects
the full response to 64 bits. Its running time includes the native simulation.
The statistical term already covers the underlying PRP/PRF switch and CBC
collisions. Charge it once in `delta_crypto`; do not add another generic block
switch or encoding-alias term for the same construction.

The count `q` is not the accepted-access horizon. It includes distinct inputs
used by initialization, all rebuild paths, real and dummy probe candidates,
and speculative execution. Reusing a family prefix or recomputing a message
does not add a distinct message, but physical block-call and running-time
budgets must account for executed work, including retries and SIMD padding.
The hierarchy enforces `max_routing_evaluations = R` at both leaf tag
routines, including all of that work. Nonrefundable atomic reservations give
`q <= actual evaluations <= reserved evaluations <= R` and at most `2R`
physical routing AES block calls. The default `UINT64_MAX` is only an arithmetic
ceiling; selecting a useful security budget remains a deployment obligation.
Exhaustion permanently stops the instance and can interrupt accepted work.
The [routing derivation](../../src/oram/levelarena/DESIGN.md#routing-budget)
states the exact accounting and stop contract. Substituting `q = R` is
conservative; it supplies neither a numerical AES advantage nor a running-time
bound for the full simulation, which also includes waits and client callbacks.
The reduction assumes secret internal state and no observations of intermediate
CBC values; connecting the declared native address/control-flow transcript to
that oracle experiment still requires execution/observation correspondence.

At `q = 2^32`, the conservative statistical term is `2^-61`; native routing
volume can be larger than the API request count. This construction therefore
does not establish a total native `2^-64` target. A tighter reduction or changed
cryptographic parameters is needed if that total target is required. The
normalization CBC reduction and its block budget remain separate.

## Outstanding native obligations

The engine enforces `max_accesses` for online requests and reserves complete
scalar/batch dummy-counter ranges before probes, with checked multiplication
and addition. Callback adapters preflight their composed access count; tree
batches check the whole position-remapping operation. Access-horizon refusals
preserve the unexecuted operation and allow accepted work to drain.
Construction checks the full declared horizon plus direct initialization,
including one speculative carry per level and complete window endpoints.
That bound also covers padded dense windows and shifted dense IDs; hashed ID
allocation stops below the dense namespace.

The separate normalization budget bounds normalization inputs and block
calls as above; access-horizon refusal is checked before scalar conversion.
The independent routing allowance covers initialization, rebuilds, padding,
speculative work, retries and repeated value-worker evaluations, at every key
width. It supplies a conservative query/block bound without assuming that an
accepted-access counter counts all primitive use. Running-time bounds, native
correspondence, entropy and downstream seeded-construction assumptions remain
separate obligations; a stopped instance is not guaranteed to have completed
its accepted accesses.

1. Establish compiled correspondence and the declared stored-key secrecy
   boundary. The finite default-production lane masks, dense uniqueness,
   full native adaptive first-divergence proof, actual geometry-derived counts,
   exact allocation, sparse local API guard and complete-message coupling are
   proved in the finite operational model. Canonical
   `NativeFailureBound`/`NativeObservationBound` instantiations and the
   complete-message birthday, linear and best-allowance failure/observation
   endpoints are checked ([LEAN_CLAIMS.md](LEAN_CLAIMS.md#api-semantics-and-the-conditional-native-adapter)).
   Public checks discharge model encoding/counter fit and ring readiness; they
   do not establish native schedule realization, discharge deployment
   resource/completion stops or model eager compiled startup.
2. Specify workload/adversary observations and connect the enforced query/block
   allowances to that experiment, including its stop event and simulation time.
3. Discharge entropy, identity correspondence/reuse and exclusive fixed-width
   key-use premises for the actual seeded construction. Key separation,
   normalization and routing have explicit reductions above; their AES
   assumptions, query/time bounds and entropy contract remain conditional.
4. Prove the coupled source-history/placement induction and unconditional
   first-failure coverage; reserve all error subtotals, including resource
   refusal under the advertised completion contract, in the lifetime target.

Until these are discharged, the checker must remain `unproved_applicability`
and its unconditional bound remains one.
