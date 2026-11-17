# Record-level semantics of the separated-sources ordinary merge at general digits

Extracted from the engine by reading its code and checked against it: a Python
model built from this text (`oracle/fixtures-radix/model3.py`) matched the
engine lane-exactly on 8594 fixtures at digits 2-8. The Lean model `Sep.lean`
follows these semantics. The fixture counts, failure distributions and
schedule comparisons in this note describe the original pre-CBC extraction.
The current two-block CBC battery produces 8592 fixtures from 9000 knob sets,
with 408 construction refusals; see `oracle/fixtures-radix/README.md` for
regeneration and comparison. This job is the engine's only routing at a
sparse digit above one.
File:line anchors (such as `J:1580-1586`) refer to the
engine revision the extraction was read from and may have shifted; the
function names identify the code.

The Python model written from this text (`model3.py`) matched the engine **lane-exactly on 8594 of
8594 fixtures**, at every digit d = 2, ..., 8. That covers 4 cases with a terminal radix
(d = 3, 5, 6, 7), 3 binary cases with continuation levels (d = 2, 4, 8), stage stashes one and
two buckets deep, one- and two-page tiers, and `range_index_bits` I = 0, 1, 2. It is the
general-digit successor of `ENGINE_D2.md`, which it contains as the case r = 1, e = 1. Section 10
lists what changes relative to that document and to `Job.lean`.

Job: `LevelMergeJob` at an ordinary level l (1 < l < L) and digit d > 1,
`LevelResidualRouting{kDfs, separated_sources = true}`, lanes = 1, whole-phase budget, call
sequence `Begin; PrepareOlder; InstallCarry; FinishMerge`. Paths are relative to `src/oram/`:

| tag | file | tag | file |
|---|---|---|---|
| J | levelarena/cpu_byteslice_level_arena_job.hpp | M | levelarena/cpu_byteslice_level_arena_merge.hpp |
| ST | levelarena/cpu_byteslice_level_arena_stash.hpp | G | levelarena/cpu_byteslice_level_arena_geometry.hpp |
| P | scheduler/cpu_byteslice_subtask_plan.hpp | R | scheduler/cpu_byteslice_subtask_run.hpp |
| RP | scheduler/cpu_byteslice_residual_pass.hpp | SC | rebuild/cpu_byteslice_second_chance.hpp |
| RR | rebuild/cpu_byteslice_residual_range.hpp | DFS | rebuild/cpu_byteslice_dfs_residual.hpp |
| MS | rebuild/cpu_byteslice_mergesplit.hpp | MSS | rebuild/cpu_byteslice_mergesplit_stash.hpp |
| BS | rebuild/cpu_byteslice_butterfly_stash.hpp | RX | rebuild/cpu_byteslice_radix_stash.hpp |
| DN | rebuild/cpu_byteslice_dedup_network.hpp | RM | table/cpu_byteslice_routing_map.hpp |
| RS | rebuild/cpu_byteslice_residual_stash.hpp | DM | rebuild/cpu_byteslice_dedup_masks.hpp |

---------------------------------------------------------------------------------------------------
## 0. Notation and geometry

* `C = 64`. A bucket is a partial map lane(0..63) → record. **Lane order** means ascending lane.
  `LowestFree(X, n)` is the n smallest lanes that X does not occupy.
* `U = 2^K` carry buckets. The digit is `d = r·2^e` with r odd. `k = K + e` is `block_bits`
  (REPORT's b). The output has `N = dU = r·2^k` buckets: r blocks of 2^k. A has `(d−1)U` buckets.
  `m = ⌈log2 N⌉` is `pool_main_levels`. `Log2Exact` is the ceiling log (layout.hpp:563; J:382).
  All of these come from `MakeMergeShape` (M:141-171).
* **Stash depth.** Every stash slot of the job has the same depth `S_A` buckets:
  `LevelStashSlots(MaxOutputBuckets(l), target)/64` (ST:137-181), given to every slot by
  `MakeStashes` (J:1904). This covers the stage stashes, the radix stash and the insertion stash.
  Slot indices: stage j is `older_sheds_[j]` for j < k. The radix stash is
  `older_sheds_[k+1]`, and the insertion stash is `older_sheds_[k+2]` (ST:314-327, J:2169-2172).
* **Tiers.** A's tier is `T_A = OlderTierBuckets(l,d)` buckets. That is `TierBucketsOf(l−1)`
  when d = 2 and P_1 was adopted, and `TierBucketsOf(l)` otherwise (G:602-608). B's tier is
  `T_B = CarryTierBuckets(l) = TierBucketsOf(l−1)`. The output tier is
  `T_out = TierBucketsOf(l)`.
* **Pool and range plan.** The A pool has `P_A = (k + [r>1])·S_A + T_A` buckets.
  `LevelFinishRangePlan` (J:542) calls `ResidualRangePlanFor(kDfs, P_A, m, pages = 1)`, which
  goes through `DfsResidualRangePlan` (DFS:93) and then `PlanResidualRange` (RR:196). This gives
  `D_c = range_bits = min(⌈log2(8·P_A)⌉, m)` and `I = range_index_bits = m − D_c`, with
  `groups = 1` and `range_buckets = 2^{D_c}` leaves. Leaf v covers homes
  `[v·2^I, (v+1)·2^I)`. Leaves `v ≥ ⌈N/2^I⌉` are **padding**. DFS pages = 1 whenever separated
  (`FinishDfsPages`, J:536). The range table has `2^{D_c} + T_B` buckets (RP:354-366, 404-406).

Geometries of the validated fixtures (level l of an L-level fanout-B arena; key 8, value 8,
tag 4 bytes, so `digit_shift = 24`):

| config | d | U | K | k | r | e | N | m | S_A | T_A=T_B=T_out | P_A | D_c | I | live leaves |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| B=2 L=3 l=2 | 2 | 8 | 3 | 4 | 1 | 1 | 16 | 4 | 1 | 1 | 5 | 4 | 0 | 16 |
| B=4 L=3 l=2 | 2,3,4 | 16 | 4 | 5,4,6 | 1,3,1 | 1,0,2 | 32,48,64 | 5,6,6 | 1 | 1 or 2 | 6,6,7 (+1 if T=2) | 5,6,6 | 0 | 32,48,64 |
| same, horizon 2^48 | 3,4 | 16 | 4 | 4,6 | 3,1 | 0,2 | 48,64 | 6 | **2** | 1 | 11,13 | 6 | 0 | 48,64 |
| B=4 L=4 l=3 | 2,3,4 | 64 | 6 | 7,6,8 | 1,3,1 | 1,0,2 | 128,192,256 | 7,8,8 | 1 | 1 | 8,8,9 | 6,6,7 | 1,2,1 | 64,48,128 |
| B=8 L=3 l=2 | 5,6,7,8 | 32 | 5 | 5,6,5,8 | 5,3,7,1 | 0,1,0,3 | 160..256 | 8 | 1 | 1 (d=5: also 2) | 7,8,7,9 | 6,6,6,7 | 2,2,2,1 | 40,48,56,128 |
| B=8 d=6, horizon 2^48 | 6 | 32 | 5 | 6 | 3 | 1 | 192 | 8 | **2** | 1 | 15 | 7 | 1 | 96 |

---------------------------------------------------------------------------------------------------
## 1. Records, words, maps, homes

* A **record** is (key: 8 bytes, value: 8 bytes, whose last byte is the meta byte). Meta bit 0x80
  marks a tombstone. Bit 0x40 is engine scratch (the residual class). The source (A or B) is
  structural. §1 of ENGINE_D2.md applies unchanged.
* **Raw word** `t(x)` is the low 64 bits of AES(key ‖ merge-family nonce) (RM:1029;
  `AesCtrTagU128WordsHost`). The merge family is `CanonicalFamily(l, ordinal)` (J:1528-1531); the fixtures use ordinal = d.
* **Index map** (J:2133-2140). For r = 1 it is `kRaw`: the stored word is `t`. For r > 1 it is
  `kRadixDigit(low_bits = k, modulus = r, digit_shift = RoutingDigitShift(layout) = 24)`, and
  the stored word is `W = (t mod 2^k) | (q(x) << 24)` (`ApplyRadixIndexMap`, RM:245-249). Tag
  bit j < k is bit j of t. The most significant tag byte (`Layout::DigitLine`) holds q.
* **Radix class** `q(x) = (t >> k) mod r`. The whole 64−k-bit high field is reduced
  (`ModSmallOdd` RM:212-239; the fixed-time lane form `ModSmallLanes` RM:353-386 gave the same
  value on every fixture key). With `Q = ⌊2^{64−k}/r⌋` and `s = 2^{64−k} mod r`, the exact
  class masses are **`q_a = (Q + [a < s]) / 2^{64−k}`**, REPORT's q_a in the "Completed-A
  coarse-range bound". Examples: at r = 3, s = 1 for even k and 2 for odd k. At (r,k) = (5,5),
  s = 3. At (7,5), s = 4.
* **Flat home** `H(x) = (t mod 2^k) + 2^k·q(x) ∈ [0, N)`. This is REPORT's D(H), the output
  bucket, and the flat destination word the residual pass tags with: `BasePassSpec` sets
  `digit_shift = low_bits` (J:2254-2268). For r = 1 the residual tag is t itself, whose low k
  bits are H.
* **Way** of a B key: `way(x) = ((t >> K) mod 2^e) + 2^e·q(x) ∈ [0, d)`, so that
  `H(x) = (t mod U) + U·way(x)`. It is recomputed from the key (`FixedMergeRetagOf` R:350-363,
  `PlanBucketWay` RM:793-811 with `way_bits = e` and `reads_digit = (r > 1)`,
  `ComputeBucketWayLine` RM:813-846). B's stored tags are never read.
* **Which bits are read where.** A's binary stage j (block routes and continuations) reads bit j
  of t, j < k. The radix pass reads q. The DFS reads bits [I, I+D_c) of H. The A-leaf offer
  reads the low I bits of H, and the B-tier offer reads the low m bits of H, which is H itself.
  B's placement in its input bucket is `t mod U`, an unchecked input contract.
* Key equality is exact. `CrossBucketDuplicateMask(F, Fm, S, Sm)` returns the lanes of S whose
  key occurs in F.

---------------------------------------------------------------------------------------------------
## 2. Primitives

**MergeSplit(i, j, bit b, stash, kind)** (`PlanMergePair` MS:118-138, `MergeSplitPairStash`
MSS:175-215). It operates on the pair `F = out[i]`, `S = out[j]`. F's records keep their lane
numbers. S's records fill the lowest free lanes in S-lane order. Only S's surplus is shed:
```
F0 = {(l,x) ∈ F : bit_b(x)=0}   F1 = F \ F0
S0 = [x ∈ S, lane order : bit_b(x)=0]   S1 = [... bit_b(x)=1]
a0 = min(|S0|, 64−|F0|);  a1 = min(|S1|, 64−|F1|)
out[i] = F0 ∪ zip(LowestFree(F0,a0), S0[:a0]);  out[j] = F1 ∪ zip(LowestFree(F1,a1), S1[:a1])
Append(stash, S0[a0:] ∪ S1[a1:] in S-lane order, kind)
```
**BlankSplit(i, j, b)** (`MergeSplitPair<Check, BlankFirst=true>`, MS:189-236). F is taken as
empty, and its mask and bytes are not read: `out[i]` := S's bit-0 records compacted into lanes
0,1,..., and `out[j]` := its bit-1 records compacted the same way. Lane order is preserved. It
cannot shed.

**Quad** (`MergeSplitQuadStashFixed`, MSS:336-470). On the members `i + m·2^b` for m = 0..3 it
equals, byte for byte, pairs (0,1) and (2,3) on bit b followed by pairs (0,2) and (1,3) on bit
b+1. Each pair appends to its own bit's stash in that order (`PlanStashMergePermute2`
MSS:277-300). The only difference is that it tests both levels' capacities before writing
(MSS:420), which is the same verdict.

**Append(X, list, kind)**. X is a stash or tier of n buckets. The test is
**`|X| + |list| > 64·n` → FAIL**. On success, `list` goes in order into the lowest free lanes of
bucket 0, then bucket 1, and so on (`PlanStashMergePermute` RS:148-164; the radix kernel's own
loop RX:196-222; `PlanStashMergePermuteRounds` MSS:567-588; `MergeBucketIntoResidualStash`
MSS:650-667). Stage and radix stashes lose nothing during preparation, so their lane order is
their append order. A tier that the leftover dedup has thinned refills its holes first.

**Route(base, s, L)**: `RouteSubnetworkRecursive` (BS:199-251), the only butterfly order. It
routes bits [s, s+L) over the buckets `base + (j << s)`, j < 2^L:
```
if L ≤ 4:                                    -- kernel leaf (kButterflyLeafLevels = 4, BS:153)
  lev = 0
  while lev+1 < L:                           -- fused quads on bits (s+lev, s+lev+1)
    for mid in 0..2^L−1 with mid & (3<<lev) == 0:  Quad at i = base + (mid<<s), b = s+lev
    lev += 2
  if lev < L:                                -- odd last level as pairs
    for mid in 0..2^L−1 with mid & (1<<lev) == 0:
      MergeSplit(base+(mid<<s), base+((mid|1<<lev)<<s), s+lev, stash[s+lev], butterfly)
else:  low = (L>>1) & ~1;  high = L − low    -- SplitSubnetwork, BS:188-191
  for h in 0..2^high−1: Route(base + (h << (s+low)), s, low)
  for l in 0..2^low−1:  Route(base + (l << s), s+low, high)
```
The planner cuts this same tree (`PlanSubnetwork`/`PlanButterfly` P:187-219, tiled arrival
P:249-338), so the order of MergeSplits is this recursion at every budget and tile size.
**The order is not "stage by stage, ascending pairs"** once a route has 4 or more levels (a leaf
quad on bits ≥ 2, or a split). For example, bit-2 pairs run (0,4),(8,12),(1,5),(9,13),...
Pairs with equal low-j bits still run in ascending order. For its effect see §9.

**RadixSplit(p, blank)** (`RadixPassStashRange` RX:377-400 → `MergeSplitRadixStashFixed`
RX:121-283) acts on tuple p ∈ [0, 2^k). It takes the inputs `X_i = out[i·2^k + p]` for
i = 0..r−1, with `X_0 := ∅` without reading its mask when blank.
```
R[i][a] = [lanes of X_i, ascending : q(X_i[l]) = a]
for a in 0..r−1:                                -- output a = bucket a·2^k + p
  Y_a = {l ↦ X_a[l] : l ∈ R[a][a]}              -- block a's own class-a records KEEP their lanes
  for i in 0..r−1, i ≠ a, ascending:            -- the others, LOWER BLOCK FIRST
    n = min(|R[i][a]|, 64 − |Y_a|)
    place X_i[R[i][a][:n]] into LowestFree(Y_a, n), in order   -- lanes not currently in Y_a
    shed_i ∪= R[i][a][n:]                       -- input i's highest class-a lanes
test |radix| + Σ_i |shed_i| > 64·S_A → FAIL prepare-older / radix-route     (RX:184)
Append(radix, X_0[shed_0 asc] ++ X_1[shed_1 asc] ++ ... ++ X_{r−1}[shed_{r−1} asc])
out[a·2^k + p] = Y_a  for every a
```
An input's shed is ordered by its lanes and ignores the class (`shed[i]` is a lane mask). The
merged stash plan (RX:196-222) equals appending input 0's shed, then input 1's, and so on. A
blank output 0 is built only from inputs 1..r−1, filling lanes 0,1,... (RX:95-104).

---------------------------------------------------------------------------------------------------
## 3. A's layout, the embedding, the blank region

* **A is P_{d−1}**, as the previous ordinal's merge published it: `(d−1)U` main buckets plus a
  T_A-bucket tier (RunCase job_test.cpp:469-560; fd3 "the older operand"). It was built under the
  **previous** family `CanonicalFamily(l, d−1)` with that digit's map. With
  `d−1 = r'·2^{e'}` and `k' = K+e'`, record y sits at old home
  `D'(H') = (H' mod 2^{k'}) + 2^{k'}·((H' >> k') mod r')`, where H' is its word under the old
  nonce (REPORT "Completed non-top tables"). The old maps are:

  | d | d−1 | old map | d | d−1 | old map |
  |---|---|---|---|---|---|
  | 2 | 1 | P_1, kRaw K bits (adopted carry at B ≥ 4, in inbox[1]) | 5 | 4 | kRaw, K+2 bits |
  | 3 | 2 | kRaw, K+1 bits | 6 | 5 | radix-5, k' = K |
  | 4 | 3 | radix-3, k' = K | 7 | 6 | radix-3, k' = K+1 |
  |   |   |   | 8 | 7 | radix-7, k' = K |

  **The engine never reads A's old tags or relies on old-home placement.** The copy recomputes
  every tag under the new nonce and the route is complete. The old layout matters only as the
  **input order (bucket, lane)** of A's records. That order decides which records a MergeSplit
  keeps and which it sheds, and the order of stash appends. The fixtures used both the test
  battery's sequential placement and true old-home placement (`--a-at-homes`, 4852 fixtures).
* **P1: embedding** (`PlanPrepareOlderSources` M:292-314 → `PlanMergeOlderBlocks` P:1000-1015,
  `kCopyAndRetagRange/Tile` R:522-531, `CopyAndRetagRange` RM:903). For o < (d−1)U,
  **`out[U + o] := A_main[o]`, with the same lanes and records and new tags**. The region
  `[0, U)` is **publicly blank**. Its masks and bytes are stale, never cleared, and never read:
  the first pass over it is told the region is blank (M:861-872). With stale random masks
  (`--stale-blank`, 2602 fixtures) the output was unchanged.
* **Writers of A's route**, in execution order, in units of U (REPORT's span table plus the
  engine's order):

| d | r,e | P2a pure blocks (Route k levels) | P2b block-0 spans (Route K+u), u = e−1..0 | P3 continuations | P4 radix |
|---|---|---|---|---|---|
| 2 | 1,1 | – | [1,2) | bit K: BlankSplit over [0,1)×[1,2) | – |
| 3 | 3,0 | [1,2), [2,3) | – | – | r=3, input 0 blank, p < U |
| 4 | 1,2 | – | [2,4), then [1,2) | bit K blank; bit K+1 over [0,2)×[2,4) | – |
| 5 | 5,0 | [q,q+1), q = 1..4 | – | – | r=5, blank, p < U |
| 6 | 3,1 | [2,4), [4,6) | [1,2) | bit K blank over [0,1)×[1,2) | r=3, **not** blank, p < 2U |
| 7 | 7,0 | [q,q+1), q = 1..6 | – | – | r=7, blank, p < U |
| 8 | 1,3 | – | [4,8), [2,4), [1,2) | bit K blank; K+1 over [0,2)×[2,4); K+2 over [0,4)×[4,8) | – |

Afterwards, a surviving A-main record x sits in `out[H(x)]`. §4 gives the lanes.

---------------------------------------------------------------------------------------------------
## 4. PrepareOlder

**P0 (Begin, J:1511-1561).** Begin derives the digit, family and nonce and runs `Validate`. It
resets every stash slot and the output tier (`ResetStorage` J:1926-1962) and builds the contexts
(J:2133-2208). Settings: `drop_unshadowed = false`, and `retag_fresher_digits = true` (d > 1,
separated; J:2186). It then copies A's tier occupancy into a private descriptor (`BorrowTier`,
J:1549, J:2230-2245). The plan is the separated branch of `PlanLevelMergePhase` (M:861-903),
with every stage run in plan order on the shared context. With lanes = 1, `StageLanes` is 1 and
no lane stash or fold exists (subtask_cursor.hpp:309-313, 483-491).

**P1** is §3. The copy of each block or span directly precedes its route. Regions are disjoint,
so the interleaving has no effect.

**P2 (A's own networks, kind `butterfly`; `kButterflySubnetwork` R:534-542).**
```
for q in 1..r−1:          Route(q·2^k, 0, k)          -- pure blocks, ascending q
for u in e−1 down to 0:   Route(2^{K+u}, 0, K+u)      -- block-0 spans, LARGEST FIRST
```
Every MergeSplit and quad on bit j uses **`stash[j] = older_sheds_[j]`**. This is **one stash
per bit, shared by every block, every span and the continuation on that bit**, with capacity
64·S_A. Appends are in the execution order above. Fail test (per append):
`|stash[j]| + |shed| > 64·S_A` gives "prepare-older ... at butterfly". No dedup happens anywhere
in A's route. Bit K is written only by spans with u ≥ 1 and by pure blocks with e ≥ 1 (d = 6).

**P3 (continuations, bits K..k−1, `kRouteLevelRange` M:874-889, R:422-445).**
```
for b in K..k−1:
  for i in 0..2^b−1 ascending:
    if b == K: BlankSplit(i, i+U, K)                      -- [0,U) blank: cannot shed or fail
    else:      MergeSplit(i, i+2^b, b, stash[b], route-level)
```
The first continuation is BlankSplit. It leaves `stash[K]` untouched, and it exists only at even
d. The later continuations (d = 4: bit K+1; d = 8: bits K+1 and K+2) **can shed** into the
shared `stash[b]`. At d = 8, `stash[K+1]` already holds span [4,8)'s last-level sheds. So the
"route-level" test counts those too. In 71 fixtures a continuation shed into a `stash[K+1]` that
already held span sheds, and 29 of them then failed at route-level.

**P4 (terminal radix, r > 1; `kRadixRouteRange` M:890-901, R:653-660).**
```
for p in 0..2^k−1 ascending:  RadixSplit(p, blank = (e == 0))          -- radix = older_sheds_[k+1]
```
At odd d (e = 0) block 0 = [0,U) is blank, and **input 0 is blank**: it is neither read nor
shed, and output 0 is filled from blocks 1..r−1 in block order. At d = 6 block 0 = [0,2U)
already holds the continuation's result and takes part like any block. No dedup happens.

After P4 (or after P3 when r = 1) every surviving A-main record is at `out[H(x)]`. Stage
stashes, the radix stash and A's private tier hold the rest of A. The multiset in each stash does
not depend on the order of the MergeSplits; the lane order does.

**Install (I1).** No kernel runs (M:904-906, `ExpectFixedCarry` M:584-592). `BindCarry`
(J:2210-2228) binds B main as `finish_.fresher` **without copying** and borrows B's tier
occupancy into a private descriptor.

---------------------------------------------------------------------------------------------------
## 5. FinishMerge: the fused pass on the fixed insertion

Pool (`SeparatedFinishPoolSlots` J:250-265, bound by `BuildFinishPass` J:2345-2383):

| slot | storage | rank | role |
|---|---|---|---|
| 0 | insertion stash `older_sheds_[k+2]` (S_A buckets) | 0 | drain-only |
| 1..k | stage stashes `stash[0..k−1]` | 2 | swept, distributed |
| k+1 (r>1) | radix stash `older_sheds_[k+1]` | 2 | swept, distributed |
| next | A tier (private descriptor, T_A buckets) | 2 | swept, distributed |
| last | B tier (private descriptor, T_B buckets), `tier_class` | 0 | swept, **direct** (RP:354-366) |

The pass has rule `kClassMark`, fuse site `kFixedMerge`, and all slots owned (reset). The plan is
`PlanFixedCarryInsertion` (M:603-625) → `PlanFixedMerge` (P:895-944), with `merge.bit =
FixedMergeRadix = N/U = d` (P:889). It consists of the prologue (P:620-634), `kFixedMergeOffers`
over B buckets 0..U−1, the epilogue (P:636-647) and **no tombstone drop** (P:943).

**F1 (pool dedup, window kSweptOnly; `ResidualPoolDedupRange` RR:669).** The eligible pairs
(f, s) have rank[f] < rank[s], so only the B tier against each A slot:
`slot_s := slot_s − {x : key(x) ∈ keys(B tier)}` for every A slot (stage stashes, radix, A
tier). Lanes of the private copies are cleared. Nothing else is compared here.

**F2 (direct B copy; R:681-688, `ScatterAndRetagResidualPoolRange` RR:459).** Range buckets
`2^{D_c} + g := B-tier bucket g` for g < T_B. The copy keeps the **same lanes**, retags with the
flat word, and **sets** class bit 0x40.

**F3 (DFS gather; R:724-745).** The gather buckets are the A slots in slot order (stash[0], ...,
stash[k−1], radix, A tier), bucket by bucket, copied lane for lane and retagged with the flat
word. Class bit 0x40 is **cleared**. The **gather order is (slot, bucket, lane)**.

**F4 (DFS partition, `kResidualDfsPartition` R:746-752; DFS:573-936).** Pages = 1, so a leaf
holds S = 64 records. Pool `P = 64·P_A` slots. Node capacity at height h is
`C(h) = min(P, 64·2^h)` (DFS:692-698). The direct height `hd` is the first h with
`64·2^{h+1} ≥ P`, capped at D_c (DFS:702-710). The unit list (DFS:784-818) is: for each live
node c at height hd, first `Direct(hd, c)` (gather → node, selecting bits [I+hd, I+D_c) of H),
then its splits in preorder (left child, then the right one compacted in place). A node is
**padding**, skipped with its leaves cleared, if `node·2^{h+I} ≥ N` (DFS:769-772, 824-830).
Every compaction is stable. So
**leaf v = [pool records with ⌊H/2^I⌋ = v, in gather order], in lanes 0..n_v−1**. One leaf
holds 2^I homes, interleaved in gather order.
* **Fail test:** a unit's child count exceeds its capacity (DFS:936) → "finish ... at
  residual-dfs-partition". The capacities are nested, so this happens **iff some leaf has more
  than 64 records**, counting the sum over its 2^I homes after F1. In 178 fixtures the partition
  failed although no single home exceeded 64. The unit that trips only chooses which unit
  reports. Nothing is shed.
* **The model's trace is not this unit list.** `sDfsTrace` tests every node of the padded tree,
  depth by depth, including the nodes above `hd`. When the pool fits its slots, both orders fail
  iff some leaf holds more than 64 records, so the verdict and the kind agree. The node named by
  `.dfs dd c` can differ from the unit that trips here, and the oracle does not compare it.

**F5 (fixed insertion with fused offers; `kFixedMergeOffers` R:568-582 →
`MergeFixedLevelSourcesOffersRange` SC:1012-1080 → `MergeRadixSourceBucket` DN:523-565 and
`MergeBucketWithResidualOffers` SC:923-996).** The offer sets come from `GatherFusedOffers`
(R:316-345). Set 0 is the leaves under **kTableWins**. Set 1 is the direct B-tier copy under
**kResidualWins**, one plan per tier bucket (`DirectResidualPlan` R:153-156: groups = T_B,
index_bits = m). Tombstone policy is kMerge (R:259-274), so every B record is inserted.
```
ins := insertion stash (empty, S_A buckets)
for i in 0..U−1:                                    -- B bucket i; its records have t mod U = i
  -- (a) dedup of ALL d destinations before any capacity decision (DedupBucketDestinations DM:453)
  for w in 0..d−1: out[i+wU] := out[i+wU] − {x : key(x) ∈ keys(B_main[i])}
  for w in 0..d−1:                                   -- ascending way = ascending bucket i+wU
    ci  := i + w·U
    src := [x ∈ B_main[i], lane order : way(x) == w]
    -- (b) insertion (SC:931-938)
    n := min(|src|, 64 − |out[ci]|);  place src[:n] into LowestFree(out[ci], n), in order
    shed_w := src[n:]                                -- B's highest lanes of that way
    if w == d−1:                                     -- (c) SC:939-949, at the LAST direction only
      if |ins| + Σ_w |shed_w| > 64·S_A: FAIL "finish ... at fixed-merge-offers"
      Append(ins, shed_0 ++ shed_1 ++ ... ++ shed_{d−1})    -- way order, B-lane order in each
    -- (d) A-leaf offer, kTableWins (PlanResidualOfferMerge SC:281-345, round 1 only)
    L    := leaf[ci >> I];  mk := keys(out[ci])
    cand := [lanes of L, ascending : H(L[l]) == ci]  -- low I tag bits == ci mod 2^I (SC:180-206)
    drop := {c ∈ cand : key ∈ mk};  stale := cand \ drop
    u := min(|stale|, 64 − |out[ci]|);  place L[stale[:u]] into LowestFree(out[ci], u), in order
    L := L − (drop ∪ stale[:u])                      -- survivors keep their leaf lanes
    -- (e) B-tier offer, kResidualWins, one ROUND PER TIER BUCKET g = 0..T_B−1 (ChainedResidualOffer SC:502-572)
    for g in 0..T_B−1:
      fc  := [lanes of Bcopy_g, ascending : H == ci]           -- full-home match
      out[ci] := out[ci] − {x : key(x) ∈ keys(fc)}             -- clear (only A-main copies can match)
      v := min(|fc|, 64 − |out[ci]|);  place fc[:v] into LowestFree(out[ci], v), in order
      Bcopy_g := Bcopy_g − fc[:v]
```
* **Selection rules:** B's highest lanes of a way are shed. A candidates are taken in leaf (gather)
  order; B-tier candidates in tier-bucket order, then lane order. A later tier bucket is its own
  round: clears after an earlier round may free lanes lower than those that round filled (202
  fixtures absorbed from bucket 1).
* **Who wins** is as at d = 2. B main beats A main by (a) and beats A pool copies at home by (d).
  B tier beats A main by the (e) clear and beats the A pool by F1. A shed B record beats an A
  leftover by F7.
* The chained single pass and the fallback when there are more than 16 plans
  (`kMaxBucketChainedOfferGroups`, SC:499) give the same bytes. The d destinations of bucket i are
  offered in ascending order. Each candidate is offered only to its own home, so the destination
  order does not change the absorption.

**F6 (epilogue, first drain; P:517-543, R:782-806, SC:1198-1223).** The kDrainOnly pool dedup is
**not planned**: no slot ranks below the drain-only slot's 0 (`ResidualPoolDedupNeeded`
RR:779). The leftover dedup is planned (RR:807).
```
tier := output tier (T_out buckets, reset at Begin)
for rb in leaves 0..2^{D_c}−1 (padding ones empty), then Bcopy_0..Bcopy_{T_B−1}:
  if |tier| + |rb| > 64·T_out: FAIL "finish ... at residual-drain";  Append(tier, rb in lane order)
```
**F7 (leftover dedup; SC:1135-1188, R:605-613).** Units run over (tier bucket, insertion bucket)
pairs. The class is read from each lane's 0x40 bit:
`tier −= {A-class lanes with key ∈ keys(ins)}`; `ins −= {lanes with key ∈ keys(B-class tier lanes)}`.
The second is empty under B main/tier disjointness.
**F8 (second drain; SC:1226-1250).** For each insertion-stash bucket in order:
`if |tier| + |bucket| > 64·T_out: FAIL residual-drain`, else Append. This refills F7's holes first.
**F9 (reset).** It clears every pool slot and does not affect the output.

Output: main `out[0..N)` plus the output tier (T_out buckets). Main counts equal min(X_v, 64),
and the tier holds Σ(X_v − 64)+ records, as the dumper's O1 self-check confirmed on all 3904
successes.

---------------------------------------------------------------------------------------------------
## 6. Failure messages and test order

A capacity failure is `std::runtime_error("level arena: the <phase> phase ran out of room at
<kind>; the certified depth did not hold")` (J:2656-2662). The phase aborts and nothing is
published. The **first failing test in execution order is the one reported**:

| # | step | phase / kind | tested quantity > threshold |
|---|---|---|---|
| 1 | P2, blocks q = 1..r−1, then spans u = e−1..0 | prepare-older / `butterfly` | `|stash[j]| + shed` > 64·S_A, per MergeSplit (a quad tests both of its bits first) |
| 2 | P3, bit K | (route-level) | checked, cannot fail |
| 3 | P3, bits K+1..k−1 (d = 4, 8 only) | prepare-older / `route-level` | `|stash[b]| + shed` > 64·S_A, **including P2's appends to stash[b]** |
| 4 | P4, tuples ascending (r > 1) | prepare-older / `radix-route` | `|radix| + Σ_i |shed_i|` > 64·S_A |
| 5 | F4 | finish / `residual-dfs-partition` | some leaf (2^I homes) holds > 64 post-F1 A-pool records |
| 6 | F5c, per B bucket | finish / `fixed-merge-offers` | `|ins| + Σ_w |shed_w|` > 64·S_A |
| 7 | F6 | finish / `residual-drain` | running total of drained A and B-tier leftovers > 64·T_out, per range bucket |
| 8 | F8 | finish / `residual-drain` | `|tier after F7| + |ins bucket|` > 64·T_out |

Every append only adds, so step 1 fails iff some stage stash receives more than 64·S_A records
during P2. Step 3 is reported iff step 1 passed and some `stash[b]` with b ≥ K+1 holds more than
64·S_A records by the end of P3, counting P2's and P3's appends together. F1-F3, F7 and
F9 always succeed. Engine verdicts observed in the fixtures, per digit (d = 2..8):
butterfly 352/264/330/147/105/56/84; route-level −/−/112/−/−/−/68;
radix-route −/130/−/208/106/111/−; dfs 206/207/361/103/150/58/73;
fixed-merge-offers 95/105/95/57/37/23/15; residual-drain 203/260/294/24/167/31/53.

---------------------------------------------------------------------------------------------------
## 7. Tombstones, class bits, contracts

* **Tombstones are never dropped** and compete like live records: `drop_unshadowed = false`
  (J:2176), kMerge, and no `kDropErased` step (P:943). 2537 fixtures used `--tombs`.
* **Class-bit scratch.** B-tier-derived output records carry meta 0x40 set, and A-pool-derived
  ones carry it cleared. The dumper masks the bit out, so a model should treat it as don't-care.
* **Unchecked input contracts:** B main bucket i holds exactly B's keys with t mod U = i (the
  fixture's own route enforces this, and 406 draws that broke it were skipped as harness
  errors); B main and B tier are disjoint; A main ∪ A tier and B main ∪ B tier are each
  distinct; every bucket holds at most 64 records. **Not required:** A's old-home placement (§3).
* Inputs are never written. B's masks are copied per direction (DN:545-560), and both tiers go
  through private descriptors.
* Budget and resumption: the whole budget runs in plan order. Slicing, pauses, lanes and helpers
  are claimed to be byte-identical (J:1580-1586, job_test.cpp:1419-1480). This is not verified here.

---------------------------------------------------------------------------------------------------
## 8. Order-dependent choices (what a Lean model must reproduce)

* Every capacity **verdict** and every per-home count depends only on multisets. That covers
  stash totals, leaf counts, `min(|src|, free)` and the drain totals.
* **Which records** are absorbed, shed or left over, and every **lane**, depend on these orders:
  1. which surplus a MergeSplit sheds: the second bucket's highest lanes per direction;
  2. which a RadixSplit sheds: each input's highest class-a lanes, with lower blocks placed first;
  3. the **stage-stash append order**: P2's writer order (pure blocks ascending, then spans
     largest first), the Route recursion order inside each writer, then P3. This becomes the
     gather order, then the leaf order, and so decides which A candidates a nearly full home
     absorbs and the leftover lanes;
  4. B's highest lanes of a way are shed; A candidates absorbed in leaf order; B-tier candidates
     absorbed by tier bucket, then lane;
  5. the insertion stash in (B bucket, way, lane) order.

---------------------------------------------------------------------------------------------------
## 9. Schedule variants measured against the engine

`model3.py` can replace P2+P3 with two alternatives. **blank-full** is the "simple form" of the
schedule: Route over the pure blocks, then `Route(0, 0, k)` over all of block 0 with [0,U)
blank, which is the same MergeSplit set. **canonical** is `Job.lean`'s d = 2 schedule
generalized: for each bit j, every pair (i, i+2^j) with bit j of i clear, ascending i over [0, N).
Both are compared with the engine on all 8594 fixtures:

| order | verdict agrees | failure kind agrees | successes record-exact (d=4 / 6 / 8) | lane-exact (d=4 / 6 / 8) |
|---|---|---|---|---|
| engine (this document) | 8594/8594 | 8594/8594 | all | all |
| blank-full | 8594/8594 | all except 180 fixtures at d = 4, 8 | 760/765 · 418/418 · 194/200 | 746/765 · 418/418 · 188/200 |
| canonical | 8594/8594 | same 180 | 760/765 · 416/418 · 194/200 | 746/765 · 414/418 · 188/200 |

Both variants are lane-exact at d = 2, 3, 5 and 7 on these fixtures. They disagree on the kind
name because they have no `route-level` stage: a continuation overflow is reported as
`butterfly`. Their record-level differences come from item 3 of §8. This supports the
approach of T6 (the verdict does not depend on the order). A record- or lane-exact oracle comparison at
even digits needs the engine's Route recursion and writer order. That order is a short
structural definition, given in §2 and §4.

---------------------------------------------------------------------------------------------------
## 10. What differs from d = 2 (ENGINE_D2.md, Job.lean), and what changes at 7 and 8

1. **Map and homes.** Homes are no longer `w mod 2^k` but `H = (t mod 2^k) + 2^k((t>>k) mod r)`,
   with N = r·2^k homes, not a power of two when r > 1. Hence `m = ⌈log2 N⌉`, padding leaves and
   the exact q_a masses (§1).
2. **Several writers per stage stash.** There are r−1 pure blocks and e spans, run in the order
   of §3, instead of one span. `Job.lean`'s `canonicalOps` (stage by stage, ascending) differs from
   the engine in two ways:
   * inside a writer, once a route has 4 or more levels (§2). This never changed an output in
     the fixtures; at d = 2 with K = 3 the two orders are identical, which is why ENGINE_D2's
     "equivalent sequential order" was exact;
   * in writer order at d = 4, 6, 8 (spans largest first, pure blocks before span [1,2)). This
     changes records and lanes in a few percent of cases (§9).
3. **Continuations that shed** (d = 4, 8): bits K+1..k−1 go through a normal MergeSplit into the
   shared stash with test kind `route-level`. Only bit K is blank. At d = 8 the continuation
   shares `stash[K+1]` with span [4,8).
4. **Terminal radix** (d = 3, 5, 6, 7): RadixSplit per tuple, with its own stash
   (`older_sheds_[k+1]`, depth S_A) in the swept pool after the stage stashes. It is blank-first
   at odd d. The kind is `radix-route`.
5. **The insertion fans out d ways.** The way is `((t>>K) mod 2^e) + 2^e q`, computed from the
   key. All d destinations are deduplicated before any insertion. The insertion capacity is tested
   once per B bucket, at the last way, with sheds appended in way order.
6. **I > 0** (all B = 8 shapes, and U = 64 at B = 4). A leaf holds 2^I homes. The A-leaf offer
   selects by the low I bits. The DFS event is a leaf sum. The drain order interleaves homes
   within a leaf.
7. **Tier widths.** With T_B = 2, B's tier is two offer rounds per destination. With
   `T_out = 2`, drains fill tier bucket 0 and then bucket 1. With S_A = 2 (horizon 2^48), every
   stash fills bucket 0 and then bucket 1. All three were exercised.
8. **d = 7**: r = 7, e = 0. There are six pure blocks, blank-first radix-7 (R = 7 kernel;
   `kMaxRadix = 7`, RX:52), way = q, and a 3-bit digit. **d = 8**: r = 1, e = 3. The map is kRaw,
   with no radix stash. The spans are [4,8), [2,4), [1,2), with continuations K (blank), K+1 and
   K+2. The way is `(t>>K) & 7` (way_bits 3, no digit). The fan-in reaches
   `kMaxFixedMergeWays = 8` (RX:61), and separated routing requires `d ≤ 8` (M:862-864). Both
   were validated at B = 8: 491 fixtures at d = 7 and 493 at d = 8.
9. **Unchanged:** the pool ranks, F1, the direct B copy, the one-page DFS, the kTableWins and
   kResidualWins chain, the coordinated drain with the leftover dedup, and tombstone handling.

---------------------------------------------------------------------------------------------------
## 11. Where the prose and the code differ, or need care

1. **Span order.** REPORT does not fix the order of the prepared spans, and its bounds do not
   depend on it. The engine runs pure blocks in ascending order and then block-0
   spans largest first (P:1000-1015). This matters for lanes and occasionally for which records
   are placed (§9).
2. **Original-source drain dedup** (REPORT's separated-job argument, sec:separated-residuals).
   As at d = 2 that emission is never planned (RR:779-800). The
   insertion shed meets A only in F7, against drained leftovers. That is correct because of B's
   main/tier disjointness and because a home that received a B shed was already full, so round 1
   absorbs nothing there.
3. **B-tier page scans.** A scan of the B tier's one or two pages is implemented as one kResidualWins round per page,
   in page order. It is not one combined round. Counts agree; lanes do not.
4. **Completed-A proposition (CA).** REPORT's b is this document's k, and its "U = 2^k" is
   2^K. The production I satisfies 0 ≤ I < k in every validated shape (I ≤ 2, k ≥ 4). The event
   "some coarse range > L = 64" is exactly the F4 test. The early population (T_A plus stages
   1..I) is only a proof frontier. The gather order (stash[0..k−1], radix, then A tier *last*)
   affects lanes and which candidates are absorbed, not the F4 event.
5. **"Direct small-pool plan"**: `PlanResidualRange` is direct only when m ≤ 3
   (`kResidualDirectMaxLevels`, RR:103), i.e. N ≤ 8. That never happens in these geometries.
6. **Separated-job storage events.** The claim that preparation and continuation
   writers of one stage visit disjoint nodes of the expanded blank-B network, once each, holds
   (§3 table). The capacity test is on the shared stash (§6 rows 1 and 3), so a continuation can
   fail on room consumed by a span (d = 8).
7. **Cross stages.** At digits 4, 6 and 8 the high cross stages, under separated sources, are
   A-only continuations: they deduplicate nothing and read no B.

---------------------------------------------------------------------------------------------------
## 12. Validation

The tools are in `oracle/fixtures-radix/` (see its README).
* `fd3.cpp`: the extended dumper, copied from `fixtures-d2/fd2.cpp`. Build:
  `c++ -O2 -DNDEBUG -std=c++17 -march=native -mno-avx512vp2intersect -I$REPO/include -I$REPO fd3.cpp -o fd3`.
  `fd3a` is the same build with `-UNDEBUG`, so the engine's assertions are live. Additional knobs:
  `--branching --levels --level --digit --tier-buckets --horizon-log2`, `--a-at-homes`
  (A at old homes under family (l, d−1)), `--stale-blank` (random stale masks in [0,U)),
  `--older-list/--fresh-list/--atier-list/--btier-list "n@H"` (n keys with flat home H) or
  `"n@h/b"` (low b bits of t equal h). The fd2 knobs are kept. The job setup replicates
  RunCase's "sparse", "two-page B tier" and "mixed radix" separated cases (job_test.cpp:2024-2072)
  with the radix map (job_test.cpp:453-462).
* `model3.py` is this document as code (about 370 lines, with coverage counters and the §9
  variants). `gen.py` is the battery: 18 configurations × 500 draws, eight knob modes aimed at
  every test, 8 workers. `stats.py` produces `stats.txt`. `fx/results.json` holds every run and
  `fx/<config>/` keeps two fixtures per configuration.
* **Results:** 8594/8594 lane-exact on main and tier (bucket, lane, key, value, tombstone), with
  the same verdict and message. Every failure named the same phase and kind.

| d | fixtures | successes | failures (bfly / route-level / radix / dfs / fixed-merge / drain) |
|---|---|---|---|
| 2 | 1787 | 931 | 352 / – / – / 206 / 95 / 203 |
| 3 | 1901 | 935 | 264 / – / 130 / 207 / 105 / 260 |
| 4 | 1957 | 765 | 330 / 112 / – / 361 / 95 / 294 |
| 5 | 982 | 443 | 147 / – / 208 / 103 / 57 / 24 |
| 6 | 983 | 418 | 105 / – / 106 / 150 / 37 / 167 |
| 7 | 491 | 212 | 56 / – / 111 / 58 / 23 / 31 |
| 8 | 493 | 200 | 84 / 68 / – / 73 / 15 / 53 |

  A further 1033 fixtures run through the assertions build all matched and triggered no engine
  assertion. Stash sharing between continuations and spans at d = 4 and 8 is exercised by the
  battery (see §10 item 3).

  Path coverage, per digit (`stats.txt` has the full table): sheds at every stage bit 0..k−1;
  continuation sheds at d = 4 and 8; radix sheds at d = 3, 5, 6, 7, with sheds from several
  inputs in one tuple at d = 5, 6, 7; stashes shared by several writers; insertion sheds at every
  way 0..d−1; A-leaf drops and absorptions, including from shared leaves (I > 0); B-tier clears,
  absorptions (with tier bucket 1) and leftovers; pool dedup; leftover dedup; the second bucket
  of stage, radix, insertion and output stashes; and leaf-sum DFS failures.
