# Record-level semantics of the d = 2 separated-sources ordinary merge

Extracted from the engine by reading its code and checked against it: a Python
model built from this text (`oracle/fixtures-d2/model.py`) matched the engine
lane-exactly on 1964 fixtures. The Lean model `Job.lean` follows these semantics.
The fixture counts and failure distributions in this note describe that
original pre-CBC extraction. The current two-block CBC battery produces 1949
fixtures from 1964 knob sets, with 15 checked construction refusals; see
`oracle/fixtures-d2/README.md` for regeneration and comparison.
This job is the engine's only routing at a sparse digit above one.
File:line anchors (such as `J:1580-1586`) refer to the
engine revision the extraction was read from and may have shifted; the
function names identify the code.

Job: `LevelMergeJob` at level 2, ordinal/digit 2, `LevelResidualRouting{kDfs,
separated_sources=true}`, lanes = 1, whole-phase budget; call sequence
`Begin; PrepareOlder; InstallCarry; FinishMerge` (fixture_dump.cpp:490-506).
Paths below are relative to `src/oram/`; `J` = levelarena/cpu_byteslice_level_arena_job.hpp,
`M` = levelarena/cpu_byteslice_level_arena_merge.hpp, `P` = scheduler/cpu_byteslice_subtask_plan.hpp,
`R` = scheduler/cpu_byteslice_subtask_run.hpp, `RP` = scheduler/cpu_byteslice_residual_pass.hpp,
`SC` = rebuild/cpu_byteslice_second_chance.hpp, `RR` = rebuild/cpu_byteslice_residual_range.hpp,
`DFS` = rebuild/cpu_byteslice_dfs_residual.hpp, `MS` = rebuild/cpu_byteslice_mergesplit.hpp,
`MSS` = rebuild/cpu_byteslice_mergesplit_stash.hpp, `DN` = rebuild/cpu_byteslice_dedup_network.hpp.

**How this was checked.** The fixture dumper `oracle/fixtures-d2/fd2.cpp` drives the engine's job
with extra input knobs (A records per bucket, lists of per-home forced keys for A and B, B-tier keys
drawn from A's tier, forced B-tier keys, tombstones). This document was transcribed into a Python
model (`oracle/fixtures-d2/model.py`, about 200 lines) and compared with the engine on **1964
fixtures**. It matched on every output main and tier record's **(bucket, lane, key, value,
tombstone)**. It also named the same failing stage on all 809 failures: 336 `butterfly`, 36
`fixed-merge-offers`, 140 `residual-dfs-partition` and 297 `residual-drain`. The fixtures cover every
path below: sheds at stage bits 0, 1 and 2; insertion sheds; A-leaf drops; B-tier clears; A and B
leftovers; leftover dedup; and pool dedup. The model compares lanes on the input lanes given in the
fixture.

---------------------------------------------------------------------------------------------------
## 0. Notation and fixture geometry

* `C = 64` = `kBucketCapacity`. A bucket is a partial map lane(0..63) -> record. "Lane order" means
  ascending lane. `LowestFree(X, n)` means the n smallest lanes not occupied in X.
* The fixture gives: `U = 8`, `K = 3`, digit `d = 2`, so `r = 1, e = 1`. `block_bits b = K+e = 4` and
  `out_buckets N = 16`. There is no radix pass (M:118-140 `MakeMergeShape`).
* Capacities and their planners:

| quantity | value | where computed |
|---|---|---|
| stage stash depth `S_A` (bucket depth of every `older_sheds_` slot, including the insertion stash) | 1 bucket = 64 recs | `LevelArenaStashSizing::Buckets(2)` (levelarena/…_stash.hpp:214). It is `LevelStashSlots(route_buckets = MaxOutputBuckets(2) = 16, target = -(66 + ceil log2((L+1)·executions·stages)))/64` (stash.hpp:151-180). `MakeStashes` (J:1904) gives every slot this depth |
| number of stash slots | 7 = `LevelMergeStashSlots(4,false)` = 4+1+2 | stash.hpp:324. `max_block_bits_ = sizing.At(2).block_bits = 4` (J:1261). Slots [0,5) are route bits (slot 4 is unused at d=2), slot 5 is the radix stash (unused), slot 6 is the insertion ("merge") stash = `older_sheds_[b+2]` (J:2171) |
| A tier width | 1 bucket | `OlderTierBuckets(2,2)` = `TierBucketsOf(2)` (geometry.hpp:602, 579) |
| B tier width | 1 bucket | `CarryTierBuckets(2)` = `TierBucketsOf(1)` (geometry.hpp:594) |
| output tier width | 1 bucket = 64 recs | `TierBucketsOf(2)`. This is `binding.out_tier`, reset at Begin (J:1957) |
| DFS pages | **1** | `FinishDfsPages` (J:536-540) returns 1 whenever `pool.direct_buckets != 0`, which is always true when separated. **The fixture's `dfs_pages: 2` is `routing.dfs_pages`, which this job does not use** (see LevelResidualRouting comment, J:462-463) |
| pool shape | swept 6, direct 1, main_levels 4, fused | `LevelMergePoolShapeOf` (J:394-408) |
| range plan | `range_bits = 4`, `index_bits = 0`, `groups = 1`, `range_buckets = 16`, `scatter_per_bucket = 64` | `LevelFinishRangePlan` (J:542) calls `ResidualRangePlanFor(kDfs, 6-1 = 5, 4, 1, -1)` (RP:57), then `DfsResidualRangePlan` (DFS:93). That uses `PlanResidualRange(5,4)` (RR:196): bits = 6 (2^6 >= 40), capped at main_levels 4. Its result is overwritten with groups = pages = 1 |
| range table | 17 buckets = 16 A leaves + 1 direct B-tier copy | `BuildResidualPassFields` returns `range_buckets + direct_buckets` (RP:404-406) |
| DFS shape | pool P = 5 buckets = 320 slots, coarse_bits D_c = 4, index_bits 0, main 16 | `AttachResidualDfs` (RP:446-472), `MaxLevelDfsAllocation` (J:593) |

* **`range_bits`** is `D_c` = log2 of the number of coarse ranges (leaves). **`range_index_bits`**
  is `I` = log2 of the homes per range. Here there are 16 ranges of exactly one home each, and range
  v is home v.

---------------------------------------------------------------------------------------------------
## 1. Records, sources, words

* **Record** = (key: `key_bytes` = 8 bytes, value: `value_bytes` = 8 bytes). The last value byte is
  the **meta byte** (`Layout::MetaLine`, table/cpu_byteslice_layout.hpp:191). Meta bits:
  * 0x80 `kMetaErased` is the tombstone;
  * 0x20 `kMetaUnshadowed` is used only at the top and is never read here;
  * 0x40 `kMetaResidualClass` is engine scratch (meta.hpp:64/93/125).

  The stored **tag** (4 bytes) is the low 32 bits of the word, rewritten by retags and not part of
  the record's identity.
* The engine never reads a stored "source" byte. The fixture's value byte 0 (1 = A, 2 = B) is plain
  payload. Freshness is structural: A (the older partial) is older and B (the carry) is fresher.
  Inside the residual pass, freshness is a **public rank per pool slot**:
  * `kLevelMergeFresherRank = 0` for the B-insertion stash and B's tier;
  * `kLevelMergeOlderRank = 2` for A's stage stashes and A's tier (J:136-138, 250-265).

  Stash and tier carry no separate rank. Equal ranks are never compared with each other.
* **Word** `w(k)` is the low 64 bits of AES(key ‖ merge-family nonce), `kRaw` map (map_ is kRaw
  because r = 1, J:2133-2140). Tag bit j is bit j of w (tag byte j/8 is stored reversed,
  layout.hpp:161). **Home** `h(k) = w & 15`. The index map is the identity; no radix digit is used.
* Which bits are read where:
  * A route stage j reads bit j (j = 0, 1, 2), and the continuation reads bit 3.
  * B's placement in its input bucket is `w & 7`. That is an input contract, not checked.
  * B's way is **recomputed from the key** as `(w >> 3) & 1` (`ComputeBucketWayLine`,
    table/…routing_map.hpp:813, `PlanBucketWay` 793, way_bits 1; `FixedMergeRetagOf` R:350).
  * The DFS reads bits 2..3, then bit 1, then bit 0.
  * The A-leaf offer tests no bits, because index_bits = 0.
  * The B-tier offer compares the **full 4-bit home** (`ResidualOfferCandidates` SC:180 with
    `index_bits = 4`).
* Key equality is exact for 8-byte keys (`CrossBucketDuplicateMask`, dedup_masks.hpp:323-360).
  `CrossBucketDuplicateMask(F, Fm, S, Sm)` returns **S's** lanes whose key occurs in F.

---------------------------------------------------------------------------------------------------
## 2. The MergeSplit and stash primitives (used by the A route)

`MergeSplit(F = first, S = second, bit j, stash)`: this is `PlanMergePair` (MS:118-138),
`MergeSplitPairStash` (MSS:175-215), and the quad (MSS:336-470), which gives the same result as two
pair levels.
```
F0 = {(l,r) in F : bit_j(r)=0}   F1 = F \ F0          -- F's records keep their lane NUMBER
S0 = [r in S, lane order : bit_j(r)=0]   S1 = [... bit_j(r)=1]
a0 = min(|S0|, 64-|F0|)          a1 = min(|S1|, 64-|F1|)
out_first  = F0 ∪ zip(LowestFree(F0, a0), S0[0:a0])  -- "free" = lanes not held by F0 (F1's old lanes are free)
out_second = F1 ∪ zip(LowestFree(F1, a1), S1[0:a1])  -- F1 moves to the second bucket at the same lane numbers
shed = S0[a0:] ∪ S1[a1:], in S-lane order            -- only the SECOND bucket's surplus is shed
```
The quoted rule ("first keeps lanes; second fills lowest free lanes in lane order; only second's
surplus shed") is **confirmed**. The first bucket can never shed.

`Append(stash, list)`: this is `PlanStashMergePermute` (residual_stash.hpp:148). It is preceded by
the **capacity test** `stash.Count() + |list| > 64·S_A` → fail (MSS:188; the quad tests both levels
before writing anything, MSS:420). If the test passes, the list's records go in list order into the
lowest free lanes of stash bucket 0, then bucket 1, and so on. Nothing is removed from a stage stash
during preparation, so **stash lane order = append order**.

---------------------------------------------------------------------------------------------------
## 3. Begin / PrepareOlder

**B0 (Begin, J:1511-1561).** This step derives digit 2, the family and the nonce, and runs
`Validate` (checks extents and layouts only). It then resets every stash slot and the output tier
(J:1926-1962, `ResetStorage`), and builds the contexts (J:2133-2208). `drop_unshadowed = false`
(J:2176). `retag_fresher_digits = true`, because separated sources and d > 1 (J:2186). It copies A's
tier occupancy into a private view: `BorrowTier(older_tier)` (J:2230-2245). The job's pool dedup
later clears lanes of this private copy, never of the published tier. The output main is not cleared,
and its stale contents are never read (see P2).

The PrepareOlder plan is `PlanLevelMergePhase`'s separated branch (M:861-891):
`PlanPrepareOlderSources`, then one `kRouteLevelRange` per bit in `[K, b) = {3}`, then no radix
pass.

**P1 (copy + retag).** `PlanMergeOlderBlocks(3, 1, 1)` (P:1000-1015) has no pure blocks because
r = 1, and one span for u = 0 with offset 8, 8 buckets and route depth 3. It uses the untiled arrival
because 3 ≤ `kButterflyLeafLevels` (P:267). `kCopyAndRetagRange` over [8,16) (R:522-533,
`CopyAndRetagRange` routing_map.hpp:903) sets **out[8+j] := A_main[j] with the same lanes and
masks**. Tags are recomputed and records are unchanged. out[0,8) is left unwritten; it is the
publicly blank B region.

**P2 (A's own butterfly, bits 0,1,2 inside [8,16)).** This is one `kButterflySubnetwork` leaf
(base 8, stride 0, 3 levels) running `RouteSubnetworkRecursive` (butterfly_stash.hpp:199-236). It
does a quad on bits 0,1 over {8..11} and then over {12..15}, then pair passes on bit 2. The
equivalent sequential order is:
```
for j in 0,1,2:
  for i in 8..15 ascending with ((i-8) >> j) & 1 == 0:        -- pairs (i, i+2^j)
     (out[i], out[i+2^j]) := MergeSplit(out[i], out[i+2^j], j, stash[j])   -- stash[j] = older_sheds_[j]
```
so bit 0 runs pairs (8,9),(10,11),(12,13),(14,15); bit 1 runs (8,10),(9,11),(12,14),(13,15); and
bit 2 runs (8,12),(9,13),(10,14),(11,15). The quad's append order into each level's own stash equals
this order (`PlanStashMergePermute2` MSS:277: pair (0,1) before (2,3); (0,2) before (1,3)).

* **One shared stash per bit j** (`stash[j]`, capacity 64 records). **Fail test:**
  `|stash[j]| + |shed| > 64` raises `"level arena: the prepare-older phase ran out of room at
  butterfly; the certified depth did not hold"` (R:534-543, J:2656-2662).
* **No dedup of any kind** happens in A's route. A holds each key at most once.
* Afterwards a surviving record r sits in out[8 + (w & 7)].

**P3 (first continuation, bit K = 3, blank first).** `kRouteLevelRange` with `blank_first` over
i in [0,8) (M:878-890, R:422-445) calls `MergeSplitPair<Check=true, BlankFirst=true>` (MS:189-236).
The first bucket out[i] is taken as empty; its mask and bytes are never read.
```
for i in 0..7:
  L = records of out[i+8] in lane order
  out[i]   := L filtered bit_3 = 0, compacted into lanes 0,1,2,...   (lane order preserved)
  out[i+8] := L filtered bit_3 = 1, compacted into lanes 0,1,2,...
```
This step uses no stash, so `stash[3]` stays empty at d = 2. **It cannot fail**, because each side
holds at most 64 records and the checked residual is always 0. Now every surviving A-main record sits
at `out[h(k)]`, compacted into low lanes.

**Install (I1).** The plan is empty (`ExpectFixedCarry` only, M:904-906). `BindCarry` (J:2210-2228)
binds B main as `finish_.fresher`, **without copying**, and copies B's tier occupancy into a private
view (`BorrowTier(carry.tier)`). This phase cannot fail.

---------------------------------------------------------------------------------------------------
## 4. FinishMerge: the one residual pass riding the fixed insertion

The pass is built by `BuildFinishPass` (J:2345-2383) from `SeparatedFinishPoolSlots` (J:250-265).
Pool slots, in order:

| slot | storage | rank | role |
|---|---|---|---|
| 0 | insertion stash `older_sheds_[6]` | 0 | **drain-only** (starts empty) |
| 1..4 | A stage stashes `stash[0..3]` (`stash[3]` is always empty here) | 2 | swept, distributed |
| 5 | A tier (private view) | 2 | swept, distributed |
| 6 | B tier (private view), `tier_class` | 0 | swept, **direct** (`separate_direct_tier`, RP:354-366) |

rule = `kClassMark`, fuse = `kFixedMerge`, `reset_slots` = 7 (all owned), `tier_class_from = 5`
(RP:383-390). The finish plan is `PlanFixedCarryInsertion` (M:603-626) calling `PlanFixedMerge`
(P:895-944): prologue, `kFixedMergeOffers`, epilogue. It plans no standalone passes (the other
residual passes are inactive) and **no tombstone drop**, because `drop_unshadowed` is false
(P:943).

**F1 (pool dedup, window kSweptOnly, P:629; RR:669-700).** The pairs are (fresher slot f, staler
slot s) with f, s ∈ [1,7) and rank[f] < rank[s], which means only f = 6 (B tier) against s = 1..5:
```
for s in 1..5: slot_s := slot_s minus { r : key(r) ∈ keys(B tier) }      -- mask clear, A copy removed
```
This dedup does **not** compare against A main, B main or the insertion stash. The B tier itself is
never cleared.

**F2 (direct B-tier copy, `kResidualScatterRetag` levels = 1; P:418-422, R:681-688).** Range bucket
16 := B tier, **same lanes**, tag := w, meta class bit 0x40 **set** (`ScatterAndRetagResidualPoolRange`
with `tier_from_group = 0`, RR:459-503; per = 64 means a lane-preserving copy, meta.hpp:367-381).

**F3 (DFS gather, R:724-745).** Gather buckets 0..4 := slots 1..5 (stash[0], stash[1], stash[2],
stash[3], A tier). Each is copied lane-for-lane, retagged with w, and gets class bit 0x40 **cleared**
(boundary 5, RR:433-455). The distributed population is **A only**: all A routing losses plus A's
tier, minus F1's removals.

**F4 (DFS partition, `kResidualDfsPartition`, R:746-752; DFS:573-936).**
* S = 64·pages = 64. P = 5·64 = 320 slots.
* Node capacity at height h (a node covers 2^h leaves) is `C(h) = min(P, S·2^h)` (DFS:692-698):
  C(0) = 64, C(1) = 128, C(2) = 256, C(3) = C(4) = 320.
* The direct height `hd` = 2 (DFS:702-710). This is the first height with C(h) < P. Heights 3 and 4
  are never materialised.

The unit list (DFS:784-818), run in order, is:
```
for c in 0..3:                                        -- height-2 node c = homes 4c..4c+3 (bits 2..3 == c)
  Direct(h=2,c): gather -> node c, test count <= 256
  Pair(h=1, nodes 2c | 2c+1)   (bit 1 = 0 | 1):  each child count <= 128
  Pair(h=0, leaves 4c | 4c+1)  (bit 0):          each leaf  count <= 64
  Pair(h=0, leaves 4c+2 | 4c+3):                 each leaf  count <= 64
```
* Each compaction is a stable (order-preserving) ORCompact. So **leaf v, page 0 = [A-pool records
  with h = v, in gather order (gather bucket 0..4, then lane)], in lanes 0..n_v-1**. Range bucket v
  is leaf v.
* Nothing is shed: the step is either lossless or it fails.
* **Fail test:** any unit whose child count exceeds its capacity raises `"level arena: the finish
  phase ran out of room at residual-dfs-partition; the certified depth did not hold"`
  (DFS:936, R:746-752).
* Since P = 320 ≥ every count, this fails **iff max_v n_v > 64**, where n_v counts post-F1 A-pool
  records with home v. The unit that trips first only changes which unit reports it.
* Compared with REPORT eq. (dfs-capacity): `C_j = min(P_pool, S·2^{max(D_c-j,0)})` with depth
  j = D_c - h is the same function. Differences:
  * R_f = 0: there are no refinement levels, because I = 0.
  * P_pool is the pool's slot capacity (320), not a record count.
  * Depths j < D_c - hd (where C = P) are skipped by compacting the gathered pool straight into each
    height-2 node (DFS:24-29). That is the REPORT's "gathering the root" containment.

**F5 (fixed carry insertion with fused offers, `kFixedMergeOffers` over B buckets 0..7).** This is
R:568-582 calling `MergeFixedLevelSourcesOffersRange` (SC:1012-1080) with `MergeRadixSourceBucket`
(DN:523-565) and `MergeBucketWithResidualOffers` (SC:923-996). The offer sets come from
`GatherFusedOffers` (R:316-345): set 0 is the 16 A leaves under **kTableWins** (the direct slot
forces that rule, R:327), and set 1 is the direct B-tier copy under **kResidualWins**. Tombstone
policy is kMerge (R:259-274), so no B record is skipped.
```
ins := insertion stash (empty)
for i in 0..7:                                            -- B bucket i (its records have w&7 = i)
  -- (a) dedup, before any capacity decision (DedupBucketDestinations, DN:539):
  for q in 0,1:  out[i+8q] := out[i+8q] minus { r : key(r) ∈ keys(B_main[i]) }   -- A copy removed, B wins
  shed := []
  for q in 0,1:
    ci  := i + 8q
    src := [r in B_main[i], lane order : (w(r)>>3)&1 == q]
    -- (b) insertion (SC:931-938):
    alloc := min(|src|, 64 - |out[ci]|)
    place src[0:alloc] into LowestFree(out[ci], alloc), in order
    shed_q := src[alloc:]                                 -- higher B lanes are shed
    if q == 1:                                            -- (c) test + append at the LAST direction (SC:939-949)
      if |ins| + |shed_0| + |shed_1| > 64: FAIL "finish ... fixed-merge-offers"
      Append(ins, shed_0 ++ shed_1)                       -- direction 0's sheds first, then direction 1's, each in B-lane order
    -- (d) A-leaf offer to ci, kTableWins (SC:281-345, round 1 only):
    m    := |out[ci]|
    cand := leaf[ci] records in leaf-lane order
    drop := { c ∈ cand : key(c) ∈ keys(out[ci]) }         -- A candidate whose B copy is in main: consumed
    stale:= cand \ drop                                   -- s = |stale|
    u    := min(s, 64 - m)
    place stale[0:u] into LowestFree(out[ci], u), in order
    leaf[ci] := leaf[ci] minus (drop ∪ stale[0:u])        -- consumption mask; survivors keep their leaf lanes
    -- (e) B-tier offer to ci, kResidualWins (round 2 only):
    fcand:= [c in B-tier copy, lane order : h(c) == ci]   -- f = |fcand|, full-home match
    clear:= { l : key(out[ci][l]) ∈ keys(fcand) }         -- q = |clear|; stale main copies (only A-main survivors can match)
    out[ci] := out[ci] minus clear
    v    := min(f, 64 - |out[ci]|)                        -- = min(f, 64 - m + q - u)
    place fcand[0:v] into LowestFree(out[ci], v), in order   -- freed lanes are reused if they are lowest
    Bcopy := Bcopy minus fcand[0:v]
```
* **Who wins.**
  * B main beats A main: rule (a) removes A's copy.
  * B main in main beats an A-pool copy: rule (d), drop.
  * B tier beats A main: rule (e), clear. The clear applies even if the B-tier record is not absorbed.
  * B tier beats the A pool: F1.
  * B main that was shed beats an A-pool copy: F7.
* A candidates can never meet B-tier keys (F1). The two B sources are assumed disjoint (contract,
  not checked).
* The REPORT's two-round formula `u = min(s, C-m)`, `v = min(f, C-m+q-u)` ("Completed non-top
  tables") is implemented exactly, but as **two chained offer sets** (kTableWins, then
  kResidualWins; `ChainedResidualOffer` SC:548-575), not as one kClassMark offer. q is computed
  after round 1; this equals the formula because F1 guarantees no absorbed A candidate matches a
  B-tier key.
* A home that was full when B shed into it (m = 64) absorbs no A candidate: round 1 sees 0 free
  lanes.
* Destination order: C[i], then C[i+8], for i ascending. Each candidate is offered only to its own
  home, so this order cannot change which records are absorbed.
* Lane order is fixed by the steps above.

**F6 (epilogue, first drain; P:636-647, P:517-543, R:782-806, SC:1198-1223).** The kDrainOnly
pool-dedup emission is **not planned**: no slot has rank < 0, the rank of the drain-only slot
(`ResidualPoolDedupNeeded`, RR:779-800). Since `ResidualLeftoverDedupNeeded` holds (slot 0 rank 0 <
rank 2, RR:807-817), the drain is split around the leftover dedup:
```
tier := output tier (empty)
for rb in 0..16:            -- leaves 0..15 (A leftovers), then bucket 16 (B-tier leftovers)
  L := remaining records of range bucket rb, lane order
  if |tier| + |L| > 64: FAIL "finish ... residual-drain"
  Append(tier, L)
```
**F7 (leftover dedup, `kResidualLeftoverDedup`, 1 unit; SC:1135-1188, R:605-613).** The class of
each drained lane is read from its meta 0x40 bit.
```
tier := tier minus { A-class lanes (0x40 clear) whose key ∈ keys(ins) }   -- B shed beats A leftover
ins  := ins  minus { lanes whose key ∈ keys(B-class tier lanes) }         -- empty by B main/tier disjointness
```
**F8 (second drain).** `if |tier| + |ins| > 64: FAIL "finish ... residual-drain"`. Otherwise
`Append(tier, ins in lane order)`. That order is the append order of F5c, and it fills the lowest free
lanes, including the holes F7 left.

**F9 (reset, R:808-811).** This clears the masks of all 7 pool slots. It has no effect on the
output.

Output = main out[0..15] plus the output tier (one bucket).

---------------------------------------------------------------------------------------------------
## 5. Failure verdicts

Every capacity failure is a `std::runtime_error` with the text `"level arena: the <phase> phase ran
out of room at <kind>; the certified depth did not hold"` (J:2656-2662). The phase is aborted
(`RunWhole`) and nothing is published. In execution order:

| step | phase / kind | tested quantity > threshold |
|---|---|---|
| P2 | `prepare-older` / `butterfly` | `|stash[j]| + |shed of this MergeSplit|` > 64, for j = 0,1,2 |
| P3 | `route-level` | checked, but provably never fails |
| F4 | `finish` / `residual-dfs-partition` | some node's selected count > C(h); equivalent to some home having > 64 post-F1 A-pool records |
| F5 | `finish` / `fixed-merge-offers` | after B bucket i, `|ins| + sheds(i,0) + sheds(i,1)` > 64 (running total of insertion sheds) |
| F6 | `finish` / `residual-drain` | running total of drained A and B-tier leftovers > 64. This can fire before F7 would have removed A duplicates |
| F8 | `finish` / `residual-drain` | `|tier after F7| + |ins|` > 64 |

Steps F1-F3, F7 and F9 always succeed. With lanes > 1 there would also be a fold check (J:2800-2833),
but it cannot occur with lanes = 1 (subtask_cursor.hpp:309-313). Anything else (`logic_error` or
`invalid_argument`) is a misconfiguration, not a capacity verdict. The fixture with
`--forced-older 128` fails at F4, as the README says.

---------------------------------------------------------------------------------------------------
## 6. Tombstones

Tombstones are **never dropped**, and they compete exactly like live records:
* `drop_unshadowed = false` (J:2176);
* the kMerge policy skips no B record (DN:330-350);
* the scatter and gather are called with `drop_unshadowed = false`;
* no `kDropErased` or `kDropErasedTier` step is planned (P:943).

For example, a B tombstone removes A's value in F5a or F5d. This was checked with `--tombs`
fixtures (A main, A tier and B main tombstones).

---------------------------------------------------------------------------------------------------
## 7. Where the prose and the code differ, or need care

1. **DFS pages.** The prose says "one-page A leaves" and the code agrees (1 page). The fixture's
   `dfs_pages: 2` field is the routing knob, and this job ignores it (J:536-540).
2. **Drain-only dedup against original sources.** REPORT's separated-job argument
   (sec:separated-residuals) runs a drain-only dedup against the original fresh sources, including
   consumed records. **In this job that emission never runs.** The drain-only insertion stash has rank 0, equal to the B tier, so no pair is
   eligible (RR:779-800). The only resolution against the shed is F7, against the drained leftovers.
   It is correct only because (i) B main and B tier are disjoint, which is an unchecked input
   contract, and (ii) a home that received a shed was full, so round 1 absorbs nothing there.
3. **The two-round allocation** is two separate rule sets (kTableWins, then kResidualWins), not the
   kClassMark class split the REPORT describes. The arithmetic is identical. The pass's own
   `rule = kClassMark` is used only by F3's class stamping and F7.
4. **Stage-stash sharing.** REPORT says `S_j` bounds the stash across its "preparation and
   continuation writers". At d = 2 only preparation writes stash[0..2]. stash[3], the continuation
   bit, is in the pool but always empty.
5. **"range_index_bits".** The production plan gives I = 0 (one home per range), which satisfies
   the REPORT's 0 ≤ I < k.
6. The REPORT's formulas (CA, E and so on) are probability bounds. The code tests only the
   capacities in §5.

---------------------------------------------------------------------------------------------------
## 8. Other details that affect placement or the verdict

* **Input contracts the code relies on but does not check at run time:**
  * B main bucket i holds exactly the B records with `w & 7 = i`. The dumper checks this.
  * B main and B tier are key-disjoint.
  * A main ∪ A tier is key-distinct, and so is B main ∪ B tier.
  * Every bucket holds at most 64 records.
* **Class-bit scratch in the output.** Records that came from B's tier, whether absorbed into main
  or drained into the tier, carry meta 0x40 **set** in the output bytes. Records that came from the A
  pool carry it **cleared**. A-main and B-main records keep their input meta. The dumper masks 0x40
  out (fixture_dump.cpp:126-130), so a Lean model should treat bit 0x40 as don't-care.
* **Inputs are never written.** B main's masks are copied per direction (DN:545-560), and both tiers
  go through private mask copies.
* The **order-dependent choices** in this job are all listed above:
  * which B records are shed: the highest B lanes of the direction;
  * which A candidates are absorbed: the first ones in leaf (gather) order;
  * which B-tier records are absorbed: the first ones in B-tier lane order;
  * which A records are shed in the route: the second bucket's highest-lane surplus.

  All of them depend on lanes. The resulting per-home counts do not.
* **Budget and resumability.** The plan is fixed at the whole budget and run in order. Slicing or
  resuming is claimed to be byte-identical (J:1580-1586). This is not verified here; the
  fixture uses the whole budget.
