# Record-level semantics of the top finish (the top merge's FinishMerge phase)

Extracted from the engine by reading its code and checked against it: `model_top.py`, written from this text, matched the engine
**lane-exactly on 772 successful runs and on verdict plus failing kind on 228
failures, 1000 of 1000 fixtures**, with the engine built with `-DNDEBUG` and
again with engine asserts on (`-UNDEBUG`, byte-identical output, no assert
fired). The Lean model `Top.lean` follows it and agrees on every fixture. The
tools are in `oracle/fixtures-top/` (see its README): `fdtop.cpp` (dumper), `build_fdtop.sh`, `model_top.py`, `gen_top.py`
(generator, deterministic), `run_top.py` (driver and coverage), `report_check.py`
(REPORT cross-check); the generated fixtures (`fx/`) and the driver's output
(`RESULTS.txt`) go under `.lake/oracle/fixtures-top/`. File:line anchors refer to the engine revision the extraction was read from and
may have shifted; the function names identify the code.

Job: `LevelMergeJob` at the top level (`level == geometry.Levels()`), ordinal 3,
digit `D` = the geometry's top digit, whole budget, `lanes = 1`. Call sequence
`Begin; PrepareOlder(budget, &scratch); InstallCarry; FinishMerge(&scratch, budget)`
(the order of `cpu_byteslice_level_arena_top_test.cpp:693-784`). **This document
covers `FinishMerge`**; the preparation is described only through what it leaves
behind (C and R, section 2).

Paths are relative to `src/oram/`. `J` = levelarena/cpu_byteslice_level_arena_job.hpp,
`M` = levelarena/cpu_byteslice_level_arena_merge.hpp, `ST` = levelarena/cpu_byteslice_level_arena_stash.hpp,
`G` = levelarena/cpu_byteslice_level_arena_geometry.hpp,
`P` = scheduler/cpu_byteslice_subtask_plan.hpp, `R` = scheduler/cpu_byteslice_subtask_run.hpp,
`RP` = scheduler/cpu_byteslice_residual_pass.hpp, `SC` = rebuild/cpu_byteslice_second_chance.hpp,
`RR` = rebuild/cpu_byteslice_residual_range.hpp, `DFS` = rebuild/cpu_byteslice_dfs_residual.hpp,
`DN` = rebuild/cpu_byteslice_dedup_network.hpp, `DM` = rebuild/cpu_byteslice_dedup_masks.hpp,
`MSS` = rebuild/cpu_byteslice_mergesplit_stash.hpp, `RS` = rebuild/cpu_byteslice_residual_stash.hpp,
`MT` = table/cpu_byteslice_meta.hpp, `RM` = table/cpu_byteslice_routing_map.hpp,
`SK` = scheduler/cpu_byteslice_subtask.hpp. `REPORT` = analysis/bound_certification/REPORT.tex.
Where the d = 2 ordinary merge (`ENGINE_D2.md`, `Job.lean`) and the top agree, the
text says so; section 9 lists the differences in one place.

---------------------------------------------------------------------------------------------------
## 0. Notation and geometry

* `C = 64` = `kBucketCapacity`. A bucket is a partial map lane (0..63) -> record.
  "Lane order" is ascending lane. `LowestFree(X, n)` is the n smallest lanes not
  occupied in X. These two words are used exactly as in `ENGINE_D2.md`.
* `T` = number of homes = number of buckets of C = `D * U` (a power of two).
  `U` = `CarryBuckets(top)` = `Z * B^(L-1)` with `Z = 2 * r0 * s` (G:525-528; `r0` flushes, `s`
  online stash buckets, `B` fanout, `L` levels), so `U >= 8` and `T >= 8`.
  `D` in {1, 2, 4, 8}, `D <= B`. `K = log2 U`, `e = log2 D`, `block_bits = K + e = log2 T`
  (`MakeTopMergeShape`, M:202-209; the top has no radix pass, `r = 1`).
* `S_R` = number of pages (64-lane buckets) of the retained-carry stash R. It is
  `LevelArenaStashSizing::Buckets(top)` (ST:79-180; the slot count of the Chernoff table, `slots / 64`) and is the depth of **every**
  `older_sheds_` slot of the job, so **the merge stash has the same number of pages
  `S_A = S_R`**. It depends on `T`, `L` and the request horizon, not on the tier
  width: the fixtures get `S_R = 1` at horizon 2^32 and `S_R = 2` at horizon 2^56 (`--acc 32` / `--acc 56`, the
  dumper's log2 horizon). `kMaxResidualStashBuckets = 8` (RS:80) bounds `S_R`, the tier widths and the
  output tier at 8 pages.
* `tb` = pages of B's tier = pages of the output tier = `TierBucketsOf(top-1)` =
  `TierBucketsOf(top)` (G:577-598; one shared width in this setup). A's tier is the same
  width.
* The finish's pool (J:320-333, 425-434, `TopMergePoolShapeOf`): swept buckets
  `S_R + tb`, of which the last `tb` are the direct B tier; distributed pool =
  `S_R` buckets = `S_R * 64` slots (`dfs_pool_slots` in the fixtures);
  `main_levels = log2 T`.
* **Finish range plan** (`LevelFinishRangePlan`, J:488-491, `FinishDfsPages` = 1 pages
  per leaf because a direct B tier exists, J:482-484):
  ```
  ml  = log2 T
  if ml <= 3:   DIRECT plan (kResidualDirectMaxLevels = 3, RR:87):  no DFS
                range_bits rho = 0, index_bits I = ml, groups = S_R, range_buckets = S_R
                (the range table IS R, one range bucket per R page)
  else:         DFS plan (RR:174-195, DFS:112-125):
                bits = smallest b with 2^b >= 8*S_R      (3 for S_R = 1, 4 for S_R = 2)
                rho  = min(bits, ml);  I = ml - rho      (and I <= 18: kDfsMaxRangeIndexBits, DFS:85-111)
                groups = pages per leaf = 1;  range_buckets = 2^rho
  ```
  A **range** is the set of homes `{v : v >> I == r}`; `rho` = `range_bits` = log2 of
  the number of ranges (leaves), `I` = `range_index_bits` = log2 of the homes per range.
  `DIRECT` happens only at `T = 8` (`D = 1`, `U = 8`), because `U >= 8`.
* Fixture fields: `geometry.{T, D, U, K, e, block_bits, stage_stash_buckets (=S_R=S_A),
  r_pages, r_slots, b_tier_pages, a_tier_pages, merge_stash_pages, merge_stash_capacity,
  out_tier_pages, out_tier_capacity, main_levels, pool_swept_buckets, pool_direct_buckets,
  dfs (1 = DFS plan, 0 = direct), range_bits, range_index_bits, range_groups,
  range_buckets, range_scatter_per_bucket, dfs_pool_slots, dfs_leaf_slots (=64*groups
  for DFS, 0 for direct)}`.
* Geometries covered (T, D, U, rho, I, S_R; `tb` in {1, 2, 4, 8} for each):
  (8,1,8,0,3,1) (8,1,8,0,3,2) (16,1,16,3,1,1) (16,1,16,4,0,2) (16,2,8,3,1,1)
  (16,2,8,4,0,2) (32,1,32,3,2,1) (32,1,32,4,1,2) (32,2,16,3,2,1) (32,2,16,4,1,2)
  (64,4,16,3,3,1) (64,4,16,4,2,2) (128,4,32,3,4,1) (128,4,32,4,3,2) (256,8,32,3,5,1)
  (256,8,32,4,4,2). Not covered: `S_R >= 3` (in the sizing probes, T up to 2^16 at B = 2 and T = 2^24 at B = 8, three pages
  appear only at `T = 2^24`, a 25 GB bank per table; above 2^25 homes a floor gives 4 or more), `I > 18` (the 2^18 width cap needs `T > 2^21`), and
  `T < 8` (`U >= 8`).

---------------------------------------------------------------------------------------------------
## 1. Records, classes, meta bits, words

* **Record** = (key, value). Key 8 bytes (the layout of the fixtures), value 8 bytes; the
  last value byte is the **meta byte** (`Layout::MetaLine`). Meta bits (MT:64, 93, 125):
  * `0x80` `kMetaErased` = tombstone;
  * `0x20` `kMetaUnshadowed` = "this tombstone has no older live copy anywhere"
    (meaningful only together with `0x80`; `UnshadowedSlotMask` tests both bits, MT:198-204);
  * `0x40` `kMetaResidualClass` = engine scratch (the class of a range-table lane).
  **In the fixtures** `0x40` is masked out of the value bytes (it is don't-care in every
  input: the pass re-stamps it, section 4.2, and output records may carry it), and `0x20`
  **stays in the value bytes** and is also exposed as the record's `unshadowed` field
  (`unshadowed = tombstone && bit 0x20`). The value hex is compared with the model.
  Output live records are copies of input records: the engine never rewrites a payload.
* The stored **tag** (4 bytes) is scratch: the finish recomputes it from the key wherever it
  reads one (`FixedMergeSourceDigits`, the retag of the range table). The tests poison it.
* **Classes and freshness.** A = C and R (the previous top, compacted by the preparation).
  B = B main and B tier (the inbox carry, published by level L-1). B is fresher than A. Inside
  the pass freshness is the **public rank of a pool slot** (J:136-141, 320-333): merge stash
  rank 0 (drain-only), R rank 2 (`kLevelMergeOlderRank`), B tier rank 0 and `tier_class`. Records
  carry no source byte; the fixtures put 1 = A, 2 = B main, 3 = B tier in value byte 0 as payload.
* **Word** `w(k)` = low 64 bits of `AesCtrTagU128WordsHost(nonce_lo, nonce_hi, key.w0, key.w1,
  round_keys)` under the merge family's nonce; `map_` is `kRaw` (no radix, J:2043-2050). The
  fixtures list `w` for every key (`words`). Tag bit j is bit j of `w`.
  * **home** `h(k) = w & (T-1)`. This **confirms** the report's `h(t) = t mod T` for D in
    {1, 2, 4, 8}: the merge map is `kRaw` and `T` is a power of two.
  * **carry bucket** of B's key `i(k) = w & (U-1)` (B was published under a `kRaw` map over `K`
    bits; it is an input contract that B main bucket `i` holds exactly the keys with this `i`).
  * **way** of B's key `q(k) = (w >> K) & (D-1)`, **recomputed from the key** per source bucket
    (`FixedMergeRetagOf`, R:349-362, `PlanBucketWay` RM:793-811, `ComputeBucketWayLine`
    RM:813-846; `retag_fresher_digits` is true at the top when `D > 1`, J:2096-2098). At
    `D = 1` there is one way and nothing is recomputed. Then `h(k) = i(k) + q(k) * U`.
  * A range candidate is matched by the **low `I` bits of the stored tag** inside its leaf
    (`ResidualOfferCandidates`, SC:179-207), a B-tier candidate by the **full `ml = log2 T`
    bits** (`DirectResidualPlan`, R:223-226). Both equal `h(k) == ci`.
* Key equality is exact for 8-byte keys. `CrossBucketDuplicateMask(F, Fm, S, Sm)` returns
  **S's** lanes whose key occurs among F's real lanes (DM:345-380). All-zero keys are
  handled by a repair path (`RepairZeroKeyMatches`); the fixtures never use key 0.
  Dummy lanes (unoccupied) carry arbitrary key bytes in the fixtures (some equal to real
  keys); they never matter, only the occupancy masks do.

---------------------------------------------------------------------------------------------------
## 2. The finish's inputs (what the dumper reads and the model takes)

The model is a function of: the geometry, `words`, and these four record lists.

| input | what it is | where the dumper reads it |
|---|---|---|
| `C_main` | A's main after the preparation: `T` buckets, bucket `h` holds records of home `h` (at most 64), lanes arbitrary (holes possible). Tombstones present only if A had plain tombstones. | `binding.out` after `PrepareOlder`, before `InstallCarry` (read-only) |
| `R` | the preparation's **retained carry**: A's records that the preparation's offer could not place. `r_pages = S_R` pages. Appended by a drain into an empty stash, so in a real run its lanes are `0..n-1` of page 0, then page 1, ... (no holes; the model does not need that). | `job.older_sheds()[block_bits + kLevelMergePrepCarryStashOffset]` (J:2390-2393, ST:336) |
| `B_main` | the inbox carry's main: `U` buckets, bucket `i` holds the B keys with `w & (U-1) == i`, at most 64, lanes arbitrary | published `LevelCarry.main` |
| `B_tier` | the carry's tier: `b_tier_pages` pages, lanes arbitrary, any home | published `LevelCarry.tier` |

* A is **never written** by the finish and neither is B: B's occupancy masks are copied per
  direction (DN:544-560), both tiers are read through private mask copies (`BorrowTier`,
  J:2140-2155), the R pool slot is private. (Checked: `sources_unchanged` in every fixture.)
* **What `FinishMerge` starts from.** `Begin` reset every stash slot (so the merge stash is
  empty) and the output tier (J:1836-1872); the preparation filled R. `InstallCarry` is a
  validation only at the top (`PlanLevelMergePhase` kInstallCarry, M:846-849; `BindCarry`
  J:2120-2136 binds B main as `finish_.fresher` without copying and takes private masks of B's
  tier). The output main is not cleared; its stale bytes are never read (every bucket of C is
  written by the preparation).
* **Pool slots** (`TopMergePoolSlots`, J:320-333; `BindPool`, J:2217-2240):

  | slot | storage | rank | class | role |
  |---|---|---|---|---|
  | 0 | merge stash `older_sheds_[block_bits+2]`, `S_A` pages (empty at start) | 0 | drain-only | receives B's sheds; drained after the range leftovers |
  | 1 | R, `S_R` pages | 2 | A class | swept; distributed (DFS leaves, or the direct pages) |
  | 2 | B tier private view, `tb` pages | 0 | tier class, **direct** | swept; offered directly, never distributed (`separate_direct_tier`, RP:320-338) |

  `rule = kClassMark`, fuse site `kFixedMerge`, `reset_slots = 3`, `drain = out_tier`.

---------------------------------------------------------------------------------------------------
## 3. Execution order of the finish

The planner (`PlanFixedMerge`, P:858-887, `PlanFusedPassPrologue/Epilogue`, P:583-611) emits,
in this order (all at the whole budget, one stage each):

```
1  F1  pool dedup            (kResidualPoolDedup, window kSweptOnly, P:385-400, R:658)
2  F2  range-table build     (kResidualScatterRetag for B's tier, then either
                              kResidualDfsGather + kResidualDfsPartition, or, in the
                              direct plan, kResidualScatter + kResidualRetag; P:406-453)
3  F3  the sweep             (kFixedMergeOffers over B buckets 0..U-1, R:565-579)
4  F4  the epilogue          (drain 1, leftover dedup, drain 2, reset; P:480-507, 599-611)
5  F5  trailing drops        (kDropErased over C, kDropErasedTier over the tier; P:907-926)
```
The epilogue's pool-dedup emission (window kDrainOnly) is **not planned**: no pair has
`rank[f] < rank[s]` with `s` the drain-only slot of rank 0 (`ResidualPoolDedupNeeded`, RR:638-655).

### Primitives

```
Append(stash, list)        # MergeBucketIntoResidualStash / PlanStashMergePermute(Rounds), MSS:563-663, RS:148-165
    list's records, in list order, go into the lowest free lanes of stash page 0, then page 1, ...
    (page-by-page, so holes left by earlier removals are refilled first).
    The capacity test is made BEFORE writing:  Count(stash) + |list| > 64 * pages  -> FAIL.
PlaceInOrder(bucket X, list)       # the merge permutes, SC:915-984 and PlanResidualOfferMerge
    n = min(|list|, 64 - |X|);  the first n records of the list go, in list order, into
    LowestFree(X, n)   (lanes freed earlier in the same visit are free lanes).
```

### F1. Pool dedup (the combined dedup of R against B's tier)

```
btier_keys = { key(r) : r in any B-tier page, any real lane }      # tombstones and unshadowed ones included
R := R minus { r : key(r) in btier_keys }                          # R's occupancy masks are cleared (private)
```
This is the only pair with `rank[f] < rank[s]` among swept slots (f = B tier, s = R). It does
**not** look at C, B main, the merge stash, or R itself. B's tier is never cleared. It runs on
the stashes' own masks, so it sees flagged tombstones that F2 will drop.
(`ResidualPoolDedupRange`, RR:528-562, units = ordered bucket pairs, idempotent.)

### F2. Range-table build

**F2a, B's tier, direct copy** (`kResidualScatterRetag`, R:667-686, `ScatterAndRetagResidualPoolRange`
RR:318-359 with `tier_from_group = 0`, `drop_unshadowed = true`): range bucket `rho_end + p` :=
B-tier page `p`, **same lanes** (`per = 64`: a lane-preserving copy, MT:366-381), with the
class bit 0x40 **set**, **after removing every lane that is a tombstone with bit 0x20**
(`DropUnshadowedFromMask`, RR:345-347). B's tier is not distributed: one range bucket per page,
`tb` pages (plan: `groups = tb`, `index_bits = ml`, `range_bits = 0`).
Call the resulting `Btc[p]`.

**F2b, A's class, DFS plan (`dfs = 1`, `ml >= 4`)** (`kResidualDfsGather`, `kResidualDfsPartition`,
R:711-740; `DfsResidualWorkspace`, DFS:560-973):
```
gather:   pool = [ r : for page in R pages 0..S_R-1 (after F1), for lane ascending,
                      r is not (tombstone and unshadowed) ]        # RR:345, drop_unshadowed = true
          (class bit cleared on every gathered lane; this is the A class)
leaf l :  Lf[l] = [ r in pool, in pool order : (h(r) >> I) == l ]  for l = 0 .. 2^rho - 1
          stored as ONE page per leaf, lanes 0..|Lf[l]|-1 (stable compaction)
FAIL      "residual-dfs-partition"  iff  some leaf has more than 64 records
```
Node capacities are `C(height) = min(P, 64 * 2^height)` with `P = 64 * S_R` slots (DFS:724-729) and
the unit list compacts the pool straight into each node at the first height whose capacity is
below `P` (DFS:734-743, 816-826); every node holds only records of its descendants, so a node can
exceed its capacity only if a leaf exceeds 64. Hence **the verdict is exactly "max leaf > 64"**;
the unit that reports it is irrelevant. For `S_R = 1`, `P = 64`, so this **cannot fail**. The
count includes plain tombstones of R (they are removed only later, at (c)) and excludes
flagged ones (already dropped at the gather). The partition itself is lossless and stable.

**F2c, A's class, direct plan (`dfs = 0`, `ml <= 3`, i.e. `T = 8`)** (`kResidualScatter` +
`kResidualRetag`, R:667-710): range bucket `g` (`g = 0..S_R-1`) := R page `g` after F1, lanes
preserved, with the flagged tombstones removed (`ScatterResidualPoolRange`, RR:236-271), class
bit cleared. No partition, no test, no failure. Call `Lf[g]` the pages ("groups = S_R").

Visiting order of A's pages by a destination `ci`:
`pages_A(ci) = [Lf[ci >> I]]` (DFS: one page) or `[Lf[0], ..., Lf[S_R-1]]` (direct plan, group order).
A candidate of `ci` on a page is a lane with `h(r) == ci`.

### F3. The sweep (the `kFixedMergeOffers` kernel)

`MergeFixedLevelSourcesOffersRange` (SC:1004-1071) with `MergeRadixSourceBucket` (DN:523-562),
`ResolveTopDestination` (SC:854-890), `MergeBucketWithResidualOffers` (SC:915-984). The offer sets
are `GatherFusedOffers` (R:316-345): set 0 = A's pages (`kTableWins`, forced by the direct slot),
set 1 = B's tier pages (`kResidualWins`); the tombstone policy is `kAll`
(`FixedMergeTombstonesOf`, R:257-269: `drop_unshadowed` is true at the top and every active pass
is fused at the sweep). Because `kAll` is the resolved mode, **every offer is allocated as
`kNoDedup`** (SC:1036-1063, 967-971): no dedup is repeated in the offers.

```
ins := merge stash (empty), S_A pages
for i in 0 .. U-1:                                   # B bucket i, ascending
  bk := { key(r) : r real lane of B_main[i] }         # tombstones and flagged ones included
  # (0) dedup of every destination against ALL of B[i]      (DedupBucketDestinations, DN:539, DM:453-478)
  for q in 0 .. D-1:   C[i + q*U] := C[i + q*U] minus { r : key(r) in bk }
  sheds := []
  for q in 0 .. D-1:                                  # way q, destination ci = i + q*U
    direction_q := [ r in B_main[i], lane order : q(r) == q ]       # tombstones included
    dkeys       := { key(r) : r in direction_q }
    # ---- RESOLUTION, before any capacity decision (ResolveTopDestination) ----------------
    (d)  C[ci] := C[ci] minus { tombstones }                          # every tombstone, flagged or not
    for page in pages_A(ci), group order:                              # set 0, A candidates naming ci
         (a) remove candidates c (h(c) == ci) with key(c) in dkeys     # B main beats A, live or tombstone
         (c) remove candidates c (h(c) == ci) that are tombstones      # whatever is left
    for page in Btc[0..tb-1]:                                          # set 1, B-tier candidates naming ci
         let F = { c in page : h(c) == ci }                            # lanes of the page, all of them
         (b) C[ci] := C[ci] minus { r : key(r) in keys(F) }            # F includes tombstone candidates
         (c) remove from the page the tombstones of F
    # ---- B's direction merged into C[ci]: live records only ------------------------------
    src   := [ r in direction_q : r is not a tombstone ]               # every B tombstone is left out
    place the first min(|src|, 64-|C[ci]|) records of src, in order, into LowestFree(C[ci], .)
    shed_q := the rest of src, in B-lane order
    sheds.append(shed_q)
    if q == D-1:                                                        # the stash is written once per source bucket
        if Count(ins) + sum(|shed_q|) > 64*S_A:   FAIL "fixed-merge-offers"
        Append(ins, shed_0 ++ shed_1 ++ ... ++ shed_{D-1})              # direction order, each in B-lane order
    # ---- the offers, set 0 then set 1 (kNoDedup allocation) -------------------------------
    for page in pages_A(ci), group order:
         cand := [ lanes of page, lane order : h == ci ]
         PlaceInOrder(C[ci], cand);  the placed candidates leave the page
    for page in Btc[0..tb-1], page order:
         cand := [ lanes of page, lane order : h == ci ]
         PlaceInOrder(C[ci], cand);  the placed candidates leave the page
```
Order in which destinations are processed: `ci = i` (q = 0), `i + U` (q = 1), ... for `i` ascending.
Each candidate names exactly one destination, so this order cannot change which candidates are
absorbed; it does fix the failure order and the shed order.

Facts the model relies on (all checked by the 1000 fixtures):
* The resolution is a **set-valued** clear: the relative order of (a), (b), (c) inside one visit
  does not matter except that (b) must see the tier's tombstone candidates before (c) removes them
  (the code order is (d), then set 0 (a)/(c), then set 1 (b)/(c)).
* **Which candidates clear what.** Flagged tombstones are already absent from `Btc` and from the A
  pages (F2), so they take part in no step of the resolution *except* through `dkeys`: a flagged
  **B-main** tombstone still counts in `bk` and `dkeys` (it clears C and R candidates).
* B tombstones are never inserted and so never shed. Sheds are live B records only.
* The merge into C and the offers never remove a record of C: after the resolution C[ci], the
  merged B records and the candidates of `ci` are key-disjoint (given the input contracts of
  section 10), so absorbed candidates do not displace anything. Only a **full** `C[ci]` sheds
  or leaves candidates.

### F4. The epilogue (`PlanResidualFinishPhases`, P:480-507)

`ResidualPassHasLeftoverDedup` holds (the drain-only slot 0 has rank 0 < rank 2 of R), so the drain
is split around the leftover dedup:
```
tier := output tier, empty, `tb` pages
# drain 1: range leftovers into the tier (kResidualDrain units [0, range_units), SC:1189-1200, R:748-773)
for rb in range buckets, ascending:           # A's: DFS leaves 0..2^rho-1 (page 0 of each),
                                              #      or, direct plan, R pages 0..S_R-1;
                                              # then B's tier copy pages 0..tb-1
    L := remaining records of rb, lane order
    if Count(tier) + |L| > 64*tb:   FAIL "residual-drain"            # the running total, BEFORE any dedup
    Append(tier, L)
# leftover dedup (kResidualLeftoverDedup, SC:1127-1177, R:602-610); a lane's class = its range
# bucket's class: A's pages class A (bit 0x40 clear), B's tier copy class B (bit set)
shed_keys   := keys of the merge stash;   tierB_keys := keys of the class-B lanes now in the tier
tier := tier minus { class-A lanes whose key in shed_keys }               # a B shed beats an A leftover
ins  := ins  minus { lanes whose key in tierB_keys }                      # a B-tier leftover beats a B-main shed
# drain 2: the merge stash (units past range_units; DrainResidualPoolRange, SC:1217-1241)
for page in ins pages ascending:
    L := lanes of page, lane order
    if Count(tier) + |L| > 64*tb:   FAIL "residual-drain"
    Append(tier, L)                  # fills the lowest free lanes, including the holes the dedup left
# reset (kResidualReset, R:774-778): clears the masks of the three pool slots; no effect on the output
```
The leftover dedup is a public step that, **on inputs satisfying the contracts of section 10, removes
nothing** (0 removals in all 823 contract-satisfying fixtures); it removes records only if B main and B
tier share a key, or a B-main record sits in the wrong carry bucket (section 9).

### F5. Trailing tombstone drops (`kDropErased`, `kDropErasedTier`; P:918-926, R:809-830)

```
for every bucket of C:   remove every tombstone lane          (DropErasedEntriesRange, MT:244)
for every tier page:     remove every tombstone lane
```
Public work. At the top it **always finds nothing** (the checked build asserts it,
`TopResolutionRuns`, R:293-303, R:819-829): every tombstone that could reach C or the tier is removed
earlier (section 8). 0 nonzero drops in all 1000 fixtures, including the contract-violating ones and with
engine asserts on.

**Output** = C's main (`T` buckets, lanes as left by the steps above) and the output tier
(`tb` pages, lanes as left by the appends). All output records are input records, unchanged.

---------------------------------------------------------------------------------------------------
## 4. Where each destination reads B's tier and A's pages

* **B's tier pages are read directly by every destination.** The direct copy `Btc` has one range
  bucket per tier page and **each of the `T` destinations scans all `tb` pages** (`groups = tb`,
  `index_bits = ml`, `r = g`), picking the lanes whose full home equals `ci`. Order across pages:
  page 0, 1, ...; inside a page, lane order. B's tier is therefore allocated **after** A's pages.
* A's class is read from `pages_A(ci)` (F2): its one DFS leaf `ci >> I` (compacted lanes), or, in the
  direct plan, all `S_R` pages of R in page order.
* The resolution reads **every page of both sets** before the first allocation of a destination,
  and the pages are read-only (B) or private (R copy).
* Hence `candidates(ci)` in absorption order is
  `A pages (leaf order) ++ B-tier pages (page order, lane order)`, each filtered by `h == ci`.
  Lane placement: i-th absorbed record into the i-th lowest free lane of `C[ci]`
  (free lanes include the holes left by the resolution clears).

---------------------------------------------------------------------------------------------------
## 5. Failure table

All finish failures are `std::runtime_error("level arena: the finish phase ran out of room at
<kind>; the certified depth did not hold")` (J:2555-2561, `SubtaskKindName` SK:319-346). The phase is
aborted and nothing is published. In execution order:

| step | `<kind>` | tested quantity > threshold |
|---|---|---|
| F2b | `residual-dfs-partition` | the number of records of some leaf (DFS plan only) > 64. Impossible for `S_R = 1` (P = 64). Count = R after F1, minus flagged tombstones, plain tombstones included. |
| F3 | `fixed-merge-offers` | after the sheds of **all D ways of B bucket i**: `Count(merge stash) + sum_q |shed_q|` > `64 * S_A` (`merge_stash_capacity`). The running total over buckets; made once per source bucket, before that bucket's last-way offers (irrelevant, the run aborts). |
| F4 drain 1 | `residual-drain` | after appending the leftovers of range bucket `rb`: `Count(tier) + |L|` > `64 * tb` (`out_tier_capacity`); the running total of A leftovers then B-tier leftovers, **before** the leftover dedup |
| F4 drain 2 | `residual-drain` | `Count(tier after the leftover dedup) + |page of the merge stash|` > `64 * tb`, running over the stash pages |

Drain 1 and drain 2 raise the same message; the model's counters `fail_drain1` / `fail_drain2` tell them
apart. Anything else (`logic_error`, `invalid_argument`) is a misconfiguration, not a verdict. The preparation
has its own failures (`prepare-older ... butterfly`, `residual-dfs-partition`, `residual-drain` of
its drain into R); a run whose preparation fails is **skipped** by the dumper (exit 3, counted in
`fx/manifest.json`: 117 of 1152 attempts). With one lane there is no fold check.

Under the report's premises each tested quantity is bounded by `E = sum_v (X_v - 64)+` (checked,
section 9, item 1), so an F3 or F4 failure needs `E > capacity`; F2b failures are not E events.

---------------------------------------------------------------------------------------------------
## 6. Merge stash and output tier

* The merge stash is **drain-only**: it is never swept, never in the range table, never offered back.
  It receives B's live sheds only (F3), in direction order then B-lane order, appended into the lowest free
  lanes of page 0, then page 1. It is read twice: by the leftover dedup (as the key set that removes class-A
  leftovers, and as the list that loses to class-B leftovers) and by drain 2.
* The output tier receives, in this order: A's range leftovers (leaf/page order, lane order), B's tier
  leftovers (page order, lane order), then the merge stash minus the dedup. Class-A leftovers that duplicate a shed
  are removed from the tier lane where they sit (a hole), and drain 2 refills holes first.
* `merge_stash_pages == S_A == S_R` and `out_tier_pages == tb` are independent parameters.

---------------------------------------------------------------------------------------------------
## 7. What sets `kMetaUnshadowed`

A tombstone is inserted by an access; the access marks it unshadowed iff its probe **found nothing, or found a
tombstone that is itself unshadowed** (`NoOlderLiveCopy`, levelarena/cpu_byteslice_level_arena_engine.hpp:677-709;
the batch path forwards the same bit, table/cpu_byteslice_batch_probe.hpp:540-600). A found live entry or a found
shadowing tombstone clears it. The bit is a **promise**: no live copy of that key exists older than the tombstone,
anywhere in the hierarchy (MT:67-93). It is "conservative-safe": clearing it costs only capacity; setting it wrongly
is a silent correctness bug (a stale value resurrects). The engine never checks it. A is the oldest table, so at the
top the promise is about C, R and everything of B older than the tombstone.

---------------------------------------------------------------------------------------------------
## 8. Tombstones: every path

`drop_unshadowed = true` at the top (J:2086). A tombstone leaves at one of these points; plain = no 0x20.

| source | plain tombstone | tombstone with 0x20 |
|---|---|---|
| **A main** (preparation, not the finish) | copied to C, routed like any record, ends in C (or R) | removed at the preparation's copy (`CopyAndRetagRange`, `drop_unshadowed`): never in C; fixtures with 0x20 in `C_main`/`R` exist only through `--inject-flag` (synthetic) |
| **A tier / stage stashes** | routed into the preparation's pool, ends in C or R | removed at the preparation's scatter (RR:264-266); never in R (same remark) |
| **C main** (finish) | removed at the visit of its home, step (d), for every tombstone (flagged or not) | same |
| **R** (finish) | takes part in F1 as a staler lane (cleared if B's tier holds its key); counted by the DFS leaf test; removed at (c) when its home is visited, or earlier at (a) if B main holds its key | removed at F2 (gather, RR:345-347), after F1; not counted by the DFS leaf test; never reaches (a)/(c) |
| **B main** | clears C's copy of its key in step (0) (all of `bk`) and the A candidates of its key at (a) (`dkeys`); never merged (every B tombstone is left out of `src`, so never shed) | identical to a plain one (`FixedMergeSkippedSlots` `always`/`shadowing`, DN:340-350 give the same `src`; `bk` and `dkeys` include it) |
| **B tier** | takes part in F1 (clears R's copy of its key); is in `Btc`; clears C's copy at (b); removed from `Btc` at (c); never absorbed, never drained | **removed at F2a (the direct copy), after F1**: it clears R's copy (F1) but **not C's copy** (it is absent when (b) runs), and is never absorbed or drained |
| **merge stash, drains, tier** | cannot hold one (sheds are live; candidates are cleared before the offers) | cannot hold one |
| **trailing drops** | no-ops | no-ops |

Consequences: (i) every tombstone is forgotten at the top, but at **three different moments**: at the preparation's
reads (flagged A), at F2 (flagged R and B-tier), at the visit of its home (all others), and the trailing drop is
never the one that forgets one. (ii) A flagged tombstone is exactly as good as a plain one **iff its promise
holds**; if C holds a live copy of a key that a flagged B-tier tombstone names, the copy **survives** (it is not
cleared at (b)); a flagged B-main tombstone is safe in that case (C is cleared by step (0), R by (a)); R is cleared
by F1 for B-tier tombstones. The fixture family `badflag` of the generated battery
(`oracle/fixtures-top/gen_top.py`) exhibits the surviving copy.
(iii) An A tombstone in C or R is handled (d)/(c); A is tombstone-free on an engine history.

---------------------------------------------------------------------------------------------------
## 9. Differences from the report (REPORT.tex, Proposition prop:top-resolution, Lemma lem:resolved-compression, Corollary cor:top-finish-separated)

Method: `report_check.py` computes the report's logical reference from the inputs (A = C u R, B = B main u B
tier, B over A, a winning tombstone removes the key, `X_v`, `E = sum (X_v-64)+`) and compares it with the
**engine's output** on the 823 fixtures that satisfy the proposition's premises. All 823 agree (C holds
`min(X_v,64)` records at every home, all of them winners with the winner's value, the tier holds exactly `E`
records, no tombstone anywhere, each winner exactly once; the merge stash plus the first drain hold exactly `E`;
every F3/F4 failure has `E` above the capacity). 177 more fixtures break a premise on purpose and disagree.

1. **Order of steps and what is resolved against what: none found.** The engine does (0) the dedup of C against
   all of B main, then per destination (d), (a), (c-leaf), (b), (c-tier), then merge, then the offers; the report's
   (a)-(d) are exactly these, with the same sources and the same directions. The pool dedup before the scatter is
   "R minus the keys of B's tier" (nothing else). Step (a) compares with direction `q` of bucket `i` only; by
   (P2) that holds every B-main copy of a key homed at `ci`.
2. **Not every tombstone takes part in (a)-(d): the unshadowed early drop.** The report's (b) says C[v]'s copies of
   the T candidates are cleared and (c) drops every tombstone candidate. In the engine a tombstone **with bit 0x20 is
   removed from the range copies at F2, before the resolution**, so a flagged B-tier tombstone does **not** clear
   C's copy (it does clear R's copy through F1, and a flagged B-main tombstone still clears C and R). The report
   mentions the unshadowed drops only for R's DFS accounting ("Combined dedup and the unshadowed drops only delete
   them") and its premise (P1) does not state the flag's contract. The two agree only under the flag's promise.
   Reproduction: family `badflag` of the generated battery in `fx/` (33 of 37 fixtures disagree
   with the logical reference for this reason). The Lean model must carry the flag and the promise.
3. **Whether every tombstone is dropped:** yes, and the trailing drops are public no-ops (0 nonzero in 1000
   fixtures). The tombstones of B main are never inserted (dropped at the merge, not by the trailing drop), those of R
   and B's tier are removed from the range copies, those of C at (d).
4. **Whether R alone is distributed:** yes. R is the only distributed class; B's tier is offered directly. In the
   **direct plan (`T = 8` only)** the "one-page A leaf" is `S_R` pages (groups = `S_R`), nothing is distributed and
   there is no DFS test; this is consistent with the report's "a direct plan has no first term", but its "A leaf"
   is `S_R` pages and the offer visits them in page order.
5. **Whether B's tier pages are read directly by every destination:** yes, all `tb` pages by all `T`
   destinations, matched by full home; offers visit A's pages first, then B's pages.
6. **Whether the merge stash is drain-only:** yes. Its capacity test is per **source bucket** (all `D` ways at
   once, after the last way's merge), on the running total, and it is appended in direction order. It is
   equivalent to a test on the running total.
7. **The offers are not the report's "class-marked" offer.** The engine's pass has `rule = kClassMark`, but at the
   top the resolution runs first and every offer is allocated as `kNoDedup`, set 0 (A pages) then set 1 (B pages),
   "lowest-indexed candidates that fit". The class bit is used only by the leftover dedup. Same result as the
   report's description under the premises.
8. **Leftover dedup:** the report says it removes nothing; true on premise-satisfying inputs (0 removals in 823
   fixtures). It removes records only when a premise is broken: **B main and B tier share a key** (a shed is removed
   by a class-B leftover) or **a B-main record sits in the wrong carry bucket** (an A leftover is removed by a shed).
   Families `dupmain`, `dupmain2`, `misplace`, `misplacefull`: 75 fixtures with removals.
9. **What the DFS test counts:** the report's `R_r` counts live R records homed in range `r`. The engine counts
   every lane of R after F1 and the flagged drop, **plain tombstones included** (they are removed at (c), later).
   Equal on a tombstone-free A (an engine history). Failure is exactly "some leaf > 64", impossible at `S_R = 1`
   (`P = 64`) — consistent with "impossible when `S_R <= C`".
10. **Capacity tests and prefixes:** `drain1 + merge stash = E` exactly (not only `<= E`) on every premise-satisfying
    fixture; the tests compare totals before the leftover dedup (drain 1) and after it (drain 2).
11. **What the tests compare:** the engine's own tests (`cpu_byteslice_level_arena_top_test.cpp`,
    `cpu_byteslice_top_resolution_test.cpp`) compare live sets, homes, counts and `E`, never lanes. Lanes are
    deterministic and fixed by section 3 (lowest free lanes, B-lane order for sheds, leaf order for A, page/lane order
    for B's tier, direction order for appends); the report does not constrain them.
12. **Not verified here:** `lanes > 1` (private range masks AND-folded), pause/resume slices, helper threads. The
    engine's own battery claims byte-identity for them; the fixtures are whole-budget, one lane.

---------------------------------------------------------------------------------------------------
## 10. Input contracts the engine relies on without checking

(The generator respects all of them except in the four named violation families, which exist to show what each one
buys.)

1. **B main bucket `i` holds exactly the keys with `w & (U-1) == i`**, each at most once. The sweep recomputes the
   way (`(w >> K) & (D-1)`) but never the bucket: a misplaced record is merged into `C[i + q*U]`, a home that is not
   its own, and the dedup (a) misses its A copy (family `misplace`, `misplacefull`).
2. **B main and B tier are key-disjoint**, and each is internally distinct (family `dupmain`, `dupmain2`).
3. **A (C u R) is key-distinct**, and C bucket `h` holds only records with home `h` (R's records name their home by
   their key; the retag recomputes it).
4. **A flagged tombstone's promise** (section 7): no live copy of its key is older than it, in particular none in C,
   R, or older in B. Not checked anywhere.
5. Every bucket, page and tier holds at most 64 records, occupancy words are honest; dummy lanes may hold any bytes.
6. The nonce family of B equals the job's family (`ValidateArrival`, J:2007-2035: **checked**); B main has `U`
   buckets and a tier (checked).
7. The pool shape is public and consistent (`ExpectPoolMatchesShape`, J:2188-2199: checked).
8. R was produced by the preparation's drain (A class, rank 2); nothing in R is fresher than anything of B. The
   pool dedup (F1) and the resolution are the only places that rank it.
9. Key 0 is handled by a repair path in the intersect kernels; the fixtures avoid it.
10. A **bucket-width bound**: `S_R`, `S_A`, `tb` are at most 8 (`kMaxResidualStashBuckets`); the engine throws at
    construction otherwise.
11. `drop_unshadowed` is enabled only at the top (`ExpectMergeView(ctx->drop_unshadowed == spec.top)`, M:764).

---------------------------------------------------------------------------------------------------
## 11. How this differs from the d = 2 model (`Job.lean`)

| piece | d = 2 (`Job.lean`) | top finish |
|---|---|---|
| A's route | `routeA` (butterfly with sheds) | none in the finish; C and R are inputs |
| pool | `poolA`: stages ++ A tier, minus B-tier keys | R only (page, lane order), minus B-tier keys, then minus flagged tombstones; **A tier is not in the pool** (it was drained into R by the preparation) |
| DFS | `dfsTrace` over every node | one test per leaf (> 64), impossible at `S_R = 1`; **direct plan** (`T = 8`) has none and keeps R's pages |
| leaves | `leavesOf` by range, pool order | the same for the DFS plan (stable, page 0 only); direct plan: the S_R pages |
| `fill` | lowest free lanes in order | reuse as is (`PlaceInOrder`) |
| `insertBucket` | B bucket into `i`, `i+U` (bit `k`), dedup of the two outputs, then `offerA` (consumes A candidates whose key is in main), `offerB` (clears the main copy first) | `D` ways, dedup of all `D` destinations against B bucket `i` first; **resolution (d),(a),(b),(c) before the merge**; B tombstones left out; then offers that never compare keys |
| `offerA` | absorbs, and consumes candidates with a key already in main | absorbs only (candidates are already distinct from C and B); same lane rule |
| `offerB` | frees the lane of the A-main copy of each candidate | no freeing in the offer; the freeing is step (b) of the resolution, **before the merge** |
| shed test | after both ways of bucket `i` (`.insertion`) | after all `D` ways of bucket `i` (same shape) |
| `drain` | A leaves (range order), B tier leftovers, leftover dedup, insertion stash | same shape; the first drain runs over the **range buckets** (leaves or R pages) then `tb` pages of B tier, the second over the stash **pages**; class A = range bucket, class B = B-tier copy |
| tombstones | none dropped | B tombstones omitted, early drop of flagged ones, (c)/(d), trailing no-op drops |
| `Caps` | route/dfs/insertion/drain | dfs (leaf), insertion (`64*S_A`), drain (`64*tb`) |

---------------------------------------------------------------------------------------------------
## 12. Validation record

* **1000 fixtures** (`fx/f0000..f0999`, fixed seed, regenerated byte-identically): 772 successes (lane-exact
  `(bucket, lane, key, value, tombstone)` on `C` main and output tier) and 228 failures (verdict and failing kind);
  by D (fixtures / failures): D=1 383/94, D=2 260/42, D=4 246/58, D=8 111/34; failures: 105
  `residual-dfs-partition`, 34 `fixed-merge-offers`, 89 `residual-drain` (61 at drain 1, 28 at drain 2). Per D the
  four failure points: D=1 (54, 10, 21, 9), D=2 (15, 9, 9, 9), D=4 (22, 11, 18, 7), D=8 (14, 4, 13, 3), as
  (dfs, merge stash, drain 1, drain 2). 117 preparation failures were skipped.
* **Coverage** (fixtures with a nonzero effect, of 1000): (a) 328, (b) 411, (c) A-candidate tombstones 155 and
  B-tier tombstones 345, (d) 349; A-leaf absorbs 219, A-candidate drops by (a)/(c) as counted, B-tier absorbs 412,
  B-tier clears of C by (b) 411, merge-stash appends 359 (second stash page used 26), output tier second page 133,
  pool-dedup removals 339, early drops: R 56 (synthetic), B tier 102, B main 106; leftover-dedup removals
  37 + 38 (violation families only); trailing drops 0; R on a second page 221; B tier above 64 records 111,
  on two or more pages 571; DFS gathered 611.
* **Engine asserts on** (`fdtop_assert`, `-UNDEBUG`): all 1000 runs complete with byte-identical JSON, including
  `ResidualPoolEqualRanksDisjoint` and the "trailing drops find nothing" asserts (R:819-829).
