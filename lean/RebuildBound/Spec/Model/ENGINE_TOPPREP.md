# Record-level semantics of the top preparation and of the direct initialization's route

Extracted from the engine by reading its code and checked against it:
`model_tp.py`, written from this text, matched the engine **lane-exactly on every successful run
and on verdict plus failing kind on every failure: 2519 of 2519 fixtures** (1599 top preparations,
800 initialization routes driven at job level, 120 initializations driven through the public
`LevelArenaEngine::Initialize` and read back from the publisher's live table). The engine was built
with `-DNDEBUG` and again with engine asserts on (`-UNDEBUG`): byte-identical output on every
fixture, no assert fired. The Lean model `TopPrep.lean` follows it. Reproducible
sources under `oracle/fixtures-tp/`
(see its README for build and regeneration commands): `fdtp.cpp` (dumper,
both modes), `fdtp_engine.cpp` (public-engine initialization dumper), `build_fdtp.sh`,
`build_fdtp_engine.sh`, `model_tp.py`, `gen_tp.py`, `gen_engine_tp.py` (deterministic, fixed
seed), `run_tp.py` (driver + coverage), `report_check_tp.py` (REPORT cross-check),
`mutate_tp.py` (mutation check of the model). Generated artifacts stay under
`.lake/oracle/fixtures-tp/`: `fx/` `fx-assert/` `fx-engine/` `fx-engine-assert/`
(the fixtures), `RESULTS.txt`, `REPORT_CHECK.txt`, `MUTATIONS.txt`. File:line anchors refer to the engine revision the extraction was read from and
may have shifted; the function names identify the code.

Paths are relative to `src/oram/`. Abbreviations: `M` = levelarena/cpu_byteslice_level_arena_merge.hpp,
`J` = levelarena/cpu_byteslice_level_arena_job.hpp, `PS` = levelarena/cpu_byteslice_level_arena_pass_shape.hpp,
`ST` = levelarena/cpu_byteslice_level_arena_stash.hpp, `G` = levelarena/cpu_byteslice_level_arena_geometry.hpp,
`LV` = levelarena/cpu_byteslice_level_arena_level.hpp, `EN` = levelarena/cpu_byteslice_level_arena_engine.hpp,
`P` = scheduler/cpu_byteslice_subtask_plan.hpp, `R` = scheduler/cpu_byteslice_subtask_run.hpp,
`SK` = scheduler/cpu_byteslice_subtask.hpp, `BF` = rebuild/cpu_byteslice_butterfly_stash.hpp,
`MS` = rebuild/cpu_byteslice_mergesplit.hpp, `MSS` = rebuild/cpu_byteslice_mergesplit_stash.hpp,
`SC` = rebuild/cpu_byteslice_second_chance.hpp, `RR` = rebuild/cpu_byteslice_residual_range.hpp,
`DFS` = rebuild/cpu_byteslice_dfs_residual.hpp, `INIT` = rebuild/cpu_byteslice_initialization.hpp,
`RM` = table/cpu_byteslice_routing_map.hpp, `MT` = table/cpu_byteslice_meta.hpp,
`REPORT` = analysis/bound_certification/REPORT.tex. The twin documents are `ENGINE_TOP.md` (the finish),
`ENGINE_D2.md`, `ENGINE_RADIX.md` (the ordinary merge); section 11 lists the differences from the d = 2
merge item by item.

**Summary in six lines.**
(1) Both passes are one job phase: `PrepareOlder` of the top `LevelMergeJob` (`PlanTopPrepare`, M:508-526,
which is `PlanPrepareOlderHalf`, P:682-731), or `RouteInitialTop` (J:1084-1119) which runs the same phase
in place. (2) C is copied (preparation) or already scattered (initialization), then routed by **two
independent half-block butterflies of `k-1` levels** (`k = log2 T`; recursive cache-oblivious order, quads
of two levels), each level shedding into its own stash `older_sheds_[bit]` of `S` pages. (3) A one-page DFS
(or, at `T = 8`, a direct plan) is built over the pool = sheds of bits `0..k-2` in bit order, then A's old
tier. (4) The **last level (bit `k-1`) is fused**: per pair `(i, i+T/2)`, the merge-split, then the offers
of bucket `i`, then of `i+T/2`; its sheds are the drain-only stash and are **not** in the pool. (5) The
drain is: range leftovers (leaf order, lane order), then the last level's stash (page order, lane order),
into R (stash slot `older_sheds_[k+3]`, `S` pages) or into the published tier (initialization). (6) Four
capacity tests, in order: stage stashes (`butterfly`), DFS leaves > 64 (`residual-dfs-partition`), last-level
stash (`butterfly-offers`), drain (`residual-drain`). No dedup, no tombstone drop except the flagged
(0x20) ones, no leftover dedup, no trailing drop.

---------------------------------------------------------------------------------------------------
## 0. Notation

* `C = 64` = `kBucketCapacity`. A bucket is a partial map lane (0..63) -> record; "lane order" is ascending
  lane. `LowestFree(X, n)` = the `n` smallest lanes not occupied in `X`. As in `ENGINE_D2.md`/`ENGINE_TOP.md`.
* `Append(stash, list)` (`MergeBucketIntoResidualStash`, MSS:644; `PlanStashMergePermute(2)`, MSS:277): the
  records of `list`, in list order, go into the lowest free lanes of page 0, then of page 1, and so on. The
  capacity test comes BEFORE any write: `Count(stash) + |list| > 64 * pages` -> FAIL. Nothing is ever removed
  from a stage stash or from the drain target during these passes, so the **lane order of every stash equals
  its append order** and has no holes.
* `home(r) = w(key(r)) & (T-1)`, `bit(r, b) = (w(key(r)) >> b) & 1`, where `w` is the low 64 bits of the
  AES-CTR word of the key under the NEW family's nonce (`map_` is `kRaw`; the tag bit `b` is bit `b` of `w`).
  The fixtures list `w` of every key (`words`).

---------------------------------------------------------------------------------------------------
## 1. Geometry

| symbol | value | where |
|---|---|---|
| `U` | `Z * B^(L-1)`, `Z = 2 r0 s` (`r0` in {2,4,8}, `s` online-stash buckets, `B` in {2,4,8}, `L >= 2`) | `CarryBuckets`, G:559 |
| `D` | top digit, a power of two in {1,2,4,8}, `D <= B` (the top is binary) | `IsTopDigit`, G (`kMaxTopDigit = 8`) |
| `T` | `D * U`, a power of two, `T >= 8` (`U >= 8`) | `MakeTopMergeShape`, M:202-209 (`out_buckets`, `older_buckets = out_buckets`) |
| `K`, `e`, `k` | `log2 U`, `log2 D`, `block_bits = k = K + e = log2 T` (`r = 1`, no radix pass) | M:202, `MakeMergeShape` |
| `S` | `LevelArenaStashSizing::Buckets(top)`: the depth in pages (64-lane buckets) of **every** `older_sheds_` slot (`MakeStashes`, J:~1180) | ST:209; sizing ST:~100-190 (`stages = block_bits + 2`, `+1` for the retained carry, ST:~141-146; `executions = carries + 1` at the top: "Initialize routes the top once", ST:113) |
| `R_old = tb_A` | pages of A's old tier = `OlderTierBuckets(top, D) = TierBucketsOf(top)` | G:524, G:501 |
| `tb_P` | pages of the published tier (initialization) = `TierBucketsOf(top)` = `binding.out_tier->num_buckets` | G:501 |
| `S_R` | pages of R = `S` (R is `older_sheds_[k + 3]`, a slot like every other) | `PrepCarry`, J:1714; `kLevelMergePrepCarryStashOffset = 3`, ST:311 |
| stash slots | `k + 1 + 3 = k + 4` slots `older_sheds_[0 .. k+3]` | `LevelMergeStashSlots(k, top=true)`, ST:313 |

* `S` depends on `T`, `L` and the request horizon only (`max_accesses = 2^acc`): in all geometries probed
  (T = 8 .. 8192, B,L,D,r0,s of the 400-entry sweep) `S = 1` for `acc = 32`, `S = 2` for `acc` in {48, 56}
  (and `S = 3` is not reached below `T = 2^24`; REPORT: floor of 4 above `2^25` homes). `kMaxResidualStashBuckets
  = 8` (RR/residual_stash.hpp:80) bounds `S`, `R_old` and `tb_P` at 8 pages. The fixtures cover `S` in {1, 2},
  `R_old = tb_P = tb` in {1, 2, 4, 8} (one shared tier width).
* **Stage stashes.** Slot `b` (`0 <= b <= k-1`) collects the sheds of the merge-splits on tag bit `b`
  (`level_stashes[bit]`, BF:~48, R:526-535). `k` slots are used by the route. Slots `0 .. k-2` are the
  swept pool, slot `k-1` is the drain-only prefix. Slots `k .. k+2` are unused here (radix, merge, ...); slot
  `k+3` is R.
* **Pool slots** (`TopPreparePoolSlots`, PS:232-244), in this order, with `kLevelMergePrepRank = 0` for all:

  | position | storage | pages | role |
  |---|---|---|---|
  | drain-only 0 | `older_sheds_[k-1]` (the last level's stash) | `S` | not swept, not in the range table; drained after the range leftovers |
  | swept 0 .. k-2 | `older_sheds_[0]`, ..., `older_sheds_[k-2]` (bit order) | `S` each | distributed |
  | swept k-1 | A's old tier (a private view, `kOlderTierView`) | `R_old` | distributed |

  `rule = kNoDedup`, `fuse = kOwnLastLevel`, `shed_slots = k`. Swept pages `W = (k-1) S + R_old`
  (`TopPreparePoolShapeOf`, PS:350). The pool is **gathered in slot order, page order, lane order**:
  `shed[0]` page 0.., `shed[1]`.., ..., `shed[k-2]`.., then A's tier pages.
  In an initialization the tier slot is still in the pool (public shape: `ExpectPoolMatchesShape`,
  J:1516) but it is zero-masked (J:1200-1212: "the initial top has no tier"), so it is empty and only
  adds `R_old` pages to `W`.
* **Range plan** (`TopPrepareRangePlan`, PS:431; `kTopPrepareDfsPages = 1`, PS:408; `PlanResidualRange`
  RR:174, `DfsResidualRangePlan` DFS:97, `DfsResidualRangeApplies` DFS:77), with `ml = k`:
  ```
  if ml <= 3 (kResidualDirectMaxLevels, RR:87; only T = 8):   DIRECT plan, no DFS
        range_bits rho = 0, index_bits I = ml, groups = range_buckets = W
        (range bucket g = pool page g in the pool order above)
  else:                                                       DFS plan, one page per leaf
        bits = smallest b with 2^b >= 8 W   (kResidualsPerRange = 8, RR:76)
        rho  = min(bits, ml);   I = ml - rho
        if I > 18 (kDfsMaxRangeIndexBits, DFS:92):  rho += I - 18; I = 18      (needs T > 2^21: not covered)
        groups = 1, range_buckets = 2^rho, scatter_per_bucket = 64
  ```
  A **range** (leaf) is the set of homes `{v : v >> I == r}`; `rho = range_bits` = log2 of the number of
  leaves, `I = range_index_bits` = log2 of the homes per leaf. Example: `(T, S, tb) = (16, 1, 1)`: `W = 4`, `rho = 4`, `I = 0`.
  `(1024, 2, 1)`: `W = 19`, `rho = 8`, `I = 2`. `(4096, 1, 1)`: `W = 12`, `rho = 7`, `I = 5`.
* **DFS workspace** (`DfsResidualWorkspace`, DFS:~540-990): `P = 64 W` pool slots, node capacity
  `C(h) = P` if `h > 16` or `64 * 2^h >= P`, else `64 * 2^h` (`NodeCapacity`, DFS:724), for `h = 0 .. rho`;
  direct height `hd` = the largest `h <= rho` with `64 * 2^h < P` (`DirectHeight`, DFS:734); the unit list
  (`ForEachUnit`, DFS:816) has exactly `2^rho` units (one per leaf's worth of splits). The fixtures dump `dfs_direct_height`,
  `dfs_capacities`, `dfs_units`, and the model's formulas agree on every DFS fixture.
* Fixture fields (`geometry`): `T, D, U, K, e, block_bits, stage_stash_buckets (= S), r_pages, a_tier_pages
  (= R_old, also in an initialization), out_tier_pages (= tb_P), out_tier_capacity, tier_buckets_param,
  n_sheds (= k-1), pool_swept_buckets (= W), main_levels, dfs, range_bits, range_index_bits, range_groups,
  range_buckets, range_scatter_per_bucket, pool_slots (= 64 W), dfs_direct_height, dfs_units,
  dfs_capacities`.
* Geometries covered: `T` in {8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096}, `D` in {1,2,4,8} (D = 8 needs
  `T >= 256`, D = 4 needs `T >= 64`), `(rho, I)` from (0,3) [direct] and (4,0) up to (8,4)/(7,5). Not covered: `T > 4096`,
  `I > 18`, `S >= 3`, tier widths other than 1/2/4/8 (the public-engine battery uses the automatic width, 1 page).

---------------------------------------------------------------------------------------------------
## 2. Records, meta bits, tombstones

* Record = (key 8 bytes, value 8 bytes); the last value byte is the meta byte. `0x80` `kMetaErased` = tombstone;
  `0x20` `kMetaUnshadowed` (meaningful with `0x80`); `0x40` `kMetaResidualClass` = engine scratch (the fixtures
  mask it out of the value; this pass never writes it: it is `kNoDedup`, not class-marked, so `class_mark` is false at the gather).
  Output records are copies of input records: **the engine never rewrites a payload or the meta byte**.
  A *flagged* tombstone = tombstone with `0x20`; a *plain* tombstone = tombstone without `0x20`.
* **Where flagged tombstones are dropped** (`drop_unshadowed = top_`, J:1416; `DropUnshadowedFromMask`, MT:149):
  1. at the **copy** of A's main (`CopyAndRetagRange`, RM:802-930, the `drop_unshadowed` branch RM:914-919):
     the occupancy mask of the copied bucket loses every flagged lane; all other lanes keep their lane numbers;
  2. at the **gather** of the pool (DFS plan: `kResidualDfsGather` = `ScatterAndRetagResidualPoolRange`,
     R:706-727, RR:318-; direct plan: `ScatterResidualPoolRange`, RR:236-): a flagged lane of any pool page
     (A's tier; a stash shed, which cannot be flagged because of 1) is not gathered. The pool pages' own
     masks are not edited.
  Plain tombstones are **ordinary records** in every step (they are routed, shed, counted by every capacity
  test, offered, drained). A's tier is never copied: its flagged lanes are dropped only at the gather.
  An initialization has neither (its scattered records have meta 0, section 9).
* The stored tag (4 bytes) is scratch: the copy retags A under the new nonce; the initialization retags in place.
  The route reads tag bit `b` of every record at level `b` (so the fixtures' words fix every decision).
* The engine reads no source byte; the fixtures put 1 in value byte 0 of every A record as payload.
* Class bit: not used (`kNoDedup`).

---------------------------------------------------------------------------------------------------
## 3. Execution order of the phase

`PlanPrepareOlderHalf` (P:682-731) with `n = T` buckets, `levels = k`, `fuse_last = true` (the pass is
`kOwnLastLevel` and sweeps) emits, in this order (whole budget, `lanes = 1`):
```
 1  arrival     preparation: kCopyAndRetagRange over [0, T)  (A -> C, retag, drop flagged)      P:242-300, R:514-525
             initialization: kRetagRange over [0, T) only (source_in_place)                      P:649-662, R:501-507
 2  route       PlanButterfly / PlanCopyThenRoute with route_levels = k-1: two independent
             blocks [0,T/2) and [T/2,T), each a recursive butterfly on bits 0..k-2                P:209, 242, R:526-535
 3  pool dedup  planned (kFull window) but EMITS NOTHING: every pool slot ranks equal (rank 0)   RR:638 (ResidualPoolDedupNeeded)
 4  build       DFS: kResidualDfsGather, kResidualDfsPartition   |  direct: kResidualScatter, kResidualRetag   P:386-455, R:663-741
 5  last level  kButterflyLevelOffers, bit = k-1, over pairs i in [0, T/2): split, offer(i), offer(i+T/2)   P:716-726, R:606-626, SC:672
 6  finish      kResidualDrain over [0, range_units) then the drain-only pages; (no leftover dedup:  P:460-495, R:743-768
             ResidualLeftoverDedupNeeded false); kResidualReset
```
`range_units` = `range_buckets` (`2^rho` leaves, or `W` pages in the direct plan). No tombstone drop, no
leftover dedup, no trailing drop is planned in this phase (those exist only in the top finish).
`Begin` first resets every `older_sheds_` slot (R included), the three tier views and the destination tier
(`ResetStorage`, J:1192-1226), then borrows A's tier occupancy into a private view (J:904, `BorrowTier`,
J:1468) so that A's tier is never written (`sources_unchanged` is checked in every fixture). The destination
main is not cleared; every bucket of C is written by the arrival.

---------------------------------------------------------------------------------------------------
## 4. The route (steps 1-2)

### 4.1 The merge-split of one pair `(i, j)` on bit `b` into stash `b`

`MergeSplitPairStash` (MSS:175-215; plan `PlanMergePair`, MS:117-138). `F` = bucket `i` (the lower index, the
"first"), `Sx` = bucket `j`:
```
F0 = { (l, r) in F : bit(r,b) = 0 }      F1 = F \ F0                    -- F keeps its lane NUMBERS
S0 = [ r in Sx, lane order : bit(r,b) = 0 ]      S1 = [ ... = 1 ]
a0 = min(|S0|, 64 - |F0|)      a1 = min(|S1|, 64 - |F1|)
bucket i := F0 + zip(LowestFree(F0, a0), S0[:a0])     bucket j := F1 + zip(LowestFree(F1, a1), S1[:a1])
shed     := the records of S0[a0:] and S1[a1:], in Sx LANE ORDER
test     : Count(stash b) + |shed| > 64 S  ->  FAIL
Append(stash b, shed)
```
This **is** `engineSplit` of `Basic.lean` (F0/F1 keep lanes, the second bucket's direction-d records fill the
lowest free lanes of the d-side in lane order, only the second bucket's surplus is shed, in lane order; the
first bucket never sheds) with `dir r = bit(r, b)`. The selection rule is not changed by anything in this
pass: no dedup, no blank-first (unlike `ENGINE_D2.md` P3). Failure kind of the test: **`butterfly`**
(`SubtaskKindName(kButterflySubnetwork)`, SK:314) for bits `0 .. k-2`; **`butterfly-offers`** (SK:318) for bit
`k-1` (section 6). Message: `level arena: the prepare-older phase ran out of room at <kind>; the certified
depth did not hold` (J:1883, 2167). A shed is **never** offered back at its own level; it goes to the stash
and is re-offered (stages `0..k-2`) from the pool.

### 4.2 Order of the pairs: two blocks, a recursion, quads

`PlanArriveThenRoute`/`PlanCopyThenRoute` with `route_levels = k-1` (P:649, 242) cut the arrival into
`T / 2^(k-1) = 2` independent blocks and route **block 0 completely, then block 1** (blocks `[0, T/2)` and
`[T/2, T)`; levels `0 .. k-2` only). Inside a block the order is the cache-oblivious recursion
`RouteSubnetworkRecursive(base, stride, levels)` (BF:199-236, `SplitSubnetwork` BF:191, `kButterflyLeafLevels = 4`
BF:153), executed at the whole budget exactly as the kernel does (the plan only cuts the same tree):
```
route(base, stride, levels):                       -- bits stride .. stride+levels-1 of the buckets base + (m << stride)
  if levels <= 4:                                  -- a LEAF
      lev = 0
      while lev + 1 < levels:                      -- quads: two levels at once
          h = 1 << lev;  bit = stride + lev
          for mid in 0 .. 2^levels - 1, skipping mid with mid & (h | 2h) != 0:      -- ascending
              q0..q3 = base + ((mid + t*h) << stride)  for t = 0..3
              split(q0, q1, bit); split(q2, q3, bit)           -- level `bit`:   pairs (0,1), (2,3)
              split(q0, q2, bit+1); split(q1, q3, bit+1)       -- level `bit+1`: pairs (0,2), (1,3)
          lev += 2
      while lev < levels:                          -- an odd last level: plain pairs
          h = 1 << lev;  bit = stride + lev
          for mid ascending with mid & h == 0:  split(base + (mid << stride), base + ((mid|h) << stride), bit)
          lev += 1
  else:
      low = (levels >> 1) & ~1;  high = levels - low             -- `low` is even
      for hh in 0 .. 2^high - 1:  route(base + (hh << (stride + low)), stride, low)
      for ll in 0 .. 2^low  - 1:  route(base + (ll << stride), stride + low, high)
for blk in (0, 1):  route(blk * T/2, 0, k-1)
```
The set of merge-splits and each one's input state equal the flat level-by-level order (the dependency cone of
earlier levels); **only the order in which sheds enter a level's stash differs**, and a stash's lane order is
its append order. That order is visible in the output only through the pool order of records of homes of the
same leaf (`I >= 1`, or two sheds of one home) -> the leaf lanes -> which candidates are absorbed first and the
lane order of R. The fixtures (`orderprobe`, `orderinit`, `leafmix`) make it visible: with the level-by-level
order instead of the quads 42 fixtures disagree, with an odd `low` 3, with the blocks swapped 75
(`MUTATIONS.txt`). Equivalent description for `levels <= 3`: pairs of level `b` in ascending `mid` order
(the quad on bits `(0,1)` produces, for each of the two stashes, the same sequence as the sequential order).
`levels = k-1` is 2 at `T = 8`, 3 at `T = 16`, 4 at `T = 32`, 5 at `T = 64`, ... .

### 4.3 What the route leaves behind

After step 2, every record sits in the bucket of its home restricted to bits `0..k-2` within its block: in
bucket `blk * T/2 + (home mod T/2)`, or it was shed. After the last level (section 6) it sits at
`home` (bit `k-1` of the word decides the half). Sheds are in the stage stashes in append order.

---------------------------------------------------------------------------------------------------
## 5. The pool and the range table (step 4)

```
pool_pages = [ older_sheds_[b].page[p] : b = 0 .. k-2, p = 0 .. S-1 ]  ++  [ A_tier.page[p] : p = 0 .. R_old-1 ]
```
(initialization: the tier pages are empty). Flagged tombstones are dropped (section 2); the class bit is not written.

**DFS plan (`T >= 16`)** (`kResidualDfsGather`, R:706; `kResidualDfsPartition`, R:728; `DfsResidualWorkspace::Run`):
```
pool   := [ r : page in pool_pages, lane in ascending order, r not a flagged tombstone ]     -- gather order
Leaf[l] := [ r in pool, in pool order : home(r) >> I == l ]          l = 0 .. 2^rho - 1      -- stable compaction
FAIL "residual-dfs-partition"   iff   some |Leaf[l]| > 64
range bucket l := Leaf[l] stored on ONE page, lanes 0 .. |Leaf[l]|-1
```
Every unit is a stable compaction; internal nodes at height `h` hold only records of their descendants and are
tested against `C(h) = min(P, 64 * 2^h)` (section 1). A node over capacity implies a leaf over 64 (pigeonhole), and
a leaf is tested last on its path, so **the verdict is exactly "max leaf > 64"**; which unit reports it is
irrelevant to the verdict. The count includes plain tombstones, excludes flagged ones, and does not include the
last level's stash. `P = 64 W >= 64 * 3 > 64` for `T >= 16`, so the test can fire in every DFS geometry.

**Direct plan (`T = 8`, `ml <= 3`)** (`kResidualScatter` + `kResidualRetag`; R:663-720; `ScatterResidualPoolRange`, RR:236):
range bucket `g = 0 .. W-1` := pool page `g` (same order as above), **lanes preserved**, flagged lanes removed.
No partition, no test, no failure. For bucket `b` the offer visits **all `W` range buckets in order `g = 0 .. W-1`**
(`groups = W`, a (bucket, group) unit space; the candidates of a bucket are the lanes with `home = b`).

---------------------------------------------------------------------------------------------------
## 6. The last level fused with the offers (step 5)

`kButterflyLevelOffers` (R:606-626) calls `ButterflyLevelOffersRange` (SC:672-693) over `i = 0 .. T/2 - 1` in
ascending order (the pairs are `(i, i + T/2)`, tag bit `k-1`):
```
for i in 0 .. T/2 - 1:
    split(i, i + T/2, bit k-1)  into  older_sheds_[k-1]       -- section 4.1, test Count + |shed| > 64 S  ->  FAIL "butterfly-offers"
    offer(i)                                                   -- then
    offer(i + T/2)
offer(b):                                                      -- OfferResidualGroupsToBucket, SC:567; PlanResidualOfferMerge<kNoDedup>, SC:279
    for rb in the range buckets of b:   DFS plan: [ Leaf[b >> I] ];   direct plan: [page_0, ..., page_{W-1}] in order
        cand := [ r in rb, lane order : home(r) == b ]         -- (the low I bits of the stored tag, == home(r) given the leaf)
        n    := min(|cand|, 64 - |C[b]|)
        the first n records of cand go, in order, into LowestFree(C[b], n);  they leave rb
```
Facts: (a) **no key is compared**: `kNoDedup` is exact because A, its tier and every shed are one duplicate-free union
(REPORT, `sec:binary-top-preparation`; `ButterflyLevelOffersRange` comment SC:~650-670). (b) Each candidate names
exactly one bucket, so the order of the buckets (pair order) cannot change which candidates are absorbed; it fixes only the
shed order of the last level and the failure order. (c) The offer of bucket `b` sees `C[b]` **after** its own pair's
merge-split and nothing later changes `C[b]`, so `C[b]` is final after `offer(b)`. (d) The last level's sheds are drain-only (not in the pool,
never re-offered): their target bucket was full at the shed and offers never take a full bucket below full
(SC:~650-670). (e) A candidate is absorbed only if its bucket has a free lane; absorbed lanes are the lowest free
lanes, in candidate order (holes left by the merge-splits are reused). (f) The range buckets are **not** emptied
of unabsorbed candidates: they stay for the drain.

---------------------------------------------------------------------------------------------------
## 7. The drain (step 6)

`PlanResidualFinishPhases` (P:460-495): units `[0, range_units)` are the range buckets, units past it are the pages of
the drain-only slots (here: `older_sheds_[k-1]`, pages `0 .. S-1`); there is no leftover dedup (`ResidualPassHasLeftoverDedup`
is false: the drain-only slot has rank 0, not below the swept ranks, `ResidualLeftoverDedupNeeded`, RR:666), so one drain:
```
target := R   (preparation: older_sheds_[k+3], S pages)    or    the published tier (initialization: tb_P pages, = out_tier)
for rb in range buckets, ascending (DFS: leaf 0 .. 2^rho-1; direct: page 0 .. W-1):
    L := the remaining records of rb in lane order                      -- DrainResidualTableRange, SC:1188
    if Count(target) + |L| > 64 * pages(target):  FAIL "residual-drain"
    Append(target, L)
for page in older_sheds_[k-1].page[0 .. S-1]:
    L := the records of the page in lane order                          -- DrainResidualPoolRange, SC:1216
    if Count(target) + |L| > 64 * pages(target):  FAIL "residual-drain"
    Append(target, L)
reset (kResidualReset, R:769): clears the masks of the pool slots (the stage stashes and the tier view). R is not a pool
slot of this pass; it survives.
```
The tests are made per unit on the running total (and the first test that fails ends the phase). The drain target is
empty at the start (`Begin`), so R's lanes are `0 .. n-1` of page 0, then page 1, ...; in a successful run
`|R| = E = sum_v (X_v - 64)+` exactly (section 12). The output of the preparation is C (the `T` main buckets as left by the
offers) and R. A, its tier, and nothing else are read-only.

---------------------------------------------------------------------------------------------------
## 8. Every capacity test of the pass, in execution order

| # | where | `kind` | tested quantity > threshold | can fire? |
|---|---|---|---|---|
| 1 | every merge-split on bit `b <= k-2`, in the order of section 4.2 | `butterfly` | `Count(stage stash b) + |shed|` > `64 S` | yes (`E_b > 64 S`) |
| 2 | the DFS (after the whole route, before the last level) | `residual-dfs-partition` | some leaf holds > 64 gathered records | yes for `T >= 16`; never at `T = 8` (no DFS) |
| 3 | every merge-split of the last level, `i = 0 .. T/2-1` | `butterfly-offers` | `Count(older_sheds_[k-1]) + |shed|` > `64 S` | yes (`E_k > 64 S`) |
| 4 | the drain, per range bucket then per page of the last stash | `residual-drain` | `Count(target) + |unit|` > `64 * pages(target)` | yes (`E > 64 pages`) |

* Stage stashes only grow, so test 1 and test 3 fail iff some stash's total reaches over its capacity at some append; the *kind*
  of the first failure follows the execution order (a stage overflow is reported before a DFS failure, which is reported before a
  last-level overflow, which is reported before a drain failure, even if all four would occur).
* There is no other test: no pool dedup, no leftover dedup, no tombstone drop, no merge stash. Anything else thrown
  (`logic_error`, `invalid_argument`) is a misconfiguration. With `lanes = 1` there is no fold check.
* Under the report's premises each quantity is bounded by the report's `E_b` (stage `b`) and `E` (drain): section 12.

---------------------------------------------------------------------------------------------------
## 9. Direct initialization's route (`LevelState::PublishInitialTop`, `LevelMergeJob::RouteInitialTop`)

Path: `LevelArenaEngine::Initialize(first, count)` (EN:668-) -> `LevelState::PublishInitialTop(scatter)` (LV:756-) ->
`scatter(main)`, `job_.RouteInitialTop(binding, scratch, budget)` (LV:798, J:1084-1119) -> publication.

### 9.1 The scatter rule (EN:700, INIT:86-148)

```
scatter(main):  load := PlanInitialLoad(T, per_bucket = kBucketCapacity / 2 = 32, count)      -- count <= 32 T
                ScatterInitialRecords(main, load, first, StoredKey)
bucket b receives  RecordsFor(b) = 32 if b < count/32,  count mod 32 if b == count/32,  0 otherwise
input record j (0-based, in input order)  ->  bucket  j / 32,  lane  j mod 32            (the lowest 32 lanes of the bucket)
```
`ScatterInitialRecords` zero-fills every byte of the destination region first (`memset(stage, 0, ...)` per bucket), writes the
key (`StoredKey`: the 8 user-key bytes verbatim, `EncodeStoredKey`, table/cpu_byteslice_stored_key.hpp), copies the value bytes
`value_bytes - 1` (= 7 here) and **leaves the meta byte 0**: no tombstone, no flag, no class bit. The occupancy of bucket `b` is
`LowMask64(take)` (lanes `0 .. take-1`); the buckets `>= ceil(count/32)` are empty. `count` is public; `count == 0` returns before
anything is routed; `count > Capacity() = 32 T` is refused. The scatter depends on the input position and `count` only, never on a key.
The fixtures carry the input list, the scattered main as the engine wrote it (read between scatter and route), and the
model recomputes the scattered main from the rule: equal on all 800 fixtures.

### 9.2 What differs from the preparation

| | preparation (`PrepareOlder`) | initialization (`RouteInitialTop`) |
|---|---|---|
| source | A's published main, copied | the destination itself (`binding.older_main = out`, checked; `source_in_place`) |
| arrival | `kCopyAndRetagRange` (retag + flagged tombstones dropped) | `kRetagRange` only (tags only; nothing dropped, there is no tombstone) |
| A's old tier | `R_old` pages, private view, swept | none: `older_tier = nullptr`; the pool still has the tier slot, zero-masked (J:1200-1212), so `W` is the same |
| drain target | R = `older_sheds_[k+3]`, `S` pages | the published tier = `binding.out_tier`, `tb_P` pages (`Capacity() = 64 tb_P`) |
| family | caller's ordinal | `binding.ordinal = D` (`LV:790`): nonce = `FamilyNonce(CanonicalFamily(geometry, top, D))` |
| stage 1 (bit 0) | can shed | **cannot shed**: at most 32 + 32 records per pair (checked on every fixture, section 12) |
| failure | `PrepareOlder` throws; nothing published | the same exception escapes `Initialize` (message `... prepare-older phase ran out of room at <kind> ...`); `PublishInitialTop` cancels the lease and leaves the engine pristine |
| after the route | `InstallCarry`, `FinishMerge` | publication of `C` + tier and seeding of the counters (not part of this semantics) |

Everything else (the route of section 4, the pool, the DFS, the fused last level, the drain order, all four capacity tests)
is the **same code with the same parameters**. `S` is the same (`older_sheds_` depth), the stage stashes are the same slots.

### 9.3 How the fixtures drive it

`--mode init` of `fdtp` calls `PlanInitialLoad` + `ScatterInitialRecords` (with the engine's lambda: 32 per bucket, identity stored key)
over the leased destination bank and then `LevelMergeJob::RouteInitialTop` with the binding `PublishInitialTop` builds (same fields).
`fdtp_engine` calls the **public** `LevelArenaEngine::Initialize` (inline executor, `kSettle`, secret seed fixed so the fixture knows the tag
keys), finds the top in `publisher().LiveTables()` (`owner == top`, `main_buckets == T`) and reads its main and its tier
lane by lane. Both modes agree with the same model.

---------------------------------------------------------------------------------------------------
## 10. Tombstones and the class bit: every path

| source | plain tombstone | flagged tombstone (0x20) |
|---|---|---|
| A main | copied, routed like a record, ends in C or R (counts in every capacity test) | removed at the copy (RM:914-919); never routed; never in C or R |
| A tier | in the pool, gathered, offered, ends in C or R | removed at the gather (not counted by the DFS leaf test) |
| stage stash (shed) | gathered like any record | cannot occur (dropped at the copy) |
| last-level stash | drained into R / the tier like any record | cannot occur |
| initialization input | cannot occur (meta byte 0) | cannot occur |

So C and R may contain plain tombstones and never a flagged one (except fixtures that inject them; none here). Because flagged
tombstones are removed before the route, `X_v` (the report's population) counts the surviving records, plain tombstones included.
The class bit `0x40` is never written by this pass.

---------------------------------------------------------------------------------------------------
## 11. Agreement with and difference from the d = 2 ordinary merge (`ENGINE_D2.md`, `Job.lean`)

| item | d = 2 ordinary merge | top preparation / initialization |
|---|---|---|
| A's source buckets | A copied into `[U, 2U)`; `[0, U)` publicly blank (B's region) | A fills **all `T`** buckets (offset 0); no blank half, no `blank_first` continuation (D2 P3 has no counterpart) |
| butterfly levels | bits `0 .. K-1` inside `[U, 2U)` (one 3-level leaf at the fixture size), then the continuation `kRouteLevelRange` on bit `K` (blank first, no shed) | bits `0 .. k-2` inside **two** half-blocks of `T/2`, then the fused last level on bit `k-1` over pairs `(i, i+T/2)`; the last level is a real merge-split that sheds |
| pair rule | `MergeSplit`/`PlanMergePair` (`engineSplit`) | **the same primitive** and `engineSplit` rule; the same stash test `Count + |shed| > 64 S` |
| order of pairs | sequential per bit (D2 P2) at 3 levels | recursion of section 4.2 (quads); equals the sequential order up to 3 levels per block (`T <= 16`), differs beyond |
| stash per bit | `stash[j]`, `S_A` pages | `older_sheds_[b]`, `S` pages; the last level's (bit `k-1`) is the drain-only slot |
| dedup | none in the route; F1 pool dedup of the B tier against A pool | **none anywhere** (`kNoDedup`, equal ranks, no B) |
| pool | `stash[0..3]` (incl. the continuation bit's, always empty) + A tier, minus B-tier keys | sheds of bits `0 .. k-2` (bit order) + A tier; the last level's stash is excluded |
| DFS | pages 1, `P = 5 * 64`, range plan from `(5, 4)`, B tier offered directly | pages 1, `P = 64 W`, range plan from `(W, k)`, no direct slot; direct plan at `T = 8` |
| DFS test | node capacities `min(P, 64 2^h)`; fails iff max leaf > 64 | the same |
| offers | `kTableWins` set 0 (A leaf) then `kResidualWins` set 1 (B tier), after B's insertion | one set, `kNoDedup`, fused to the last level, right after each pair's merge-split; candidates absorbed in lowest free lanes, in leaf order |
| `fill` | lowest free lanes, in order | the same |
| drain | A leaves (range order), B-tier leftovers, leftover dedup, insertion stash | range leftovers (leaf/page order), then the last level's stash pages; **no** leftover dedup; target R (`S` pages) or the published tier |
| tombstones | none dropped | flagged ones dropped at the copy/gather; plain ones are records |
| capacity tests | route, dfs, insertion, drain | stages, dfs, last-level stash (`butterfly-offers`), drain |
| A tier | in the pool | in the pool |
| output | main + output tier | C + R (preparation; the finish then resolves R), or main + published tier |

The Lean model `TopPrep.lean` shares with `Job.lean` the split rule (`CapRule`), `fill`, `appendFill`, `occupied` and the
shape of the test trace (stages, dfs, offers, drain), and routes the two half-blocks with the butterfly recursion `routeRec`
(`Sep.lean`). It adds its own one-page DFS leaves (`tpLeaves`), a pool without the last level's stash, the fused last level
(`split; offer i; offer i+T/2`, `tpLastStep`) and the `drop flagged` at the copy and gather; it has no `offerB` and no dedup.

---------------------------------------------------------------------------------------------------
## 12. REPORT cross-check (`sec:binary-top-preparation`, `sec:top-final-ranges`, `sec:top-dfs-decision`, `cor:top-dfs-transfer`)

Method (`report_check_tp.py`, `REPORT_CHECK.txt`): from the INPUT only, `X_v` = surviving records homed at `v`, `E = sum (X_v - 64)+`,
`E_b = sum_v (X_{b,v} - 64)+` with `V_b(x) = 2^b floor(O_x / 2^b) + (H_x mod 2^b)` (`O_x` = the old bucket / the scattered bucket); compared
with the engine's output on every fixture.

Agreement (all checked on all fixtures):
1. **Stage structure.** `k` stage stashes of `S` pages each, stages `1 .. k-1` (bits `0 .. k-2`) in the swept pool together with the old tier,
   stage `k` (bit `k-1`) drain-only; the retained carry R has `S` pages (`r_pages == S` in 1062/1062 successful preparations); the
   published tier has `64 tb_P` slots. The pool's source buckets are `(k-1) S + R_old` (REPORT's "44 source buckets" at `T = 2^22`, `S = 2`, `R_old = 2`: `21*2+2`).
2. **Raw stage arrivals.** Every successful stage stash holds at most `E_b` records (1062/1062 preparations, 478/478 initializations).
3. **A-only packing witness.** In every successful run `|R|` (resp. the published tier) `= E` exactly and every leftover names a full home;
   `main` holds `min(X_v, 64)` at every home; the output multiset is the input minus flagged tombstones. A failure `butterfly` implies some `E_b > 64 S`
   (b < k), `butterfly-offers` implies `E_k > 64 S`, `residual-drain` implies `E > 64 * pages(target)` (every failing fixture satisfies it).
4. **kNoDedup, no early dedup, drain order** (range leftovers first, then the drain-only stash) and "no temporary second drain capacity": as stated.
5. **Initialization**: the first stage never sheds (bit 0 stash empty on every initialization fixture); scatter of at most 32 per bucket in input order.
6. **DFS (Corollary `cor:top-dfs-transfer`)**: node capacities `C(h) = min(P, 64 2^h)` with `P` the pool slot capacity; the verdict is exactly "max leaf > 64";
   the leaf count is that of the swept pool only (the last stage's stash is not counted).

Disagreements and remarks (none changes a certificate, but the Lean model must state them):
* **D1 (REPORT `sec:top-dfs-decision`: "The preparation builder always uses the existing DFS distributor")**: at `T = 8` (the minimal top: `B=2, L=2, D=1, r0=2, s=1`, `ml = 3 <= kResidualDirectMaxLevels`) the engine uses the
  **direct** plan: no DFS, no range event, every bucket is offered all `W` range buckets in order. The corollary's premise "coarse partition" does not apply there; the direct plan has no first-failure range term. 44 fixtures.
* **D2 (REPORT premise "tombstone-free A")**: the engine does not need it. Plain tombstones are records everywhere (they occupy lanes, count in `X_v`, in every capacity test, in `Y_r`, and appear in C and R: 178 fixtures); flagged ones are dropped before routing (copy for main, gather for the tier: 114 fixtures with drops).
  So the report's `X_v` equals the engine's count only if "tombstone" is read as "flagged tombstone".
* **D3 (REPORT `P_0 = IS` for initialization)**: as a population cap it is right (the old tier holds nothing), but the engine's public pool shape for an initialization still contains the old-tier slot (`R_old` empty pages), so the swept
  pool, the coarse width `rho`, the node capacities `C(h)` and the DFS price are those of a preparation (`P = 64((k-1)S + R_old)`); the certificate's `P` (as a slot capacity) is larger than `IS * 64` by `R_old * 64`.
* **D4 (naming)**: the last stage's overflow is reported as `butterfly-offers` and the earlier stages' as `butterfly`; both are the report's "stage stash" events; the DFS failure is `residual-dfs-partition` and a drain failure is `residual-drain` for both the retained carry and the published tier.
* **D5 (what the engine does not check)**: the report's premises (A of at most `32 T` keys, uniform old homes, independence of the families) are not checked; the fixtures violate them on purpose (hot homes, packed old buckets, off-contract placements: `--a-spread`), which is why every failure kind fires.
* **D6 (order dependence)**: the report's pointwise bounds (E_b, E, Y_r) do not depend on the shed order; the **lanes** of C and R do (section 4.2). The report does not constrain lanes.

In outline, the top preparation is the d = 2 job's route with A filling all T buckets, no B, a one-page DFS of the pool (A tier + sheds of every level but the last), offers into main fused with the last level, and a drain of range leftovers then the last level's drain-only stash into R. More precisely:
(i) the route is two independent half-block networks plus the fused last level, in the recursion/quad order of section 4.2, not a stage-by-stage sweep over `T` buckets;
(ii) at `T = 8` there is no DFS (direct plan); (iii) flagged tombstones are dropped at the copy and the gather (A is not copied verbatim); (iv) in an initialization the pool still has the (empty) old-tier slot;
(v) there is no leftover dedup and no pool dedup at all (the d = 2 merge has both); (vi) the DFS pool is gathered **in bit order of the stashes, then the tier**.

---------------------------------------------------------------------------------------------------
## 13. Input contracts the engine relies on without checking

1. A (main and tier) is key-distinct (`kNoDedup`; `ResidualPoolEqualRanksDisjoint` is asserted only in checked builds, R:~680). For an initialization `kDistinct` is the caller's promise.
2. A's main bucket `h_old` holds records of the previous family's home `h_old` (the preparation never reads it; the fixtures use it for
   the main placement, and for `--a-spread` (explicit old buckets) they depart from it, which is legal input for the engine).
3. Every bucket, page and tier holds at most 64 records; occupancy words are honest (dummy lanes carry arbitrary key bytes in the fixtures).
4. A flagged tombstone's promise (section 2) is not used by this pass.
5. `count <= 32 T` (initialization; checked: `Initialize` throws). `S, R_old, tb_P <= 8`.
6. The nonce family of the output is the job's (`Validate`, J).
7. Nothing in this pass reads B, the inbox, or the old family.

---------------------------------------------------------------------------------------------------
## 14. Validation record

* **Fixtures**: 1599 preparation (of 1600 attempts: one scenario with more records than `T * 64` is refused by the dumper), 800 initialization (job level),
  120 initialization (public engine). All 2519: model == engine (`RESULTS.txt`). Preparation: 1062 successes lane-exact on `C` and `R`, 537 failures with the same kind;
  initialization: 478 successes lane-exact on the scattered main, `C` and the published tier, 322 failures with the same kind; public engine: 79 + 41.
  Failure kinds: preparation `butterfly` 124, `butterfly-offers` 159, `residual-dfs-partition` 157, `residual-drain` 97; initialization 174 / 9 / 124 / 15; public engine 26 / 5 / 4 / 6.
* **Geometries**: `T` 8..4096, `D` 1/2/4/8, `S` 1/2, tier 1/2/4/8, 58 distinct `(T, D, rho, I)` range plans (17 distinct `(T, rho, I)`) including the direct plan; every plan field and the DFS workspace
  (`dfs_direct_height`, `dfs_capacities`, `dfs_units`) agree with the formulas of section 1 on every fixture.
* **Coverage** (preparations with a nonzero effect, of 1599): sheds at every bit 0..11 (stage stash on page 1: 123; last-level stash on page 1: 75), DFS gathered 961, leaves with records of several homes 309, a leaf of 62 or more records: 54,
  offers absorbed 695, offers blocked by a full bucket 576, absorbed into a non-empty bucket 477, range leftovers 506, last-level drain 243, R on page 1: 132, A tier used 715, plain tombstones in A 221, flagged drops at the copy 151 and at the gather 126.
* **Mutation check of the model** (`mutate_tp.py`; fixtures failing when one rule is altered): shed order reversed 677, quads replaced by the level-by-level order 42, odd `low` in the recursion 3, blocks routed in the other order 75, pool tier-first 47,
  pool sheds in reverse bit order 247, no flagged drop at the gather 100, DFS cap 65 15, offer order reversed 581, drain cap -1 23, drain-only stash before the range leftovers 151, no flagged drop at the copy 114, stage stash cap -1 18.
* **Engine asserts on**: all 2519 outputs byte-identical to the `-DNDEBUG` build; no assert fired.
* **Not verified**: `lanes > 1` (private range masks), pauses/resumes and helper threads (the plan is cut at the same recursion frontier; the engine's own tests claim byte-identity), `T > 4096`, `I > 18`, `S >= 3`, a
  per-level tier profile other than the shared width (the automatic profile of the public-engine fixtures gives 1 page), the publication and counter seeding that follow an initialization.
