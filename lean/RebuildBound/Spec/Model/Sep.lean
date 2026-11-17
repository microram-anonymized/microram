import RebuildBound.Spec.Model.Job

/-!
# The separated-sources ordinary merge at a general digit (trusted model)

The reference construction of `REPORT.tex` (sections `sec:dfs-theorem` and
`sec:separated-residuals`, Propositions `prop:separated-capacity` and
"Completed-A coarse-range bound") at a digit `d = r 2^e`, with the engine's
evaluation choices. The record-level semantics are
`Spec/Model/ENGINE_RADIX.md`, extracted from the engine and checked
lane-exactly against it at every digit 2–8; its Python transcription is
`oracle/fixtures-radix/model3.py`. The d = 2 model `Job.lean` is a separate
module; reused from it: `Rec`, `Bucket`,
`fill`, `appendFill`, `occupied`, `CapRule` (the binary merge-split's
selection rule, a parameter), `dirBit` and `Output`.

**Geometry** (`SepGeom`, the configuration probe's row): `U = 2^K` carry
buckets; `k = K + e` block bits; `N = d U = r 2^k` homes in `r` blocks of
`2^k`; one-page DFS leaves over `2^rangeBits` coarse ranges of `2^I` homes
each (the leaves past `N` are padding); stashes of `stashPages` pages, A's
tier of `aTierPages`, B's of `bTierPages` and the output tier of `tierPages`.

**Words.** The merge family's raw word of key `x` is `w x`. Binary stage `j`
reads bit `j < k`; the radix class is `q = ⌊w / 2^k⌋ mod r`; the home is
`H = (w mod 2^k) + 2^k q`; B's way is `(⌊w / 2^K⌋ mod 2^e) + 2^e q`, so that
`H = (w mod U) + U · way`. At `r = 1` the class is 0 and `H = w mod 2^k`.

**Phases**, each a pure function of the previous state:

1. **A's binary route** (`runSOps`). A's main is embedded at `[U, dU)` and
   `[0, U)` is blank (empty buckets). A schedule is a list of pair operations
   `(j, i)`: merge-split the pair `(i, i + 2^j)` by bit `j` with the selection
   rule, and append the second bucket's surplus to the one stash of bit `j`,
   which every writer of that bit shares. The engine's schedule
   (`engineOps`) is: the pure blocks `q = 1 … r - 1` (`routeRec`, the
   engine's butterfly recursion), then block 0's spans largest first, then
   the continuations on bits `K … k - 1` over block 0. The first continuation
   (bit `K`) has a blank first bucket and cannot shed. `canonicalOps` is the
   same set of operations stage by stage, with the operations inside the
   blank region omitted.
2. **Terminal radix** (`radixPass`, only when `r > 1`). For each tuple `p`
   ascending, the `r` buckets `a 2^k + p` are split by class (`radixSplit`):
   output `a` keeps input `a`'s class-`a` records in their lanes and takes
   the other inputs' class-`a` records, lower input first, into its lowest
   free lanes; each input's surplus is shed in its lane order, input by input,
   into the radix stash.
3. **Pool** (`sPool`). The stage stashes in bit order, the radix stash, then
   A's old tier, minus every record whose key is in B's tier.
4. **DFS** (`sLeaves`, `sDfsTrace`). Leaf `v` holds the pool records with
   `⌊H / 2^I⌋ = v`, in pool order. Every node of the padded tree is
   capacity-tested, depth by depth. As in `Job.lean`, this part of the trace
   is abstract, not the engine's preorder of units below its direct height.
   It has the engine's verdict when the pool fits its `poolPages` (A's tier
   fits and the stash tests passed), and only the failing node can differ.
5. **Insertion and offers** (`sFinish`). For each B bucket `i`: remove the A
   copies of B's keys from all `d` destinations `i + wU`; then for each way
   `w` ascending, at `ci = i + wU`: B's records of that way fill the lowest
   free lanes, the surplus (B's highest lanes) is this way's shed; after the
   last way the bucket's sheds (way order) go to the insertion stash, which is
   then tested; after each way's insertion its home receives A's leaf
   candidates (`sOfferA`) and then, one round per B-tier page, B's tier
   candidates (`sOfferB`).
6. **Drain** (`sDrain`). A's leaf leftovers (range order), then each B-tier
   page's leftovers, go to the output tier; A-class tier records whose key
   was shed by B's insertion are removed; the insertion stash (minus keys of
   B-class tier records) is appended.

**Capacity tests.** As in `Job.lean`: no test changes the state, so the
model is the reference execution with every test recorded in a trace in
execution order (the DFS part excepted, see phase 4), and the bounded job
(`sJob`) fails at the first trace entry above its capacity
(`SepGeom.capOf`); otherwise it publishes the reference output. A stage-stash test records whether its writer is a continuation
(`route-level` in the engine) or a block or span (`butterfly`).
-/

namespace RebuildBound.Model

/-- Public geometry of one separated-sources ordinary merge at digit
`d = r 2^e`: the fields of the configuration probe's row. Capacities are in
pages of `C` slots. -/
structure SepGeom where
  /-- Bucket capacity (slots per home and per page). -/
  C : Nat
  /-- `U = 2^K` carry buckets (`carry_bits`). -/
  K : Nat
  /-- The digit's power of two, `d = r 2^e`. -/
  e : Nat
  /-- The digit's odd part, the radix (`radix`). -/
  r : Nat
  /-- `2^rangeBits` coarse ranges (DFS leaves, `range_bits`). -/
  rangeBits : Nat
  /-- `2^I` homes per coarse range (`index_bits`). -/
  I : Nat
  /-- Pages of each stage stash, of the radix stash and of the insertion
  stash (`stash_buckets`). -/
  stashPages : Nat
  /-- Pages of A's old tier (`older_tier_buckets`). -/
  aTierPages : Nat
  /-- Pages of B's tier (`carry_tier_buckets`), one offer round each. -/
  bTierPages : Nat
  /-- Pages of the output tier (`tier_buckets`). -/
  tierPages : Nat
  deriving Repr, DecidableEq

namespace SepGeom

/-- Carry buckets `U = 2^K`. -/
def U (g : SepGeom) : Nat := 2 ^ g.K

/-- The digit `d = r 2^e`. -/
def d (g : SepGeom) : Nat := g.r * 2 ^ g.e

/-- Block bits `k = K + e` (the report's `b`): the binary stages. -/
def k (g : SepGeom) : Nat := g.K + g.e

/-- Buckets per block, `2^k`. -/
def blk (g : SepGeom) : Nat := 2 ^ g.k

/-- Homes `N = d U = r 2^k`. -/
def N (g : SepGeom) : Nat := g.r * 2 ^ g.k

/-- Coarse ranges `2^rangeBits`. -/
def ranges (g : SepGeom) : Nat := 2 ^ g.rangeBits

/-- Pages of the swept A pool: the stage stashes, the radix stash when
`r > 1`, and A's tier (the probe's `pool_buckets` minus the direct B tier). -/
def poolPages (g : SepGeom) : Nat :=
  (g.k + if 1 < g.r then 1 else 0) * g.stashPages + g.aTierPages

/-- The domain of the model: a digit above one and a range plan that covers
every home. -/
def Valid (g : SepGeom) : Prop :=
  1 ≤ g.r ∧ 2 ≤ g.d ∧ g.N ≤ 2 ^ (g.I + g.rangeBits)

instance (g : SepGeom) : Decidable g.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The radix class `⌊t / 2^k⌋ mod r` of a raw word `t`. -/
def cls (g : SepGeom) (t : Nat) : Nat := t / 2 ^ g.k % g.r

/-- The home `(t mod 2^k) + 2^k · class` of a raw word `t`. -/
def homeOf (g : SepGeom) (t : Nat) : Nat := t % 2 ^ g.k + 2 ^ g.k * g.cls t

/-- B's way `(⌊t / 2^K⌋ mod 2^e) + 2^e · class` of a raw word `t`. -/
def wayOf (g : SepGeom) (t : Nat) : Nat := t / 2 ^ g.K % 2 ^ g.e + 2 ^ g.e * g.cls t

end SepGeom

/-! ### Tests and the route state -/

/-- The capacity tests of the job, in the order the model performs them. -/
inductive STest where
  /-- The shared stash of bit `bit`, after one merge-split; `cont` when the
  writer is a continuation (`route-level`), else a block or span
  (`butterfly`). -/
  | stash (bit : Nat) (cont : Bool)
  /-- The radix stash, after one tuple's radix split. -/
  | radix
  /-- DFS node `pre` at depth `depth` (it covers the ranges whose top `depth`
  bits are `pre`). -/
  | dfs (depth pre : Nat)
  /-- The insertion stash, after one B bucket's insertion. -/
  | insertion
  /-- The output tier, after one append. -/
  | drain
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The capacity of a test, in records: `C_h = min(P_pool, C 2^h)` for a DFS
node of height `h` (one-page leaves, `eq:dfs-capacity`). -/
def SepGeom.capOf (g : SepGeom) : STest → Nat
  | .stash _ _ => g.stashPages * g.C
  | .radix => g.stashPages * g.C
  | .dfs dd _ => min (g.poolPages * g.C) (g.C * 2 ^ (g.rangeBits - dd))
  | .insertion => g.stashPages * g.C
  | .drain => g.tierPages * g.C

/-- The job's inputs. Main buckets have `C` lanes: A's main has `(d - 1) U`
buckets (A's old layout), B's main bucket `i` holds B's records with carry
bucket `i`. A's tier is listed in (page, lane) order; B's tier is a list of
pages, each in lane order. -/
structure SInputs where
  aMain : List Bucket
  aTier : List Rec
  bMain : List Bucket
  bTier : List (List Rec)

/-- The state of A's route: `N` buckets, one stash per bit (append order), the
radix stash (append order), and the capacity trace so far. -/
structure SRoute where
  main : List Bucket
  stash : List (List Rec)
  radix : List Rec
  trace : List (STest × Nat)

/-! ### Phase 1: A's binary route -/

/-- The merge-split of the pair `(i, i + 2^j)` by bit `j`. -/
def sPairStep (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (j i : Nat) (st : SRoute) :
    SRoute :=
  let p := rule.split g.C (dirBit w j) (st.main.getD i []) (st.main.getD (i + 2 ^ j) [])
  let sj := st.stash.getD j [] ++ p.2.2
  { st with
    main := (st.main.set i p.1).set (i + 2 ^ j) p.2.1
    stash := st.stash.set j sj
    trace := st.trace ++ [(.stash j (decide (i < 2 ^ j)), sj.length)] }

/-- Run a list of pair operations `(j, i)`. -/
def runSOps (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (ops : List (Nat × Nat))
    (st : SRoute) : SRoute :=
  ops.foldl (fun st o => sPairStep rule g w o.1 o.2 st) st

/-- The quads of a butterfly leaf at level `lev`: for each `mid < 2^L` whose
bits `lev, lev + 1` are clear, at `i = base + mid 2^s` and bit `b = s + lev`,
the pairs `(i, i + 2^b)` and `(i + 2·2^b, i + 3·2^b)` on bit `b`, then
`(i, i + 2·2^b)` and `(i + 2^b, i + 3·2^b)` on bit `b + 1`. -/
def quadOps (base s L lev : Nat) : List (Nat × Nat) :=
  ((List.range (2 ^ L)).filter fun mid => mid / 2 ^ lev % 4 == 0).flatMap fun mid =>
    let i := base + mid * 2 ^ s
    let b := s + lev
    [(b, i), (b, i + 2 * 2 ^ b), (b + 1, i), (b + 1, i + 2 ^ b)]

/-- The pairs of a butterfly leaf's odd last level `lev`. -/
def pairOps (base s L lev : Nat) : List (Nat × Nat) :=
  ((List.range (2 ^ L)).filter fun mid => mid / 2 ^ lev % 2 == 0).map fun mid =>
    (s + lev, base + mid * 2 ^ s)

/-- A butterfly leaf of `L ≤ 4` levels: fused quads, then an odd last level
as pairs. -/
def leafOps (base s : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | 1 => pairOps base s 1 0
  | 2 => quadOps base s 2 0
  | 3 => quadOps base s 3 0 ++ pairOps base s 3 2
  | 4 => quadOps base s 4 0 ++ quadOps base s 4 2
  | _ => []

/-- `RouteSubnetworkRecursive(base, s, L)` with fuel: it routes bits
`[s, s + L)` over the buckets `base + j 2^s`, `j < 2^L`. A route of more than
four levels is split into `low = ⌊L/2⌋` rounded down to even levels and
`high = L - low`: first the `2^high` low sub-routes, then the `2^low` high
ones. -/
def routeRecAux : Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _ => []
  | fuel + 1, base, s, L =>
    if L ≤ 4 then leafOps base s L
    else
      let low := L / 2 - L / 2 % 2
      let high := L - low
      (List.range (2 ^ high)).flatMap (fun h => routeRecAux fuel (base + h * 2 ^ (s + low)) s low) ++
        (List.range (2 ^ low)).flatMap (fun l => routeRecAux fuel (base + l * 2 ^ s) (s + low) high)

/-- The engine's butterfly over bits `[s, s + L)` of the buckets
`base + j 2^s`. -/
def routeRec (base s L : Nat) : List (Nat × Nat) := routeRecAux L base s L

/-- The engine's schedule of A's binary route: the pure blocks `q = 1 … r - 1`
(all `k` bits), block 0's spans `[2^(K+u), 2^(K+u+1))` for `u = e - 1 … 0`
(bits `< K + u`), then the continuations on bits `K … k - 1`, each over the
pairs `(i, i + 2^b)`, `i < 2^b`. -/
def engineOps (g : SepGeom) : List (Nat × Nat) :=
  (List.range (g.r - 1)).flatMap (fun q => routeRec ((q + 1) * g.blk) 0 g.k) ++
    (List.range g.e).reverse.flatMap (fun u => routeRec (2 ^ (g.K + u)) 0 (g.K + u)) ++
    (List.range g.e).flatMap (fun v => (List.range (2 ^ (g.K + v))).map fun i => (g.K + v, i))

/-- The model's stage-by-stage schedule: for each bit `j < k`, every pair
`(i, i + 2^j)` with bit `j` of `i` clear, in ascending `i`, except the pairs
inside the blank region `[0, U)`. -/
def SepGeom.canonicalOps (g : SepGeom) : List (Nat × Nat) :=
  (List.range g.k).flatMap fun j =>
    ((List.range g.N).filter fun i => !i.testBit j && decide (g.U ≤ i + 2 ^ j)).map fun i => (j, i)

/-! ### Phase 2: the terminal radix -/

/-- Walk `S` in lane order, keeping the first `n c` records of each class `c`.
Returns the kept and the shed records, both in lane order. -/
def pickClass (cls : Rec → Nat) (n : Nat → Nat) : List Rec → List Rec × List Rec
  | [] => ([], [])
  | x :: S =>
    if n (cls x) = 0 then
      let p := pickClass cls n S
      (p.1, x :: p.2)
    else
      let p := pickClass cls (fun c => if c = cls x then n c - 1 else n c) S
      (x :: p.1, p.2)

/-- Output `a` of the radix split of the inputs `X`: input `a`'s class-`a`
records keep their lanes; then the class-`a` records of every other input,
lower input first and each in lane order, fill the lowest free lanes. Returns
the bucket and the number of records each input placed. -/
def radixOutput (cls : Rec → Nat) (X : List Bucket) (a : Nat) : Bucket × List Nat :=
  (List.range X.length).foldl
    (fun acc i =>
      if i = a then (acc.1, acc.2 ++ [0])
      else
        let cand := (X.getD i []).recs.filter fun x => cls x == a
        let f := fill acc.1 cand
        (f.1, acc.2 ++ [cand.length - f.2.length]))
    ((X.getD a []).map (fun s => s.filter fun x => cls x == a), [])

/-- The radix split of one tuple: the outputs (one per class) and the shed
records, input by input, each input's in lane order. Input `i` keeps its
class-`i` records and sheds, in each other class, the records the output of
that class did not place (its highest lanes of the class). -/
def radixSplit (cls : Rec → Nat) (X : List Bucket) : List Bucket × List Rec :=
  let outs := (List.range X.length).map (radixOutput cls X)
  let shed := (List.range X.length).flatMap fun i =>
    (pickClass cls
      (fun a => if a = i then (X.getD i []).length else ((outs.getD a ([], [])).2.getD i 0))
      (X.getD i []).recs).2
  (outs.map Prod.fst, shed)

/-- The radix split of tuple `p`: the buckets `a 2^k + p`, `a < r`. -/
def radixStep (g : SepGeom) (w : LogicalKey → Nat) (p : Nat) (st : SRoute) : SRoute :=
  let idx := (List.range g.r).map fun a => a * g.blk + p
  let s := radixSplit (fun x => g.cls (w x.key)) (idx.map fun j => st.main.getD j [])
  let rad := st.radix ++ s.2
  { st with
    main := (idx.zip s.1).foldl (fun m q => m.set q.1 q.2) st.main
    radix := rad
    trace := st.trace ++ [(.radix, rad.length)] }

/-- The terminal radix pass: every tuple `p < 2^k` in ascending order, when
`r > 1`. -/
def radixPass (g : SepGeom) (w : LogicalKey → Nat) (st : SRoute) : SRoute :=
  if 1 < g.r then (List.range g.blk).foldl (fun st p => radixStep g w p st) st else st

/-- The route's initial state: `[0, U)` blank, A's main at `[U, dU)`. -/
def sRouteInit (g : SepGeom) (aMain : List Bucket) : SRoute :=
  { main := List.replicate g.U (Bucket.empty g.C) ++ aMain
    stash := List.replicate g.k []
    radix := []
    trace := [] }

/-- A's complete route under a schedule of its binary pair operations: the
binary route, then the terminal radix. -/
def sRouteWith (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (aMain : List Bucket)
    (ops : List (Nat × Nat)) : SRoute :=
  radixPass g w (runSOps rule g w ops (sRouteInit g aMain))

/-- The binary route's state after the first `n` stages of the stage-by-stage
schedule (they read bits `0, …, n - 1`). -/
def sRouteUpTo (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (aMain : List Bucket) (n : Nat) :
    SRoute :=
  runSOps rule g w (g.canonicalOps.filter fun o => o.1 < n) (sRouteInit g aMain)

/-! ### Phases 3 and 4: the swept A pool and its DFS -/

/-- The home of a record under the merge family's words `w`. -/
def sHome (g : SepGeom) (w : LogicalKey → Nat) (x : Rec) : Nat := g.homeOf (w x.key)

/-- The coarse range of a record: `⌊H / 2^I⌋`. -/
def sRange (g : SepGeom) (w : LogicalKey → Nat) (x : Rec) : Nat := sHome g w x / 2 ^ g.I

/-- The swept A pool: the stage stashes in bit order, the radix stash, then
A's old tier, minus every record whose key is in B's tier (B is fresher). -/
def sPool (st : SRoute) (aTier : List Rec) (bTier : List (List Rec)) : List Rec :=
  (st.stash.flatten ++ st.radix ++ aTier).filter fun x =>
    !(bTier.flatten.map Rec.key).contains x.key

/-- DFS leaf `v`: the pool records of coarse range `v`, in pool order. -/
def sLeaves (g : SepGeom) (w : LogicalKey → Nat) (pool : List Rec) : List (List Rec) :=
  (List.range g.ranges).map fun v => pool.filter fun x => sRange g w x == v

/-- The DFS capacity tests: every node of the padded tree, depth by depth (an
abstract order with the engine's verdict, as `dfsTrace`). -/
def sDfsTrace (g : SepGeom) (w : LogicalKey → Nat) (pool : List Rec) : List (STest × Nat) :=
  (List.range (g.rangeBits + 1)).flatMap fun dd =>
    (List.range (2 ^ dd)).map fun c =>
      (.dfs dd c, (pool.filter fun x => sRange g w x / 2 ^ (g.rangeBits - dd) == c).length)

/-! ### Phase 5: B's insertion with the fused offers -/

/-- The finish state: main buckets, the insertion stash (append order), the
remaining A leaf candidates, the remaining B tier candidates (pages, each in
lane order), and the capacity trace of this phase. -/
structure SFin where
  main : List Bucket
  ins : List Rec
  leaves : List (List Rec)
  bcopy : List (List Rec)
  trace : List (STest × Nat)

/-- Offer A's leaf candidates for home `ci`. A candidate whose key is already in
main (B's copy) is consumed; the others fill the lowest free lanes in leaf
order, and those placed are consumed. -/
def sOfferA (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) : SFin :=
  let R := ci / 2 ^ g.I
  let leaf := st.leaves.getD R []
  let B := st.main.getD ci []
  let cand := leaf.filter fun x => sHome g w x == ci
  let drop := cand.filter fun x => B.keys.contains x.key
  let stale := cand.filter fun x => !B.keys.contains x.key
  let f := fill B stale
  let gone := (drop ++ stale.take (stale.length - f.2.length)).map Rec.key
  { st with
    main := st.main.set ci f.1
    leaves := st.leaves.set R (leaf.filter fun x => !gone.contains x.key) }

/-- One offer round of B-tier page `pg` to home `ci` (full-home match, lane
order). Each candidate first frees the lane of a main copy of its key (an A
main record); then the candidates fill the lowest free lanes, and those placed
are consumed. -/
def sOfferPage (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat) : SFin :=
  let page := st.bcopy.getD pg []
  let fc := page.filter fun x => sHome g w x == ci
  let B := (st.main.getD ci []).clear fun key => (fc.map Rec.key).contains key
  let f := fill B fc
  let placed := (fc.take (fc.length - f.2.length)).map Rec.key
  { st with
    main := st.main.set ci f.1
    bcopy := st.bcopy.set pg (page.filter fun x => !placed.contains x.key) }

/-- B's tier offers to home `ci`: one round per page, in page order. -/
def sOfferB (g : SepGeom) (w : LogicalKey → Nat) (ci : Nat) (st : SFin) : SFin :=
  (List.range st.bcopy.length).foldl (sOfferPage g w ci) st

/-- Insert B's main bucket `i` into its `d` destinations `i + qU`: first remove
the A copies of B's keys from all of them; then for each way `q` ascending,
insert B's records of that way, and after the last way append the sheds (way
order) to the insertion stash and test it; each destination receives its
offers right after its insertion. -/
def sInsertBucket (g : SepGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : SFin) :
    SFin :=
  let Bi := bMain.getD i []
  let bk := Bi.keys
  let st := { st with
    main := (List.range g.d).foldl
      (fun m q => m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key => bk.contains key))
      st.main }
  let res := (List.range g.d).foldl
    (fun (acc : SFin × List Rec) q =>
      let ci := i + q * g.U
      let f := fill (acc.1.main.getD ci []) (Bi.recs.filter fun x => g.wayOf (w x.key) == q)
      let sheds := acc.2 ++ f.2
      let st := { acc.1 with main := acc.1.main.set ci f.1 }
      let st := if q + 1 = g.d then
          let ins := st.ins ++ sheds
          { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
        else st
      (sOfferB g w ci (sOfferA g w ci st), sheds))
    (st, [])
  res.1

/-- B's insertion over all `U` carry buckets, in ascending order. B's tier is
read through its direct copy, page by page. -/
def sFinish (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) (routed : List Bucket)
    (leaves : List (List Rec)) : SFin :=
  (List.range g.U).foldl (fun st i => sInsertBucket g w inp.bMain i st)
    { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }

/-! ### Phase 6: the coordinated drain -/

/-- Append one list of leftovers (tagged `true` for A's class) to the output
tier and record the tier's occupancy. -/
def sDrainStep (acc : List (Option (Rec × Bool)) × List (STest × Nat)) (L : List (Rec × Bool)) :
    List (Option (Rec × Bool)) × List (STest × Nat) :=
  let t := appendFill acc.1 L
  (t, acc.2 ++ [(.drain, occupied t)])

/-- The drain: A's leftovers (range order), each B-tier page's leftovers, the
leftover dedup against the insertion stash, then the insertion stash. Returns
the tier's lanes (index `page · C + lane`) and the capacity trace. -/
def sDrain (st : SFin) : List (Option Rec) × List (STest × Nat) :=
  let first := (st.leaves.map fun L => L.map fun x => (x, true)) ++
    st.bcopy.map fun L => L.map fun x => (x, false)
  let d := first.foldl sDrainStep ([], [])
  let insKeys := st.ins.map Rec.key
  let t := d.1.map fun s => s.filter fun p => !(p.2 && insKeys.contains p.1.key)
  let bKeys := ((t.filterMap id).filter fun p => !p.2).map fun p => p.1.key
  let ins := st.ins.filter fun x => !bKeys.contains x.key
  let d2 := sDrainStep (t, d.2) (ins.map fun x => (x, false))
  (d2.1.map fun s => s.map Prod.fst, d2.2)

/-! ### The reference execution and the bounded job -/

/-- Everything the reference execution computes. -/
structure SRun where
  route : SRoute
  pool : List Rec
  leaves : List (List Rec)
  fin : SFin
  output : Output
  /-- Every capacity test in execution order, with its tested quantity. -/
  trace : List (STest × Nat)

/-- The reference execution under a schedule of A's binary pair operations:
every phase with unbounded storage. It never fails and is defined for every
word assignment. -/
def sReferenceWith (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) : SRun :=
  let route := sRouteWith rule g w inp.aMain ops
  let pool := sPool route inp.aTier inp.bTier
  let leaves := sLeaves g w pool
  let fin := sFinish g w inp route.main leaves
  let dr := sDrain fin
  { route, pool, leaves, fin
    output := { main := fin.main, tier := dr.1 }
    trace := route.trace ++ sDfsTrace g w pool ++ fin.trace ++ dr.2 }

/-- The reference execution under the engine's schedule. -/
def sReference (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) : SRun :=
  sReferenceWith rule g w inp (engineOps g)

/-- The first capacity test of a trace that exceeds its capacity. -/
def sFirstFailure (g : SepGeom) (trace : List (STest × Nat)) : Option STest :=
  (trace.find? fun t => decide (g.capOf t.1 < t.2)).map Prod.fst

/-- The bounded job under a schedule of A's binary pair operations. -/
def sJobWith (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs)
    (ops : List (Nat × Nat)) : Except STest Output :=
  let r := sReferenceWith rule g w inp ops
  match sFirstFailure g r.trace with
  | some t => .error t
  | none => .ok r.output

/-- The bounded job under the engine's schedule: it fails at the first
failing capacity test, and otherwise publishes the reference output. -/
def sJob (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) : Except STest Output :=
  sJobWith rule g w inp (engineOps g)

end RebuildBound.Model
