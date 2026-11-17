import RebuildBound.Spec.Model.Basic

/-!
# The d = 2 separated-sources ordinary merge (trusted model)

The reference construction of `REPORT.tex` (sections `sec:dfs-theorem` and
`sec:separated-residuals`, Proposition `prop:separated-capacity`) at digit
`d = 2`, with the engine's evaluation choices. The record-level semantics were
extracted from the engine and checked lane-exactly against it on 1964
fixtures (`oracle/README.md`).

Geometry: `U = 2^k` carry buckets, `2U` output buckets, `b = k + 1` binary
stages, bucket capacity `C`, coarse ranges of `2^lo` homes each.
The routing word of key `x` under the merge family is `w x`; its home is
`w x mod 2U`, and stage `j + 1` reads bit `j`.

**Phases**, each a pure function of the previous state:

1. **Route A** (`routeA`). A's main is embedded at `[U, 2U)` and `[0, U)` is
   blank. Stage `j + 1` (`j = 0 … k`) merge-splits every pair
   `(i, i + 2^j)` with bit `j` of `i` clear, in ascending `i`, by the
   selection rule; stage `j + 1`'s sheds are appended to one shared stash.
   Pairs in the blank region and the first continuation stage (bit `k`,
   blank first) never shed. There is no deduplication in A's route.
2. **Pool** (`poolA`). A's stashes (bit order, append order) and then A's old
   tier (lane order), minus every record whose key is in B's tier.
3. **DFS** (`leavesOf`, `dfsTrace`). Leaf `R` holds the pool records of coarse
   range `R` in pool order. Every node of the padded binary tree over the
   ranges is capacity-tested; the partition is lossless.
4. **Insertion and offers** (`finish`). For each B bucket `i`: remove the A
   copies of B's keys from outputs `i` and `i + U`; insert B's records of
   each direction (bit `k`) into the lowest free lanes, shedding B's
   highest-lane surplus into the insertion stash. After each direction's
   insertion its home receives two offers: A's leaf candidates for that home
   (an A candidate whose key is already in main is consumed), then B tier
   candidates for that home (a B tier candidate first frees the lane of the
   A main copy of its key).
5. **Drain** (`drain`). A's leaf leftovers (range order) and then B's tier
   leftovers go to the output tier; A-class tier records whose key was shed
   by B's insertion are removed; the insertion stash (minus keys of B-class
   tier records) is appended.

**Capacity tests.** No capacity test changes the state: the engine aborts at
its first failing test and publishes nothing. The model therefore runs every
phase with unbounded storage (this is the *reference execution*, which never
fails and is defined for every word assignment) and records each capacity
test, with its tested quantity, in a trace. The trace keeps the engine's
order of the phases and, within every phase but the DFS, of the tests. The
bounded job (`job`) fails at the first trace entry that exceeds its capacity,
and otherwise returns the reference output. A capacity `none` is unbounded.

**The DFS part of the trace is abstract.** `dfsTrace` tests every node of
the padded tree, depth by depth. The engine tests only the nodes at and below
its direct height, skips padding nodes, and runs each direct node and then
its splits in preorder. The verdicts agree whenever the pool fits its slots
(the stash tests passed and A's tier fits). Then every count is at most
`P_pool`, the capacities are nested, and in both orders some DFS test fails
iff some leaf exceeds its capacity. Padding nodes are empty, and the DFS
tests sit between the same neighbouring phases. Only the node named by the
failure `.dfs d c` can differ from the engine's, and the oracle compares
the failing test's kind, not the node. The statements quantify over every
node.
-/

namespace RebuildBound.Model

/-- Public geometry of one d = 2 merge. -/
structure Geom where
  /-- Bucket capacity (records per main bucket). -/
  C : Nat
  /-- `U = 2^k` carry buckets; the output has `2U` buckets. -/
  k : Nat
  /-- Each coarse DFS range covers `2^lo` homes (the report's `I`). -/
  lo : Nat
  /-- Physical slots of the swept A pool, `P_pool` of `eq:dfs-capacity`. -/
  poolSlots : Nat
  deriving Repr

namespace Geom

/-- Carry buckets `U`. -/
def U (g : Geom) : Nat := 2 ^ g.k

/-- Output buckets (homes) `2U`. -/
def homes (g : Geom) : Nat := 2 ^ (g.k + 1)

/-- Binary stages `b = k + 1`. -/
def stages (g : Geom) : Nat := g.k + 1

/-- Depth of the coarse DFS partition, `D_c = b - lo`. -/
def depth (g : Geom) : Nat := g.k + 1 - g.lo

/-- Number of coarse ranges, `2^(b - lo)`. -/
def ranges (g : Geom) : Nat := 2 ^ g.depth

end Geom

/-- Public capacities of the tests. `none` is unbounded. -/
structure Caps where
  /-- Stage stash of the stage that reads bit `j`, in records. -/
  stash : Nat → Option Nat
  /-- DFS leaf capacity `S` (one page: `C`). -/
  leaf : Option Nat
  /-- The insertion (drain-only) stash, in records. -/
  ins : Option Nat
  /-- The output tier, in records. -/
  out : Option Nat

/-- Every capacity unbounded: the reference execution. -/
def Caps.unbounded : Caps := ⟨fun _ => none, none, none, none⟩

/-- The capacity tests of the job, in the order the model performs them. -/
inductive Test where
  /-- The shared stash of the stage that reads bit `bit`, after one merge-split. -/
  | stash (bit : Nat)
  /-- DFS node `pre` at depth `depth` (it covers the ranges whose top `depth`
  bits are `pre`). -/
  | dfs (depth pre : Nat)
  /-- The insertion stash, after one B bucket's insertion. -/
  | insertion
  /-- The output tier, after one append. -/
  | drain
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The capacity of a test: `C_j = min(P_pool, S 2^(D_c - j))` for a DFS node
at depth `j` (`eq:dfs-capacity` with no refinement levels). -/
def Caps.capOf (g : Geom) (c : Caps) : Test → Option Nat
  | .stash j => c.stash j
  | .dfs d _ => c.leaf.map fun S => min g.poolSlots (S * 2 ^ (g.depth - d))
  | .insertion => c.ins
  | .drain => c.out

/-- The tested quantity `n` exceeds the capacity `c`. -/
def exceeds : Option Nat → Nat → Bool
  | none, _ => false
  | some c, n => decide (c < n)

/-- The job's inputs. Buckets have `C` lanes. B's main bucket `i` holds B's
records with carry home `i`; tiers are listed in lane order. -/
structure Inputs where
  aMain : List Bucket
  aTier : List Rec
  bMain : List Bucket
  bTier : List Rec

/-- The published result: `2U` main buckets and the output tier's lanes. -/
structure Output where
  main : List Bucket
  tier : List (Option Rec)
  deriving DecidableEq

/-- The home of a record under the merge family's words `w`. -/
def home (g : Geom) (w : LogicalKey → Nat) (r : Rec) : Nat := w r.key % g.homes

/-- The coarse range of a record. -/
def rangeOf (g : Geom) (w : LogicalKey → Nat) (r : Rec) : Nat := home g w r / 2 ^ g.lo

/-- The routing bit `j` of a record. -/
def dirBit (w : LogicalKey → Nat) (j : Nat) (r : Rec) : Bool := (w r.key).testBit j

/-! ### Phase 1: A's route -/

/-- The state of A's route: `2U` buckets, one stash per bit (append order), and
the capacity trace so far. -/
structure RouteState where
  main : List Bucket
  stash : List (List Rec)
  trace : List (Test × Nat)

/-- The merge-split of the pair `(i, i + 2^j)` by bit `j`. -/
def pairStep (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (j i : Nat) (st : RouteState) :
    RouteState :=
  let r := rule.split g.C (dirBit w j) (st.main.getD i []) (st.main.getD (i + 2 ^ j) [])
  let sj := st.stash.getD j [] ++ r.2.2
  { main := (st.main.set i r.1).set (i + 2 ^ j) r.2.1
    stash := st.stash.set j sj
    trace := st.trace ++ [(.stash j, sj.length)] }

/-- The pair operations of the stage that reads bit `j`: `(j, i)` for every
`i` with bit `j` clear, in ascending `i`. -/
def stageOps (g : Geom) (j : Nat) : List (Nat × Nat) :=
  ((List.range g.homes).filter fun i => !i.testBit j).map fun i => (j, i)

/-- The model's schedule: stage by stage, pairs in ascending order. -/
def canonicalOps (g : Geom) : List (Nat × Nat) :=
  (List.range g.stages).flatMap (stageOps g)

/-- Run a list of pair operations `(j, i)`. -/
def runOps (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (ops : List (Nat × Nat))
    (st : RouteState) : RouteState :=
  ops.foldl (fun st o => pairStep rule g w o.1 o.2 st) st

/-- The stage that reads bit `j`. -/
def stageStep (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (j : Nat) (st : RouteState) :
    RouteState :=
  runOps rule g w (stageOps g j) st

/-- The route's initial state: `[0, U)` blank, A's main at `[U, 2U)`. -/
def routeInit (g : Geom) (aMain : List Bucket) : RouteState :=
  { main := List.replicate g.U (Bucket.empty g.C) ++ aMain
    stash := List.replicate g.stages []
    trace := [] }

/-- A's route under an arbitrary schedule of pair operations (package D6). -/
def routeWith (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (aMain : List Bucket)
    (ops : List (Nat × Nat)) : RouteState :=
  runOps rule g w ops (routeInit g aMain)

/-- The state after the first `n` stages (they read bits `0, …, n - 1`). -/
def routeUpTo (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (aMain : List Bucket) (n : Nat) :
    RouteState :=
  routeWith rule g w aMain ((List.range n).flatMap (stageOps g))

/-- A's complete route: all `b = k + 1` stages. -/
def routeA (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (aMain : List Bucket) : RouteState :=
  routeUpTo rule g w aMain g.stages

/-! ### Phases 2 and 3: the swept A pool and its DFS -/

/-- The swept A pool: A's stashes in bit order, then A's old tier, minus every
record whose key is in B's tier (B is fresher). -/
def poolA (st : RouteState) (aTier bTier : List Rec) : List Rec :=
  (st.stash.flatten ++ aTier).filter fun r => !(bTier.map Rec.key).contains r.key

/-- DFS leaf `R`: the pool records of coarse range `R`, in pool order. -/
def leavesOf (g : Geom) (w : LogicalKey → Nat) (pool : List Rec) : List (List Rec) :=
  (List.range g.ranges).map fun R => pool.filter fun r => rangeOf g w r == R

/-- The DFS capacity tests: every node of the padded tree, depth by depth (an
abstract order with the engine's verdict, not the engine's unit order; see
the module doc). -/
def dfsTrace (g : Geom) (w : LogicalKey → Nat) (pool : List Rec) : List (Test × Nat) :=
  (List.range (g.depth + 1)).flatMap fun d =>
    (List.range (2 ^ d)).map fun c =>
      (.dfs d c, (pool.filter fun r => rangeOf g w r / 2 ^ (g.depth - d) == c).length)

/-! ### Phase 4: B's insertion with the fused offers -/

/-- The finish state: main buckets, the insertion stash (append order), the
remaining A leaf candidates, the remaining B tier candidates (lane order), and
the capacity trace of this phase. -/
structure FinState where
  main : List Bucket
  ins : List Rec
  leaves : List (List Rec)
  bcopy : List Rec
  trace : List (Test × Nat)

/-- Offer A's leaf candidates for home `ci`. A candidate whose key is already in
main (B's copy) is consumed; the others fill the lowest free lanes in leaf
order, and those placed are consumed. -/
def offerA (g : Geom) (w : LogicalKey → Nat) (ci : Nat) (st : FinState) : FinState :=
  let R := ci / 2 ^ g.lo
  let leaf := st.leaves.getD R []
  let B := st.main.getD ci []
  let cand := leaf.filter fun r => home g w r == ci
  let drop := cand.filter fun r => B.keys.contains r.key
  let stale := cand.filter fun r => !B.keys.contains r.key
  let f := fill B stale
  let gone := (drop ++ stale.take (stale.length - f.2.length)).map Rec.key
  { st with
    main := st.main.set ci f.1
    leaves := st.leaves.set R (leaf.filter fun r => !gone.contains r.key) }

/-- Offer B's tier candidates for home `ci` (full-home match, lane order). Each
candidate first frees the lane of a main copy of its key (an A main record);
then the candidates fill the lowest free lanes, and those placed are
consumed. -/
def offerB (g : Geom) (w : LogicalKey → Nat) (ci : Nat) (st : FinState) : FinState :=
  let fc := st.bcopy.filter fun r => home g w r == ci
  let B := (st.main.getD ci []).clear fun key => (fc.map Rec.key).contains key
  let f := fill B fc
  let placed := (fc.take (fc.length - f.2.length)).map Rec.key
  { st with
    main := st.main.set ci f.1
    bcopy := st.bcopy.filter fun r => !placed.contains r.key }

/-- Insert B's main bucket `i` into outputs `i` and `i + U`, with the offers to
each output right after its insertion. -/
def insertBucket (g : Geom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) :
    FinState :=
  let Bi := bMain.getD i []
  let bk := Bi.keys
  let m0 := (st.main.getD i []).clear fun key => bk.contains key
  let m1 := (st.main.getD (i + g.U) []).clear fun key => bk.contains key
  let f0 := fill m0 (Bi.recs.filter fun r => !dirBit w g.k r)
  let st := { st with main := (st.main.set i f0.1).set (i + g.U) m1 }
  let st := offerB g w i (offerA g w i st)
  let f1 := fill (st.main.getD (i + g.U) []) (Bi.recs.filter fun r => dirBit w g.k r)
  let ins := st.ins ++ f0.2 ++ f1.2
  let st := { st with
    main := st.main.set (i + g.U) f1.1
    ins := ins
    trace := st.trace ++ [(.insertion, ins.length)] }
  offerB g w (i + g.U) (offerA g w (i + g.U) st)

/-- B's insertion over all `U` carry buckets, in ascending order. -/
def finish (g : Geom) (w : LogicalKey → Nat) (inp : Inputs) (routed : List Bucket)
    (leaves : List (List Rec)) : FinState :=
  (List.range g.U).foldl (fun st i => insertBucket g w inp.bMain i st)
    { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }

/-! ### Phase 5: the coordinated drain -/

/-- Append one list of leftovers (tagged `true` for A's class) to the output
tier and record the tier's occupancy. -/
def drainStep (acc : List (Option (Rec × Bool)) × List (Test × Nat)) (L : List (Rec × Bool)) :
    List (Option (Rec × Bool)) × List (Test × Nat) :=
  let t := appendFill acc.1 L
  (t, acc.2 ++ [(.drain, occupied t)])

/-- The drain: A's leftovers (range order), B's tier leftovers, the leftover
dedup against the insertion stash, then the insertion stash. Returns the
tier's lanes and the capacity trace. -/
def drain (st : FinState) : List (Option Rec) × List (Test × Nat) :=
  let first := (st.leaves.map fun L => L.map fun r => (r, true)) ++
    [st.bcopy.map fun r => (r, false)]
  let d := first.foldl drainStep ([], [])
  let insKeys := st.ins.map Rec.key
  let t := d.1.map fun s => s.filter fun p => !(p.2 && insKeys.contains p.1.key)
  let bKeys := ((t.filterMap id).filter fun p => !p.2).map fun p => p.1.key
  let ins := st.ins.filter fun r => !bKeys.contains r.key
  let d2 := drainStep (t, d.2) (ins.map fun r => (r, false))
  (d2.1.map fun s => s.map Prod.fst, d2.2)

/-! ### The reference execution and the bounded job -/

/-- Everything the reference execution computes. -/
structure Run where
  route : RouteState
  pool : List Rec
  leaves : List (List Rec)
  fin : FinState
  output : Output
  /-- Every capacity test in execution order, with its tested quantity. -/
  trace : List (Test × Nat)

/-- The reference execution under a schedule of A's pair operations. -/
def referenceWith (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (inp : Inputs)
    (ops : List (Nat × Nat)) : Run :=
  let route := routeWith rule g w inp.aMain ops
  let pool := poolA route inp.aTier inp.bTier
  let leaves := leavesOf g w pool
  let fin := finish g w inp route.main leaves
  let dr := drain fin
  { route, pool, leaves, fin
    output := { main := fin.main, tier := dr.1 }
    trace := route.trace ++ dfsTrace g w pool ++ fin.trace ++ dr.2 }

/-- The reference execution: every phase with unbounded storage, under the
model's schedule. It never fails and is defined for every word assignment. -/
def reference (rule : CapRule) (g : Geom) (w : LogicalKey → Nat) (inp : Inputs) : Run :=
  referenceWith rule g w inp (canonicalOps g)

/-- The first capacity test of the reference trace that fails under `caps`. -/
def firstFailure (g : Geom) (caps : Caps) (trace : List (Test × Nat)) : Option Test :=
  (trace.find? fun t => exceeds (caps.capOf g t.1) t.2).map Prod.fst

/-- The bounded job under a schedule of A's pair operations. -/
def jobWith (rule : CapRule) (g : Geom) (caps : Caps) (w : LogicalKey → Nat) (inp : Inputs)
    (ops : List (Nat × Nat)) : Except Test Output :=
  let r := referenceWith rule g w inp ops
  match firstFailure g caps r.trace with
  | some t => .error t
  | none => .ok r.output

/-- The bounded job: it fails at the first failing capacity test, and
otherwise publishes the reference output. -/
def job (rule : CapRule) (g : Geom) (caps : Caps) (w : LogicalKey → Nat) (inp : Inputs) :
    Except Test Output :=
  jobWith rule g caps w inp (canonicalOps g)

end RebuildBound.Model
