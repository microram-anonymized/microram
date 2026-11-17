import RebuildBound.Spec.Model.Sep

/-!
# The top preparation and the initialization's route (trusted model)

`REPORT.tex`, sections `sec:binary-top-preparation`, `sec:top-final-ranges`
and `sec:top-dfs-decision` (Corollary `cor:top-dfs-transfer`), with the
engine's evaluation choices. The record-level semantics are
`Spec/Model/ENGINE_TOPPREP.md`, extracted from the engine and checked
lane-exactly against it on 2519 fixtures; its Python transcription is
`oracle/fixtures-tp/model_tp.py`. New definitions only. Reused: `Rec`,
`Bucket`, `fill`, `appendFill`, `occupied`, `CapRule`, `dirBit`, `Output`
(`Basic.lean`, `Job.lean`) and the engine's butterfly recursion `routeRec`
(`Sep.lean`).

Both passes are one job phase over A, a single population on all `T = 2^k`
homes of the top. The top preparation (`PrepareOlder` at the top) copies A's
main, routes it under the new family and packs the residuals into the
retained carry `R`, which the top finish then consumes as its A pool. The
direct initialization scatters the input over the top's main and runs the
same phase in place, draining into the published tier.

**Geometry** (`TPGeom`, the configuration probe's `top_prepare` row): `T = 2^k`
homes; every stage stash has `stashPages` pages; A's old tier slot in the
pool has `aTierPages` pages (also in an initialization, where it is empty);
the drain target has `drainPages` pages (R, or the published tier). The DFS
plan has `2^rangeBits` one-page leaves of `2^I` homes each, with
`rangeBits + I = k`; the direct plan (`dfs = false`, the minimal top `T = 8`)
has no DFS: one range holds the whole pool.

**Words.** The new family's word of key `x` is `w x`; its home is `w x mod T`
and stage `j + 1` reads bit `j`.

**Phases**, each a pure function of the previous state:

1. **Arrival** (`copyMain`). A's main keeps its lanes, minus the flagged
   tombstones (`r.tomb` and the unshadowed flag `unsh r`, the engine's meta
   bit `0x20`), which the copy drops. Plain tombstones are ordinary records
   throughout. An initialization drops nothing (`unsh = fun _ => false`).
2. **Route** (`runTPOps`). Bits `0 … k - 2` only. A schedule is a list of
   pair operations `(j, i)`: merge-split the pair `(i, i + 2^j)` by bit `j`
   with the selection rule, and append the second bucket's surplus to the
   stash of bit `j`. The engine's schedule (`tpEngineOps`) routes the half
   `[0, T/2)` and then the half `[T/2, T)`, each by the engine's butterfly
   recursion on bits `0 … k - 2`. `canonicalOps` is the same set of
   operations stage by stage. There is no deduplication anywhere.
3. **Pool** (`tpPool`). The stashes of bits `0 … k - 2` in bit order, then A's
   old tier, minus the flagged tombstones (dropped at the gather). The last
   level's stash is not in the pool.
4. **DFS** (`tpLeaves`, `tpDfsTrace`). Leaf `v` holds the pool records whose
   home `h` has `⌊h / 2^I⌋ = v`, in pool order. In the DFS plan every node of
   the padded tree is capacity-tested, depth by depth: as in `Job.lean`, an
   abstract order with the engine's verdict (the engine fails iff some leaf
   holds more than `C` records). The direct plan has one leaf and no test.
5. **The last level, fused with the offers** (`tpFinish`). For each
   `i < T/2` ascending: merge-split the pair `(i, i + T/2)` by bit `k - 1`,
   appending the second bucket's surplus to the last level's stash (drain
   only); then offer bucket `i`, then bucket `i + T/2`. An offer to home `b`
   places the first `min(candidates, free lanes)` records of `b`'s leaf whose
   home is `b`, in leaf order, into the lowest free lanes, and removes them
   from the leaf. No key is compared.
6. **Drain** (`tpDrain`). Each leaf's leftovers in leaf order, then the last
   level's stash, appended to the drain target.

**Capacity tests.** As in `Job.lean`: no test changes the state, so the
model is the reference execution with every test recorded in a trace in
execution order (the DFS part excepted, see phase 4), and the bounded job
(`tpJob`) fails at the first trace entry above its capacity
(`TPGeom.capOf`); otherwise it publishes the reference output: the main
buckets and the drain target. The engine names a failing stash test of bits
`< k - 1` `butterfly` and of bit `k - 1` `butterfly-offers`; it tests the
drain once per leaf and once per page of the last stash, here once per leaf
and once for the whole last stash (same verdict and kind).
-/

namespace RebuildBound.Model

/-- Public geometry of one top preparation or initialization route: the fields
of the configuration probe's `top_prepare` row. Capacities are in pages of `C`
slots. -/
structure TPGeom where
  /-- Bucket capacity (slots per home and per page). -/
  C : Nat
  /-- `T = 2^k` homes (`block_bits`). -/
  k : Nat
  /-- Pages of every stage stash (`stash_buckets`). -/
  stashPages : Nat
  /-- Pages of A's old tier slot in the pool. -/
  aTierPages : Nat
  /-- Pages of the drain target: the retained carry R, or the published tier. -/
  drainPages : Nat
  /-- `2^rangeBits` DFS leaves (`range_bits`). -/
  rangeBits : Nat
  /-- `2^I` homes per leaf (`index_bits`). -/
  I : Nat
  /-- The DFS plan (`true`), or the direct plan of the minimal top. -/
  dfs : Bool
  deriving Repr, DecidableEq

namespace TPGeom

/-- Homes `T = 2^k`. -/
def T (g : TPGeom) : Nat := 2 ^ g.k

/-- Half the homes, `T / 2 = 2^(k - 1)`: the last level's pair distance. -/
def half (g : TPGeom) : Nat := 2 ^ (g.k - 1)

/-- Pages of the swept pool: the stashes of bits `0 … k - 2` and A's tier slot. -/
def poolPages (g : TPGeom) : Nat := (g.k - 1) * g.stashPages + g.aTierPages

/-- Leaves `2^rangeBits`. -/
def ranges (g : TPGeom) : Nat := 2 ^ g.rangeBits

/-- The domain of the model: at least one bit, a range plan that covers every
home exactly, and one range in the direct plan. -/
def Valid (g : TPGeom) : Prop :=
  1 ≤ g.k ∧ g.rangeBits + g.I = g.k ∧ (g.dfs = false → g.rangeBits = 0)

instance (g : TPGeom) : Decidable g.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end TPGeom

/-- The capacity tests of the job, in the order the model performs them. -/
inductive TPTest where
  /-- The stash of bit `bit`, after one merge-split. -/
  | stash (bit : Nat)
  /-- DFS node `pre` at depth `depth` (it covers the leaves whose top `depth`
  bits are `pre`). -/
  | dfs (depth pre : Nat)
  /-- The drain target, after one append. -/
  | drain
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The capacity of a test, in records: `C_h = min(P_pool, C 2^h)` for a DFS node
of height `h` (one-page leaves, `eq:dfs-capacity`). -/
def TPGeom.capOf (g : TPGeom) : TPTest → Nat
  | .stash _ => g.stashPages * g.C
  | .dfs dd _ => min (g.poolPages * g.C) (g.C * 2 ^ (g.rangeBits - dd))
  | .drain => g.drainPages * g.C

/-- The job's inputs: A's main (`T` buckets of `C` lanes; for an initialization
the scattered input, `initMain`) and A's old tier in (page, lane) order (empty
for an initialization). -/
structure TPInputs where
  aMain : List Bucket
  aTier : List Rec

/-- A flagged tombstone: a tombstone with the unshadowed flag. -/
def flagged (unsh : Rec → Bool) (r : Rec) : Bool := r.tomb && unsh r

/-- The arrival: A's main minus its flagged tombstones, lanes kept. -/
def copyMain (unsh : Rec → Bool) (aMain : List Bucket) : List Bucket :=
  aMain.map fun B => B.map fun s => s.filter fun r => !flagged unsh r

/-- The initialization's scatter: input record `j` at bucket `j / (C/2)`, lane
`j mod (C/2)`; `T` buckets of `C` lanes. -/
def initMain (g : TPGeom) (input : List Rec) : List Bucket :=
  (List.range g.T).map fun b =>
    (List.range g.C).map fun l => if l < g.C / 2 then input[b * (g.C / 2) + l]? else none

/-! ### Phase 2: the route -/

/-- The state of the route: `T` buckets, one stash per bit `0 … k - 1` (append
order; the last is filled by phase 5), and the capacity trace so far. -/
structure TPRoute where
  main : List Bucket
  stash : List (List Rec)
  trace : List (TPTest × Nat)

/-- The merge-split of the pair `(i, i + 2^j)` by bit `j`. -/
def tpPairStep (rule : CapRule) (g : TPGeom) (w : LogicalKey → Nat) (j i : Nat) (st : TPRoute) :
    TPRoute :=
  let p := rule.split g.C (dirBit w j) (st.main.getD i []) (st.main.getD (i + 2 ^ j) [])
  let sj := st.stash.getD j [] ++ p.2.2
  { main := (st.main.set i p.1).set (i + 2 ^ j) p.2.1
    stash := st.stash.set j sj
    trace := st.trace ++ [(.stash j, sj.length)] }

/-- Run a list of pair operations `(j, i)`. -/
def runTPOps (rule : CapRule) (g : TPGeom) (w : LogicalKey → Nat) (ops : List (Nat × Nat))
    (st : TPRoute) : TPRoute :=
  ops.foldl (fun st o => tpPairStep rule g w o.1 o.2 st) st

/-- The engine's schedule of the route: the half `[0, T/2)` and then the half
`[T/2, T)`, each by the engine's butterfly recursion on bits `0 … k - 2`. -/
def tpEngineOps (g : TPGeom) : List (Nat × Nat) :=
  routeRec 0 0 (g.k - 1) ++ routeRec g.half 0 (g.k - 1)

/-- The model's stage-by-stage schedule: for each bit `j < k - 1`, every pair
`(i, i + 2^j)` with bit `j` of `i` clear, in ascending `i`. -/
def TPGeom.canonicalOps (g : TPGeom) : List (Nat × Nat) :=
  (List.range (g.k - 1)).flatMap fun j =>
    ((List.range g.T).filter fun i => !i.testBit j).map fun i => (j, i)

/-- The route's initial state. -/
def tpRouteInit (g : TPGeom) (main : List Bucket) : TPRoute :=
  { main := main, stash := List.replicate g.k [], trace := [] }

/-- The route after the first `n` stages of the stage-by-stage schedule (they read
bits `0, …, n - 1`). -/
def tpRouteUpTo (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat)
    (aMain : List Bucket) (n : Nat) : TPRoute :=
  runTPOps rule g w (g.canonicalOps.filter fun o => o.1 < n) (tpRouteInit g (copyMain unsh aMain))

/-! ### Phases 3 and 4: the pool and its DFS -/

/-- The home of a record under the new family's words `w`. -/
def tpHome (g : TPGeom) (w : LogicalKey → Nat) (r : Rec) : Nat := w r.key % g.T

/-- The leaf of a record: `⌊home / 2^I⌋`. -/
def tpRange (g : TPGeom) (w : LogicalKey → Nat) (r : Rec) : Nat := tpHome g w r / 2 ^ g.I

/-- The swept pool: the stashes of bits `0 … k - 2` in bit order, then A's old
tier, minus the flagged tombstones. -/
def tpPool (g : TPGeom) (unsh : Rec → Bool) (st : TPRoute) (aTier : List Rec) : List Rec :=
  ((st.stash.take (g.k - 1)).flatten ++ aTier).filter fun r => !flagged unsh r

/-- Leaf `v`: the pool records of leaf `v`, in pool order. -/
def tpLeaves (g : TPGeom) (w : LogicalKey → Nat) (pool : List Rec) : List (List Rec) :=
  (List.range g.ranges).map fun v => pool.filter fun r => tpRange g w r == v

/-- The DFS capacity tests: every node of the padded tree, depth by depth (an
abstract order with the engine's verdict, as `dfsTrace`). -/
def tpDfsTrace (g : TPGeom) (w : LogicalKey → Nat) (pool : List Rec) : List (TPTest × Nat) :=
  (List.range (g.rangeBits + 1)).flatMap fun dd =>
    (List.range (2 ^ dd)).map fun c =>
      (.dfs dd c, (pool.filter fun r => tpRange g w r / 2 ^ (g.rangeBits - dd) == c).length)

/-! ### Phase 5: the last level fused with the offers -/

/-- The finish state: main buckets, the last level's stash (append order), the
remaining leaf candidates, and the capacity trace of this phase. -/
structure TPFin where
  main : List Bucket
  last : List Rec
  leaves : List (List Rec)
  trace : List (TPTest × Nat)

/-- Remove the first `n` records of `L` that satisfy `p`. -/
def eraseFirst (p : Rec → Bool) : Nat → List Rec → List Rec
  | 0, L => L
  | _ + 1, [] => []
  | n + 1, x :: L => if p x then eraseFirst p n L else x :: eraseFirst p (n + 1) L

/-- Offer home `b` its leaf's candidates: the first `min(candidates, free)` leaf
records whose home is `b`, in leaf order, fill the lowest free lanes and leave
the leaf. -/
def tpOffer (g : TPGeom) (w : LogicalKey → Nat) (b : Nat) (st : TPFin) : TPFin :=
  let R := b / 2 ^ g.I
  let leaf := st.leaves.getD R []
  let cand := leaf.filter fun r => tpHome g w r == b
  let f := fill (st.main.getD b []) cand
  { st with
    main := st.main.set b f.1
    leaves := st.leaves.set R
      (eraseFirst (fun r => tpHome g w r == b) (cand.length - f.2.length) leaf) }

/-- The last level at pair `i`: merge-split `(i, i + T/2)` by bit `k - 1` into the
last stash and test it, then offer bucket `i`, then bucket `i + T/2`. -/
def tpLastStep (rule : CapRule) (g : TPGeom) (w : LogicalKey → Nat) (i : Nat) (st : TPFin) : TPFin :=
  let p := rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i []) (st.main.getD (i + g.half) [])
  let last := st.last ++ p.2.2
  let st := { st with
    main := (st.main.set i p.1).set (i + g.half) p.2.1
    last := last
    trace := st.trace ++ [(.stash (g.k - 1), last.length)] }
  tpOffer g w (i + g.half) (tpOffer g w i st)

/-- The last level over all pairs `i < T/2`, in ascending order. -/
def tpFinish (rule : CapRule) (g : TPGeom) (w : LogicalKey → Nat) (routed : List Bucket)
    (leaves : List (List Rec)) : TPFin :=
  (List.range g.half).foldl (fun st i => tpLastStep rule g w i st)
    { main := routed, last := [], leaves := leaves, trace := [] }

/-! ### Phase 6: the drain -/

/-- Append one list of leftovers to the drain target and record its occupancy. -/
def tpDrainStep (acc : List (Option Rec) × List (TPTest × Nat)) (L : List Rec) :
    List (Option Rec) × List (TPTest × Nat) :=
  let t := appendFill acc.1 L
  (t, acc.2 ++ [(.drain, occupied t)])

/-- The drain: each leaf's leftovers in leaf order, then the last level's stash.
Returns the target's lanes (index `page · C + lane`) and the capacity trace. -/
def tpDrain (st : TPFin) : List (Option Rec) × List (TPTest × Nat) :=
  (st.leaves ++ [st.last]).foldl tpDrainStep ([], [])

/-! ### The reference execution and the bounded job -/

/-- Everything the reference execution computes. -/
structure TPRun where
  route : TPRoute
  pool : List Rec
  leaves : List (List Rec)
  fin : TPFin
  output : Output
  /-- Every capacity test in execution order, with its tested quantity. -/
  trace : List (TPTest × Nat)

/-- The reference execution under a schedule of the route's pair operations:
every phase with unbounded storage. It never fails and is defined for every
word assignment. -/
def tpReferenceWith (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat)
    (inp : TPInputs) (ops : List (Nat × Nat)) : TPRun :=
  let route := runTPOps rule g w ops (tpRouteInit g (copyMain unsh inp.aMain))
  let pool := tpPool g unsh route inp.aTier
  let leaves := tpLeaves g w pool
  let fin := tpFinish rule g w route.main leaves
  let dr := tpDrain fin
  { route, pool, leaves, fin
    output := { main := fin.main, tier := dr.1 }
    trace := route.trace ++ (if g.dfs then tpDfsTrace g w pool else []) ++ fin.trace ++ dr.2 }

/-- The reference execution under the engine's schedule. -/
def tpReference (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat)
    (inp : TPInputs) : TPRun :=
  tpReferenceWith rule g unsh w inp (tpEngineOps g)

/-- The first capacity test of a trace that exceeds its capacity. -/
def tpFirstFailure (g : TPGeom) (trace : List (TPTest × Nat)) : Option TPTest :=
  (trace.find? fun t => decide (g.capOf t.1 < t.2)).map Prod.fst

/-- The bounded job under a schedule of the route's pair operations. -/
def tpJobWith (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat)
    (inp : TPInputs) (ops : List (Nat × Nat)) : Except TPTest Output :=
  let r := tpReferenceWith rule g unsh w inp ops
  match tpFirstFailure g r.trace with
  | some t => .error t
  | none => .ok r.output

/-- The bounded top preparation under the engine's schedule: it fails at the first
failing capacity test, and otherwise publishes the reference output (C and R). -/
def tpJob (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs) :
    Except TPTest Output :=
  tpJobWith rule g unsh w inp (tpEngineOps g)

/-- The bounded initialization route: the input scattered by `initMain`, no old
tier, nothing dropped; it publishes the main and the published tier. -/
def initJob (rule : CapRule) (g : TPGeom) (w : LogicalKey → Nat) (input : List Rec) :
    Except TPTest Output :=
  tpJob rule g (fun _ => false) w ⟨initMain g input, []⟩

end RebuildBound.Model
