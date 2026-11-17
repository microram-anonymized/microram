import RebuildBound.Spec.Model.Job

/-!
# The top finish (trusted model)

`REPORT.tex`, Proposition `prop:top-resolution` and Corollary
`cor:top-finish-separated`, with the engine's evaluation order. The
record-level semantics are `Spec/Model/ENGINE_TOP.md`, extracted from the
engine and checked lane-exactly against it on the top fixtures.

The top finish is the separated job's finish with A's pool replaced by the
retained carry R, A's main C already at its final homes, B inserted into the
top's `D` ways, and the resolution steps (a)–(d) before each destination's
merge. New definitions only: `Job.lean` is untouched, so no proved package
changes. Reused from it: `fill`, `Bucket.clear`, `leavesOf` and `dfsTrace`
(through `TopGeom.toGeom`, see `toGeom_homes` and `toGeom_depth`), `FinState`,
`drain` (the coordinated drain with the leftover dedup), the test kinds
`Test`, `Caps.capOf` and `firstFailure`, and `Output`.

Geometry: `T = D U` homes, `U = 2^k`, `D = 2^e`; the home of key `x` is
`w x mod T`, its carry bucket `w x mod U` and its way `⌊home / U⌋`. Coarse
range `r` holds the homes `v` with `⌊v / 2^I⌋ = r`.

**Phases**, each a pure function of the previous state:

1. **Pool** (`topPool`). R minus every record whose key is in B's tier (the
   pool dedup, premise (P3)), then minus R's tombstones flagged unshadowed.
   B's tier is read through a direct copy minus its own flagged tombstones
   (`topTierCopy`). The flag is a parameter `unsh : Rec → Bool`; the engine's
   is bit `0x20` (`kMetaUnshadowed`) of the meta byte, the record value's last
   byte.
2. **DFS** (`leavesOf`, `dfsTrace`). Leaf `r` holds the pool records of coarse
   range `r`, in pool order. Every node of the padded tree is capacity-tested,
   capacity `min(S_R, C 2^(ρ - depth))`. A direct plan (`dfs = false`, with
   `ρ = 0`) has its one leaf and no test.
3. **Sweep** (`topSweep`). For each B bucket `i` ascending: clear C's copies
   of all of B's main keys at the `D` destinations `i + qU`; then for each way
   `q` ascending, at `ci = i + qU` (`topDest`):
   - resolution (`topResolve`): (d) drop C[ci]'s tombstones; (a) drop the
     leaf candidates for `ci` whose key B's direction-`q` records hold, and
     (c) the leaf's tombstone candidates for `ci`; (b) clear C[ci]'s copies of
     the B-tier candidates for `ci`, then (c) drop the B-tier tombstone
     candidates for `ci`;
   - the merge: B's live direction-`q` records fill C[ci]'s lowest free
     lanes; the rest are this direction's sheds;
   - the offers (`topOffer`): the leaf candidates for `ci`, then the B-tier
     candidates for `ci`, fill the lowest free lanes, in order; those placed
     are consumed.
   After the last way, the bucket's sheds (way order) are appended to the
   merge stash, which is then capacity-tested.
4. **Epilogue** (`drain`, then the trailing drops). Leaf leftovers (range
   order), then B-tier leftovers, go to the output tier; the leftover dedup;
   the merge stash is drained. Finally every tombstone in C and in the tier is
   dropped (the report proves there is none left).

**Capacity tests.** As in `Job.lean`, no test changes the state, so the model
is the reference execution with every test recorded in a trace (its DFS part
abstract, as there: the verdict is the engine's when R fits `S_R`, the
failing node may not be), and the bounded finish fails at the first trace
entry above its capacity. The merge
stash's test is `Test.insertion` (the engine's `fixed-merge-offers`), the
output tier's `Test.drain` (`residual-drain`) and the DFS's `Test.dfs`
(`residual-dfs-partition`), the d = 2 job's kinds.
-/

namespace RebuildBound.Model

/-- Public geometry of one top finish: the fields of the configuration probe's
`top_finish` row. Capacities are in pages of `C` slots. -/
structure TopGeom where
  /-- Bucket capacity (slots per home and per page). -/
  C : Nat
  /-- `U = 2^k` carry buckets. -/
  k : Nat
  /-- `D = 2^e` top ways; the top has `T = D U = 2^(k + e)` homes. -/
  e : Nat
  /-- `2^rho` coarse ranges of the finish range plan. -/
  rho : Nat
  /-- `2^I` homes per coarse range (`range_index_bits`). -/
  I : Nat
  /-- The plan distributes R through one-page DFS leaves; `false` is the
  direct plan (one leaf, the whole pool, no test), which has `rho = 0`. -/
  dfs : Bool
  /-- Pages of the retained carry R (the DFS pool). -/
  rPages : Nat
  /-- Pages of B's tier, read directly by every destination. -/
  bPages : Nat
  /-- Pages of the merge stash. -/
  mergePages : Nat
  /-- Pages of the output tier. -/
  tierPages : Nat
  deriving Repr, DecidableEq

namespace TopGeom

/-- Carry buckets `U = 2^k`. -/
def U (g : TopGeom) : Nat := 2 ^ g.k

/-- Top ways `D = 2^e`. -/
def D (g : TopGeom) : Nat := 2 ^ g.e

/-- Homes `T = 2^(k + e)`. -/
def T (g : TopGeom) : Nat := 2 ^ (g.k + g.e)

/-- Coarse ranges `2^rho`. -/
def ranges (g : TopGeom) : Nat := 2 ^ g.rho

/-- The retained carry's capacity `S_R`, in records. -/
def SR (g : TopGeom) : Nat := g.rPages * g.C

/-- B's tier capacity, in records. -/
def SB (g : TopGeom) : Nat := g.bPages * g.C

/-- The merge stash's capacity, in records. -/
def SMerge (g : TopGeom) : Nat := g.mergePages * g.C

/-- The output tier's capacity, in records. -/
def STier (g : TopGeom) : Nat := g.tierPages * g.C

/-- The domain of the model: at least two homes, the range plan partitions
the homes (`rho + I = k + e`), and a direct plan has one range. -/
def Valid (g : TopGeom) : Prop :=
  1 ≤ g.k + g.e ∧ g.rho + g.I = g.k + g.e ∧ (g.dfs = false → g.rho = 0)

instance (g : TopGeom) : Decidable g.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The d = 2 geometry whose `leavesOf`, `dfsTrace` and DFS capacities are the
top's: `2^((k + e - 1) + 1) = T` homes, ranges of `2^I` homes, pool `S_R`. -/
def toGeom (g : TopGeom) : Geom :=
  { C := g.C, k := g.k + g.e - 1, lo := g.I, poolSlots := g.SR }

/-- The finish's public capacities: one-page DFS leaves, the merge stash and
the output tier. -/
def caps (g : TopGeom) : Caps :=
  ⟨fun _ => none, some g.C, some g.SMerge, some g.STier⟩

theorem toGeom_homes (g : TopGeom) (h : g.Valid) : g.toGeom.homes = g.T := by
  unfold toGeom Geom.homes T Valid at *
  have : g.k + g.e - 1 + 1 = g.k + g.e := by omega
  simp [this]

theorem toGeom_depth (g : TopGeom) (h : g.Valid) : g.toGeom.depth = g.rho := by
  unfold toGeom Geom.depth Valid at *
  simp only
  omega

end TopGeom

/-- The finish's inputs. `cMain`: A's main after preparation, `T` buckets of
`C` lanes at their final homes. `carry`: the retained carry R, in its storage
order (page by page, lane order). `bMain`: B's main, `U` carry buckets of `C`
lanes. `bTier`: B's tier, in storage order. -/
structure TopInputs where
  cMain : List Bucket
  carry : List Rec
  bMain : List Bucket
  bTier : List Rec

namespace TopInputs

/-- A's records: C (bucket order, lane order), then R. -/
def aAll (inp : TopInputs) : List Rec := inp.cMain.flatMap Bucket.recs ++ inp.carry

/-- B's records: main, then tier. -/
def bAll (inp : TopInputs) : List Rec := inp.bMain.flatMap Bucket.recs ++ inp.bTier

/-- The newest version of every key of A ∪ B: all of B, and A's records whose
key B lacks. -/
def winners (inp : TopInputs) : List Rec :=
  inp.bAll ++ inp.aAll.filter fun r => !(inp.bAll.map Rec.key).contains r.key

/-- The resolved live set `W`: the winners that are not tombstones. Nothing
older than A and B is live, so a winning tombstone deletes its key. -/
def live (inp : TopInputs) : List Rec := inp.winners.filter fun r => !r.tomb

end TopInputs

/-- The home of a record under the top's current family: `w x mod T`. -/
def topHome (g : TopGeom) (w : LogicalKey → Nat) (r : Rec) : Nat := w r.key % g.T

/-- The way of a record: `⌊home / U⌋`. -/
def topWay (g : TopGeom) (w : LogicalKey → Nat) (r : Rec) : Nat := topHome g w r / g.U

/-- The coarse range of a record: `⌊home / 2^I⌋`. -/
def topRange (g : TopGeom) (w : LogicalKey → Nat) (r : Rec) : Nat := topHome g w r / 2 ^ g.I

/-- A tombstone flagged unshadowed (it shadows nothing older). -/
def earlyDrop (unsh : Rec → Bool) (r : Rec) : Bool := r.tomb && unsh r

/-! ### Phases 1 and 2: the pool and its DFS -/

/-- The swept A pool: R minus the keys of B's tier, minus R's flagged
tombstones, in R's storage order. -/
def topPool (unsh : Rec → Bool) (inp : TopInputs) : List Rec :=
  (inp.carry.filter fun r => !(inp.bTier.map Rec.key).contains r.key).filter
    fun r => !earlyDrop unsh r

/-- The direct copy of B's tier, minus its flagged tombstones. -/
def topTierCopy (unsh : Rec → Bool) (inp : TopInputs) : List Rec :=
  inp.bTier.filter fun r => !earlyDrop unsh r

/-- The DFS capacity tests: every node of the padded tree (none for a direct
plan). -/
def topDfsTrace (g : TopGeom) (w : LogicalKey → Nat) (pool : List Rec) : List (Test × Nat) :=
  if g.dfs then dfsTrace g.toGeom w pool else []

/-! ### Phase 3: the sweep -/

/-- Free the lanes of a bucket that hold tombstones. -/
def dropTombs (B : Bucket) : Bucket := B.map fun s => s.filter fun r => !r.tomb

/-- The resolution at destination `ci`, before its merge; `dk` are the keys of
B's direction-`q` records (tombstones included). (d) C[ci]'s tombstones;
(a) and (c) on the leaf candidates for `ci`; (b) and (c) on the B-tier
candidates for `ci`. -/
def topResolve (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat) (dk : List LogicalKey) (st : FinState) :
    FinState :=
  let R := ci / 2 ^ g.I
  let leaf := (st.leaves.getD R []).filter fun r =>
    !(topHome g w r == ci && (dk.contains r.key || r.tomb))
  let fc := st.bcopy.filter fun r => topHome g w r == ci
  let m := (dropTombs (st.main.getD ci [])).clear fun key => (fc.map Rec.key).contains key
  { st with
    main := st.main.set ci m
    leaves := st.leaves.set R leaf
    bcopy := st.bcopy.filter fun r => !(topHome g w r == ci && r.tomb) }

/-- The offers to destination `ci`: the leaf candidates for `ci`, then the
B-tier candidates for `ci`, each filling the lowest free lanes in order; the
placed candidates are consumed. -/
def topOffer (g : TopGeom) (w : LogicalKey → Nat) (ci : Nat) (st : FinState) : FinState :=
  let R := ci / 2 ^ g.I
  let leaf := st.leaves.getD R []
  let ca := leaf.filter fun r => topHome g w r == ci
  let fa := fill (st.main.getD ci []) ca
  let ga := (ca.take (ca.length - fa.2.length)).map Rec.key
  let cb := st.bcopy.filter fun r => topHome g w r == ci
  let fb := fill fa.1 cb
  let gb := (cb.take (cb.length - fb.2.length)).map Rec.key
  { st with
    main := st.main.set ci fb.1
    leaves := st.leaves.set R (leaf.filter fun r => !ga.contains r.key)
    bcopy := st.bcopy.filter fun r => !gb.contains r.key }

/-- Destination `ci = i + qU` of B bucket `Bi`: the resolution, the merge of B's
live direction-`q` records, and the offers. Returns the state and the
direction's sheds. -/
def topDest (g : TopGeom) (w : LogicalKey → Nat) (Bi : Bucket) (i q : Nat) (st : FinState) :
    FinState × List Rec :=
  let ci := i + q * g.U
  let dir := Bi.recs.filter fun r => topWay g w r == q
  let st := topResolve g w ci (dir.map Rec.key) st
  let f := fill (st.main.getD ci []) (dir.filter fun r => !r.tomb)
  (topOffer g w ci { st with main := st.main.set ci f.1 }, f.2)

/-- B bucket `i`: clear C's copies of B's main keys at all `D` destinations,
visit each way in order, then append the sheds (way order) to the merge stash
and test it. -/
def topBucket (g : TopGeom) (w : LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState) :
    FinState :=
  let Bi := bMain.getD i []
  let main := (List.range g.D).foldl (fun m q =>
    m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key => Bi.keys.contains key)) st.main
  let r := (List.range g.D).foldl (fun acc q =>
    let p := topDest g w Bi i q acc.1
    (p.1, acc.2 ++ p.2)) ({ st with main := main }, [])
  let ins := r.1.ins ++ r.2
  { r.1 with ins := ins, trace := r.1.trace ++ [(.insertion, ins.length)] }

/-- The sweep over B's `U` carry buckets, in ascending order. -/
def topSweep (g : TopGeom) (w : LogicalKey → Nat) (inp : TopInputs) (leaves : List (List Rec))
    (bcopy : List Rec) : FinState :=
  (List.range g.U).foldl (fun st i => topBucket g w inp.bMain i st)
    { main := inp.cMain, ins := [], leaves := leaves, bcopy := bcopy, trace := [] }

/-! ### The reference execution and the bounded finish -/

/-- Everything the reference top finish computes. -/
structure TopRun where
  pool : List Rec
  leaves : List (List Rec)
  fin : FinState
  output : Output
  /-- Every capacity test in execution order, with its tested quantity. -/
  trace : List (Test × Nat)

/-- The reference top finish: every phase with unbounded storage. It never
fails and is defined for every word assignment. -/
def topReference (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs) :
    TopRun :=
  let pool := topPool unsh inp
  let leaves := leavesOf g.toGeom w pool
  let fin := topSweep g w inp leaves (topTierCopy unsh inp)
  let dr := drain fin
  { pool, leaves, fin
    output := { main := fin.main.map dropTombs, tier := dr.1.map fun s => s.filter fun r => !r.tomb }
    trace := topDfsTrace g w pool ++ fin.trace ++ dr.2 }

/-- The bounded top finish: it fails at the first failing capacity test, and
otherwise publishes the reference output. -/
def topJob (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs) :
    Except Test Output :=
  let r := topReference g unsh w inp
  match firstFailure g.toGeom g.caps r.trace with
  | some t => .error t
  | none => .ok r.output

end RebuildBound.Model
