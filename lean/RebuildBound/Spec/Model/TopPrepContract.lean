import RebuildBound.Spec.Model.TopPrep
import RebuildBound.Spec.Model.Contract

/-!
# The top preparation's input contract and reference events (trusted)

Core Lean only, like the model.

* `TPShape`: the structural contract of one top preparation (or
  initialization) for one assignment of starting buckets `pos`. A's main has
  `T` buckets of `C` lanes, A (main and old tier) is distinct by key, A's main
  records sit at their starting buckets, and every old-tier record names a
  starting bucket below `T`. For a preparation `pos x` is `x`'s old home under
  the previous top's family; for an initialization it is the scatter bucket.
  It holds on every outcome, reference inputs after an earlier failure
  included. Nothing about the old tier's fullness is needed.
* `TPTiersFit`: A's old tier fits its pool slot. Only on outcomes where the
  producer did not fail.
* **Reference events**, on the complete surviving population (A's records
  minus the flagged tombstones, `TPInputs.survivors`), defined whether or not
  the bounded job fails earlier:
  - `tpRawStageExcess j`: `Σ_v (X_{j,v} - C)₊` at the raw destinations after
    the stage that reads bit `j`, bits `≤ j` from the new word and the others
    from the starting bucket (at `j = k - 1` the raw destination is the home);
  - `tpRefCoarse R`: the coarse count of leaf `R`: the early list (A's old
    tier, then the stashes of bits `< I`), truncated to its public bound `P`
    in that bit-blind order, plus the sheds of bits `I … k - 2`;
  - `tpHomeExcess`: `Σ_v (X_v - C)₊` over the homes.
* `TPValidSchedule`: a permutation of the stage-by-stage schedule of the route
  (bits `0 … k - 2`) in which two operations of different stages that touch a
  common bucket run in stage order.
-/

namespace RebuildBound.Model

namespace TPInputs

/-- A's records: main (bucket order, lane order), then the old tier. -/
def aAll (inp : TPInputs) : List Rec := inp.aMain.flatMap Bucket.recs ++ inp.aTier

/-- The surviving population: A's records minus the flagged tombstones. -/
def survivors (unsh : Rec → Bool) (inp : TPInputs) : List Rec :=
  inp.aAll.filter fun r => !flagged unsh r

end TPInputs

/-- The structural input contract of one top preparation or initialization, for
one assignment of starting buckets `pos`. -/
structure TPShape (g : TPGeom) (pos : LogicalKey → Nat) (inp : TPInputs) : Prop where
  /-- A's main has `T` buckets of `C` lanes. -/
  aLen : inp.aMain.length = g.T
  aLanes : ∀ B ∈ inp.aMain, B.length = g.C
  /-- A's main and old tier together are distinct by key. -/
  aNodup : (inp.aAll.map Rec.key).Nodup
  /-- A's main records sit at their starting buckets. -/
  aHome : ∀ i < g.T, ∀ r ∈ (inp.aMain.getD i []).recs, pos r.key = i
  /-- Every old-tier record has a starting bucket below `T`. -/
  tierHome : ∀ r ∈ inp.aTier, pos r.key < g.T

/-- A's old tier fits its pool slot. -/
def TPTiersFit (g : TPGeom) (inp : TPInputs) : Prop :=
  inp.aTier.length ≤ g.aTierPages * g.C

/-- The number of records of `L` homed at `v`. -/
def tpHomeCount (g : TPGeom) (w : LogicalKey → Nat) (L : List Rec) (v : Nat) : Nat :=
  L.countP fun r => tpHome g w r == v

/-- The complete-home excess `Σ_v (X_v - C)₊` of the surviving population. -/
def tpHomeExcess (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs) : Nat :=
  ((List.range g.T).map fun v => tpHomeCount g w (inp.survivors unsh) v - g.C).sum

/-- The raw destination of key `x` after the stage that reads bit `j`: bits `≤ j`
from its new word, the others from its starting bucket `pos x`. -/
def tpRawDest (pos w : LogicalKey → Nat) (j : Nat) (x : LogicalKey) : Nat :=
  2 ^ (j + 1) * (pos x / 2 ^ (j + 1)) + w x % 2 ^ (j + 1)

/-- The raw excess `Σ_v (X_{j,v} - C)₊` of the surviving population at its raw
destinations after the stage that reads bit `j`. -/
def tpRawStageExcess (g : TPGeom) (unsh : Rec → Bool) (pos w : LogicalKey → Nat) (inp : TPInputs)
    (j : Nat) : Nat :=
  ((List.range g.T).map fun v =>
    ((inp.survivors unsh).countP fun r => tpRawDest pos w j r.key == v) - g.C).sum

/-- The public bound `P = T_A + I S` of the early list, in records: A's old tier
slot and the stashes of bits `< I`. -/
def TPGeom.earlyCap (g : TPGeom) : Nat := g.aTierPages * g.C + g.I * (g.stashPages * g.C)

/-- The early list of a run in its bit-blind order: A's old tier minus its flagged
tombstones, then the stashes of bits `0, …, I - 1` (append order). -/
def tpEarlyList (g : TPGeom) (unsh : Rec → Bool) (r : TPRun) (inp : TPInputs) : List Rec :=
  inp.aTier.filter (fun x => !flagged unsh x) ++ (r.route.stash.take g.I).flatten

/-- The sheds of the stages that read bits `I, …, k - 2`. -/
def tpLateSheds (g : TPGeom) (r : TPRun) : List Rec :=
  ((r.route.stash.take (g.k - 1)).drop g.I).flatten

/-- The reference coarse count of leaf `R`: the early list truncated to `P`, plus
the later sheds, counted in leaf `R`. -/
def tpRefCoarse (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (r : TPRun) (inp : TPInputs)
    (P R : Nat) : Nat :=
  ((tpEarlyList g unsh r inp).take P ++ tpLateSheds g r).countP fun x => tpRange g w x == R

/-- The pair operations of the stage that reads bit `j`: `(j, i)` for every `i`
with bit `j` clear, in ascending `i`. -/
def tpStageOps (g : TPGeom) (j : Nat) : List (Nat × Nat) :=
  ((List.range g.T).filter fun i => !i.testBit j).map fun i => (j, i)

/-- A schedule of the route's pair operations is valid when it runs each
operation of the stage-by-stage schedule once, and two operations of different
stages that touch a common bucket run in stage order. -/
def TPValidSchedule (g : TPGeom) (ops : List (Nat × Nat)) : Prop :=
  List.Perm ops g.canonicalOps ∧
  ∀ a ∈ ops, ∀ b ∈ ops, a.1 < b.1 →
    (a.2 = b.2 ∨ a.2 = b.2 + 2 ^ b.1 ∨ a.2 + 2 ^ a.1 = b.2 ∨ a.2 + 2 ^ a.1 = b.2 + 2 ^ b.1) →
    ops.idxOf a < ops.idxOf b

end RebuildBound.Model
