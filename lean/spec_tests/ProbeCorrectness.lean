import RebuildBound.Spec.Model.Probe
import RebuildBound.Spec.DirectJobSelected
import RebuildBound.Proofs.HierarchyInvariant.Low

/-! Small kernel-checked semantic controls. No selected-size table is evaluated. -/
namespace ProbeCorrectnessTests
open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open RebuildBound.Model.Probe RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

private def old : Rec := ⟨LogicalKey.ofNat (7), 10, false⟩
private def fresh : Rec := ⟨LogicalKey.ofNat (7), 20, false⟩
private def dead : Rec := ⟨LogicalKey.ofNat (7), 30, true⟩
private def other : Rec := ⟨LogicalKey.ofNat (8), 40, false⟩
private def empty : Output := ⟨[[], []], []⟩
private def mainHit : Output := ⟨[[some old], []], []⟩
private def tierHit : Output := ⟨[[], []], [some fresh]⟩
private def deletion : Output := ⟨[[some dead], []], []⟩
private def laterDummyHit : Output := ⟨[[], [some old]], []⟩
private def coords : List (Nat × Nat) := [(1, 1), (2, 1)]
private def go (first second : Output) (initial : Option Rec := none) : Result :=
  cascade (LogicalKey.ofNat 7) (fun c => if c.1 = 1 then first else second) (fun _ => 0)
    (fun _ _ => 1) coords initial 0

example : latestValue (LogicalKey.ofNat 7) [old, fresh] = some 20 := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) [old, dead] = none := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) [old, dead, fresh] = some 20 := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) [other] = none := by decide +kernel
-- Choosing the oldest dense record would return 10.
example : (DirectPrefix.latest (LogicalKey.ofNat 7) [old, fresh]) ≠ some old := by decide +kernel
example : (go mainHit tierHit).found = some old := by decide +kernel
example : (go empty tierHit).found = some fresh := by decide +kernel
example : (go empty empty).found = none := by decide +kernel
example : (go empty tierHit).addresses = [0, 0] := by decide +kernel
-- A tombstone remains found, and a queried key in a later dummy bucket cannot replace it.
example : go deletion laterDummyHit = ⟨some dead, [0, 1]⟩ := by decide +kernel
example : go mainHit laterDummyHit (some fresh) = ⟨some fresh, [1, 1]⟩ := by decide +kernel
example : decode (go deletion tierHit).found = none := by decide +kernel
-- Continuing past the tombstone would incorrectly return 20.
example : decode (go deletion tierHit).found ≠ some 20 := by decide +kernel

private def cfg : Config :=
  { fanouts := [2], carry1 := 1, topDigit := 1, load := 2, horizon := 32,
    initialized := false }
private def geom : OnlineGeom := ⟨2, 1⟩
private def densePlan : Schedule := fun _ => ⟨0, []⟩
private def run : OnlineRun := ⟨[.probe old, .probe other, .probe fresh, .probe dead,
  .probe fresh, .probe old], [], fun _ => false⟩
-- Repeated key in the current unit and across frozen units; erase then reinsertion.
example : latestValue (LogicalKey.ofNat 7) (denseRecords cfg geom run densePlan 3) = some 20 := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) (denseRecords cfg geom run densePlan 4) = none := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) (denseRecords cfg geom run densePlan 5) = some 20 := by decide +kernel

private def batchRun : OnlineBatch.BatchRun :=
  ⟨[.probe other, .batch [old, dead, fresh]], [], fun _ => false⟩
-- The superseded key crosses a unit and a prefix boundary. Only its final lane is real.
example : (OnlineBatch.stateAt geom batchRun 2).frozen.map Bucket.recs =
    [[other], [fresh]] := by decide +kernel
example : earlier batchRun ⟨1, 2, fresh, true⟩ = [old, dead] := by decide +kernel
example : latestValue (LogicalKey.ofNat 7) (earlier batchRun ⟨1, 2, fresh, true⟩) = none := by decide +kernel
example : OnlineBatch.duplicate batchRun ⟨1, 2, fresh, true⟩ = true := by decide +kernel
example : go mainHit tierHit (DirectPrefix.latest (LogicalKey.ofNat 7) (earlier batchRun ⟨1, 2, fresh, true⟩)) =
    ⟨some dead, [1, 1]⟩ := by decide +kernel

-- A tiny hierarchy: digit reset forwards the completed low table to the top.
private def direct (d : Nat) : DirectJob.Geometry :=
  { K := 0, digit := d, outputHomes := d, outputCapacity := 0,
    aTierCapacity := 0, routeCapacity := 0, radixCapacity := 0,
    insertionCapacity := 0, copyCapacity := 0, ranges := .direct }
private def top : TopGeom :=
  { C := 64, k := 1, e := 0, rho := 0, I := 1, dfs := false,
    rPages := 1, bPages := 1, mergePages := 1, tierPages := 1 }
private def prep : TPGeom :=
  { C := 64, k := 1, stashPages := 1, aTierPages := 1, drainPages := 1,
    rangeBits := 0, I := 1, dfs := false }
private def shapes : Shapes := ⟨direct, fun _ _ => selectedDirectSep 2, top, prep, prep⟩
private def words : Words := fun _ _ _ => 0
private def trace : Trace :=
  ⟨fun i => if i = 0 then [[some old]] else if i = 1 then [[some dead]]
    else [[some fresh]], [], fun _ => false⟩

private theorem low_zero : table cfg shapes trace words 1 0 = DirectJob.emptyOutput := by
  rw [table_base (Or.inr (Or.inr (by decide +kernel))), base_low (by decide +kernel)]

private theorem low_one : table cfg shapes trace words 1 1 =
    step cfg shapes trace words 1 1 DirectJob.emptyOutput DirectJob.emptyOutput := by
  rw [table_step (by decide +kernel) (by decide +kernel) (by decide +kernel), low_zero]
  rfl

private theorem low_two : table cfg shapes trace words 1 2 =
    step cfg shapes trace words 1 2
      (step cfg shapes trace words 1 1 DirectJob.emptyOutput DirectJob.emptyOutput)
      DirectJob.emptyOutput := by
  rw [table_step (by decide +kernel) (by decide +kernel) (by decide +kernel), low_one]
  rfl

private theorem low_three : table cfg shapes trace words 1 3 =
    levelOneStep (direct 1) (jobWord cfg words 1 2) (jobWord cfg words 1 3)
      DirectJob.emptyOutput (trace.units 2) := by
  rw [table_step (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

private theorem top_one : table cfg shapes trace words 2 1 =
    step cfg shapes trace words 2 1 (base cfg shapes trace words 2)
      (step cfg shapes trace words 1 2
        (step cfg shapes trace words 1 1 DirectJob.emptyOutput DirectJob.emptyOutput)
        DirectJob.emptyOutput) := by
  rw [table_step (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rw [table_base (v := 0) (Or.inr (Or.inr (by decide +kernel)))]
  change step cfg shapes trace words 2 1 _ (table cfg shapes trace words 1 2) = _
  rw [low_two]

set_option maxRecDepth 20000 in
example : scan (LogicalKey.ofNat 7) (table cfg shapes trace words 1 2) 0 = some dead := by
  rw [low_two]
  decide +kernel
set_option maxRecDepth 20000 in
example : (table cfg shapes trace words 2 1).records = [] := by
  rw [top_one]
  decide +kernel
set_option maxRecDepth 20000 in
example : decode (hierarchy cfg shapes trace words (fun _ => 1) (LogicalKey.ofNat 7) [(2, 1)] none).found =
    none := by
  simp only [hierarchy, cascade, cascadeWith]
  rw [top_one]
  decide +kernel
set_option maxRecDepth 20000 in
example : decode (hierarchy cfg shapes trace words (fun _ => 1) (LogicalKey.ofNat 7) [(1, 3), (2, 1)] none).found =
    some 20 := by
  simp only [hierarchy, cascade, cascadeWith]
  rw [low_three, top_one]
  decide +kernel

-- The scalar wrapper excludes its own fresh insertion after a preceding erase.
example : decode (scalar cfg shapes geom run densePlan words (fun _ _ => 1) 4).found =
    none := by decide +kernel

-- The actual batch wrapper forwards a live value, then a tombstone, from earlier lanes.
example : decode (batch cfg shapes geom batchRun densePlan words (fun _ _ => 1) 2).found =
    some 10 := by decide +kernel
example : decode (batch cfg shapes geom batchRun densePlan words (fun _ _ => 1) 3).found =
    none := by decide +kernel

-- Initialization is queried before the first operation.
private def initialized : Config := { cfg with initialized := true }
private def initTrace : Trace := ⟨fun _ => [], [old], fun _ => false⟩
set_option maxRecDepth 20000 in
example : decode (hierarchy initialized shapes initTrace words (fun _ => 1) (LogicalKey.ofNat 7) [(2, 1)] none).found =
    some 10 := by
  simp only [hierarchy, cascade, cascadeWith]
  rw [table_base (Or.inr (Or.inr (by decide +kernel)))]
  decide +kernel

-- 65 distinct records routed to one 64-lane home overflow a zero-capacity tier.
private def overflowUnits : List Bucket :=
  [(List.range 65).map fun k => some (⟨LogicalKey.ofNat (k), k + 100, false⟩ : Rec)]
set_option maxRecDepth 20000 in
example : (match DirectJob.runJob (direct 1) (fun _ => 0) (fun _ => 0)
    (DirectJob.adopt DirectJob.emptyOutput overflowUnits) with
    | .failed _ => true
    | _ => false) = true := by decide +kernel
set_option maxRecDepth 20000 in
example : scan (LogicalKey.ofNat 64) (levelOneStep (direct 1) (fun _ => 0) (fun _ => 0)
    DirectJob.emptyOutput overflowUnits) 0 = some ⟨LogicalKey.ofNat (64), 164, false⟩ := by decide +kernel

end ProbeCorrectnessTests
