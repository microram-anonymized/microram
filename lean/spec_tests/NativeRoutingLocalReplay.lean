import RebuildBound.Proofs.NativeRoutingLocalReplay

/-! Concrete sparse routing regressions distinguish real/dummy addresses,
blind accesses, absent plan entries and same-frame repeated logical keys. -/
namespace RebuildBound.NativeRoutingLocalReplayTests
open Model Model.Hierarchy Model.DirectJob Model.Online Spec NativeRoutingActual NativeRoutingLocalReplay

private def cfg : Config := ⟨[4], 2, 8, 32, 128, false⟩
private def unit : OnlineGeom := ⟨64, 1⟩
private def keyA : LogicalKey := [0]
private def keyB : LogicalKey := [1]
private def recordA : Rec := ⟨keyA, 7, false⟩
private def tombA : Rec := ⟨keyA, 0, true⟩
private def recordB : Rec := ⟨keyB, 9, false⟩
private def plan : Schedule := fun _ => ⟨0, [(1, 1), (2, 0)]⟩
private def run : OnlineBatch.BatchRun := ⟨[.probe recordA], [], fun _ => false⟩
private def blind : OnlineBatch.BatchRun := ⟨[.blind recordA], [], fun _ => false⟩
private def denseRun : OnlineBatch.BatchRun := ⟨[.blind recordA, .probe recordA], [], fun _ => false⟩
private def repeated : OnlineBatch.BatchRun := ⟨[.batch [recordA, recordA]], [], fun _ => false⟩
private def hit : Output := ⟨[], [some tombA, none]⟩

/-- The current entry is real until an earlier table contains the key. -/
example : realFromTables cfg unit run plan [hit, emptyOutput] 0 0 = true ∧
    realFromTables cfg unit run plan [hit, emptyOutput] 0 1 = false := by
  decide +kernel

/-- Tombstones suppress subsequent real reads just as retained live values do. -/
example (tape : IdealKey.Tape) :
    (ReadTree.reads tape (entryProgram cfg unit run plan [hit, emptyOutput] 0 1)).map Prod.fst =
      [.inr (0, 1)] := by
  rfl

/-- An unrelated key in the previous table leaves the later read real. -/
example (tape : IdealKey.Tape) :
    (ReadTree.reads tape (entryProgram cfg unit run plan [⟨[], [some recordB]⟩, emptyOutput] 0 1)).map Prod.fst =
      [.inl ((2, 0), keyA)] := by
  rfl

/-- The duplicate lane uses dummy coordinates even when every table is empty. -/
example (tape : IdealKey.Tape) :
    (ReadTree.reads tape (entryProgram cfg unit repeated plan [emptyOutput, emptyOutput] 1 0)).map Prod.fst =
      [.inr (1, 0)] := by
  rfl

/-- A hit in the current requester prefix suppresses the first table read. -/
example (tape : IdealKey.Tape) :
    (ReadTree.reads tape (entryProgram cfg unit denseRun plan [emptyOutput, emptyOutput] 1 0)).map Prod.fst =
      [.inr (1, 0)] := by
  rfl

/-- Neither blind lanes nor missing slots reconstruct tables or read addresses. -/
example (sh : Shapes) (tape : IdealKey.Tape) (schedule : Schedule) (m : Nat) :
    ReadTree.reads tape (laneProgram cfg sh unit blind schedule 0 m) = [] ∧
      ReadTree.reads tape (laneProgram cfg sh unit run schedule 7 m) = [] := by
  constructor <;> rfl

/-- A missing entry has no query even on a probing lane. -/
example (tape : IdealKey.Tape) :
    ReadTree.reads tape (entryProgram cfg unit run plan [emptyOutput, emptyOutput] 0 2) = [] := by
  rfl

/-- Zero issued operations do not force a horizon-wide initialization read.
Native initialization failures are a separate pending diagnostic obligation. -/
example (sh : Shapes) (tape : IdealKey.Tape) (initial : List Rec) :
    ReadTree.reads tape (NativeRoutingLocalReplay.readProgram { cfg with initialized := true } sh unit plan
      (⟨[], initial, fun _ => false, fun _ _ => recordA⟩ : Model.Adaptive.AdaptiveRun 2)) = [] := by
  rfl

end RebuildBound.NativeRoutingLocalReplayTests
