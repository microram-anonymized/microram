import RebuildBound.Proofs.NativeMatchDenseTrace
import RebuildBound.Proofs.NativeMatchDenseTrace.Physical

set_option maxRecDepth 4000
set_option maxHeartbeats 400000

namespace RebuildBound.NativeMatchDenseTraceTests
open Model Spec Spec.NativeMatch Spec.NativeMatch.Lanes Spec.NativeMatchTrace Spec.NativeMatchPhysical

def tomb : Rec := ⟨[1], 17, true⟩
def other : Rec := ⟨[2], 29, false⟩
def single : Page := (fun _ => tomb, 1)

/-- A genuine stored zero still selects the complete tombstone record. -/
example : denseRecord (fun _ => 0) single [1] true = some tomb := by decide +kernel

/-- Deferred duplicate requests OR the same physical bit only once. -/
example : denseDeferredMask (fun _ => 0) single [[1], [1]] = 1 := by decide +kernel

/-- Zero activity cannot clear or return a stale occupied lane. -/
example : denseMask (fun _ => 0) single [1] false = 0 ∧
    denseRecord (fun _ => 0) single [1] false = none := by decide +kernel

/-- Physical reconstruction retains an interior hole and pads its suffix. -/
example : (((bucketPages 1 [some tomb, none, some other]).flatMap Page.bucket).take 5) =
    [some tomb, none, some other, none, none] := by decide +kernel

/-- Complete stored equality can select another logical key only on the
explicit normalization-collision branch. -/
example : storedLatest (fun _ => 0) [1] [tomb, other] = some other ∧
    listNormalizeBad (fun _ => 0) [tomb, other] [1] := by
  constructor
  · decide +kernel
  · exact ⟨other, by simp, by decide, rfl⟩

/-- A selected tombstone forces every later table address to be a dummy. -/
example : Probe.cascadeWith (fun _ _ => some tomb) (fun c => c.1)
    (fun i c => 100 + i + c.1) [(3, 1), (5, 2), (7, 3)] none 0 =
    (⟨some tomb, [3, 106, 109]⟩ : Probe.Result) := by decide +kernel

/-- Retiring and republishing a physical slot keeps one occupancy; attempting
to publish into the same retained slot leaves the old snapshot unchanged. -/
def t0 : LiveTable 2 := ⟨0, (1, 1), 100, true⟩
def t1 : LiveTable 2 := ⟨0, (1, 2), 200, true⟩
example : publications [⟨[], some t0⟩, ⟨[], some t1⟩] = [t0] := by decide +kernel
example : publications [⟨[], some t0⟩, ⟨[0], some t1⟩] = [t1] := by decide +kernel

def t2 : LiveTable 2 := ⟨1, (2, 7), 300, true⟩
example : hashedEntries [t0, t2] = [(2, 7), (1, 1)] := by
  simp [hashedEntries, composeEntries, sourceEntries, t0, t2, entryBefore, List.mergeSort]
example : (composeEntries [t0, t2]).map (fun e => (e.table.coordinate, e.tier)) =
    [((2, 7), false), ((2, 7), true), ((1, 1), false), ((1, 1), true)] := by
  simp [composeEntries, sourceEntries, t0, t2, entryBefore, List.mergeSort]

/-- Two full prefixes, one partial and the current unit exhaust the q=2,
r0=2 ring envelope; a third outstanding prefix is rejected before iteration. -/
example : fillDenseUnits 2 2 4 13 = some [8, 9, 10, 11, 12, 13] := by decide +kernel
example : fillDenseUnits 2 2 3 13 = none := by decide +kernel

end RebuildBound.NativeMatchDenseTraceTests
