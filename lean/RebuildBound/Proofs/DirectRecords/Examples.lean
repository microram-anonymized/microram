import RebuildBound.Proofs.DirectRecords

/-! Executable witnesses and controls for the logical record-restoration
contract. These do not claim correspondence with native lane addresses. -/
namespace RebuildBound.DirectRecordsExamples
open Model Model.DirectRecords

private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def fresh : Rec := ⟨LogicalKey.ofNat 7, 30, false⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 40, false⟩
private def third : Rec := ⟨LogicalKey.ofNat 9, 50, true⟩

-- Complete payloads survive deduplication and stable home grouping.
example : build 1 0 2 LogicalKey.toNat [old, other, tomb, third] [[0], [1, 2]] =
    some ([[other], [tomb, third]], []) := by decide +kernel
example : build 1 0 1 LogicalKey.toNat [old, tomb, fresh] [[0]] =
    some ([[fresh]], []) := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 7) [old, other, tomb] = some tomb := by decide +kernel
example : DirectPrefix.latest (LogicalKey.ofNat 99) [old, other, tomb] = none := by decide +kernel

-- Empty chunks do not alter the logical result.
example : ValidChunks [old, other, tomb] [[], [0], [], [1], []] := by unfold ValidChunks; decide +kernel
example : build 1 0 2 LogicalKey.toNat [old, other, tomb] [[], [0], [], [1], []] =
    build 1 0 2 LogicalKey.toNat [old, other, tomb] [[0, 1]] := by
  apply DirectRecordsRechunk
  rfl
example : build 1 0 1 LogicalKey.toNat [] [] = some ([[]], []) := by decide +kernel

private def population (n : Nat) : List Rec :=
  (List.range n).map (fun key => ⟨LogicalKey.ofNat key, key + 1, key % 2 == 0⟩)

-- Excess 64 is accepted above digit one; 65 is rejected. Digit one can use
-- a larger configured output tier, preserving the exact overflow payloads.
example : (build 2 128 1 LogicalKey.toNat (population 128) [List.range 128]).isSome = true := by decide +kernel
example : build 2 128 1 LogicalKey.toNat (population 129) [List.range 129] = none := by decide +kernel
example : build 1 128 1 LogicalKey.toNat (population 130) [List.range 130] =
    some ([(population 130).take 64], (population 130).drop 64) := by decide +kernel

-- A malformed index can restore the default record: valid chunking is essential.
example : ¬ ValidChunks [old] [[1]] := by unfold ValidChunks; decide +kernel
example : build 1 0 1 LogicalKey.toNat [old] [[1]] = some ([[default]], []) := by decide +kernel
example : ¬ ValidChunks [old, other] [[0, 0]] := by unfold ValidChunks; decide +kernel
example : ¬ ValidChunks [old, other] [[1, 0]] := by unfold ValidChunks; decide +kernel

-- Without positive U, grouped excess can be zero while the drain fails.
example : ValidChunks [old] [[0]] := by unfold ValidChunks; decide +kernel
example : DirectB.excess 64 (DirectGroups.groups 0 (home [old] LogicalKey.toNat 0) (source [old])) = 0 :=
  by decide +kernel
example : build 1 0 0 LogicalKey.toNat [old] [[0]] = none := by decide +kernel

end RebuildBound.DirectRecordsExamples
