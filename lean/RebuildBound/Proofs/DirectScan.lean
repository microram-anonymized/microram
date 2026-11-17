import RebuildBound.Spec.DirectScan
import Mathlib.Tactic
namespace RebuildBound
open Model.DirectScan

theorem DirectScanSelected : Spec.DirectScanSelected_statement := by
  intro α cap chunks
  induction chunks generalizing cap with
  | nil => simp [run]
  | cons xs chunks ih => simp [run, ih, List.take_append]

theorem DirectScanRejected : Spec.DirectScanRejected_statement := by
  intro α cap chunks
  induction chunks generalizing cap with
  | nil => simp [run]
  | cons xs chunks ih => simp [run, ih, List.drop_append]

theorem DirectScanRemaining : Spec.DirectScanRemaining_statement := by
  intro α cap chunks
  induction chunks generalizing cap with
  | nil => simp [run]
  | cons xs chunks ih => simp [run, ih, Nat.sub_sub]

theorem DirectScanResume : Spec.DirectScanResume_statement := by
  intro α cap front back
  induction front generalizing cap with
  | nil => simp [run]
  | cons xs front ih => simp [run, ih, List.append_assoc]
theorem DirectScanCandidates : Spec.DirectScanCandidates_statement := by
  intro home h chunks
  exact List.filter_flatten.symm

theorem DirectScanHomeSelected : Spec.DirectScanHomeSelected_statement := by
  intro cap home h chunks
  rw [DirectScanSelected, DirectScanCandidates]

theorem DirectScanHomeRejected : Spec.DirectScanHomeRejected_statement := by
  intro cap home h chunks
  rw [DirectScanRejected, DirectScanCandidates]

-- Crossing capacity inside a chunk, including a later empty chunk.
example : run 3 [[0, 1], [2, 3, 4], [], [5]] =
    (⟨0, [0, 1, 2], [3, 4, 5]⟩ : Result Nat) := by decide
example : run 0 [[0, 1], [2]] =
    (⟨0, [], [0, 1, 2]⟩ : Result Nat) := by decide
end RebuildBound
