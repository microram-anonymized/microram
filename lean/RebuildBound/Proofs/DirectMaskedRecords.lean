import RebuildBound.Spec.DirectMaskedRecords
import RebuildBound.Proofs.DirectMasks
import RebuildBound.Proofs.DirectRecords

namespace RebuildBound
open Model Model.DirectMaskedRecords

theorem DirectMaskedRecordsIndexFlatten (start : Nat) (sizes : List Nat) :
    (indexChunks start sizes).flatten = List.range' start sizes.sum := by
  induction sizes generalizing start with
  | nil => simp [indexChunks]
  | cons n ns ih => simp [indexChunks, ih]

theorem DirectMaskedRecordsIndexLengths (start : Nat) (sizes : List Nat) :
    (indexChunks start sizes).map List.length = sizes := by
  induction sizes generalizing start with
  | nil => rfl
  | cons n ns ih => simp [indexChunks, ih]

theorem DirectMaskedRecordsValid : Spec.DirectMaskedRecordsValid_statement := by
  intro compare units he hu
  unfold DirectRecords.ValidChunks chunks
  rw [DirectMaskedRecordsIndexFlatten]
  have hw := congrArg List.length (DirectMasksWinners compare units he hu)
  rw [← List.range_eq_range']
  apply congrArg List.range
  simpa [DirectMasks.records, List.length_flatMap, DirectRecords.source] using hw

theorem DirectMaskedRecordsRestore : Spec.DirectMaskedRecordsRestore_statement := by
  intro compare units he hu
  refine List.eq_iff_flatten_eq.mpr ⟨?_, ?_⟩
  · rw [← List.map_flatten]
    rw [DirectMaskedRecordsValid compare units he hu, DirectRecordsSource]
    exact (DirectMasksWinners compare units he hu).symm
  · simp only [List.map_map, List.length_map, Function.comp_def, chunks]
    exact DirectMaskedRecordsIndexLengths _ _

theorem DirectMaskedRecordsFailure : Spec.DirectMaskedRecordsFailure_statement := by
  intro compare digit output U word units hU he hu
  exact DirectRecordsFailure digit output U word _ _ hU
    (DirectMaskedRecordsValid compare units he hu)

theorem DirectMaskedRecordsSuccess : Spec.DirectMaskedRecordsSuccess_statement := by
  intro compare digit output U word units main tier hU he hu hs
  exact DirectRecordsSuccess digit output U word _ _ main tier hU
    (DirectMaskedRecordsValid compare units he hu) hs

theorem DirectMaskedRecordsMain : Spec.DirectMaskedRecordsMain_statement := by
  intro compare digit output U word units main tier hU he hu hs
  exact DirectRecordsMain digit output U word _ _ main tier hU
    (DirectMaskedRecordsValid compare units he hu) hs

theorem DirectMaskedRecordsRechunk : Spec.DirectMaskedRecordsRechunk_statement := by
  intro compare digit output U word first second he hf hs hr
  unfold build
  rw [hr]
  apply DirectRecordsRechunk
  rw [DirectMaskedRecordsValid compare first he hf,
    DirectMaskedRecordsValid compare second he hs, hr]

-- Cleared and empty units retain their chunk positions; tombstones survive.
private def old : Rec := ⟨LogicalKey.ofNat 7, 10, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 7, 20, true⟩
private def other : Rec := ⟨LogicalKey.ofNat 8, 30, false⟩
private def exactCompare : DirectMasks.Comparison := fun a b => a == b
private def sample : List Bucket :=
  [[some old, none], [], [none, some other], [some tomb]]
example : DirectMasks.ExactComparison exactCompare := by intro a b; rfl
example : ∀ unit ∈ sample, (unit.recs.map Rec.key).Nodup := by decide +kernel
example : chunks (DirectMasks.run exactCompare [] sample) = [[], [], [0], [1]] := by
  decide +kernel
example : build exactCompare 1 0 1 (fun _ => 0) sample =
    some ([[other, tomb]], []) := by decide +kernel
-- Omitting either premise can break the constructed index enumeration.
example : ¬ DirectRecords.ValidChunks [old, tomb]
    (chunks (DirectMasks.run exactCompare [] [[some old, some tomb]])) := by
  unfold DirectRecords.ValidChunks
  decide +kernel
example : ¬ DirectRecords.ValidChunks [other, tomb]
    (chunks (DirectMasks.run (fun _ _ => true) [] [[some other], [some tomb]])) := by
  unfold DirectRecords.ValidChunks
  decide +kernel
-- Distributed excess: 97 records at each of two homes leave 66 residuals.
-- Digit one may use all 66 output slots; another digit has only 64 slots.
private def distributed : List Bucket :=
  [(List.range 194).map (fun k => some (⟨LogicalKey.ofNat k, k, false⟩ : Rec))]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
example : (build exactCompare 1 66 2 LogicalKey.toNat distributed).map (fun p => p.2.length) =
    some 66 := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
example : build exactCompare 2 66 2 LogicalKey.toNat distributed = none := by decide +kernel

end RebuildBound
