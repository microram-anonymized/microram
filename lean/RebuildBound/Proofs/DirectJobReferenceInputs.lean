import Mathlib.Data.List.GetD
import RebuildBound.Spec.DirectJobReferenceGeometry
import RebuildBound.Proofs.DirectJobReference
import RebuildBound.Proofs.DirectJobSelected

namespace RebuildBound
open Model Model.DirectJob Spec

private theorem selected_outputHomes (d : Nat) :
    (selectedDirectGeometry d).outputHomes = d * 16 := by
  simp [selectedDirectGeometry]
  split <;> rfl

private theorem selected_K (d : Nat) : (selectedDirectGeometry d).K = 4 := by
  simp [selectedDirectGeometry]
  split <;> rfl

private theorem empty_main (n c : Nat) :
    (List.replicate n (List.replicate c none)).flatMap Bucket.recs = [] := by
  induction n <;> simp_all [Bucket.recs]

private theorem selected_digit (d : Nat) : (selectedDirectGeometry d).digit = d := by
  simp [selectedDirectGeometry]
  split <;> rfl

theorem DirectJobReferenceInputShapeFor : DirectJobReferenceInputShapeFor_statement := by
  intro p s hc oldWord word currentWord st units fresh history hh
  obtain ⟨hC, hB, hHomes, hK, hd⟩ := hc
  have hs := DirectJobReferenceStep oldWord st ⟨p, word, units⟩ history hh
  have hn := (hs.1.map Rec.key).nodup_iff.mpr (DirectPrefixUnique _)
  dsimp only
  let next := referenceStep oldWord st ⟨p, word, units⟩
  constructor
  · exact hs.2.1.trans hHomes
  · simpa only [referenceSepInputs, hC] using hs.2.2.1
  · simp [referenceSepInputs]
  · intro B hb
    simp only [referenceSepInputs, List.mem_replicate] at hb
    rcases hb with ⟨_, rfl⟩
    simp
  · simp [referenceSepInputs, hB]
  · exact hn
  · simpa [referenceSepInputs, SInputs.bAll, empty_main] using
      DirectPrefixUnique (DirectMasks.records fresh)
  · intro i hi x hx
    have hi' : i < p.outputHomes := by simpa only [hHomes] using hi
    have hhome := hs.2.2.2 i hi' x hx
    simpa only [Geometry.home, SepGeom.oldHome, hK, hd] using hhome
  · intro i hi x hx
    change x ∈ Bucket.recs ((List.replicate s.U
      (List.replicate s.C none)).getD i []) at hx
    rw [List.getD_replicate _ hi] at hx
    simp [Bucket.recs] at hx

theorem DirectJobReferenceInputShape : DirectJobReferenceInputShape_statement := by
  intro d hlo hhi
  apply DirectJobReferenceInputShapeFor
  have hd := (DirectJobSelectedGeometry.2 (d + 1) (by omega) (by omega)).2.2.1
  refine ⟨rfl, rfl, ?_, selected_K d, ?_⟩
  · change (selectedDirectGeometry d).outputHomes = ((selectedDirectSep (d + 1)).d - 1) * 16
    rw [selected_outputHomes, hd, Nat.add_sub_cancel]
  · rw [selected_digit, hd, Nat.add_sub_cancel]

theorem DirectJobReferenceInputMatch : DirectJobReferenceInputMatch_statement := by
  intro s st units
  refine ⟨rfl, rfl, ?_⟩
  ext key
  simp only [List.mem_toFinset]
  simpa [referenceSepInputs, SInputs.bAll, ReferenceTable.inputs, Inputs.bRecords,
    empty_main] using DirectPrefixKeys (DirectMasks.records units) key

end RebuildBound
