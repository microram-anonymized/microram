import RebuildBound.Spec.DirectJobAdoption
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.DirectJobFailure

/-! Geometry-independent publication and adoption facts. Selected numerical
certificates are intentionally absent from this import closure. -/

namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobEmptyInput : DirectJobEmptyInput_statement := by
  intro g oldWord units hd hu
  simpa [Inputs.Valid, adopt, emptyOutput, Inputs.aRecords, Bucket.recs, hd] using hu

theorem DirectJobAdoption : DirectJobAdoption_statement := by
  intro g next oldWord word inp out units hp hK hd hcap hu
  obtain ⟨hg, _, hperm, hnodup, hlen, hwidth, htier, hhome, _⟩ :=
    DirectJobPublication g oldWord word inp out hp
  have hhomes : (next.digit - 1) * next.U = g.outputHomes := by
    rw [hd, Nat.add_sub_cancel, Geometry.U, hK]
    exact hg.2.2.1.symm
  refine ⟨?_, hwidth, ?_, hnodup, hu, ?_⟩
  · exact hlen.trans hhomes.symm
  · change (Bucket.recs out.tier).length ≤ next.aTierCapacity
    exact (List.length_filterMap_le _ _).trans (htier ▸ hcap)
  · change ∀ ib ∈ out.main.zipIdx, ∀ x ∈ ib.1.recs,
      digitHome next.K (next.digit - 1) (word x.key) = ib.2
    rw [List.forall_mem_zipIdx']
    intro i hi x hx
    have hi' : i < g.outputHomes := hlen ▸ hi
    have hh := hhome i hi' x (by rw [List.getD_eq_getElem _ _ hi]; exact hx)
    simpa [Geometry.home, hK, hd] using hh

namespace DirectJobAdoptionLemmas

theorem no_rejection (g : Geometry) (oldWord word : Model.LogicalKey → Nat) (inp : DirectJob.Inputs)
    (hg : g.Valid) (hi : inp.Valid g oldWord) (reason : Rejection) :
    runJob g oldWord word inp ≠ .rejected reason := by
  rw [DirectJobSimulation]
  simp only [hg, hi, not_true_eq_false, ite_false]
  cases firstFailure (analyticalJob g word inp).trace <;> simp

end DirectJobAdoptionLemmas
end RebuildBound
