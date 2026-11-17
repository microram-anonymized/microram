import RebuildBound.Spec.DirectJobAdoption
import RebuildBound.Proofs.DirectJobCycleGeometry.Chain
import RebuildBound.Proofs.DirectJobUniformCycle.Congr
import RebuildBound.Proofs.DirectJobSelected
import Mathlib.Data.List.Enum

namespace RebuildBound
open Model Model.DirectJob Spec

theorem DirectJobSelectedAdoption : DirectJobSelectedAdoption_statement := by
  intro d hd hlast oldWord word inp out units hp hu
  have hnext : (selectedDirectGeometry (d + 1)).Valid :=
    DirectJobSelectedGeometry.1 (d + 1) (by omega) (by omega)
  refine ⟨hnext, DirectJobAdoption _ _ oldWord word inp out units hp ?_ ?_ ?_ hu⟩
  all_goals
    unfold selectedDirectGeometry
    split_ifs <;> simp_all

namespace DirectJobAdoptionLemmas


theorem selected_cycle_geometry (n : Nat) (hn : n ≤ 8) :
    DirectCycleGeometry selectedDirectGeometry n := by
  refine ⟨fun _ => rfl, fun d hd hdn => DirectJobSelectedGeometry.1 d hd (by omega), ?_⟩
  intro d hd hdn
  unfold selectedDirectGeometry
  split_ifs <;> simp_all

theorem chain (steps : List ((Model.LogicalKey → Nat) × List Bucket)) (first : Nat)
    (oldWord : Model.LogicalKey → Nat) (out : Output) (hfirst : 1 ≤ first)
    (hcount : first + steps.length ≤ 9)
    (hu : ∀ step ∈ steps, ∀ u ∈ step.2, (u.recs.map Rec.key).Nodup)
    (hstart : ∀ units : List Bucket, (∀ u ∈ units, (u.recs.map Rec.key).Nodup) →
      (adopt out units).Valid (selectedDirectGeometry first) oldWord) :
    ∀ reason, runChain oldWord out (selectedChainJobs first steps) ≠ .rejected reason := by
  simpa only [DirectJobUniformCycleProof.directChainJobs_selected] using
    DirectJobCycleGeometryProof.chain_admissible selectedDirectGeometry 8
      (selected_cycle_geometry 8 le_rfl) steps first oldWord out hfirst hcount hu hstart

end DirectJobAdoptionLemmas

theorem DirectJobSelectedChainAdmissible : DirectJobSelectedChainAdmissible_statement := by
  intro oldWord steps hcount hu
  apply DirectJobAdoptionLemmas.chain steps 1 oldWord emptyOutput (by omega) (by omega) hu
  intro units hunit
  apply DirectJobEmptyInput _ oldWord units _ hunit
  simp [selectedDirectGeometry]

end RebuildBound
