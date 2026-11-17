import RebuildBound.Proofs.AdaptiveLevelOneA.Geometry
import RebuildBound.Proofs.AdaptiveLevelOneBU.Cell
import RebuildBound.Proofs.AdaptiveLevelOneA.Event
import RebuildBound.Proofs.AdaptiveLevelOneA.Split
import RebuildBound.Proofs.HierarchyLevelOne
import RebuildBound.Proofs.HierarchyLaws31
import RebuildBound.Proofs.HierarchyLocalityChunks
import RebuildBound.Proofs.HierarchyLawsChunks31

/-! The capacity-`2^31` A theorem is a specialization of the common
geometry-parametric causal-cell adapter and its selected local certificate. -/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.AdaptiveLevelOneAProof
open Model Model.DirectJob Model.Hierarchy Spec DirectJobUniformCycleProof

theorem levelOneA31 (hCell : CausalCell_statement) : CausalLevelOneA31_statement := by
  intro h _
  apply levelOneAFor (geometry31.chunk h) (AdaptiveLevelOneBUProof.causalGeometry31 h)
    (by rw [fanout31]; omega) (by rw [seed31, fanout31]) selectedDirectSep
    (fun d _ _ => ⟨Nat.div_mul_cancel (SG1Proof.val2_dvd d), rfl⟩)
    selectedDirectABudget _ hCell
  intro d hd hdfan data hv
  have hd8 : d ≤ 8 := by rw [fanout31] at hdfan; omega
  have hvalid : data.Valid d := by
    refine ⟨hv.weight_sum, hv.before_history, hv.prior_keys, hv.fresh_keys, ?_, hv.bLoad⟩
    simpa only [show (selectedDirectSep d).d = d from
      Nat.div_mul_cancel (SG1Proof.val2_dvd d), show (selectedDirectSep d).U = 16 from rfl,
      show (geometry31.chunk h).cfg.load = 32 from rfl]
      using hv.aLoad
  refine DirectJobSelectedAProbability d hd hd8 (data.law d)
    ((selectedDirectSep d).oldDensity 64 data.KA.card)
    (DirectJobHistoryInputLaw d hd hd8 data hvalid) rfl ?_ (data.direct d)
    (fun _ _ => ⟨rfl, rfl⟩)
  apply selected_oldDensity_mono d hd hd8
  have hdd := (DirectJobSelectedGeometry.2 d hd hd8).2.2.1
  change data.KA.card ≤ 32 * (((selectedDirectSep d).d - 1) * 16)
  rw [hdd]
  exact hvalid.aLoad

end RebuildBound.AdaptiveLevelOneAProof

open RebuildBound.AdaptiveLevelOneAProof in
theorem RebuildBound.CausalLevelOneAStep : RebuildBound.Spec.CausalLevelOneAStep_statement :=
  fun _ hCell => levelOneA31 hCell
