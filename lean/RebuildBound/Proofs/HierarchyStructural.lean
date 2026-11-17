import RebuildBound.Proofs.HierarchyStructural.Restriction

/-! Range-free structural history for the existing reference hierarchy.
Finite restriction is internal to the proof; neither the statement nor the
execution bounds key identities or all-run distinct keys by storage capacity. -/
namespace RebuildBound.HierarchyStructuralProof
open Model Model.Hierarchy Spec HierarchyInvariantProof OnlineCorrectnessProof

/-- Exact finish shape and permutations on the original, unrestricted trace. -/
theorem top_step : HierarchyStructuralStep_statement := by
  intro geo hgeo tr hT hInit hU words v hv hvh
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  have hL := F.levels2
  let tr' := truncate tr (horizonUnits geo.cfg)
  obtain ⟨N, hT'⟩ := truncate_premises hT (horizonUnits geo.cfg)
  have hU' := truncate_unsh F tr hU
  have hp := top_inv'For_of_initLength geo F G hT' hInit hU' words
    (v := v - 1) (by omega) (by omega)
  have hs := top_stepFor geo F G hT' hU' words hv hvh hp
  have ht := truncate_table F tr words geo.cfg.levels (by omega) le_rfl v
    (horizonUnits geo.cfg) (unitEnd_mono geo.cfg _ hvh)
  have hf := truncate_finish F tr words v hvh
  have hprev := truncate_table F tr words geo.cfg.levels (by omega) le_rfl (v - 1)
    (horizonUnits geo.cfg) (unitEnd_mono geo.cfg _ (by omega))
  have hprep : prepInputsAt geo.cfg geo.shapes tr words v =
      prepInputsAt geo.cfg geo.shapes tr' words v := by
    unfold prepInputsAt
    exact congrArg prepInputs hprev
  rw [ht, hf, hprep]
  exact ⟨hs.1, hs.2.2.1, hs.2.2.2⟩

end RebuildBound.HierarchyStructuralProof

namespace RebuildBound
open Model Model.Hierarchy Spec HierarchyInvariantProof OnlineCorrectnessProof
open HierarchyStructuralProof

/-- Reference structure and chronological values need no global key range. -/
theorem HierarchyStructuralTop : HierarchyStructuralTop_statement := by
  intro geo hgeo tr hT hInit hU words v hvh
  have F := HierarchySemanticsProof.lower hgeo.1
  have G := TopFacts.of_compatible hgeo.2
  have hL := F.levels2
  obtain ⟨N, hT'⟩ := truncate_premises hT (horizonUnits geo.cfg)
  have hU' := truncate_unsh F tr hU
  have hI := top_invFor_of_initLength geo F G hT' hInit hU' words v hvh
  have ht := truncate_table F tr words geo.cfg.levels (by omega) le_rfl v
    (horizonUnits geo.cfg) (unitEnd_mono geo.cfg _ hvh)
  rw [← ht] at hI
  refine ⟨hI.len, hI.lanes, hI.nodup, hI.home, ?_, ?_⟩
  · intro key
    have hl := top_latestFor_of_initLength geo F G hT' hInit hU' words v hvh key
    have hslice := truncate_slice tr v hvh
    rw [← ht, ← hslice] at hl
    simpa [consumedHistory, traceSlice, unitEnd, truncate, List.range_eq_range'] using hl
  · intro hv r hr
    have hs := top_step geo hgeo tr hT hInit hU words v hv hvh
    have hm := hs.2.1.mem_iff.mp hr
    have := (List.mem_filter.mp hm).2
    simpa using this

/-- The local finite-job interface follows from range-free trace structure. -/
theorem HierarchyStructuralStep : HierarchyStructuralStep_statement := top_step

end RebuildBound
