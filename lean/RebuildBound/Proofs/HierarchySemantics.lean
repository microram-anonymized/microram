import RebuildBound.Spec.HierarchySemantics
import RebuildBound.Proofs.HierarchySemantics.Structure
import RebuildBound.Proofs.Adaptive.Semantics

/-! Generic semantic release root. All conclusions are derived from primitive
structural facts and the existing shared proofs. No numerical certificate or
finite-family inventory is imported. -/

namespace RebuildBound
open Spec Model Model.Hierarchy HierarchyInvariantProof HierarchySemanticsProof

/-- Scalar and batch reference lookup, from either start. -/
theorem HierarchyLookup : HierarchyLookup_statement := by
  intro geo h
  have F := lower h.1
  have G := TopFacts.of_compatible h.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := h.2
  exact ⟨OnlineCorrectnessProof.correctnessFor_run geo F G hD,
    BatchCorrectnessProof.correctnessFor_run geo F G hD⟩

/-- Relabel the supplied history as well as its keys, including the empty base. -/
theorem HierarchyUniverseLookup : HierarchyUniverseLookup_statement := by
  intro geo h
  obtain ⟨hO, hB⟩ := HierarchyLookup geo h
  constructor
  · intro U g run S n m hs hInit w dummy j o hj ho hp
    let e := KeyRelabel.compression U
    have hop : (KeyRelabel.onlineRun e run).ops[j]? = some (KeyRelabel.onlineOp e o) := by
      simp [KeyRelabel.onlineRun, ho]
    have hi : geo.cfg.initialized = false → (KeyRelabel.onlineRun e run).init = [] := by
      intro hf
      simp [KeyRelabel.onlineRun, hInit hf]
    have hr := hO U.card g (KeyRelabel.onlineRun e run) S n m
      (KeyRelabel.online_setting geo U g run S n m hs) hi
      (KeyRelabel.words e w) dummy j (KeyRelabel.onlineOp e o) hj hop (by simpa using hp)
    rw [KeyRelabel.online_history] at hr
    simpa only [KeyRelabel.probe_scalar_value, KeyRelabel.onlineOp_record, KeyRelabel.rec_key,
      KeyRelabel.probe_latestValue, KeyRelabel.probe_scalar_addresses, KeyRelabel.online_touched] using hr
  · intro U g run S n m hs hInit w dummy t s ht hslt hp
    let e := KeyRelabel.compression U
    have hslot : (Model.OnlineBatch.slots (KeyRelabel.batchRun e run))[t]? =
        some (KeyRelabel.slot e s) := by simp [hslt]
    have hi : geo.cfg.initialized = false → (KeyRelabel.batchRun e run).init = [] := by
      intro hf
      simp [KeyRelabel.batchRun, hInit hf]
    have hr := hB U.card g (KeyRelabel.batchRun e run) S n m
      (KeyRelabel.batch_setting geo U g run S n m hs) hi
      (KeyRelabel.words e w) dummy t (KeyRelabel.slot e s) ht hslot (by simpa using hp)
    rw [KeyRelabel.batch_history] at hr
    simpa only [KeyRelabel.probe_batch_value, KeyRelabel.slot_record, KeyRelabel.rec_key,
      KeyRelabel.probe_latestValue, KeyRelabel.probe_batch_addresses, KeyRelabel.batch_touched] using hr

/-- Pattern, freshness and exact fixed-run law, with actual-failure transfer. -/
theorem HierarchyFixedSemantics : HierarchyFixedSemantics_statement := by
  intro geo h
  have F := lower h.1
  have hOP := OnlinePatternProof.patternFor geo F
  have hOF := OnlineFreshProof.freshFor geo F
  have hOX := OnlineExactProof.exactFor_of geo hOP hOF
  have hBP := BatchPatternProof.patternFor geo F
  have hBF := BatchFreshProof.freshFor geo F
  have hBX := BatchExactProof.exactFor_of geo hBP hBF
  exact ⟨⟨hOP, hOF, hOX, OnlineFailure.forGeometry geo hOP hOF hOX⟩,
    ⟨hBP, hBF, hBX, BatchFailure.forGeometry geo hBP hBF hBX⟩⟩

/-- One universe, fixed before the tapes, supplies the arbitrary-key laws. -/
theorem HierarchyUniverseSemantics : HierarchyUniverseSemantics_statement := by
  intro geo h
  obtain ⟨hO, hB⟩ := HierarchyFixedSemantics geo h
  exact ⟨KeyRelabel.onlineExact_transport geo hO.2.2.1,
    KeyRelabel.onlineFailure_transport geo hO.2.2.2,
    KeyRelabel.batchExact_transport geo hB.2.2.1,
    KeyRelabel.batchFailure_transport geo hB.2.2.2⟩

/-- Adaptive exactness uses replay, never a fixed trace's capacity bound. -/
theorem HierarchyAdaptiveSemantics : HierarchyAdaptiveSemantics_statement := by
  intro geo h
  have hB := (HierarchyFixedSemantics geo h).2
  have hX := AdaptiveAssembly.exactFor geo
    (KeyRelabel.batch_pattern_transport geo hB.1)
    (KeyRelabel.batch_fresh_transport geo hB.2.1)
    (KeyRelabel.batchExact_transport geo hB.2.2.1) ReplayShape AdaptiveProof.adaptiveReplay
  refine ⟨hX, ?_⟩
  intro U g m a S n hs Ω _ μ _ tape dtape words hT V _ obs ι _ hι hagree A hA
  obtain ⟨hm, hmap⟩ := hX U g m a S n hs μ tape dtape words hT
  exact OnlineFailure.transfer μ _ _ obs ι _ hm hι hmap (fun ω hω => hagree ω hω) A hA

end RebuildBound
