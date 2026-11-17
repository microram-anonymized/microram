import RebuildBound.Proofs.HierarchyLevelOne
import RebuildBound.Spec.HierarchyChunk

/-! # HierarchyLevelOneChunks: level one's cycles at every chunk horizon.

`HierarchyLevelOneProof.levelOneAt` is generic in the configuration. Its
premises at `chunkConfig cfg h`: the load is horizon-free, and the step facts
hold at every horizon once each level's carry positions are the previous
level's times its fanout (`⌊(⌊H/P⌋ + 1)/b⌋ ≤ ⌊H/(P b)⌋ + 1`). -/

namespace RebuildBound.HierarchyLevelOneChunksProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof

/-- The step facts from horizon-free per-level facts. -/
theorem stepFacts_of (cfg : Config) (H : Nat)
    (hs : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.levels →
      cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧ 0 < cfg.fanout ℓ ∧
        cfg.carryPositions (ℓ + 1) = cfg.carryPositions ℓ * cfg.fanout ℓ) :
    StepFacts { cfg with horizon := H } := by
  intro ℓ h1 h2
  obtain ⟨hseed, hb, hP⟩ := hs ℓ h1 h2
  change cfg.seed ℓ = cfg.fanout ℓ * cfg.seed (ℓ + 1) ∧ 0 < cfg.fanout ℓ ∧
    (H / cfg.carryPositions ℓ + 1) / cfg.fanout ℓ ≤ H / cfg.carryPositions (ℓ + 1) + 1
  refine ⟨hseed, hb, ?_⟩
  rw [hP, ← Nat.div_div_eq_div_mul]
  calc (H / cfg.carryPositions ℓ + 1) / cfg.fanout ℓ
      ≤ (H / cfg.carryPositions ℓ + cfg.fanout ℓ) / cfg.fanout ℓ :=
        Nat.div_le_div_right (by omega)
    _ = _ := Nat.add_div_right _ hb

theorem stepFacts_uniform (h : Nat) : StepFacts (chunkConfig uniformConfig h) := by
  apply stepFacts_of
  intro ℓ h1 h2
  have : ℓ < 6 := h2
  interval_cases ℓ <;> decide

theorem stepFacts_half (h : Nat) : StepFacts (chunkConfig halfFanoutConfig h) := by
  apply stepFacts_of
  intro ℓ h1 h2
  have : ℓ < 7 := h2
  interval_cases ℓ <;> decide

end RebuildBound.HierarchyLevelOneChunksProof

theorem RebuildBound.HierarchyLevelOneChunks :
    RebuildBound.Spec.HierarchyLevelOneChunks_statement := by
  intro _ h _
  open Spec in
  exact ⟨HierarchyLevelOneProof.levelOneAt _ _ (HierarchyLevelOneChunksProof.stepFacts_uniform h)
      (by decide : uniformConfig.load * uniformConfig.carry1 = 512),
    HierarchyLevelOneProof.levelOneAt _ _ (HierarchyLevelOneChunksProof.stepFacts_half h)
      (by decide : halfFanoutConfig.load * halfFanoutConfig.carry1 = 512)⟩
