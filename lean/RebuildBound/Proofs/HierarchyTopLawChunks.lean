import RebuildBound.Proofs.HierarchyTopLaw
import RebuildBound.Proofs.HierarchyLevelOneChunks
import RebuildBound.Proofs.HierarchyChunk.Arith

/-! # HierarchyTopLawChunks: the top laws at every chunk horizon.

`HierarchyTopLawProof.topLawAt` is generic in the configuration; at
`chunkConfig cfg h` its configuration facts hold by arithmetic in `h`:
`StepFacts` by `HierarchyLevelOneChunks`, `CarryFacts` by
`HierarchyChunkArith.carry_chunk`, and the speculative top finish lies outside
the horizon since level one's time bound `s_1 + h m_1 + 1` is
`(s_L + h m_L) P_L + 1` with `P_L ≥ 2` (`bound_eq`). The horizon does not
enter the seeds, fanouts or times, so those transfer by `rfl`. No probability
obstacle arose. -/

namespace RebuildBound.HierarchyTopLawChunksProof
open Model Model.Hierarchy Spec HierarchyLevelOneProof HierarchyTopLawProof HierarchyChunkArith
open HierarchyCoveringProof (per)

theorem carryFacts_chunk {cfg : Config} (F : ChunkFacts cfg) (h : Nat) :
    CarryFacts (chunkConfig cfg h) :=
  fun _ h2 hL => carry_chunk F h h2 hL

/-- The speculative top finish lies outside every chunk horizon. -/
theorem win_chunk {cfg : Config} (F : ChunkFacts cfg) (h : Nat) :
    ∀ o, WithinHorizon (chunkConfig cfg h) (.topFinish o) →
      o < (chunkConfig cfg h).seed (chunkConfig cfg h).levels +
        (chunkConfig cfg h).ordinals (chunkConfig cfg h).levels := by
  intro o hw
  have hL := F.levels_ge
  unfold WithinHorizon at hw
  change o * per cfg cfg.levels ≤ cfg.seed 1 + (chunkConfig cfg h).ordinals 1 at hw
  change o < cfg.seed cfg.levels + (chunkConfig cfg h).ordinals cfg.levels
  rw [ordinals_chunk F h 1 le_rfl (by omega), bound_eq F h cfg.levels (by omega) le_rfl] at hw
  rw [ordinals_chunk F h _ (by omega) le_rfl]
  have := aux_le F.per_top hw
  omega

end RebuildBound.HierarchyTopLawChunksProof

open RebuildBound.HierarchyTopLawChunksProof RebuildBound.HierarchyChunkArith
  RebuildBound.HierarchyLevelOneChunksProof in
theorem RebuildBound.HierarchyTopLawChunks :
    RebuildBound.Spec.HierarchyTopLawChunks_statement := by
  intro _ hInv hLoc h h1
  exact ⟨HierarchyTopLawProof.topLawAt _ _ (stepFacts_uniform h)
      (carryFacts_chunk chunkFacts_uniform h) rfl
      (show 2 ≤ RebuildBound.Spec.uniformConfig.levels by decide)
      (win_chunk chunkFacts_uniform h) (hInv h h1).1 (hLoc h h1).1,
    HierarchyTopLawProof.topLawAt _ _ (stepFacts_half h)
      (carryFacts_chunk chunkFacts_half h) rfl
      (show 2 ≤ RebuildBound.Spec.halfFanoutConfig.levels by decide)
      (win_chunk chunkFacts_half h) (hInv h h1).2 (hLoc h h1).2⟩
