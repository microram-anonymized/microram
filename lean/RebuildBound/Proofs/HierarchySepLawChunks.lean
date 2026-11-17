import RebuildBound.Proofs.HierarchySepLaw
import RebuildBound.Proofs.HierarchyChunk.Arith

/-! # HierarchySepLawChunks: the separated laws at every chunk horizon.

`HierarchySepLawProof.sepLawAt` is generic in the configuration; it needs
`Good`, `RowsMatch`, the rows' word facts and load 32. At `chunkConfig cfg h`
the seeds, fanouts, levels and carries are those of `cfg` (definitionally),
the separated classes are too (the exposure counts are dropped), and `Good`'s
horizon clauses are the step and carry inequalities of
`HierarchyChunkArith` (every level's ordinal count scales with `h`).

No probability obstacle: nothing probabilistic is new here. -/

namespace RebuildBound.HierarchySepLawChunksProof
open Model Spec HierarchySepLawProof HierarchyChunkArith

theorem good_chunk {cfg : Config} (hg : Good cfg) (F : ChunkFacts cfg) (h : Nat) :
    Good (chunkConfig cfg h) := by
  refine ⟨fun ℓ (hℓ : ℓ < cfg.levels) h1 => ?_,
    fun ℓ (hℓ : ℓ < cfg.levels) h2 => carry_chunk F h h2 hℓ.le, hg.2.2⟩
  obtain ⟨hf, hs, -, hp⟩ := hg.1 ℓ hℓ h1
  exact ⟨hf, hs, step_chunk F h h1 hℓ (by omega), hp⟩

theorem rowsMatch_chunk {cfg : Config} {rows : List (SepGeom × Nat)} (h : Nat)
    (hr : cfg.RowsMatch rows) : (chunkConfig cfg h).RowsMatch rows := by
  have hc : (chunkConfig cfg h).separatedClasses = cfg.separatedClasses := by
    simp [Config.separatedClasses, Config.exposures, List.filterMap_flatMap,
      List.filterMap_append, chunkConfig, Config.ordinaryLevels, Config.levels, Config.fanout]
    rfl
  exact ⟨hc ▸ hr.1, hc ▸ hr.2⟩

end RebuildBound.HierarchySepLawChunksProof

open RebuildBound.HierarchySepLawProof RebuildBound.HierarchySepLawChunksProof
  RebuildBound.HierarchyChunkArith in
theorem RebuildBound.HierarchySepLawChunks : RebuildBound.Spec.HierarchySepLawChunks_statement := by
  intro _ hInv hLoc hDen h h1
  exact ⟨sepLawAt _ _ (good_chunk good_uniform chunkFacts_uniform h)
      (rowsMatch_chunk h RebuildBound.SelExpo.2.2.1) rowOK_uniform rfl (hInv h h1).1
      (hLoc h h1).1 hDen,
    sepLawAt _ _ (good_chunk good_half chunkFacts_half h)
      (rowsMatch_chunk h RebuildBound.SelExpo.2.2.2.1) rowOK_half rfl (hInv h h1).2
      (hLoc h h1).2 hDen⟩
