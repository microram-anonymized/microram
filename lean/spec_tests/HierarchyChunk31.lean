import RebuildBound.Proofs.HierarchyChunk31
import spec_tests.HierarchyUniform31

/-! Endpoint applications on the existing nonempty, full-rate trace and
canonical uniform tape. Chunk boundaries remain symbolic. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HierarchyChunk31Test
open RebuildBound RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Spec
open HierarchyHorizonTransferProof

theorem trace (h : Nat) : TracePremises (chunkConfig config31 h) keyCapacity31
    HierarchyInvariant31Test.tr := by
  have ht : TracePremises (chunkConfig config31 1) keyCapacity31
      HierarchyInvariant31Test.tr := by
    rw [HierarchyChunkArith.chunk_one HierarchyLawsChunks31Proof.chunkFacts31]
    exact HierarchyInvariant31Test.trace
  exact trace_mono ht

theorem unsh (h : Nat) : UnshPromise (chunkConfig config31 h)
    (geometry31.chunk h).shapes HierarchyInvariant31Test.tr := by
  intro words o _ r _ hr
  simp [earlyDrop, HierarchyInvariant31Test.tr] at hr

noncomputable section
abbrev Ω (h : Nat) : Type := FamilyTape (chunkConfig config31 h) keyCapacity31
abbrev μ (h : Nat) : Measure (Ω h) := uniformOn (Set.univ : Set (Ω h))
abbrev words (h : Nat) : Ω h → Words := HierarchySepLawProof.ext

theorem tape (h : Nat) : TapePremises (chunkConfig config31 h) keyCapacity31
    (μ h) id (words h) where
  measurable := measurable_id
  uniform := Measure.map_id
  agree := HierarchySepLawProof.ext_consistent

-- This quantifies over chunk zero as well as every positive chunk.
theorem chunk_applied (k : Nat) :
    μ (k + 1) {ω | ChunkFails config31 (geometry31.chunk (k + 1)).shapes
      HierarchyInvariant31Test.tr (words (k + 1) ω) k} ≤
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64) :=
  HierarchyChunk31 k keyCapacity31 _ le_rfl (trace _) (unsh _) (μ _) id (words _) (tape _)

theorem windows_applied (h : Nat) (hh : 1 ≤ h) :
    μ h {ω | Fails (chunkConfig config31 h) (geometry31.chunk h).shapes
      HierarchyInvariant31Test.tr (words h ω)} ≤ ENNReal.ofReal ((h : ℝ) / 2 ^ 64) := by
  rw [div_eq_mul_one_div (h : ℝ), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  exact HierarchyWindows31 h keyCapacity31 _ hh le_rfl (trace h) (unsh h)
    (μ h) id (words h) (tape h)

-- Retain a nonempty failure event, now stated as chunk zero.
example : {ω : HierarchyUniform31Test.Ω | ChunkFails config31 geometry31.shapes
    HierarchyUniform31Test.badTrace (HierarchyUniform31Test.words ω) 0}.Nonempty := by
  obtain ⟨ω, hω⟩ := HierarchyUniform31Test.failure_nonempty
  refine ⟨ω, ?_, fun h => by omega⟩
  rw [show 0 + 1 = 1 by omega,
    HierarchyChunkArith.chunk_one HierarchyLawsChunks31Proof.chunkFacts31]
  exact hω

-- A first-horizon failure cannot be charged again to a positive chunk.
example (k : Nat) (hk : 0 < k) :
    ¬ ChunkFails config31 geometry31.shapes HierarchyUniform31Test.badTrace
      HierarchyUniform31Test.zeroWords k := by
  intro hf
  apply hf.2 hk
  have hfirst : Fails (chunkConfig config31 1) geometry31.shapes
      HierarchyUniform31Test.badTrace HierarchyUniform31Test.zeroWords := by
    rw [HierarchyChunkArith.chunk_one HierarchyLawsChunks31Proof.chunkFacts31]
    exact HierarchyUniform31Test.fails
  exact HierarchyChunkPartitionProof.chunk_fails_mono _ _ _ _ (by omega) hfirst

-- The arbitrary-shape partition applies to every positive window horizon.
example (h : Nat) (hh : 1 ≤ h) (w : Words) :
    Fails (chunkConfig config31 h) (geometry31.chunk h).shapes HierarchyInvariant31Test.tr w ↔
      ∃ k < h, ChunkFails config31 (geometry31.chunk h).shapes HierarchyInvariant31Test.tr w k :=
  HierarchyChunkPartitionProof.chunks_partition _ _ _ _ h hh

end
end HierarchyChunk31Test

open RebuildBound RebuildBound.Model RebuildBound.Spec
example (cfg : Config) (rows : List (SepGeom × Nat)) :
    HierarchyCoveringFromAt cfg rows =
      HierarchyCoveringFromFor ⟨cfg, rows, selectedTop, selectedTP, selectedTP, 2 ^ 27, selectedDirectGeometry⟩ := rfl
