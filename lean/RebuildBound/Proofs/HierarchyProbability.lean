import RebuildBound.Spec.HierarchyFirstFailure
import RebuildBound.Proofs.G4a
import RebuildBound.Proofs.HierarchyChunkAssembly.Jobs
import RebuildBound.Proofs.HierarchyChunkPartition
import RebuildBound.Proofs.HierarchyHorizonTransfer

/-! One finite-window composition for fixed and adaptive runs at arbitrary
geometry. Per-job probability applicability is deliberately a separate premise;
the same checked class budgets can serve both forms of local law. -/

open MeasureTheory
open scoped ENNReal
namespace RebuildBound.HierarchyProbabilityProof
open Spec Model Model.Hierarchy
open HierarchyChunkAssemblyProof HierarchyChunkArith

theorem fails_chunk' {cfg : Config} (H : Nat) (sh : Shapes) (tr : Trace) (w : Words) (j : JobId) :
    jobFails (chunkConfig cfg H) sh tr w j = jobFails cfg sh tr w j :=
  ((HierarchyHorizonFree cfg (H * 2 ^ 32) []).2.2 sh tr w j).1

theorem fit_chunk' {cfg : Config} (H : Nat) (sh : Shapes) (tr : Trace) (w : Words) (j : JobId) :
    jobTiersFit (chunkConfig cfg H) sh tr w j ↔ jobTiersFit cfg sh tr w j :=
  ((HierarchyHorizonFree cfg (H * 2 ^ 32) []).2.2 sh tr w j).2

/-- A first failure within a shorter horizon is one within a longer horizon. -/
theorem jff_mono {cfg : Config} {H H' : Nat} (hle : H ≤ H') (sh : Shapes) (tr : Trace)
    (w : Words) (j : JobId) (h : JobFailsFirst (chunkConfig cfg H) sh tr w j) :
    JobFailsFirst (chunkConfig cfg H') sh tr w j := by
  obtain ⟨hW, hfit, hf, hone⟩ := h
  refine ⟨?_, (fit_chunk' H' sh tr w j).2 ((fit_chunk' H sh tr w j).1 hfit), ?_, ?_⟩
  · unfold WithinHorizon at hW ⊢
    rw [chunk_jobTime, chunk_seed] at hW ⊢
    have := HierarchyHorizonTransferProof.ordinals_mono (cfg := cfg) hle 1
    omega
  · rw [fails_chunk'] at hf ⊢; exact hf
  · intro o ho i hi0 hid
    simp only [Config.digitAt, chunk_fanout] at hid
    have := hone o ho i hi0 (by simp only [Config.digitAt, chunk_fanout]; exact hid)
    rw [fails_chunk'] at this ⊢; exact this

theorem shift_zero (cfg : Config) (j : JobId) : shift cfg 0 j = j := by
  cases j <;> simp [shift]

theorem classOf_shift {cfg : Config} (F : ChunkFacts cfg)
    {k : Nat} {j : JobId} (hj : j ∈ cfg.potentialJobs) :
    cfg.classOf (shift cfg k j) = cfg.classOf j := by
  cases j with
  | ordinary ℓ o =>
    obtain ⟨h1, h2, h3, -⟩ := HierarchyCoveringProof.mem_ordinary.1 hj
    simp only [shift, Config.classOf]
    rw [digit_shift F h1 h2 (by omega)]
  | _ => rfl

/-- From the covering and per-job bounds `b` of the classes, the failure within
`h` chunks is at most `h` times the exposure sum of `b`. -/
theorem composeFor (geo : HierarchyGeometry) (F : ChunkFacts geo.cfg)
    (hV : geo.cfg.Valid) (hCov : HierarchyFirstFailureChunksFor geo)
    (b : JobClass → ℝ≥0∞) (h : Nat)
    (hh : 1 ≤ h) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (tr : Ω → Trace) (words : Ω → Words)
    (hb : ∀ j ∈ (geo.chunk h).cfg.potentialJobs,
      μ {ω | JobFailsFirst (geo.chunk h).cfg (geo.chunk h).shapes (tr ω)
        (words ω) j} ≤ b (geo.cfg.classOf j)) :
    μ {ω | Fails (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω)} ≤
      (h : ℝ≥0∞) * geo.cfg.exposureSum b := by
  have hsh : ∀ H, (geo.chunk H).shapes = geo.shapes :=
    HierarchyHorizonTransferProof.shapes_chunkFor geo
  let E : JobId → Set Ω := fun J =>
    {ω | JobFailsFirst (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω) J}
  have hchunk : ∀ k < h, μ {ω | ChunkFails geo.cfg (geo.chunk h).shapes (tr ω)
      (words ω) k} ≤ geo.cfg.exposureSum b := by
    intro k hk
    refine (G4a geo.cfg hV μ _ (fun j => E (shift geo.cfg k j)) b ?_ ?_).trans
      (min_le_right _ _)
    · rintro ω ⟨hF, hNF⟩
      have hF' : Fails (geo.chunk (k + 1)).cfg (geo.chunk (k + 1)).shapes
          (tr ω) (words ω) := by
        rw [hsh]; rw [hsh] at hF; exact hF
      obtain ⟨J, hJ, hJF⟩ := hCov (k + 1) (by omega) (tr ω) (words ω) hF'
      rw [hsh] at hJF
      have hJF' : ω ∈ E J := by
        show JobFailsFirst (geo.chunk h).cfg (geo.chunk h).shapes (tr ω)
          (words ω) J
        rw [hsh]; exact jff_mono (by omega) _ _ _ _ hJF
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · refine ⟨J, ?_, by rw [shift_zero]; exact hJF'⟩
        have : (geo.chunk (0 + 1)).cfg = geo.cfg := chunk_one F
        rw [this] at hJ; exact hJ
      · have hT : geo.cfg.seed 1 + (k * (geo.cfg.ordinals 1 - 1) + 1) <
            jobTime geo.cfg J := by
          by_contra hle
          push_neg at hle
          apply hNF hk0
          refine ⟨J, prefix_mem F hJ hle, ?_, ?_⟩
          · show jobTime geo.cfg J ≤ geo.cfg.seed 1 + (chunkConfig geo.cfg k).ordinals 1
            rw [ordinals_chunk F k 1 le_rfl (by have := F.levels_ge; omega)]
            exact hle
          · have hJf : jobFails (chunkConfig geo.cfg (k + 1)) geo.shapes (tr ω)
                (words ω) J = true := hJF.2.2.1
            show jobFails (chunkConfig geo.cfg k) (geo.chunk h).shapes (tr ω)
              (words ω) J = true
            rw [hsh, fails_chunk']; rw [fails_chunk'] at hJf; exact hJf
        obtain ⟨j', hj', rfl⟩ := suffix_shift F hJ hT
        exact ⟨j', hj', hJF'⟩
    · intro j hj
      have hm : shift geo.cfg k j ∈ (geo.chunk h).cfg.potentialJobs :=
        HierarchyChunkPartitionProof.potential_mono geo.cfg
          (Nat.mul_le_mul_right _ (show k + 1 ≤ h by omega)) _ (shift_mem F hj)
      have := hb _ hm
      rwa [classOf_shift F hj] at this
  calc μ {ω | Fails (geo.chunk h).cfg (geo.chunk h).shapes (tr ω) (words ω)}
      ≤ μ (⋃ k ∈ Finset.range h,
          {ω | ChunkFails geo.cfg (geo.chunk h).shapes (tr ω) (words ω) k}) := by
        apply measure_mono
        intro ω hω
        obtain ⟨k, hkh, hc⟩ := (HierarchyChunkPartitionProof.chunks_partition geo.cfg _
          (tr ω) (words ω) h hh).1 hω
        exact Set.mem_biUnion (Finset.mem_range.2 hkh) hc
    _ ≤ ∑ k ∈ Finset.range h,
          μ {ω | ChunkFails geo.cfg (geo.chunk h).shapes (tr ω) (words ω) k} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range h, geo.cfg.exposureSum b :=
        Finset.sum_le_sum fun k hk => hchunk k (Finset.mem_range.1 hk)
    _ = (h : ℝ≥0∞) * geo.cfg.exposureSum b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end RebuildBound.HierarchyProbabilityProof
