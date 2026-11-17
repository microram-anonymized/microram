import RebuildBound.Proofs.HierarchyChunkAssembly.Facts

/-! # HierarchyChunkAssembly: relabelling chunk `k` into the first horizon

`shift cfg k` moves a potential job of the first horizon to the job of chunk
`k` with the same position: level `ℓ`'s ordinals (the top's for the top's
jobs) move by `k m_ℓ`; the initialization stays. It preserves membership and
digits; a potential job of `k + 1` chunks at or before the end of chunk
`k - 1` is a potential job of `k` chunks, and one after it is a shifted job.
Likewise level-one cycles move by `k C`. -/

namespace RebuildBound.HierarchyChunkAssemblyProof
open Model Model.DirectJob Model.Hierarchy Spec
open HierarchyCoveringProof (per mem_ordinary mem_prep mem_finish mem_init mem_init_iff)
open HierarchyChunkArith

/-- The job of chunk `k` at the position of a job of the first horizon. -/
def shift (cfg : Config) (k : Nat) : JobId → JobId
  | .ordinary ℓ o => .ordinary ℓ (o + k * (cfg.ordinals ℓ - 1))
  | .topPrepare o => .topPrepare (o + k * (cfg.ordinals cfg.levels - 1))
  | .topFinish o => .topFinish (o + k * (cfg.ordinals cfg.levels - 1))
  | .initialization => .initialization

theorem split_succ (k m : Nat) : (k + 1) * m = k * m + m := by ring

section
variable {cfg : Config} (F : ChunkFacts cfg)
include F

theorem shift_mem {k : Nat} {j : JobId} (hj : j ∈ cfg.potentialJobs) :
    shift cfg k j ∈ (chunkConfig cfg (k + 1)).potentialJobs := by
  cases j with
  | ordinary ℓ o =>
    obtain ⟨h1, h2, h3, h4⟩ := mem_ordinary.1 hj
    refine mem_ordinary.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) ℓ h1 h2.le, split_succ]
    have := ordinals_pos cfg ℓ
    omega
  | topPrepare o =>
    obtain ⟨h3, h4⟩ := mem_prep.1 hj
    refine mem_prep.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) _ (by have := F.levels_ge; omega) le_rfl,
      split_succ]
    have := ordinals_pos cfg cfg.levels
    omega
  | topFinish o =>
    obtain ⟨h3, h4⟩ := mem_finish.1 hj
    refine mem_finish.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) _ (by have := F.levels_ge; omega) le_rfl,
      split_succ]
    have := ordinals_pos cfg cfg.levels
    omega
  | initialization =>
    exact mem_init (by simpa only [chunk_initialized] using mem_init_iff.mp hj)

theorem digit_shift {k ℓ o : Nat} (h1 : 1 ≤ ℓ) (h2 : ℓ < cfg.levels) (ho : 1 ≤ o) :
    Config.digitOf (cfg.fanout ℓ) (o + k * (cfg.ordinals ℓ - 1)) = Config.digitOf (cfg.fanout ℓ) o := by
  unfold Config.digitOf
  obtain ⟨q, hq⟩ : cfg.fanout ℓ ∣ cfg.ordinals ℓ - 1 := ⟨_, F.scale ℓ h2 h1⟩
  rw [hq, show o + k * (cfg.fanout ℓ * q) - 1 = (o - 1) + cfg.fanout ℓ * (k * q) by
    rw [show k * (cfg.fanout ℓ * q) = cfg.fanout ℓ * (k * q) by ring]; omega,
    Nat.add_mul_mod_self_left]

/-- A potential job of `k + 1` chunks at or before the end of chunk `k - 1`
is a potential job of `k` chunks. -/
theorem prefix_mem {k : Nat} {j : JobId} (hj : j ∈ (chunkConfig cfg (k + 1)).potentialJobs)
    (ht : jobTime cfg j ≤ cfg.seed 1 + (k * (cfg.ordinals 1 - 1) + 1)) :
    j ∈ (chunkConfig cfg k).potentialJobs := by
  cases j with
  | ordinary ℓ o =>
    obtain ⟨h1, h2, h3, h4⟩ := mem_ordinary.1 hj
    simp only [chunk_levels, chunk_seed] at h2 h3 h4
    refine mem_ordinary.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F k ℓ h1 h2.le]
    rw [bound_eq F k ℓ h1 h2.le] at ht
    have := aux_le_succ (F.per_pos ℓ (by omega) h1) ht
    exact ⟨h1, h2, h3, by omega⟩
  | topPrepare o =>
    obtain ⟨h3, h4⟩ := mem_prep.1 hj
    simp only [chunk_levels, chunk_seed] at h3 h4
    have hL := F.levels_ge
    refine mem_prep.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F k _ (by omega) le_rfl]
    rw [bound_eq F k cfg.levels (by omega) le_rfl] at ht
    have := aux_le F.per_top ht
    exact ⟨h3, by omega⟩
  | topFinish o =>
    obtain ⟨h3, h4⟩ := mem_finish.1 hj
    simp only [chunk_levels, chunk_seed] at h3 h4
    have hL := F.levels_ge
    refine mem_finish.2 ?_
    rw [chunk_levels, chunk_seed, ordinals_chunk F k _ (by omega) le_rfl]
    rw [bound_eq F k cfg.levels (by omega) le_rfl] at ht
    have := aux_le_succ (F.per_pos _ (by omega) (by omega)) ht
    exact ⟨h3, by omega⟩
  | initialization =>
    exact mem_init (by simpa only [chunk_initialized] using mem_init_iff.mp hj)

/-- A potential job of `k + 1` chunks after the end of chunk `k - 1` is a
shifted potential job of the first horizon. -/
theorem suffix_shift {k : Nat} {j : JobId} (hj : j ∈ (chunkConfig cfg (k + 1)).potentialJobs)
    (ht : cfg.seed 1 + (k * (cfg.ordinals 1 - 1) + 1) < jobTime cfg j) :
    ∃ j' ∈ cfg.potentialJobs, shift cfg k j' = j := by
  cases j with
  | ordinary ℓ o =>
    obtain ⟨h1, h2, h3, h4⟩ := mem_ordinary.1 hj
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) ℓ h1 h2.le, split_succ] at *
    rw [bound_eq F k ℓ h1 h2.le] at ht
    have := aux_lt ht
    have := ordinals_pos cfg ℓ
    refine ⟨.ordinary ℓ (o - k * (cfg.ordinals ℓ - 1)), mem_ordinary.2 ⟨h1, h2, by omega, by omega⟩,
      ?_⟩
    simp only [shift, JobId.ordinary.injEq, true_and]
    omega
  | topPrepare o =>
    obtain ⟨h3, h4⟩ := mem_prep.1 hj
    have hL := F.levels_ge
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) _ (by omega) le_rfl, split_succ] at *
    rw [bound_eq F k cfg.levels (by omega) le_rfl] at ht
    have := aux_lt ht
    have := ordinals_pos cfg cfg.levels
    refine ⟨.topPrepare (o - k * (cfg.ordinals cfg.levels - 1)), mem_prep.2 ⟨by omega, by omega⟩, ?_⟩
    simp only [shift, JobId.topPrepare.injEq]
    omega
  | topFinish o =>
    obtain ⟨h3, h4⟩ := mem_finish.1 hj
    have hL := F.levels_ge
    rw [chunk_levels, chunk_seed, ordinals_chunk F (k + 1) _ (by omega) le_rfl, split_succ] at *
    rw [bound_eq F k cfg.levels (by omega) le_rfl] at ht
    have := aux_lt ht
    have := ordinals_pos cfg cfg.levels
    refine ⟨.topFinish (o - k * (cfg.ordinals cfg.levels - 1)), mem_finish.2 ⟨by omega, by omega⟩, ?_⟩
    simp only [shift, JobId.topFinish.injEq]
    omega
  | initialization => exact absurd ht (Nat.not_lt_zero _)

/-- A level-one cycle of `k + 1` chunks with an ordinal after the end of
chunk `k - 1` is a shifted cycle of the first horizon. -/
theorem cycle_suffix {k c i : Nat} (hc : c < (chunkConfig cfg (k + 1)).levelOneCycles)
    (hi : i < (chunkConfig cfg (k + 1)).cycleLength c)
    (ht : cfg.seed 1 + (k * (cfg.ordinals 1 - 1) + 1) < (chunkConfig cfg (k + 1)).cycleOrdinal c i) :
    ∃ c' < cfg.levelOneCycles, c = c' + k * cyc1 cfg := by
  rw [levelOneCycles_chunk F, split_succ] at hc
  have hib : i < cfg.fanout 1 := lt_of_lt_of_le hi (min_le_left _ _)
  have ht' : cfg.seed 1 + (k * (cfg.ordinals 1 - 1) + 1) < cfg.seed 1 + 1 + (c * cfg.fanout 1 + i) :=
    ht
  rw [m1_eq F] at ht'
  have hkc : k * cyc1 cfg ≤ c := by
    by_contra hcon
    have := Nat.mul_le_mul_right (cfg.fanout 1) (show c + 1 ≤ k * cyc1 cfg by omega)
    rw [add_mul, one_mul, mul_assoc] at this
    omega
  have h1 : cfg.levelOneCycles = cyc1 cfg + 1 := by
    have := levelOneCycles_chunk F 1
    rwa [chunk_one F, one_mul] at this
  exact ⟨c - k * cyc1 cfg, by omega, by omega⟩

end

end RebuildBound.HierarchyChunkAssemblyProof
