import RebuildBound.Spec.Oblivious
import RebuildBound.Proofs.HierarchyHorizonFree

/-! # HierarchyChunkPartition: the chunk events partition `Fails`

With the shapes fixed, `Fails` is monotone in the
horizon: the potential jobs and `WithinHorizon` only grow with it, and
`jobFails` does not read it (`HierarchyHorizonFree`). The forward direction
picks the least horizon (in chunks) at which the model fails. -/

namespace RebuildBound
open Model Model.DirectJob Model.Hierarchy Spec

namespace HierarchyChunkPartitionProof

theorem ordinals_mono (cfg : Config) {h h' : Nat} (hh : h ≤ h') (ℓ : Nat) :
    ({ cfg with horizon := h } : Config).ordinals ℓ ≤
      ({ cfg with horizon := h' } : Config).ordinals ℓ :=
  Nat.add_le_add_right (Nat.div_le_div_right hh) 1

theorem potential_mono (cfg : Config) {h h' : Nat} (hh : h ≤ h') (j : JobId)
    (hj : j ∈ ({ cfg with horizon := h } : Config).potentialJobs) :
    j ∈ ({ cfg with horizon := h' } : Config).potentialJobs := by
  have hord := ordinals_mono cfg hh
  simp only [Config.potentialJobs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range] at hj ⊢
  rcases hj with (⟨ℓ, hℓ, i, hi, rfl⟩ | ⟨i, hi, hm⟩) | hinit
  · exact Or.inl (Or.inl ⟨ℓ, hℓ, i, lt_of_lt_of_le hi (hord ℓ), rfl⟩)
  · exact Or.inl (Or.inr ⟨i, lt_of_lt_of_le hi (hord _), hm⟩)
  · exact Or.inr hinit

/-- With the shapes fixed, `Fails` at a horizon implies `Fails` at every
larger horizon. -/
theorem fails_mono (cfg : Config) (sh : Shapes) (tr : Trace) (w : Words) {h h' : Nat}
    (hh : h ≤ h') :
    Fails { cfg with horizon := h } sh tr w → Fails { cfg with horizon := h' } sh tr w := by
  rintro ⟨j, hj, hw, hf⟩
  refine ⟨j, potential_mono cfg hh j hj, ?_, ?_⟩
  · unfold WithinHorizon at hw ⊢
    exact le_trans hw (Nat.add_le_add_left (ordinals_mono cfg hh 1) _)
  · rw [((HierarchyHorizonFree cfg h' []).2.2 sh tr w j).1]
    rw [((HierarchyHorizonFree cfg h []).2.2 sh tr w j).1] at hf
    exact hf

/-- `Fails` is monotone in the number of chunks, with the shapes fixed. -/
theorem chunk_fails_mono (cfg : Config) (sh : Shapes) (tr : Trace) (w : Words) {k K : Nat}
    (hk : k ≤ K) : Fails (chunkConfig cfg k) sh tr w → Fails (chunkConfig cfg K) sh tr w :=
  fails_mono cfg sh tr w (Nat.mul_le_mul_right _ hk)

/-- For `K ≥ 1`: some chunk `k < K` holds the first failure iff the model
fails at horizon `K · 2^32`, for any fixed shapes. -/
theorem chunks_partition (cfg : Config) (sh : Shapes) (tr : Trace) (w : Words) (K : Nat)
    (hK1 : 1 ≤ K) :
    Fails (chunkConfig cfg K) sh tr w ↔ ∃ k < K, ChunkFails cfg sh tr w k := by
  constructor
  · intro hK
    have hex : ∃ n, Fails (chunkConfig cfg n) sh tr w := ⟨K, hK⟩
    classical
    have hn : Fails (chunkConfig cfg (Nat.find hex)) sh tr w := Nat.find_spec hex
    have hnK : Nat.find hex ≤ K := Nat.find_min' hex hK
    by_cases h0 : Nat.find hex = 0
    · refine ⟨0, by omega, ?_, fun h => absurd h (lt_irrefl 0)⟩
      exact chunk_fails_mono cfg sh tr w (by omega) (h0 ▸ hn)
    · refine ⟨Nat.find hex - 1, by omega, ?_, fun _ => ?_⟩
      · rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]; exact hn
      · exact Nat.find_min hex (by omega)
  · rintro ⟨k, hk, hf, -⟩
    exact chunk_fails_mono cfg sh tr w (by omega) hf

end HierarchyChunkPartitionProof

open HierarchyChunkPartitionProof in
theorem HierarchyChunkPartition : Spec.HierarchyChunkPartition_statement :=
  ⟨fun h tr words hh => chunks_partition _ _ tr words h hh,
   fun h tr words hh => chunks_partition _ _ tr words h hh⟩

end RebuildBound
