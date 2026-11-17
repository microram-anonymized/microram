import RebuildBound.Spec.HierarchyChunk
import RebuildBound.Proofs.HierarchyChunkAssembly
import RebuildBound.Proofs.HierarchyChunkPartition
import RebuildBound.Proofs.HierarchyHorizonTransfer

/-!
# Generic chunk-to-window transfer

The failure event over `h` chunks is the union of the first-failure chunk
events. Summing their common bound gives `h * error`, with trace, promise,
and family-tape premises restricted to each prefix.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound
open Spec Model Model.Hierarchy

namespace HierarchyWindowsProof
open HierarchyHorizonTransferProof in
/-- The bound over `h` chunks from the per-chunk bound. -/
theorem windowsFor (geo : HierarchyGeometry) (error : ℝ≥0∞)
    (hChunk : HierarchyChunkFor geo error) : HierarchyWindowsFor geo error := by
  intro h N tr hh hN hTr hUnsh Ω _ μ _ tape words hT
  let A : Nat → Set Ω := fun k =>
    {ω | ChunkFails geo.cfg (geo.chunk h).shapes tr (words ω) k}
  have hk : ∀ k, k < h → μ (A k) ≤ error := by
    intro k hkh
    have hle : k + 1 ≤ h := by omega
    have hTr' := trace_mono (H' := k + 1) hTr
    have hU' : UnshPromise (chunkConfig geo.cfg (k + 1)) (geo.chunk (k + 1)).shapes tr := by
      simp only [shapes_chunkFor] at hUnsh ⊢
      exact unsh_monoFor hle _ hUnsh
    have hT' := tape_restrict (fun _ => coords_mono (cfg := geo.cfg) hle) hT
    have hA : A k =
        {ω | ChunkFails geo.cfg (geo.chunk (k + 1)).shapes tr (words ω) k} := by
      simp only [A, shapes_chunkFor]
    rw [hA]
    exact hChunk k N tr hN hTr' hU' μ _ words hT'
  calc μ {ω | Fails (chunkConfig geo.cfg h) (geo.chunk h).shapes tr (words ω)}
      ≤ μ (⋃ k ∈ Finset.range h, A k) := by
        apply measure_mono
        intro ω hω
        obtain ⟨k, hkh, hc⟩ :=
          (HierarchyChunkPartitionProof.chunks_partition geo.cfg _ tr (words ω) h hh).1 hω
        exact Set.mem_biUnion (Finset.mem_range.2 hkh) hc
    _ ≤ ∑ k ∈ Finset.range h, μ (A k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range h, error :=
        Finset.sum_le_sum fun k hk' => hk k (Finset.mem_range.1 hk')
    _ = (h : ℝ≥0∞) * error := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end HierarchyWindowsProof

end RebuildBound
