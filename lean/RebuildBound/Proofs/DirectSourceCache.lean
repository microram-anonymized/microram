import RebuildBound.Spec.DirectSourceCache
import RebuildBound.Proofs.DirectAddresses
import RebuildBound.Proofs.DirectCache
import RebuildBound.Proofs.DirectScan

namespace RebuildBound
open Model Model.DirectSourceCache

theorem DirectSourceCacheEncoding : Spec.DirectSourceCacheEncoding_statement := by
  intro compare units he hu word bits i hi j hj
  unfold cache
  rw [DirectAddressesDense compare units he hu i hi]
  rfl

theorem DirectSourceCacheCandidates : Spec.DirectSourceCacheCandidates_statement := by
  intro compare units he hu word bits home chunks hh hc
  unfold candidates DirectScan.candidates
  apply List.map_congr_left
  intro chunk hchunk
  apply List.filter_congr
  intro i hi
  have hib := hc i (List.mem_flatten.mpr ⟨chunk, hchunk, hi⟩)
  apply Bool.eq_iff_iff.mpr
  rw [DirectCacheCandidate bits _ true _ home (Nat.mod_lt _ (by positivity)) hh
    (DirectSourceCacheEncoding compare units he hu word bits i hib)]
  simp [DirectRecords.home, DirectPrefix.cachedHome]

theorem DirectSourceCacheSelected : Spec.DirectSourceCacheSelected_statement := by
  intro compare units he hu word bits home cap hh
  have hc := DirectMaskedRecordsValid compare units he hu
  change (DirectMaskedRecords.chunks (DirectMasks.run compare [] units)).flatten = _ at hc
  rw [DirectSourceCacheCandidates compare units he hu word bits home _ hh (by
    intro i hi
    rw [hc] at hi
    simpa [DirectRecords.source] using hi)]
  rw [DirectScanHomeSelected, hc, List.map_take, ← DirectRecordsSource
    (DirectMasks.records units), List.filter_map]
  rfl

-- Source holes, an empty unit, and a newer tombstone survive the composition.
private def old : Rec := ⟨LogicalKey.ofNat 257, 10, false⟩
private def other : Rec := ⟨LogicalKey.ofNat 1, 20, false⟩
private def tomb : Rec := ⟨LogicalKey.ofNat 257, 30, true⟩
private def sample : List Bucket := [[some old, none, some other], [], [some tomb]]
private def exactCompare : DirectMasks.Comparison := fun a b => a == b
example : DirectMasks.ExactComparison exactCompare := by intro a b; rfl
example : ∀ unit ∈ sample, (unit.recs.map Rec.key).Nodup := by decide +kernel
example : DirectAddresses.chunks (DirectMasks.run exactCompare [] sample) =
    [[(0, 2)], [], [(2, 0)]] := by decide +kernel
-- Homes 1 and 257 share their low byte; the high byte selects only the tombstone.
example : candidates exactCompare 9 LogicalKey.toNat sample 257
    (DirectMaskedRecords.chunks (DirectMasks.run exactCompare [] sample)) =
    [[], [], [1]] := by decide +kernel
example : ((DirectScan.run 1 (candidates exactCompare 9 LogicalKey.toNat sample 257
    (DirectMaskedRecords.chunks (DirectMasks.run exactCompare [] sample)))).selected.map
      (DirectRecords.record (DirectMasks.records sample))) = [tomb] := by decide +kernel
-- The cache is valid for remaining subsets after other homes have been cleared.
example : candidates exactCompare 9 LogicalKey.toNat sample 257 [[], [], [1]] = [[], [], [1]] := by decide +kernel

-- Valid-index filtering preserves caller multiplicity; it does not deduplicate.
example : candidates exactCompare 9 LogicalKey.toNat sample 257 [[1, 1]] = [[1, 1]] := by decide +kernel
-- An invalid dense index defaults to source address (0,0), which is occupied
-- by the older record. The index bound is essential for cache correspondence.
example : candidates exactCompare 9 LogicalKey.toNat sample 257 [[99]] ≠
    DirectScan.candidates (DirectRecords.home (DirectMasks.records sample) LogicalKey.toNat (2 ^ 9))
      257 [[99]] := by decide +kernel

end RebuildBound
