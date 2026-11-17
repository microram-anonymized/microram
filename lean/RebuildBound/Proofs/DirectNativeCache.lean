import RebuildBound.Spec.DirectNativeCache
import RebuildBound.Proofs.DirectCache64
import RebuildBound.Proofs.DirectSelect64

/-! Compose the proved packed-cache lane predicate with the home mask used by
the native flat-prefix build. The arbitrary remaining mask includes every
subset produced by deduplication and earlier home selections. -/
namespace RebuildBound
open Model

theorem DirectNativeCacheCandidate : Spec.DirectNativeCacheCandidate_statement := by
  intro bits storage tags data bucket remaining home hb hh hp
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  apply Bool.eq_iff_iff.mpr
  rw [DirectCache64Candidate bits storage bucket remaining home (tags (data bucket lane).key)
    lane hb hl hh (hp lane hl)]
  rw [BitVec.getLsbD_and, DirectNative.homeMask, DirectSelect64.getLsbD_ofLanes]
  simp only [hl, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
    DirectPrefix.cachedHome]

theorem DirectNativeCacheHomeMask : Spec.DirectNativeCacheHomeMask_statement := by
  intro bits storage tags data bucket home hb hh hp
  have ht : home < 2 ^ 64 := lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) hb)
  have hn : (BitVec.ofNat 64 home).toNat = home := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
  rw [DirectNativeCacheCandidate bits storage tags data bucket _ _ hb
    (by simpa [hn] using hh) hp, hn, BitVec.allOnes_and]

end RebuildBound
