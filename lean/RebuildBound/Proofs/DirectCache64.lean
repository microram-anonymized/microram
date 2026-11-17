import RebuildBound.Spec.DirectCache64
import RebuildBound.Proofs.DirectCache

/-! Fixed-width byte and candidate-mask refinement. The scalar mask loop
reuses `DirectCacheCandidate` and `DirectCacheClear`; SIMD packing, comparison
instruction extraction, and the native hash family remain explicit boundaries. -/
namespace RebuildBound
open Model Model.DirectCache64

private theorem wordByte_nat (word : BitVec 64) (j : Nat) :
    (wordByte word j).toNat = DirectCache.byte word.toNat j := by
  simp only [wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, DirectCache.byte]
  congr 2
  rw [Nat.pow_mul]

theorem DirectCache64Byte : Spec.DirectCache64Byte_statement := by
  intro bits raw j hb
  rw [storedByte, wordByte_nat]
  congr 2
  simp only [BitVec.toNat_and, lowMask, BitVec.toNat_ofNat]
  have hpow : 2 ^ bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hb
  have hlt : 2 ^ bits - 1 < 2 ^ 64 := by
    have hp : 0 < 2 ^ bits := by positivity
    omega
  rw [Nat.mod_eq_of_lt hlt, Nat.and_two_pow_sub_one_eq_mod]

private theorem equalMask_lane (bits : Nat) (storage : Storage) (bucket j : Nat)
    (home : BitVec 64) (lane : Nat) (hl : lane < 64) :
    (equalMask bits storage bucket j home).getLsbD lane =
      ((storage (offset bits bucket j lane)).toNat == DirectCache.byte home.toNat j) := by
  simp only [equalMask, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl,
    Option.map_some, Option.getD_some, hl, decide_true, Bool.true_and]
  have he : ∀ a b : BitVec 8, (a == b) = (a.toNat == b.toNat) := by
    intro a b
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.toNat_inj]
  rw [he, wordByte_nat]

private theorem fold_lane (bits : Nat) (storage : Storage) (bucket : Nat)
    (home : BitVec 64) (lane : Nat) (hl : lane < 64) (js : List Nat)
    (remaining : BitVec 64) :
    (js.foldl (fun mask j => mask &&& equalMask bits storage bucket j home)
      remaining).getLsbD lane =
    (remaining.getLsbD lane && js.all (fun j =>
      (storage (offset bits bucket j lane)).toNat == DirectCache.byte home.toNat j)) := by
  induction js generalizing remaining with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons, ih, BitVec.getLsbD_and,
      equalMask_lane bits storage bucket j home lane hl, List.all_cons,
      Bool.and_assoc]

theorem DirectCache64Fold : Spec.DirectCache64Fold_statement := by
  intro bits storage bucket remaining home lane hl
  exact fold_lane bits storage bucket home lane hl _ remaining

theorem DirectCache64Candidate : Spec.DirectCache64Candidate_statement := by
  intro bits storage bucket remaining home raw lane hb hl hh hp
  rw [DirectCache64Fold bits storage bucket remaining home lane hl]
  apply DirectCacheCandidate bits _ _ (raw.toNat % 2 ^ bits) home.toNat
  · exact Nat.mod_lt _ (by positivity)
  · exact hh
  · intro j hj
    change (storage (offset bits bucket j lane)).toNat = _
    rw [hp j hj, DirectCache64Byte bits raw j hb]

theorem DirectCache64Clear : Spec.DirectCache64Clear_statement := by
  intro bits storage bucket remaining keep home
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  rw [DirectCache64Fold bits storage bucket (remaining &&& keep) home lane hl,
    BitVec.getLsbD_and, BitVec.getLsbD_and,
    DirectCache64Fold bits storage bucket remaining home lane hl]
  exact DirectCacheClear bits _ _ _ home.toNat

/-- Representative endpoint, partial-byte, lane, and layout checks. -/
example : (storedByte 0 (BitVec.ofNat 64 511) 0).toNat = 0 := by decide
example : (storedByte 9 (BitVec.ofNat 64 65535) 1).toNat = 1 := by decide
example : (storedByte 64 (BitVec.ofNat 64 (255 * 2 ^ 56)) 7).toNat = 255 := by decide
example : offset 9 2 1 63 = 383 := by decide
example : (storedByte 64 (BitVec.ofNat 64 (255 * 2 ^ 56 + 171)) 0).toNat = 171 := by decide
example : candidates 0 (fun a => BitVec.ofNat 8 (if a = 63 then 0 else 1)) 0
    (BitVec.ofNat 64 (2 ^ 64 - 1)) (BitVec.ofNat 64 0) =
      BitVec.ofNat 64 (2 ^ 63) := by
  apply BitVec.eq_of_getLsbD_eq
  intro lane hl
  rw [DirectCache64Fold 0 _ 0 _ _ lane hl]
  by_cases he : lane = 63
  · subst lane
    decide
  · have hz : (BitVec.ofNat 64 (2 ^ 63)).getLsbD lane = false := by
      simp only [BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
      simp [Ne.symm he]
    rw [hz]
    simp [DirectCache.candidate, DirectCache.lines, DirectCache.byte, offset, he]
example : (candidates 9 (fun a => BitVec.ofNat 8 (if a = 64 then 2 else 0)) 0
    (BitVec.ofNat 64 1) (BitVec.ofNat 64 256)).getLsbD 0 = false := by
  rw [DirectCache64Fold 9 _ 0 _ _ 0 (by decide)]
  decide
end RebuildBound
