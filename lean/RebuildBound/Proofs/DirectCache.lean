import RebuildBound.Spec.DirectCache
import Mathlib.Tactic

namespace RebuildBound
open Model Model.DirectCache

theorem DirectCacheLines : Spec.DirectCacheLines_statement := by
  intro bits
  unfold lines
  split_ifs with h
  · omega
  · omega

private theorem byte_div (a j : Nat) : byte (a / 256) j = byte a (j + 1) := by
  simp only [byte, Nat.div_div_eq_div_mul, Nat.pow_succ']

/-- Peel the low byte and induct on the remaining little-endian bytes. -/
theorem DirectCacheBytes : Spec.DirectCacheBytes_statement := by
  intro count
  induction count with
  | zero =>
    intro a b ha hb
    simp only [Nat.pow_zero] at ha hb
    have : a = b := by omega
    simp [this]
  | succ count ih =>
    intro a b ha hb
    constructor
    · intro h
      have hqa : a / 256 < 256 ^ count := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
        simpa only [Nat.pow_succ] using ha
      have hqb : b / 256 < 256 ^ count := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
        simpa only [Nat.pow_succ] using hb
      have hquot : a / 256 = b / 256 := (ih _ _ hqa hqb).mp (by
        intro j hj
        rw [byte_div, byte_div]
        exact h (j + 1) (by omega))
      have hmod : a % 256 = b % 256 := by
        simpa [byte] using h 0 (by omega)
      have ha' := Nat.mod_add_div a 256
      have hb' := Nat.mod_add_div b 256
      omega
    · intro h
      subst b
      exact fun _ _ => rfl

private theorem width_le (bits : Nat) : 2 ^ bits ≤ 256 ^ lines bits := by
  have hbits := (DirectCacheLines bits).2.1
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hbits
  simpa only [pow_mul, show (2 : Nat) ^ 8 = 256 from rfl] using h

theorem DirectCacheHome : Spec.DirectCacheHome_statement := by
  intro bits word r home hhome
  have hvalue : DirectPrefix.cachedHome word (2 ^ bits) r < 2 ^ bits :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  exact DirectCacheBytes (lines bits) _ _
    (lt_of_lt_of_le hvalue (width_le bits))
    (lt_of_lt_of_le hhome (width_le bits))

theorem DirectCacheCandidate : Spec.DirectCacheCandidate_statement := by
  intro bits cache remaining value home hvalue hhome henc
  have hb := DirectCacheBytes (lines bits) value home
    (lt_of_lt_of_le hvalue (width_le bits))
    (lt_of_lt_of_le hhome (width_le bits))
  unfold candidate
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  have he : (∀ j, j < lines bits → cache j = byte home j) ↔ value = home := by
    rw [← hb]
    constructor
    · intro h j hj
      rw [← henc j hj]
      exact h j hj
    · intro h j hj
      rw [henc j hj]
      exact h j hj
  rw [he]

theorem DirectCacheClear : Spec.DirectCacheClear_statement := by
  intro bits cache remaining keep home
  unfold candidate
  cases remaining <;> cases keep <;> simp

-- The zero-bit policy still compares one zero byte.
example : lines 0 = 1 ∧ candidate 0 (byte 0) true 0 = true ∧
    candidate 0 (byte 0) false 0 = false := by decide
-- A partial high byte is necessary for nine-bit homes sharing their low byte.
example : lines 9 = 2 ∧ byte 511 0 = 255 ∧ byte 511 1 = 1 ∧
    candidate 9 (byte 511) true 511 = true ∧
    candidate 9 (byte 255) true 511 = false := by decide
-- Eight byte lines cover the complete supported 64-bit word width.
example : lines 64 = 8 ∧ 2 ^ 64 = 256 ^ lines 64 := by decide +kernel
-- A malformed live cache can create a false match: encoding is a premise.
example : (1 : Nat) < 2 ^ 8 ∧ (0 : Nat) < 2 ^ 8 ∧
    candidate 8 (fun _ => 0) true 0 = true ∧ (1 : Nat) ≠ 0 := by decide
example : ¬ Encodes 8 (fun _ => 0) 1 := by
  intro h
  have := h 0 (by decide)
  norm_num [byte] at this
-- Dropping the queried-home range premise permits a low-byte alias.
example : candidate 8 (byte 0) true 256 = true ∧ (0 : Nat) ≠ 256 := by decide
-- A clear suppresses even a malformed matching cache, retaining its bytes.
example : candidate 9 (fun _ => 0) (true && false) 0 = false := by decide
end RebuildBound
