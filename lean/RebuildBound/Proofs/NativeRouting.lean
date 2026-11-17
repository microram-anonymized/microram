import RebuildBound.Spec.NativeRouting
import RebuildBound.Proofs.NativeRouting.Lanes

namespace RebuildBound
open Spec Spec.NativeRouting

namespace NativeRoutingProof

theorem packed_injective (d e : Bool) (c c' : Counter) (l l' : Level) :
    packed d c l = packed e c' l' ↔ d = e ∧ c = c' ∧ l = l' := by
  cases d <;> cases e <;> simp [packed, Fin.ext_iff] <;> omega

private theorem level_and_domain (l : Level) : l.val &&& 2^63 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hi : 63 = i
  · subst i
    have hl : l.val < 2^63 := by omega
    simp [Nat.testBit_lt_two_pow hl]
  · simp [hi]

theorem rawPacked_eq (d : Bool) (c : Counter) (l : Level) :
    (rawPacked (nonceLow d l) (BitVec.ofNat 64 c.val)).toNat = (packed d c l).val := by
  have hrest : c.val * 2^15 + l.val < 2^63 := by omega
  have hc : c.val < 2^64 := by omega
  have hl : l.val < 2^63 := by omega
  have hshift : c.val * 2^15 < 2^64 :=
    Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hrest) (by decide)
  have hlow : (if d then 2^63 else 0) + l.val < 2^64 := by cases d <;> simp <;> omega
  have hcounter : c.val &&& 0x0000ffffffffffff = c.val :=
    Nat.and_two_pow_sub_one_of_lt_two_pow c.isLt
  have hlevel : ((if d then 2^63 else 0) + l.val) &&& 0x7fff = l.val := by
    change ((if d then 2^63 else 0) + l.val) &&& (2^15 - 1) = l.val
    rw [Nat.and_two_pow_sub_one_eq_mod]
    cases d <;> simp <;> omega
  have hdomain : ((if d then 2^63 else 0) + l.val) &&& 2^63 =
      (if d then 2^63 else 0) := by
    cases d
    · simpa using level_and_domain l
    · simp only [↓reduceIte]
      rw [show 2^63 + l.val = 2^63 ||| l.val by
        simpa using Nat.two_pow_add_eq_or_of_lt hl 1]
      rw [Nat.and_or_distrib_right, Nat.and_self, level_and_domain, Nat.or_zero]
  simp only [rawPacked, nonceLow, BitVec.toNat_or, BitVec.toNat_and,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [Nat.mod_eq_of_lt hlow, Nat.mod_eq_of_lt hc]
  change (((if d then 2^63 else 0) + l.val) &&& 2^63) |||
      (((c.val &&& 0x0000ffffffffffff) <<< 15) % 2^64) |||
      (((if d then 2^63 else 0) + l.val) &&& 0x7fff) = _
  rw [hcounter, hlevel, hdomain, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hshift,
    Nat.or_assoc]
  have hjoin : c.val * 2^15 ||| l.val = c.val * 2^15 + l.val := by
    have h := (Nat.two_pow_add_eq_or_of_lt l.isLt c.val).symm
    rw [Nat.mul_comm (2^15)] at h
    exact h
  rw [hjoin]
  cases d
  · simp [packed]
  · have hor := Nat.two_pow_add_eq_or_of_lt hrest 1
    simp only [Nat.mul_one] at hor
    simpa [packed, Nat.add_assoc] using hor.symm

theorem message_injective (d e : Bool) (c c' : Counter) (l l' : Level)
    (lo hi lo' hi' : Word) :
    message d c l lo hi = message e c' l' lo' hi' ↔
      d = e ∧ c = c' ∧ l = l' ∧ lo = lo' ∧ hi = hi' := by
  simp only [message, Prod.mk.injEq, packed_injective, and_true]
  constructor
  · rintro ⟨⟨hd, hc, hl⟩, hlo, hhi⟩
    exact ⟨hd, hc, hl, hlo, hhi⟩
  · rintro ⟨hd, hc, hl, hlo, hhi⟩
    exact ⟨⟨hd, hc, hl⟩, hlo, hhi⟩

/-- Domains cannot alias, even when family coordinates and key words differ. -/
theorem real_dummy_ne (c c' : Counter) (l l' : Level) (lo hi lo' hi' : Word) :
    message false c l lo hi ≠ message true c' l' lo' hi' := by
  intro h
  exact Bool.noConfusion ((message_injective _ _ _ _ _ _ _ _ _ _).mp h).1

/-- The empty top's zero ordinal cannot alias an ordinary family's positive ordinal. -/
theorem ordinary_empty_ne (d e : Bool) (c : Counter) (hc : 0 < c.val)
    (l top : Level) : packed d c l ≠ packed e 0 top := by
  intro h
  have := ((packed_injective _ _ _ _ _ _).mp h).2.1
  have := congrArg Fin.val this
  simp at this
  omega

/-- One-based levels keep family identities separate from the dense sentinel. -/
theorem packed_ne_zero (d : Bool) (c : Counter) (l : Level) (hl : 0 < l.val) :
    packed d c l ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  cases d <;> simp [packed] at this <;> omega

end NativeRoutingProof

theorem NativeRoutingPacking : NativeRoutingPacking_statement :=
  ⟨NativeRoutingProof.rawPacked_eq, NativeRoutingProof.packed_injective⟩

theorem NativeRoutingMessage : NativeRoutingMessage_statement :=
  NativeRoutingProof.message_injective

end RebuildBound
