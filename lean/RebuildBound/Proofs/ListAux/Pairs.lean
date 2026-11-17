import Mathlib
import RebuildBound.Spec.T

/-!
# ListAux: pair partner indices (from D5)

`testBit_add_pow`, `pow_add_lt` (the partner `i + 2^j` of a pair stays in
range), `getD_set_ne` on buckets and `recs_getD_sub`. Moved from the binary
d = 2 chain (`D5`); namespace `RebuildBound.D5` kept.
-/

namespace RebuildBound
open RebuildBound.Model RebuildBound.Spec
namespace D5
/-- A partner index `i + 2^j` has bit `j` set when `i` has it clear. -/
theorem testBit_add_pow {i j : Nat} (h : i.testBit j = false) : (i + 2 ^ j).testBit j = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq]; simp [h]

/-- Buckets read by a pair are unchanged by writes at disjoint pairs. -/
theorem getD_set_ne (l : List Bucket) {a b : Nat} (h : a ≠ b) (x : Bucket) :
    (l.set a x).getD b [] = l.getD b [] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem recs_getD_sub (l : List Bucket) (i : Nat) :
    (l.getD i []).recs = [] ∨ l.getD i [] ∈ l := by
  by_cases h : i < l.length
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; rw [List.getD_eq_default _ _ (by omega)]; rfl

end D5
namespace D5
theorem pow_add_lt {i j k : Nat} (hj : j ≤ k) (hi : i < 2 ^ (k + 1)) (hb : i.testBit j = false) :
    i + 2 ^ j < 2 ^ (k + 1) := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hbt : i / 2 ^ j % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    have := Nat.mod_two_eq_zero_or_one (i / 2 ^ j)
    simp at hb; omega
  obtain ⟨e, he⟩ : ∃ e, k + 1 = j + 1 + e := ⟨k - j, by omega⟩
  have hpow : 2 ^ (k + 1) = 2 ^ j * (2 * 2 ^ e) := by
    rw [he, Nat.pow_add, Nat.pow_succ]; ring
  have hm : i / 2 ^ j < 2 * 2 ^ e := by
    rw [Nat.div_lt_iff_lt_mul hP]; rw [hpow] at hi; linarith
  have h1 : i < 2 ^ j * (i / 2 ^ j + 1) := by
    have := Nat.lt_mul_div_succ i hP; linarith
  have h2 : i / 2 ^ j + 2 ≤ 2 * 2 ^ e := by omega
  calc i + 2 ^ j < 2 ^ j * (i / 2 ^ j + 1) + 2 ^ j := by omega
    _ = 2 ^ j * (i / 2 ^ j + 2) := by ring
    _ ≤ 2 ^ j * (2 * 2 ^ e) := Nat.mul_le_mul_left _ h2
    _ = _ := hpow.symm

end D5
end RebuildBound
