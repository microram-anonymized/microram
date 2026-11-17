import RebuildBound.Proofs.BlindBits.Bits
import RebuildBound.Proofs.BlindBits.Words

/-!
# G2 helpers: word averages

`avg_comp`: pushing a uniform average forward along a map with fibers of
equal size gives the uniform average on the target. It is applied to

* `resW`, the low `b` bits of the merge family's words of A's keys (from
  `W`-bit words on the complete union), and
* `resO`, the low `k` bits of a `(k + 1)`-bit vector (an old home in `[0, U)`).
-/

open scoped ENNReal

namespace RebuildBound.G2

open RebuildBound.Model RebuildBound.Spec

/-- The low `b` bits of the words of `KA`'s keys. -/
def resW (KA KB : Finset Model.LogicalKey) (W b : ℕ) (hW : {x // x ∈ KA ∪ KB} → Fin (2 ^ W)) :
    {x // x ∈ KA} → Bits b :=
  fun x => natToBits b (hW ⟨x.val, Finset.mem_union_left _ x.prop⟩)

theorem fiber_resW (KA KB : Finset Model.LogicalKey) {W b : ℕ} (hb : b ≤ W) (t : {x // x ∈ KA} → Bits b) :
    (Finset.univ.filter (fun hW => resW KA KB W b hW = t)).card =
      ∏ y : {x // x ∈ KA ∪ KB}, (if y.val ∈ KA then 2 ^ (W - b) else 2 ^ W) := by
  have : Finset.univ.filter (fun hW => resW KA KB W b hW = t) =
      Fintype.piFinset (fun y : {x // x ∈ KA ∪ KB} => Finset.univ.filter
        (fun c : Fin (2 ^ W) => ∀ hy : y.val ∈ KA, natToBits b c = t ⟨y.val, hy⟩)) := by
    ext hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl y hy; rfl
    · intro h; funext x; exact h ⟨x.val, _⟩ x.prop
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun y _ => ?_
  split_ifs with hy
  · rw [show (Finset.univ.filter fun c : Fin (2 ^ W) =>
        ∀ hy : y.val ∈ KA, natToBits b c = t ⟨y.val, hy⟩) =
        Finset.univ.filter (fun c : Fin (2 ^ W) =>
          (c : ℕ) % 2 ^ b = bitsEquiv b (t ⟨y.val, hy⟩)) from ?_]
    · exact card_mod_fiber hb (Fin.isLt _)
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact (natToBits_eq_iff _ _ _).1 (h hy)
      · intro h _; exact (natToBits_eq_iff _ _ _).2 h
  · rw [show (Finset.univ.filter fun c : Fin (2 ^ W) =>
        ∀ hy : y.val ∈ KA, natToBits b c = t ⟨y.val, hy⟩) = Finset.univ from ?_]
    · simp
    · ext c; simp [hy]

theorem resW_fiber_ne_zero (KA KB : Finset Model.LogicalKey) (W b : ℕ) :
    (∏ y : {x // x ∈ KA ∪ KB}, (if y.val ∈ KA then 2 ^ (W - b) else 2 ^ W)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro y _
  split_ifs <;> positivity

/-- The low `k` bits of a `(k + 1)`-bit vector, per key. -/
noncomputable def resO (k : ℕ) {K : Type*} (o : K → Bits (k + 1)) : K → Fin (2 ^ k) :=
  fun x => ⟨(bitsEquiv (k + 1) (o x) : ℕ) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩

theorem fiber_resO (k : ℕ) {K : Type*} [Fintype K] [DecidableEq K] (o : K → Fin (2 ^ k)) :
    (Finset.univ.filter (fun o' : K → Bits (k + 1) => resO k o' = o)).card = ∏ _x : K, 2 := by
  have : Finset.univ.filter (fun o' : K → Bits (k + 1) => resO k o' = o) =
      Fintype.piFinset (fun x => Finset.univ.filter (fun t : Bits (k + 1) =>
        (bitsEquiv (k + 1) t : ℕ) % 2 ^ k = o x)) := by
    ext o'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, resO,
      funext_iff, Fin.ext_iff]
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.card_equiv (bitsEquiv (k + 1))
    (t := Finset.univ.filter (fun c : Fin (2 ^ (k + 1)) => (c : ℕ) % 2 ^ k = o x))]
  · rw [card_mod_fiber (by omega) (o x).isLt]; simp
  · intro t; simp

theorem posOf_resO (k : ℕ) {K : Type*} (o' : K → Bits (k + 1)) (x : K) :
    natToBits (k + 1) (2 ^ k + (resO k o' x : ℕ)) = Function.update (o' x) (Fin.last k) true := by
  funext i
  simp only [natToBits, resO]
  by_cases hi : i = Fin.last k
  · subst hi
    rw [Function.update_self, Fin.val_last, Nat.testBit_two_pow_add_eq,
      testBit_eq_false_of_lt_pow (Nat.mod_lt _ (by positivity)) le_rfl]
    rfl
  · rw [Function.update_of_ne hi]
    have hik : (i : ℕ) < k := by
      have := i.isLt
      have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
      omega
    rw [Nat.testBit_two_pow_add_gt hik, Nat.testBit_mod_two_pow, testBit_bitsEquiv]
    simp [hik]

end RebuildBound.G2
