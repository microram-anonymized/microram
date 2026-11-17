import Mathlib
import RebuildBound.Proofs.S12.Radix

/-!
# S4a helpers: the radix split sheds at most the class excess

For a list `X` of `r` buckets of `C` lanes whose records have classes below `r`,
`radixSplit` sheds at most `Σ_{a<r} (n_a - C)₊` records, where `n_a` is the
number of class-`a` records of `X` (`radixSplit_shed_le`): the shed of class `a`
is exactly `(n_a - C)₊` (`S12.radixSplit_countP`).
-/

namespace RebuildBound.S4aProof

open RebuildBound.Model

/-- A list of classes below `r` splits by class. -/
lemma length_eq_sum_countP (cls : Rec → ℕ) (r : ℕ) : ∀ (l : List Rec),
    (∀ x ∈ l, cls x < r) →
    l.length = ∑ c ∈ Finset.range r, l.countP (fun x => cls x == c) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro h
    have h1 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 : cls x < r := h x (by simp)
    simp only [List.countP_cons, Finset.sum_add_distrib, ← h1, List.length_cons]
    have : ∑ c ∈ Finset.range r, (if cls x == c then 1 else 0) = 1 := by
      simp [h2]
    omega

/-- The number of class-`a` records of input `i`. -/
def cnt (cls : Rec → ℕ) (X : List Bucket) (a i : ℕ) : ℕ :=
  (X.getD i []).recs.countP (fun x => cls x == a)

/-- The radix split sheds at most the class excess `Σ_a (n_a - C)₊`. -/
theorem radixSplit_shed_le (cls : Rec → ℕ) (X : List Bucket) {C : ℕ}
    (hX : ∀ i < X.length, (X.getD i []).length = C)
    (hcls : ∀ i < X.length, ∀ x ∈ (X.getD i []).recs, cls x < X.length) :
    (radixSplit cls X).2.length ≤
      ∑ c ∈ Finset.range X.length, ((∑ i ∈ Finset.range X.length, cnt cls X c i) - C) := by
  have hX' : ∀ B ∈ X, B.length = C := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    rw [← List.getD_eq_getElem _ [] hi]; exact hX i hi
  rw [length_eq_sum_countP cls X.length _ fun x hx => by
    obtain ⟨i, hi, hxi⟩ := S12.radixSplit_mem cls X hx
    exact hcls i hi x hxi]
  exact le_of_eq (Finset.sum_congr rfl fun c hc =>
    S12.radixSplit_countP cls X C hX' (Finset.mem_range.1 hc))

end RebuildBound.S4aProof
