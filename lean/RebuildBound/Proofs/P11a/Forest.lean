import RebuildBound.Proofs.ShadowNet.Core
import RebuildBound.Proofs.ShadowNet.Forest

/-!
# P11a, the forest: caps, sums and locality of the backward test

* `capAll` over a duplicate-free list is the pointwise cap of each listed node;
* `sumAlong` of a count vector is the count vector at the parents;
* `forestTest j` reads only the nodes whose bits in `[lo, j)` equal `R`'s;
* `forestTest j = backStage j (forestTest (j + 1))`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.P11aProof

open RebuildBound.Spec RebuildBound.X1Proof

section ForestTest

variable {b : ℕ}

lemma forestTest_self (C : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞) :
    forestTest C R φ b = φ := by
  simp [forestTest]

lemma forestTest_succ (C : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞) {j : ℕ} (hj : j < b) :
    forestTest C R φ j = backStage C R j (forestTest C R φ (j + 1)) := by
  unfold forestTest
  obtain ⟨n, hn⟩ : ∃ n, b - j = n + 1 := ⟨b - j - 1, by omega⟩
  have hn' : b - (j + 1) = n := by omega
  rw [hn, hn', List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  congr 1
  funext i ψ
  congr 1
  omega

lemma sumAlong_forest {lo j : ℕ} (hj : j < b) (R : Bits b) {x y : States (Bits b)}
    (hxy : ∀ v, Forest lo R j v → ∀ s, x (v, s) = y (v, s)) (v : Bits b)
    (hv : Forest lo R (j + 1) v) (s : Slot) :
    sumAlong (fun V => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩)) x (v, s) =
      sumAlong (fun V => Function.update V ⟨j, hj⟩ (R ⟨j, hj⟩)) y (v, s) := by
  unfold sumAlong
  refine Finset.sum_congr rfl fun V hV => ?_
  rw [Finset.mem_filter] at hV
  apply hxy V _ s
  intro i hi1 hi2
  have hne : i ≠ ⟨j, hj⟩ := fun e => by rw [e] at hi2; simp at hi2
  have := congrFun hV.2 i
  simp only at this
  rw [Function.update_of_ne hne] at this
  rw [this]
  exact hv i hi1 (by omega)

lemma forestTest_readsOnly (C lo : ℕ) (R : Bits b) (φ : States (Bits b) → ℝ≥0∞)
    (hφ : ∀ x y : States (Bits b), (∀ v, InRange lo R v → ∀ s, x (v, s) = y (v, s)) →
      φ x = φ y) :
    ∀ j, lo ≤ j → j ≤ b → ReadsOnly (Forest lo R j) (forestTest C R φ j) := by
  intro j hlo hjb
  obtain ⟨d, hd⟩ : ∃ d, j + d = b := ⟨b - j, by omega⟩
  induction d generalizing j with
  | zero =>
    obtain rfl : j = b := by omega
    rw [forestTest_self]
    intro x y hxy
    apply hφ
    intro v hv s
    exact hxy v (fun i hi _ => hv i hi) s
  | succ d ih =>
    have hj : j < b := by omega
    rw [forestTest_succ C R φ hj, backStage, dite_eq_left hj]
    apply thinAll_readsOnly
    intro x y hxy
    simp only [Function.comp]
    apply ih (j + 1) (by omega) (by omega) (by omega)
    intro v hv s
    apply capAll_congr_node
    intro s'
    exact sumAlong_forest hj R hxy v hv s'

end ForestTest

end RebuildBound.P11aProof
