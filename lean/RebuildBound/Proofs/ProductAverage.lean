import RebuildBound.Spec.Model.Key
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-! Uniform product averages, independent of geometry and job models.
The word interpretation law is needed only on keys in the ambient finite set. -/

open scoped ENNReal

namespace RebuildBound.ProductAverage

theorem avg_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : ι → Fin m → ℝ) :
    ((Fintype.card (ι → Fin m) : ℝ))⁻¹ * ∑ h : ι → Fin m, ∏ i, f i (h i) =
      ∏ i, ((m : ℝ)⁻¹ * ∑ a, f i a) := by
  rw [← Fintype.prod_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [inv_pow]

theorem prod_key_ite (keys K : Finset Model.LogicalKey) (hK : K ⊆ keys) (A : Model.LogicalKey → ℝ) :
    ∏ y : keys, (if (y : Model.LogicalKey) ∈ K then A y else 1) = ∏ x ∈ K, A x := by
  rw [Finset.prod_coe_sort keys (fun x => if x ∈ K then A x else 1),
    Finset.prod_ite_mem, Finset.inter_eq_right.mpr hK]

/-- Independent uniform words factor the average for any included key set.
Positivity of the word cardinal and nonnegativity of the factors are explicit. -/
theorem avg_wordFn_prod (keys : Finset Model.LogicalKey) (m : ℕ) (hm : 0 < m)
    (wordFn : (keys → Fin m) → Model.LogicalKey → ℕ)
    (hword : ∀ (h : keys → Fin m) (y : keys), wordFn h y = (h y : ℕ))
    (K : Finset Model.LogicalKey) (hK : K ⊆ keys) (φ : Model.LogicalKey → ℕ → ℝ)
    (hφ : ∀ x a, 0 ≤ φ x a) :
    (Fintype.card (keys → Fin m) : ℝ≥0∞)⁻¹ *
      ∑ h : keys → Fin m, ENNReal.ofReal (∏ x ∈ K, φ x (wordFn h x)) =
    ENNReal.ofReal (∏ x ∈ K, (m : ℝ)⁻¹ * ∑ a : Fin m, φ x a) := by
  have hcard : 0 < Fintype.card (keys → Fin m) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    positivity
  have e1 : ∀ h : keys → Fin m, ∏ x ∈ K, φ x (wordFn h x) =
      ∏ y : keys, (if (y : Model.LogicalKey) ∈ K then φ y (h y) else 1) := by
    intro h
    rw [← prod_key_ite keys K hK (fun x => φ x (wordFn h x))]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [hword]
  simp_rw [e1]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => Finset.prod_nonneg fun y _ => by
    split_ifs
    · exact hφ _ _
    · exact zero_le_one)]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcard),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [avg_prod m (fun (y : keys) (a : Fin m) => if (y : Model.LogicalKey) ∈ K then φ y a else 1)]
  rw [← prod_key_ite keys K hK]
  refine Finset.prod_congr rfl fun y _ => ?_
  split_ifs
  · rfl
  · simp [hm.ne']

end RebuildBound.ProductAverage
