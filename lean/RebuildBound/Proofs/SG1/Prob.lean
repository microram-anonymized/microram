import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Spec.SepG
import RebuildBound.Proofs.ProductAverage

/-!
# SG1: the job law's union bounds and word averages (port of `G1/MGF.lean`)

The union bounds stay for the `DirectJob*` consumers; elsewhere use
`FiniteLawProof.prob_*_of L.prob_eq`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : SepGeom} (L : SJobLaw g)

/-- Monotonicity of `SJobLaw.prob`; only the word functions `wordFn h` matter. -/
theorem prob_mono {E F : L.Hist → (Model.LogicalKey → ℕ) → Prop}
    (h : ∀ hist hw, E hist (L.wordFn hw) → F hist (L.wordFn hw)) : L.prob E ≤ L.prob F := by
  exact FiniteLawProof.prob_mono L.weight L.wordFn h

/-- Subadditivity of `SJobLaw.prob`. -/
theorem prob_or (E F : L.Hist → (Model.LogicalKey → ℕ) → Prop) :
    L.prob (fun hist w => E hist w ∨ F hist w) ≤ L.prob E + L.prob F := by
  exact FiniteLawProof.prob_or L.weight L.wordFn E F

/-- Finite subadditivity of `SJobLaw.prob`. -/
theorem prob_exists_lt (n : ℕ) (E : ℕ → L.Hist → (Model.LogicalKey → ℕ) → Prop) :
    L.prob (fun hist w => ∃ j < n, E j hist w) ≤ ∑ j ∈ Finset.range n, L.prob (E j) := by
  exact FiniteLawProof.prob_exists_lt L.weight L.wordFn n E

theorem wordFn_val (h : L.Key → Fin (2 ^ L.W)) (y : L.Key) : L.wordFn h y = (h y : ℕ) := by
  unfold SJobLaw.wordFn; simp [y.2]

theorem prod_key_ite (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) (A : Model.LogicalKey → ℝ) :
    ∏ y : L.Key, (if (y : Model.LogicalKey) ∈ K then A y else 1) = ∏ x ∈ K, A x := by
  exact ProductAverage.prod_key_ite (L.KA ∪ L.KB) K hK A

/-- The uniform average over the merge words of a product over keys `K ⊆ KA ∪ KB`
of per-key factors is the product of the per-key averages. -/
theorem avg_wordFn_prod (K : Finset Model.LogicalKey) (hK : K ⊆ L.KA ∪ L.KB) (φ : Model.LogicalKey → ℕ → ℝ)
    (hφ : ∀ x a, 0 ≤ φ x a) :
    (Fintype.card (L.Key → Fin (2 ^ L.W)) : ℝ≥0∞)⁻¹ *
      ∑ h : L.Key → Fin (2 ^ L.W), ENNReal.ofReal (∏ x ∈ K, φ x (L.wordFn h x)) =
    ENNReal.ofReal (∏ x ∈ K, (((2 ^ L.W : ℕ) : ℝ))⁻¹ * ∑ a : Fin (2 ^ L.W), φ x a) := by
  exact ProductAverage.avg_wordFn_prod (L.KA ∪ L.KB) (2 ^ L.W) (by positivity)
    L.wordFn (wordFn_val L) K hK φ hφ

end RebuildBound.SG1Proof
