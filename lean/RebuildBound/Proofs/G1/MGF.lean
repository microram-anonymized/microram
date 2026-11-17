import RebuildBound.Proofs.FiniteCoupling.Prob
import RebuildBound.Proofs.G1.Count

/-!
# G1: the subset MGF envelopes

* Stage `j` (the raw destinations of the complete A population): for every set
  `J` of the `2U` nodes and `z ≥ 1`,
  `E z^(Σ_{v ∈ J} X_{j,v}) ≤ D exp(λ |J| (z - 1))`.
  Given A's history, the merge words of A's keys are independent and uniform,
  so the conditional MGF is `Π_{x ∈ KA} ψ(O_x)` with `ψ(o)` the average of
  `z^[rawDest ∈ J]` over one word; grouping the histories by the old-home
  vector `O` and the density factor `D` give
  `D (U⁻¹ Σ_o ψ(o))^|KA| ≤ D (1 + (z - 1)|J| / U)^|KA|` (column sums of the
  raw destination map), and `|KA| ≤ λ U`.
* The complete union's homes: `E z^(Σ_{v ∈ J} X_v) ≤ exp(λ |J| (z - 1))`, the
  words of the `|KA ∪ KB| ≤ 2 λ U` keys being independent and uniform mod `2U`.
-/

open scoped ENNReal NNReal

namespace RebuildBound.G1Proof

open RebuildBound.Model RebuildBound.Spec

variable {g : Geom} (L : JobLaw g)

theorem U_pos (g : Geom) : 0 < g.U := by unfold Geom.U; positivity

theorem homes_eq (g : Geom) : g.homes = 2 * g.U := by
  unfold Geom.homes Geom.U; rw [pow_succ]; ring

theorem wordFn_val (h : L.Key → Fin (2 ^ L.W)) (y : L.Key) : L.wordFn h y = (h y : ℕ) := by
  unfold JobLaw.wordFn; simp [y.2]

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

/-- Grouping A's histories by their old-home vector: the density factor `D`. -/
theorem density_bound {lam D : ℝ≥0} (hL : InputLaw L lam D)
    (ψ : ℕ → ℝ) (hψ : ∀ o, 0 ≤ ψ o) :
    ∑ hist, L.weight hist * ENNReal.ofReal (∏ x ∈ L.KA, ψ (L.wOld hist x % g.U)) ≤
      ENNReal.ofReal (D * ((g.U : ℝ)⁻¹ * ∑ o : Fin g.U, ψ o) ^ L.KA.card) := by
  have hU := U_pos g
  let oh : L.Hist → (L.KA → Fin g.U) := fun hist x => ⟨L.wOld hist x % g.U, Nat.mod_lt _ hU⟩
  let Φ : (L.KA → Fin g.U) → ℝ := fun o => ∏ x : L.KA, ψ (o x)
  have hΦ : ∀ o, 0 ≤ Φ o := fun o => Finset.prod_nonneg fun x _ => hψ _
  have e : ∀ hist, ∏ x ∈ L.KA, ψ (L.wOld hist x % g.U) = Φ (oh hist) := by
    intro hist
    exact (Finset.prod_coe_sort L.KA (fun x => ψ (L.wOld hist x % g.U))).symm
  simp_rw [e]
  rw [← Finset.sum_fiberwise Finset.univ oh]
  calc ∑ o, ∑ hist ∈ Finset.univ.filter (fun hist => oh hist = o),
        L.weight hist * ENNReal.ofReal (Φ (oh hist))
      = ∑ o, (∑ hist ∈ Finset.univ.filter (fun hist => oh hist = o), L.weight hist) *
          ENNReal.ofReal (Φ o) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun hist hh => ?_
        rw [(Finset.mem_filter.mp hh).2]
    _ ≤ ∑ o, ((D : ℝ≥0∞) / (g.U : ℝ≥0∞) ^ L.KA.card) * ENNReal.ofReal (Φ o) := by
        gcongr with o _
        have hd := hL.density o
        convert hd using 2
        ext hist
        simp [oh, funext_iff, Fin.ext_iff]
    _ = ENNReal.ofReal (D * (((Fintype.card (L.KA → Fin g.U) : ℕ) : ℝ)⁻¹ * ∑ o, Φ o)) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun o _ => hΦ o)]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast, div_eq_mul_inv]
        push_cast
        rfl
    _ = ENNReal.ofReal (D * ((g.U : ℝ)⁻¹ * ∑ o : Fin g.U, ψ o) ^ L.KA.card) := by
        rw [avg_prod g.U (fun _ a => ψ a), Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end RebuildBound.G1Proof
