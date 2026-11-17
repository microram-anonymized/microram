import RebuildBound.Proofs.ProductAverage
import RebuildBound.Proofs.SG1.Prob

/-!
# SG1: old homes lie below `(d - 1) U`, and the density bound
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.SG1Proof

open RebuildBound.Model RebuildBound.Spec

theorem val2Aux_dvd : ∀ (fuel n : ℕ), 2 ^ (val2Aux fuel n) ∣ n
  | 0, n => by simp [val2Aux]
  | fuel + 1, n => by
    unfold val2Aux
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      have := val2Aux_dvd fuel (n / 2)
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      have : n = 2 * (n / 2) := by omega
      rw [pow_succ]
      calc n = 2 * (n / 2) := this
        _ = 2 * (2 ^ val2Aux fuel (n / 2) * c) := by rw [← hc]
        _ = _ := by ring
    · simp

theorem val2_dvd (n : ℕ) : 2 ^ val2 n ∣ n := val2Aux_dvd n n

theorem oldHome_lt (g : SepGeom) (hd : 2 ≤ g.d) (t : ℕ) : g.oldHome t < (g.d - 1) * g.U := by
  unfold SepGeom.oldHome digitHome
  simp only
  obtain ⟨m, hm⟩ := val2_dvd (g.d - 1)
  generalize val2 (g.d - 1) = e at hm ⊢
  have hpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; omega
    · exact h
  have hdm : (g.d - 1) / 2 ^ e = m := by
    rw [hm, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hdm]
  set P := 2 ^ (g.K + e) with hP
  have hPpos : 0 < P := by positivity
  have h1 : t % P < P := Nat.mod_lt _ hPpos
  have h2 : t / P % m < m := Nat.mod_lt _ hpos
  have h3 : (g.d - 1) * g.U = P * m := by
    unfold SepGeom.U
    rw [hP, pow_add, hm]; ring
  rw [h3]
  calc t % P + P * (t / P % m) < P + P * (t / P % m) := by omega
    _ = P * (t / P % m + 1) := by ring
    _ ≤ P * m := Nat.mul_le_mul_left _ h2

theorem U_pos (g : SepGeom) : 0 < g.U := by unfold SepGeom.U; positivity

theorem N_eq (g : SepGeom) : g.N = g.d * g.U := by
  unfold SepGeom.N SepGeom.d SepGeom.U SepGeom.k
  rw [pow_add]; ring

/-- Grouping histories by a function `oh` into `Fin M` with density `D`. -/
theorem density_bound_M {g : SepGeom} (L : SJobLaw g) {D : ℝ≥0} (K : Finset Model.LogicalKey) (M : ℕ) (hM : 0 < M)
    (oh : L.Hist → (K → Fin M))
    (hdens : ∀ o : K → Fin M,
      (∑ hist ∈ Finset.univ.filter (fun hist => oh hist = o), L.weight hist) ≤
        (D : ℝ≥0∞) / (M : ℝ≥0∞) ^ K.card)
    (ψ : Fin M → ℝ) (hψ : ∀ o, 0 ≤ ψ o) :
    ∑ hist, L.weight hist * ENNReal.ofReal (∏ x : K, ψ (oh hist x)) ≤
      ENNReal.ofReal (D * ((M : ℝ)⁻¹ * ∑ o : Fin M, ψ o) ^ K.card) := by
  classical
  let Φ : (K → Fin M) → ℝ := fun o => ∏ x : K, ψ (o x)
  have hΦ : ∀ o, 0 ≤ Φ o := fun o => Finset.prod_nonneg fun x _ => hψ _
  rw [← Finset.sum_fiberwise Finset.univ oh]
  calc ∑ o, ∑ hist ∈ Finset.univ.filter (fun hist => oh hist = o),
        L.weight hist * ENNReal.ofReal (∏ x : K, ψ (oh hist x))
      = ∑ o, (∑ hist ∈ Finset.univ.filter (fun hist => oh hist = o), L.weight hist) *
          ENNReal.ofReal (Φ o) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun hist hh => ?_
        rw [(Finset.mem_filter.mp hh).2]
    _ ≤ ∑ o, ((D : ℝ≥0∞) / (M : ℝ≥0∞) ^ K.card) * ENNReal.ofReal (Φ o) := by
        gcongr with o _
        exact hdens o
    _ = ENNReal.ofReal (D * (((Fintype.card (K → Fin M) : ℕ) : ℝ)⁻¹ * ∑ o, Φ o)) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun o _ => hΦ o)]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast, div_eq_mul_inv]
        push_cast
        rfl
    _ = ENNReal.ofReal (D * ((M : ℝ)⁻¹ * ∑ o : Fin M, ψ o) ^ K.card) := by
        rw [ProductAverage.avg_prod M (fun _ a => ψ a), Finset.prod_const, Finset.card_univ,
          Fintype.card_coe]

end RebuildBound.SG1Proof
