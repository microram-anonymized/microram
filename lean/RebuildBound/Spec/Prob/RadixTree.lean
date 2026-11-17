import RebuildBound.Spec.Prob.ShadowTree

/-!
# The radix root and the completed-A range law at a general digit (trusted spec)

`REPORT.tex`, Proposition "Completed-A coarse-range bound", for every odd
radix `r` (case `r = 1` included). These are the laws whose stop-loss the
completed-A certificates bound.

* `qMass W b r a`: the class mass `q_a = #{0 ≤ h < 2^(W-b) : h mod r = a} / 2^(W-b)`
  of a uniform `W`-bit word whose bits from `b` on are reduced mod `r`.
* `radixRoot C λ t r q` is the law of the root loss `Z_a` of class `a`: take `r`
  independent copies of the binary shadow tree's root state `F_t = (M_t, R_t)`
  (`shadowTree`), thin both counts of each copy independently by `q = q_a`,
  add the copies, and cap the sum: `Z_a = Σ_j V_j + (Σ_j U_j - C)₊`. At
  `r = 1`, `q = 1` it is the law of `R_t`.
* `rangeLawR C λ P g t r q` is the law of `Y_a = E_a + Z_a⁽¹⁾ + ⋯ + Z_a⁽ᵍ⁾`:
  an early count `E_a ∼ Bin(P, q 2^-t)` and `g` independent root losses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The number of `h < 2^(W - b)` with `h mod r = a`. -/
def qCount (W b r a : ℕ) : ℕ := ((Finset.range (2 ^ (W - b))).filter (fun h => h % r = a)).card

theorem qCount_le (W b r a : ℕ) : qCount W b r a ≤ 2 ^ (W - b) :=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le

/-- The class mass `q_a = #{h < 2^(W - b) : h mod r = a} / 2^(W - b)`. -/
noncomputable def qMass (W b r a : ℕ) : I :=
  ⟨(qCount W b r a : ℝ) / 2 ^ (W - b),
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _),
    (div_le_one (pow_pos (by norm_num) _)).2 (by exact_mod_cast qCount_le W b r a)⟩

/-- `pairConvPow μ n` is the law of the sum of `n` independent draws from `μ`. -/
noncomputable def pairConvPow (μ : Measure (ℕ × ℕ)) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (0, 0)
  | n + 1 => pairConvPow μ n ∗ μ

/-- The law of the root loss `Z = Σ_j V_j + (Σ_j U_j - C)₊` of the terminal radix
node over `r` independent root states `F_t`, each thinned by `q`. -/
noncomputable def radixRoot (C : ℕ) (lam : ℝ≥0) (t r : ℕ) (q : I) : Measure ℕ :=
  (pairConvPow ((shadowTree C lam t).bind (thinPair q)) r).map fun s => s.2 + (s.1 - C)

/-- The law of `Y = E + Z₁ + ⋯ + Z_g` with `E ∼ Bin(P, q 2^-t)` and independent
radix root losses `Zᵢ ∼ radixRoot C λ t r q`. -/
noncomputable def rangeLawR (C : ℕ) (lam : ℝ≥0) (P g t r : ℕ) (q : I) : Measure ℕ :=
  binomial P (q * halfPow t) ∗ natConvPow (radixRoot C lam t r q) g

end RebuildBound.Spec
