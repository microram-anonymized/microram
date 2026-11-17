import RebuildBound.Spec.Prob.Network

/-!
# The binary shadow tree and the completed-A range law (trusted spec)

`REPORT.tex`, subsection "The finite loss tree and its error bound", and
Proposition "Completed-A coarse-range bound", case `r = 1`. These are the laws
whose stop-loss the numerical certificates bound (`Proofs/NCA1`, `Proofs/NCA5`).

* `shadowTree C λ t` is the law of `F_t = (M_t, R_t)`. At depth one,
  `N ∼ Po(λ)` and `(M, R) = (min N C, (N - C)₊)`. The next depth takes two
  independent child states, thins each child's main and shadow counts
  independently by `1/2`, adds them and caps: `(min U C, V + (U - C)₊)`.
  There is no final thinning.
* `rangeLaw C λ P p g t` is the law of `Y = E + Z₁ + ⋯ + Z_g`: an early count
  `E ∼ Bin(P, p)` and `g` independent root losses `Zᵢ ∼ R_t`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The cap of one node state: `(M, R) ↦ (min M C, R + (M - C))`. -/
def capPair (C : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := (min s.1 C, s.2 + (s.1 - C))

/-- Independent binomial thinning of both counts of one node state. -/
noncomputable def thinPair (p : I) (s : ℕ × ℕ) : Measure (ℕ × ℕ) :=
  (binomial s.1 p).prod (binomial s.2 p)

/-- The law of the binary shadow tree's root state after `t` capped levels. -/
noncomputable def shadowTree (C : ℕ) (lam : ℝ≥0) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (0, 0)
  | 1 => (poissonMeasure lam).map (fun n => capPair C (n, 0))
  | t + 2 =>
    let child := (shadowTree C lam (t + 1)).bind (thinPair half)
    (child ∗ child).map (capPair C)

/-- `natConvPow μ g` is the law of the sum of `g` independent draws from `μ`. -/
noncomputable def natConvPow (μ : Measure ℕ) : ℕ → Measure ℕ
  | 0 => Measure.dirac 0
  | g + 1 => natConvPow μ g ∗ μ

/-- The law of `Y = E + Z₁ + ⋯ + Z_g` with `E ∼ Bin(P, p)` and independent root
losses `Zᵢ`, each the shadow count of `shadowTree C λ t`. -/
noncomputable def rangeLaw (C : ℕ) (lam : ℝ≥0) (P : ℕ) (p : I) (g t : ℕ) : Measure ℕ :=
  binomial P p ∗ natConvPow ((shadowTree C lam t).map Prod.snd) g

/-- The stop-loss `E (Y - L)₊` of a law on counts. -/
noncomputable def stopLoss (μ : Measure ℕ) (L : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, ((y - L : ℕ) : ℝ≥0∞) ∂μ

end RebuildBound.Spec
