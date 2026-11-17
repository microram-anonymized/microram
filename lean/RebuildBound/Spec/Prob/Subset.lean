import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The subset witness (trusted spec, package P3)

`REPORT.tex`, Proposition `prop:general-subset`. If a storage demand is at most
`Σ_v (Z_v - C)₊` and every subset `J` of the `n` nodes satisfies the MGF
envelope `E z^(Σ_{v ∈ J} Z_v) ≤ D exp(λ |J| (z - 1))` for `z ≥ 1`, then the
demand exceeds `S` with probability at most `Bsub n C λ S D`. No
independence of the `Z_v` is assumed.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec

/-- The optimized Markov base for subsets of size `j`: `(C j + S + 1) / (λ j)`. -/
noncomputable def subsetZ (C : ℕ) (lam : ℝ) (S j : ℕ) : ℝ :=
  ((C * j + S + 1 : ℕ) : ℝ) / (lam * j)

/-- `B_sub(n, C, λ, S, D) = min(1, D Σ_{j=1}^n C(n,j) exp(λ j (z_j - 1)) / z_j^(Cj+S+1))`
(`eq:general-subset`). -/
noncomputable def Bsub (n C : ℕ) (lam : ℝ) (S : ℕ) (D : ℝ) : ℝ :=
  min 1 (D * ∑ j ∈ Finset.Icc 1 n,
    (n.choose j : ℝ) * Real.exp (lam * j * (subsetZ C lam S j - 1)) /
      subsetZ C lam S j ^ (C * j + S + 1))

/-- **P3, the subset witness.** For a probability law `ν` of the count vector
`Z : Fin n → ℕ` with the subset MGF envelope and `0 < λ ≤ C`, the total
excess `Σ_v (Z_v - C)₊` exceeds `S` with probability at most `Bsub`. -/
def P3_statement : Prop :=
  ∀ (n C S : ℕ) (lam D : ℝ) (ν : Measure (Fin n → ℕ)), IsProbabilityMeasure ν →
    0 < lam → lam ≤ C → 0 ≤ D →
    (∀ (J : Finset (Fin n)) (z : ℝ), 1 ≤ z →
      ∫⁻ x, ENNReal.ofReal (z ^ (∑ v ∈ J, x v)) ∂ν ≤
        ENNReal.ofReal (D * Real.exp (lam * J.card * (z - 1)))) →
    ν {x | S < ∑ v, (x v - C)} ≤ ENNReal.ofReal (Bsub n C lam S D)

end RebuildBound.Spec
