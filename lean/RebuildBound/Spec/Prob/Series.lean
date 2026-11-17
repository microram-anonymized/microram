import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The positive-series stop-loss bound Φ_K (trusted spec)

`REPORT.tex`, Equation `eq:general-series` and the paragraph before it. For
`Z ∼ Po(λ)` put `w_j = P(Z = C + j)` for `j ≥ 1` and `W(z) = Σ_{j≥1} w_j z^j`.
The generating function of `(Z - C)₊` is coefficientwise at most `1 + W(z)`,
and `(1 + W)^n ≼ exp(n W) = Σ_k c_k z^k` with

  `c_0 = 1`,  `c_k = (n / k) Σ_{j=1}^k j w_j c_{k-j}`.

For an integer cutoff `K > S`,

  `Φ_K(n, C, λ, S) = Σ_{k=S+1}^K (k - S) c_k + (K + 1 - S) 2^-(K+1) exp(n 2^-C e^λ)`.

The definitions are real-valued and follow the equation literally; the
numerics checker (`Proofs/NTop`, `Proofs/NCA1`) proves its rational output is an upper bound of
`Phi`, and P7 proves `Phi` bounds the stop-loss. `Phi` is a formula, not a
trusted fact: a wrong `Phi` makes P7 or the checker fail, never a false
end-to-end claim.
-/

open scoped BigOperators

namespace RebuildBound.Spec

/-- `w_j = P(Po(λ) = C + j) = e^-λ λ^(C+j) / (C+j)!`, the probability that one
Poisson home has excess exactly `j` (used for `j ≥ 1`). -/
noncomputable def seriesW (C : ℕ) (lam : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-lam) * lam ^ (C + j) / ((C + j).factorial : ℝ)

/-- The coefficients of `exp(n W(z))`: `c_0 = 1` and
`c_{k+1} = n / (k+1) · Σ_{j=1}^{k+1} j w_j c_{k+1-j}` (the sum written with
`j = i + 1`, `i < k + 1`). -/
noncomputable def seriesCoeff (n C : ℕ) (lam : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (n : ℝ) / ((k + 1 : ℕ) : ℝ) *
      ∑ i ∈ Finset.range (k + 1),
        ((i + 1 : ℕ) : ℝ) * seriesW C lam (i + 1) * seriesCoeff n C lam (k - i)
termination_by k => k
decreasing_by omega

/-- **Φ_K(n, C, λ, S)** of `eq:general-series`: the finite part
`Σ_{k=S+1}^K (k - S) c_k` plus the tail `(K + 1 - S) 2^-(K+1) exp(n 2^-C e^λ)`. -/
noncomputable def Phi (K n C : ℕ) (lam : ℝ) (S : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc (S + 1) K, ((k - S : ℕ) : ℝ) * seriesCoeff n C lam k) +
    ((K + 1 - S : ℕ) : ℝ) / 2 ^ (K + 1) * Real.exp ((n : ℝ) / 2 ^ C * Real.exp lam)

end RebuildBound.Spec
