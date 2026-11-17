import RebuildBound.Spec.Prob.TruncRadix

/-!
# P10r: the truncation enclosure at a terminal radix (trusted statement)

`REPORT.tex`, Proposition "Completed-A coarse-range bound", paragraph "A
rigorous terminal truncation enclosure", every odd `r`; definitions in
`Spec/Prob/TruncRadix.lean`, `Spec/Prob/Trunc.lean`, `Spec/Prob/RadixTree.lean`.
P10 is its case `r = 1`.

In each of the `g` roots, replace the root's loss by zero on the event that
some node of its `r` trees has total above `H`, or the radix node's sum does
(a partial sum above `H` implies the final sum is). Every tree node's total is
`Po(λ)` and the radix node's total is `Po(μ)` with `μ = r λ q` (caps preserve
totals; thinning and addition preserve the Poisson law), so the event has
probability at most `β = r (2^t - 1) τ_H(λ) + [r > 1] τ_H(μ)`. A root loss is
at most its root's total, so `E[Z; discarded] ≤ √((μ + μ²) β)`, and the range
count's stop-loss grows by at most `g` times that.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **P10r, the truncation enclosure at a terminal radix.** For `λ < H + 2` and
`μ = r λ q < H + 2`, the stop-loss of the radix range law is at most that of the
zero-completed truncated law plus
`g √((μ + μ²)(r (2^t - 1) τ_H(λ) + [r > 1] τ_H(μ)))`. -/
def P10r_statement : Prop :=
  ∀ (C : ℕ) (lam : ℝ≥0) (P g t r H L : ℕ) (q : I), (lam : ℝ) < H + 2 →
    (r * (lam : ℝ) * q : ℝ) < H + 2 →
    stopLoss (rangeLawR C lam P g t r q) L ≤
      stopLoss (binomial P (q * halfPow t) ∗
          natConvPow (zeroComplete (truncRadixRoot C lam H t r q)) g) L +
        ENNReal.ofReal (g * Real.sqrt
          ((r * (lam : ℝ) * q + (r * (lam : ℝ) * q) ^ 2) *
            (r * (2 ^ t - 1) * poissonTail H lam +
              if 1 < r then poissonTail H (r * (lam : ℝ) * q) else 0)))

end RebuildBound.Spec
