import RebuildBound.Spec.Prob.Trunc

/-!
# P10: the truncation enclosure (trusted statement)

`REPORT.tex`, Proposition "Completed-A coarse-range bound", paragraph "A
rigorous terminal truncation enclosure", case `r = 1`; definitions in
`Spec/Prob/Trunc.lean`.

In each of the `g` root trees, replace the root's loss by zero on the event
that some node's total exceeds `H`. Every node's total is `Po(λ)` (caps
preserve totals; independent thinning and addition preserve the Poisson
law), so with `2^t - 1` nodes the event has probability at most
`β = (2^t - 1) τ_H(λ)`. A root loss is at most its root's total, so by
Cauchy–Schwarz `E[Z; discarded] ≤ √((λ + λ²) β)`. The stop-loss is
1-Lipschitz, so the range count's stop-loss grows by at most `g` times that.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **P10, the truncation enclosure.** For `λ < H + 2`, the stop-loss of the
range law is at most that of the zero-completed truncated law plus
`g √((λ + λ²)(2^t - 1) τ_H(λ))`. -/
def P10_statement : Prop :=
  ∀ (C : ℕ) (lam : ℝ≥0) (P : ℕ) (p : I) (g t H L : ℕ), (lam : ℝ) < H + 2 →
    stopLoss (rangeLaw C lam P p g t) L ≤
      stopLoss (binomial P p ∗ natConvPow (zeroComplete ((truncTree C lam H t).map Prod.snd)) g) L +
        ENNReal.ofReal (g * Real.sqrt (((lam : ℝ) + (lam : ℝ) ^ 2) * (2 ^ t - 1) *
          poissonTail H lam))

end RebuildBound.Spec
