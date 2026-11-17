import RebuildBound.Spec.Prob.Trunc
import RebuildBound.Spec.Prob.RadixTree

/-!
# The truncated radix root (trusted spec, package P10r)

`REPORT.tex`, Proposition "Completed-A coarse-range bound", paragraph "A
rigorous terminal truncation enclosure", every odd `r`: at the terminal radix
node, thin both coordinates of each of the `r` truncated trees with the exact
`q_a`, convolve the `r` children discarding every partial sum whose total
exceeds `H`, then cap.

* `truncPairConvPow H μ n`: the sum of `n` independent draws from `μ`, each
  partial sum restricted to totals at most `H`.
* `truncRadixRoot C λ H t r q`: the radix root `radixRoot` with every tree
  node, and every partial sum of the radix node, discarded above `H`; a
  sub-probability law, `≤ radixRoot`. At `r = 1`, `q = 1` it is the root loss of
  `truncTree`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The sum of `n` independent draws from `μ`, every partial sum restricted to
totals at most `H`. -/
noncomputable def truncPairConvPow (H : ℕ) (μ : Measure (ℕ × ℕ)) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (0, 0)
  | n + 1 => (truncPairConvPow H μ n ∗ μ).restrict (lowTotal H)

/-- The truncated radix root: `r` truncated trees, each thinned by `q`, summed
with every partial sum discarded above `H`, then capped. -/
noncomputable def truncRadixRoot (C : ℕ) (lam : ℝ≥0) (H t r : ℕ) (q : I) : Measure ℕ :=
  (truncPairConvPow H ((truncTree C lam H t).bind (thinPair q)) r).map fun s => s.2 + (s.1 - C)

end RebuildBound.Spec
