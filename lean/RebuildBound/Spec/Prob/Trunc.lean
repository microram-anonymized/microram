import RebuildBound.Spec.Prob.ShadowTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The truncated shadow tree (trusted spec, package P10)

`REPORT.tex`, Proposition "Completed-A coarse-range bound", paragraph "A
rigorous terminal truncation enclosure", case `r = 1`. These are the
evaluation objects of the completed-A numbers: a certificate
bounds the truncated law, and P10 bounds what the truncation removed.

* `truncTree C λ H t` is `shadowTree C λ t` with every node's state
  discarded when its total `M + R` exceeds `H`: the same recursion, with the
  state law restricted to `M + R ≤ H` after every node (the leaf included).
  It is a sub-probability law, the law of the root state on the event that
  no node of the tree has a total above `H`.
* `zeroComplete μ` puts the missing mass of a sub-probability law on counts
  at zero: the law of a root loss replaced by zero on the discarded event.
* `poissonTail H ν = P(Po(ν) = H + 1) / (1 - ν/(H + 2))`, the report's
  `τ_H(ν)`, an upper bound of `P(Po(ν) > H)` for `ν < H + 2`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- The node states of total at most `H`. -/
def lowTotal (H : ℕ) : Set (ℕ × ℕ) := {s | s.1 + s.2 ≤ H}

/-- The shadow tree with every node's state discarded when its total exceeds
`H` (`truncTree C λ H t ≤ shadowTree C λ t`). -/
noncomputable def truncTree (C : ℕ) (lam : ℝ≥0) (H : ℕ) : ℕ → Measure (ℕ × ℕ)
  | 0 => Measure.dirac (0, 0)
  | 1 => ((poissonMeasure lam).map (fun n => capPair C (n, 0))).restrict (lowTotal H)
  | t + 2 =>
    let child := (truncTree C lam H (t + 1)).bind (thinPair half)
    ((child ∗ child).map (capPair C)).restrict (lowTotal H)

/-- Complete a sub-probability law on counts by an atom at zero. -/
noncomputable def zeroComplete (μ : Measure ℕ) : Measure ℕ :=
  μ + (1 - μ Set.univ) • Measure.dirac 0

/-- `τ_H(ν) = P(Po(ν) = H + 1) / (1 - ν / (H + 2))`. -/
noncomputable def poissonTail (H : ℕ) (ν : ℝ) : ℝ :=
  Real.exp (-ν) * ν ^ (H + 1) / (H + 1).factorial / (1 - ν / (H + 2))

end RebuildBound.Spec
