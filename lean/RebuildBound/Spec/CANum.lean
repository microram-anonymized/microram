import RebuildBound.Spec.Prob.ShadowTree

/-!
# Completed-A range numbers (trusted statements, numerics)

The stop-loss terms of form (CA) (`REPORT.tex`, Proposition "Completed-A
coarse-range bound") at concrete shapes, checked in Lean. The density factor
and the union over the `2^(b - I)` ranges are applied in the glue; these
statements are the per-range stop-losses alone.

* **NCA1** (`r = 1`). The selected configuration's largest `r = 1` range term
  (`code/bound_table.json`, the separated-ordinary key with carry bits 16,
  digit 8, block bits 19, index bits `I = 10`; first occurrence: the uniform
  configuration, level 5, digit 8). The tree depth is `t = b - I = 9`, the
  range has `g = 2^10` roots, the early cap is
  `P = T_A + Σ_{j < I} S_j = 128 + 10 · 128 = 1408`, `C = L = 64` and `λ = 32`.
  The Python certifier's `column_upper` is `2.6909023163226949 · 10^-30`;
  the statement rounds it up to `2.691 · 10^-30`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **NCA1.** The completed-A stop-loss `E (Y - 64)₊` at the selected `r = 1`
shape (`t = 9`, `g = 2^10`, `P = 1408`) is at most `2.691 · 10^-30`. -/
def NCA1_statement : Prop :=
  stopLoss (rangeLaw 64 32 1408 (halfPow 9) (2 ^ 10) 9) 64 ≤ (2691 : ℝ≥0∞) / 10 ^ 33

end RebuildBound.Spec
