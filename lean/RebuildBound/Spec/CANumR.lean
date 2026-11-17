import RebuildBound.Spec.Prob.RadixTree

/-!
# Completed-A range numbers at an odd radix (trusted statements, numerics)

The `r > 1` counterpart of `Spec/CANum.lean`: the class sum of stop-losses of
form (CA) (`REPORT.tex`, Proposition "Completed-A coarse-range bound") at a
concrete shape. The density factor and the `2^(k - I)` ranges per class are
applied in the glue.

* **NCA5** (`r = 5`). The selected configuration's largest range term
  (`code/bound_table.json`, the separated-ordinary key with carry bits 13,
  digit 5, block bits 13, index bits `I = 8`; first occurrence: the uniform
  configuration, level 4, digit 5): `t = 13 - 8 = 5`, `g = 2^8` roots,
  `P = T_A + 8 S = 64 + 8 · 128 = 1088`, `C = L = 64`, `λ = 32`, and 64-bit words,
  so `q_a = qMass 64 13 5 a`: three classes of mass `(2^51 + 2)/5 / 2^51` and two
  of `(2^51 - 3)/5 / 2^51`. The Python certifier's columns are
  `1.4213430336949467 · 10^-27` and `1.4213430336946428 · 10^-27`, whose class
  sum `7.1067151684…·10^-27` the statement rounds up to `7.107 · 10^-27`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace RebuildBound.Spec

/-- **NCA5.** The completed-A class sum `Σ_{a < 5} E (Y_a - 64)₊` at the selected
`r = 5` shape (`t = 5`, `g = 2^8`, `P = 1088`) is at most `7.107 · 10^-27`. -/
def NCA5_statement : Prop :=
  ∑ a ∈ Finset.range 5, stopLoss (rangeLawR 64 32 1088 (2 ^ 8) 5 5 (qMass 64 13 5 a)) 64 ≤
    (7107 : ℝ≥0∞) / 10 ^ 30

end RebuildBound.Spec
