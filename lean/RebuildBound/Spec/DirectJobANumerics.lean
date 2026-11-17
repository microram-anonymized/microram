import RebuildBound.Spec.DirectJobSelected
import RebuildBound.Spec.Selected

/-! Numerical expressions only. These bounds do not assert the native input law,
source-history independence, or event transport. The shared separated bound is
used as a conservative A budget; its extra final-excess term is harmless. -/
open scoped ENNReal NNReal
namespace RebuildBound.Spec

/-- Completed-A ranges at the selected finite-word geometry and old density. -/
def DirectJobSelectedARange_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    selRange (selectedDirectSep d) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 103)

/-- Reuse the shared storage checker, including its nonnegative output term. -/
def DirectJobSelectedAStorage_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    selRest (selectedDirectSep d) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 108)

/-- A conservative budget for the entire shared expression, hence also its A
route/range summands. Applicability is supplied separately by the law adapter. -/
def DirectJobSelectedANumerics_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    selSepBound (selectedDirectSep d) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 102)

end RebuildBound.Spec
