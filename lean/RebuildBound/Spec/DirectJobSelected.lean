import RebuildBound.Spec.Model.DirectJobA
import RebuildBound.Spec.DirectJobABounds
import RebuildBound.Spec.Prob.Series

namespace RebuildBound.Spec
open Model Model.DirectJob

/-- The level-one rows shared by the selected uniform (digits 1–8) and
half-fanout (digits 1–4) configurations. The native inventory's pool includes
the direct B tier; the A distributor's pool excludes that tier. -/
def selectedDirectGeometry (d : Nat) : Geometry :=
  let base : Geometry :=
    ⟨4, d, d * 16, 64, if d = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩
  if d = 1 then base else
    { base with ranges := (.dfs (if d ≤ 4 then 0 else 1)
        (if d = 2 then 5 else 6) base.poolCapacity) }

/-- The probability geometry uses actual page capacities and range fields;
the executable A topology intentionally does not carry those fields. -/
def selectedDirectSep (d : Nat) : SepGeom :=
  ⟨64, 4, val2 d, d / 2 ^ val2 d, if d = 2 then 5 else 6,
    if d ≤ 4 then 0 else 1, 1, 1, 1, 1⟩

def DirectJobSelectedGeometry_statement : Prop :=
  (∀ d, 1 ≤ d → d ≤ 8 → (selectedDirectGeometry d).Valid) ∧
  (∀ d, 2 ≤ d → d ≤ 8 →
    (selectedDirectSep d).Valid ∧
    (selectedDirectSep d).I < (selectedDirectSep d).K ∧
    (selectedDirectSep d).d = d ∧
    (selectedDirectSep d).N = (selectedDirectGeometry d).outputHomes ∧
    (selectedDirectGeometry d).ranges = .dfs (selectedDirectSep d).I
      (selectedDirectSep d).rangeBits ((selectedDirectSep d).poolPages * 64))

def DirectJobSelectedAAdapter_statement : Prop :=
  ∀ d, 2 ≤ d → d ≤ 8 →
    AProbabilityGeometry (selectedDirectGeometry d) (selectedDirectSep d)

/-- Conditional numerical excess bounds at load 32. These certify the existing
Phi expression, not a native input law or the completed-A contribution. -/
def DirectJobSelectedExcess_statement : Prop :=
  Phi 256 16 64 32 64 ≤ 1 / (2 : ℝ) ^ 117 ∧
  ∀ d, 1 ≤ d → d ≤ 8 → Phi 256 (d * 16) 64 32 64 ≤ 1 / (2 : ℝ) ^ 112

/-- The selected union budget allows any established density factor at most
two; proving that factor bounds the finite-word input law remains a premise. -/
def DirectJobSelectedDensity_statement : Prop :=
  ∀ (d : Nat) (D : ℝ), 1 ≤ d → d ≤ 8 → 0 ≤ D → D ≤ 2 →
    D * Phi 256 (d * 16) 64 32 64 ≤ 1 / (2 : ℝ) ^ 111

end RebuildBound.Spec
