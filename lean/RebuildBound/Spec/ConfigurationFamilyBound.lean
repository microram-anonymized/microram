import RebuildBound.Spec.ConfigurationFamilyDirect
import RebuildBound.Spec.HierarchyProbability

/-! Shared analytic class budgets and the numerical exit condition for the
finite family. Missing separated shapes have bound one, so coverage cannot be
silently replaced by zero. The structural certificate proves required rows exist. -/
open MeasureTheory
open scoped ENNReal
namespace RebuildBound.Spec
open Model Model.Hierarchy
namespace ConfigurationFamily

noncomputable def classBudget (m : Member) (initialized : Bool) : JobClass → ℝ≥0∞ :=
  let geo := m.geometry initialized
  fun c => match c with
  | .ordinary ℓ d => if ℓ = 1 then directBound m d else if d = 1 then 0 else
      ((geo.cfg.sepRow geo.rows ℓ d).map selSepBound).getD 1
  | .topFinish => ENNReal.ofReal (topFinishBound geo.top.C geo.top.SR geo.top.rho geo.top.I geo.top.T
      (min geo.top.SMerge geo.top.STier) 576 576 32)
  | .topPrepare => tpBound geo.prep 32 1 576 576
  | .initialization => tpBound geo.init 32 1 576 576

end ConfigurationFamily
open ConfigurationFamily

/-- Local probability applicability composed with the exact class exposure sum. -/
def ConfigurationFamilyAnalytic_statement : Prop :=
  ∀ initialized m, m ∈ members →
    CausalWindowsFor (m.geometry initialized) ((m.config initialized).exposureSum (classBudget m initialized))

/-- All initialized-start exposure sums meet the target. Empty starts reuse
this certificate through the proved initialization-subtraction identity. -/
def ConfigurationFamilyNumerics_statement : Prop :=
  ∀ m ∈ members,
    (m.config true).exposureSum (classBudget m true) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 64)

end RebuildBound.Spec
