import RebuildBound.Spec.IdealGeometry
import RebuildBound.Spec.ConfigurationFamilyBound

/-! The certified inventory instantiates the same generic analytic interface.
No numerical certificate is included in this geometry bridge. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy
namespace IdealGeometry

def familyParameters (m : ConfigurationFamily.Member) : Parameters :=
  ⟨m.directSep, 576, 576, 576, 576, 576, 576⟩

end IdealGeometry

/-- All 94 members and both starts supply the explicit generic certificates,
with exactly the analytic class budgets used by the existing numerical proofs. -/
def IdealGeometryFamily_statement : Prop :=
  ∀ (initialized : Bool) (m : ConfigurationFamily.Member),
    m ∈ ConfigurationFamily.members →
    let geo := m.geometry initialized
    geo.Structural ∧ geo.cfg.Valid ∧ IdealGeometry.Coverage geo ∧
      IdealGeometry.Analytic geo (IdealGeometry.familyParameters m) ∧
      IdealGeometry.WindowArithmetic geo.cfg ∧
      IdealGeometry.classBudget geo (IdealGeometry.familyParameters m) =
        ConfigurationFamily.classBudget m initialized

end RebuildBound.Spec
