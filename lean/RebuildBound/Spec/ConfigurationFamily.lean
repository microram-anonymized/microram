import RebuildBound.Spec.ConfigurationFamilyData
import RebuildBound.Spec.HierarchyStructure

/-! The finite planner-family structural claim. Membership identifies the
listed geometry, not a theorem about the native planner's search loop.
Numerical failure bounds are separate obligations. -/

namespace RebuildBound.Spec

/-- Every listed member satisfies the same finite structural contract from
both initialized and empty starts. -/
def ConfigurationFamilyStructural_statement : Prop :=
  ∀ (initialized : Bool) (m : ConfigurationFamily.Member),
    m ∈ ConfigurationFamily.members → (m.geometry initialized).Structural

end RebuildBound.Spec
