import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.Hierarchy
import RebuildBound.Spec.Configuration31

/-! First-failure covering for explicit geometry. This is a deterministic
property of the reference execution, with no trace or probability premises. -/

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- Covering for the capacity-2^31 execution, with tier-fit results discharged. -/
def HierarchyCovering31_statement : Prop := HierarchyCoveringFor geometry31

end RebuildBound.Spec
