import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.Hierarchy
import RebuildBound.Spec.Configuration31

/-! Structural contracts for explicit hierarchy geometry. These statements
assert no probability bound and assume neither local laws nor covering. -/

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- The potential jobs of the D8, capacity-2^31 instance meet their structural
contracts, with their actual initialization and preparation geometry. -/
def HierarchyInvariant31_statement : Prop := HierarchyInvariantFor geometry31

end RebuildBound.Spec
