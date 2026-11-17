import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.HierarchyLaws31
import RebuildBound.Spec.HierarchyCovering31

/-! First-horizon probability for explicit hierarchy geometry and error budget.
The capacity-2^31 endpoint assumes only trace, unshadowed and ideal-tape premises.
-/

open MeasureTheory
open scoped ENNReal

namespace RebuildBound.Spec
open Model Model.Hierarchy

/-- Capacity failure within the first 2^32 accesses, including initialization
and the existing speculative trigger boundary, has probability at most 2^-64. -/
def HierarchyUniform31_statement : Prop :=
  HierarchyUniformFor geometry31 (ENNReal.ofReal (1 / (2 : ℝ) ^ 64))

end RebuildBound.Spec
