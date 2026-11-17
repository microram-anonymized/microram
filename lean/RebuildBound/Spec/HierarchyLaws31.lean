import RebuildBound.Spec.HierarchyGeometry.Interfaces
import RebuildBound.Spec.HierarchyInvariant31

/-! The ideal-tape law interfaces for explicit hierarchy geometry. The new
instance concludes the local couplings from the trace and tape premises;
no local laws, structural contracts or covering are assumed by its endpoints.
These statements assert no numerical failure bound. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace RebuildBound.Spec
open Model Model.DirectJob Model.Hierarchy

/-- Word locality of the capacity extension. -/
def HierarchyLocality31_statement : Prop := HierarchyLocalityFor config31 geometry31.shapes

/-- Local separated laws, with invariant, locality and density results discharged. -/
def HierarchySepLaw31_statement : Prop := HierarchySepLawFor geometry31

/-- Local top laws, with invariant and locality results discharged. -/
def HierarchyTopLaw31_statement : Prop := HierarchyTopLawFor geometry31

/-- The capacity extension's level-one cycle tape projections. -/
def HierarchyLevelOne31_statement : Prop := HierarchyLevelOneFor config31 keyCapacity31

end RebuildBound.Spec
