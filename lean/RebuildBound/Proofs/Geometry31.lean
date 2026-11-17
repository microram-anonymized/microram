import RebuildBound.Spec.Configuration31

namespace RebuildBound

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem Geometry31 : Spec.Geometry31_statement := by
  unfold Spec.Geometry31_statement
  constructor
  · unfold Spec.HierarchyGeometry.TopCompatible
    decide +kernel
  · decide +kernel

end RebuildBound
