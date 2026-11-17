import RebuildBound.Spec.Configuration31

namespace RebuildBound

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem Inventory31 : Spec.Inventory31_statement := by
  unfold Spec.Inventory31_statement Model.Config.Valid
  decide +kernel

set_option maxRecDepth 8192 in
theorem Budget31 : Spec.Budget31_statement := by
  unfold Spec.Budget31_statement
  decide +kernel

end RebuildBound
