import RebuildBound.Proofs.ConfigurationFamilyTop.Check

namespace RebuildBound.ConfigurationFamilyTopProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 500

theorem checked1 : (chunk 1).all check = true := by
  decide +kernel

end RebuildBound.ConfigurationFamilyTopProof
