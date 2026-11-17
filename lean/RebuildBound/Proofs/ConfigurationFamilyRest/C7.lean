import RebuildBound.Proofs.ConfigurationFamilyRest.Check

namespace RebuildBound.ConfigurationFamilyRestProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 500

theorem checked7 : (chunk 7).all check = true := by
  decide +kernel

end RebuildBound.ConfigurationFamilyRestProof
