import RebuildBound.Proofs.ConfigurationFamilyPrep.Check

namespace RebuildBound.ConfigurationFamilyPrepProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 500

theorem checked5 : (chunk 5).all check = true := by
  decide +kernel

end RebuildBound.ConfigurationFamilyPrepProof
