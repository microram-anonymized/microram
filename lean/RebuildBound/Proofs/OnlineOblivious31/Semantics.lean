import RebuildBound.Spec.Oblivious31
import RebuildBound.Proofs.OnlinePattern
import RebuildBound.Proofs.OnlineFresh
import RebuildBound.Proofs.OnlineExact
import RebuildBound.Proofs.OnlineFailure
import RebuildBound.Proofs.SyncSchedule
import RebuildBound.Proofs.HierarchyLawsChunks31

/-! Scalar ideal-tape laws at capacity 2^31, without numerical certificates.
The structural proofs use the explicit hierarchy geometry at each horizon.
Observation transfer retains the actual failure probability. -/

namespace RebuildBound
open Model Spec HierarchyInvariantProof

/-- The real/dummy pattern is independent of the tape words. -/
theorem OnlinePattern31 : OnlinePattern31_statement := by
  intro h _
  exact OnlinePatternProof.patternFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))

/-- Real probes select distinct family-tape words. -/
theorem OnlineFresh31 : OnlineFresh31_statement := by
  intro h _
  exact OnlineFreshProof.freshFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))

/-- The scalar view has exactly the public simulator's law on the joint ideal tape. -/
theorem OnlineExact31 : OnlineExact31_statement := by
  intro h hh
  exact OnlineExactProof.exactFor_of (geometry31.chunk h) (OnlinePattern31 h hh) (OnlineFresh31 h hh)

/-- An agreeing observation differs from the simulator by at most the failure probability. -/
theorem OnlineFailure31 : OnlineFailure31_statement := by
  intro h hh
  exact OnlineFailure.forGeometry (geometry31.chunk h)
    (OnlinePattern31 h hh) (OnlineFresh31 h hh) (OnlineExact31 h hh)

/-- The public synchronous schedule meets its premises for the capacity extension. -/
theorem SyncSchedule31 : SyncSchedule31_statement := by
  intro h n _
  exact SyncScheduleLemmas.syncSchedule_premises _
    (by change ∀ b ∈ config31.fanouts, 0 < b; decide +kernel)
    (by change 0 < config31.carryPositions 1; decide +kernel) n

end RebuildBound
