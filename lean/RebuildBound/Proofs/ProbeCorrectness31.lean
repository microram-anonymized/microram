import RebuildBound.Spec.Oblivious31
import RebuildBound.Proofs.OnlineCorrectness
import RebuildBound.Proofs.BatchCorrectness.Endpoint
import RebuildBound.Proofs.BatchCorrectness.Scalar
import RebuildBound.Proofs.HierarchyLawsChunks31

namespace RebuildBound
open Spec HierarchyInvariantProof HierarchyLawsChunks31Proof

/-- Deterministic scalar answers and address agreement at capacity 2^31. -/
theorem OnlineCorrectness31 : Spec.OnlineCorrectness31_statement := by
  intro h _
  exact OnlineCorrectnessProof.correctnessFor (geometry31.chunk h)
    (lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    (topFacts_chunk (TopFacts.of_compatible Geometry31.1) h) rfl
    (by change 0 < config31.seed config31.levels; decide +kernel)

/-- Effective batch answers and address agreement at capacity 2^31. -/
theorem BatchCorrectness31 : Spec.BatchCorrectness31_statement := by
  intro h _
  exact BatchCorrectnessProof.correctnessFor (geometry31.chunk h)
    (lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))
    (topFacts_chunk (TopFacts.of_compatible Geometry31.1) h) rfl
    (by change 0 < config31.seed config31.levels; decide +kernel)

end RebuildBound
