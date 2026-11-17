import RebuildBound.Spec.Oblivious31
import RebuildBound.Proofs.BatchPattern
import RebuildBound.Proofs.BatchFresh
import RebuildBound.Proofs.BatchExact
import RebuildBound.Proofs.BatchFailure
import RebuildBound.Proofs.HierarchyLawsChunks31

/-! Batch ideal-tape laws at capacity 2^31, without numerical certificates.
Observation transfer retains the actual failure probability. -/
namespace RebuildBound
open Spec

theorem BatchPattern31 : BatchPattern31_statement := by
  intro h _
  exact BatchPatternProof.patternFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))

theorem BatchFresh31 : BatchFresh31_statement := by
  intro h _
  exact BatchFreshProof.freshFor (geometry31.chunk h)
    (HierarchyLawsChunks31Proof.lowFacts_horizon HierarchyInvariant31Proof.lowFacts (h * 2 ^ 32))

theorem BatchExact31 : BatchExact31_statement := by
  intro h hh
  exact BatchExactProof.exactFor_of _ (BatchPattern31 h hh) (BatchFresh31 h hh)

theorem BatchFailure31 : BatchFailure31_statement := by
  intro h hh
  exact BatchFailure.forGeometry _ (BatchPattern31 h hh) (BatchFresh31 h hh) (BatchExact31 h hh)


end RebuildBound
