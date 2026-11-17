import RebuildBound.Spec.HierarchyInvariant31
import RebuildBound.Proofs.HierarchyInvariant
import RebuildBound.Proofs.Geometry31

/-! Instantiate the general induction using checked configuration facts.
Only finite geometry is evaluated; the execution's tables remain symbolic. -/

namespace RebuildBound.HierarchyInvariant31Proof
open Model Spec HierarchyInvariantProof

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem lowFacts : LowFacts config31 separated31 :=
  lowFacts_of _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end RebuildBound.HierarchyInvariant31Proof

/-- Structural invariant for the capacity extension, without probability assumptions. -/
theorem RebuildBound.HierarchyInvariant31 : RebuildBound.Spec.HierarchyInvariant31_statement := by
  intro N tr hN hT hU words
  exact RebuildBound.HierarchyInvariantProof.contractsFor RebuildBound.Spec.geometry31
    RebuildBound.HierarchyInvariant31Proof.lowFacts
    (RebuildBound.HierarchyInvariantProof.TopFacts.of_compatible RebuildBound.Geometry31.1)
    hN hT hU words
