import RebuildBound.Proofs.AdaptiveCausal.Generic
import RebuildBound.Proofs.BatchOblivious31
import RebuildBound.Proofs.HierarchyLaws31
import RebuildBound.Proofs.HierarchyLocalityChunks

/-! Selected causal replay is a specialization of the generic construction. -/


open RebuildBound.AdaptiveCausalProof in
theorem RebuildBound.AdaptiveCausalStep : RebuildBound.Spec.AdaptiveCausalStep_statement := by
  intro hRow hTUP _hRS hAR h hh
  exact causalFor (Spec.geometry31.chunk h) (BatchPattern31 h hh) (BatchFresh31 h hh)
    (HierarchyLocalityChunksProof.timeFacts_chunk HierarchyLaws31Proof.timeFacts h)
    hRow hTUP hAR
