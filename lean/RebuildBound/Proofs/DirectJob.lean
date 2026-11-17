import RebuildBound.Spec.DirectJob
import RebuildBound.Proofs.DirectJobPublication
import RebuildBound.Proofs.DirectJobFailure

/-- Assemble the atomic contract from the already checked phase consumers. -/
theorem RebuildBound.DirectJob : RebuildBound.Spec.DirectJob_statement :=
  ⟨RebuildBound.DirectJobPublication, RebuildBound.DirectJobSimulation,
    RebuildBound.DirectJobFirstFailure, RebuildBound.DirectJobFailureContainment⟩
