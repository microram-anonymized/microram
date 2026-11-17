import RebuildBound.Proofs.P10r
import RebuildBound.Proofs.NCA5

/-! Assembly of NCA5 from the conditional `NCA5_of` and P10r. -/

theorem RebuildBound.NCA5 : RebuildBound.Spec.NCA5_statement :=
  RebuildBound.NCA5_of RebuildBound.P10r
