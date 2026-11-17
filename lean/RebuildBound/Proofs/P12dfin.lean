import RebuildBound.Proofs.P12c
import RebuildBound.Proofs.P12d

/-! Assembly of P12d from the conditional `P12d_of` and P12c. -/

theorem RebuildBound.P12d : RebuildBound.Spec.P12d_statement :=
  RebuildBound.P12d_of RebuildBound.P12c
