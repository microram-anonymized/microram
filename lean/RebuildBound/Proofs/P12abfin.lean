import RebuildBound.Proofs.P12a
import RebuildBound.Proofs.P12b
import RebuildBound.Proofs.P12c
import RebuildBound.Proofs.P12ab

/-! Assembly of P12ab from the conditional `P12ab_of` and P12a, P12b, P12c. -/

theorem RebuildBound.P12ab : RebuildBound.Spec.P12ab_statement :=
  RebuildBound.P12ab_of RebuildBound.P12a RebuildBound.P12b RebuildBound.P12c
