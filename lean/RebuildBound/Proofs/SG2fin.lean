import RebuildBound.Proofs.P12abfin
import RebuildBound.Proofs.P12dfin
import RebuildBound.Proofs.P12e
import RebuildBound.Proofs.SG2

/-! Assembly of SG2 from the conditional `SG2_of` and P12ab, P12d, P12e. -/

theorem RebuildBound.SG2 : RebuildBound.Spec.SG2_statement :=
  RebuildBound.SG2_of RebuildBound.P12ab RebuildBound.P12d RebuildBound.P12e
