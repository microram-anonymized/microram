import RebuildBound.Proofs.S4afin
import RebuildBound.Proofs.S4bfin
import RebuildBound.Proofs.SEng
import RebuildBound.Proofs.SG1p

/-! Assembly of SG1p from the conditional `SG1p_of` and ST4a, ST4b, ST6, SEngine. -/

theorem RebuildBound.SG1p : RebuildBound.Spec.SG1p_statement :=
  RebuildBound.SG1p_of RebuildBound.ST4a RebuildBound.ST4b RebuildBound.ST6 RebuildBound.SEngine
