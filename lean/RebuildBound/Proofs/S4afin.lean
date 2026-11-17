import RebuildBound.Proofs.S6
import RebuildBound.Proofs.S4a

/-! Assembly of ST4a from the conditional `ST4a_of` and ST6. -/

theorem RebuildBound.ST4a : RebuildBound.Spec.ST4a_statement :=
  RebuildBound.ST4a_of RebuildBound.ST6
