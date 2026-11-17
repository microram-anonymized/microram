import RebuildBound.Proofs.S6
import RebuildBound.Proofs.S4b

/-! Assembly of ST4b from the conditional `ST4b_of` and ST6. -/

theorem RebuildBound.ST4b : RebuildBound.Spec.ST4b_statement :=
  RebuildBound.ST4b_of RebuildBound.ST6
