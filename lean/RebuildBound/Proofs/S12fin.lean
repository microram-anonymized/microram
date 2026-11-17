import RebuildBound.Proofs.S6
import RebuildBound.Proofs.S12

/-! Assembly of ST1 and ST2 from the conditionals `ST1_of`, `ST2_of` and ST6. -/

theorem RebuildBound.ST1 : RebuildBound.Spec.ST1_statement :=
  RebuildBound.ST1_of RebuildBound.ST6

theorem RebuildBound.ST2 : RebuildBound.Spec.ST2_statement :=
  RebuildBound.ST2_of RebuildBound.ST6
