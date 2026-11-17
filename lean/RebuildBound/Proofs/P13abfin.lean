import RebuildBound.Proofs.P13ab
import RebuildBound.Proofs.P13bc

/-! # P13ab assembled from its conditional and P13b, P13c. -/

theorem RebuildBound.P13ab : RebuildBound.Spec.P13ab_statement :=
  RebuildBound.P13ab_of RebuildBound.P13b RebuildBound.P13c
