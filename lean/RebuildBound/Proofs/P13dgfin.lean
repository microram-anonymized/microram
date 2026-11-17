import RebuildBound.Proofs.P13dg
import RebuildBound.Proofs.P13bc

/-! # P13d and P13g assembled from their conditionals and P13c. -/

theorem RebuildBound.P13d : RebuildBound.Spec.P13d_statement :=
  RebuildBound.P13d_of RebuildBound.P13c

theorem RebuildBound.P13g : RebuildBound.Spec.P13g_statement :=
  RebuildBound.P13g_of RebuildBound.P13c
