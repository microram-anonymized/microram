import RebuildBound.Proofs.TP4
import RebuildBound.Proofs.TP12fin

/-! # TP4a and TP4b assembled from their conditionals, TP6 and TP12. -/

theorem RebuildBound.TP4a : RebuildBound.Spec.TP4a_statement :=
  RebuildBound.TP4a_of RebuildBound.TP6 RebuildBound.TP12

theorem RebuildBound.TP4b : RebuildBound.Spec.TP4b_statement :=
  RebuildBound.TP4b_of RebuildBound.TP12
