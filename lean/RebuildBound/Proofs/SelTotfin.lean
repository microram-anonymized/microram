import RebuildBound.Proofs.SelTot
import RebuildBound.Proofs.TPJobfin

/-! # SelTotal assembled from its conditional, TPSel and ISel. -/

theorem RebuildBound.SelTotal : RebuildBound.Spec.SelTotal_statement :=
  RebuildBound.SelTotal_of RebuildBound.TPSel RebuildBound.ISel
