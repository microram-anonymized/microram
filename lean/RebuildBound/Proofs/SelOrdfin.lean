import RebuildBound.Proofs.SelOrd
import RebuildBound.Proofs.SelRange1
import RebuildBound.Proofs.SelRange3
import RebuildBound.Proofs.SelRange5
import RebuildBound.Proofs.SelRange7
import RebuildBound.Proofs.SelRest

/-! Assembly of SelOrd from the conditional `SelOrd_of` and the per-shape numbers. -/

theorem RebuildBound.SelOrd : RebuildBound.Spec.SelOrd_statement :=
  RebuildBound.SelOrd_of RebuildBound.SelRange1 RebuildBound.SelRange3 RebuildBound.SelRange5
    RebuildBound.SelRange7 RebuildBound.SelRest
