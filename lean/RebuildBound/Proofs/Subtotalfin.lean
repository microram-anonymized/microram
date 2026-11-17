import RebuildBound.Proofs.SelOrdfin
import RebuildBound.Proofs.Subtotal

/-! Assembly of the selected subtotal from the conditional `Subtotal_of` and SelOrd. -/

theorem RebuildBound.Subtotal : RebuildBound.Spec.Subtotal_statement :=
  RebuildBound.Subtotal_of RebuildBound.SelOrd
