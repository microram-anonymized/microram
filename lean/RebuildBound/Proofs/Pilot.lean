import RebuildBound.Proofs.G1fin
import RebuildBound.Proofs.G2

/-!
# Pilot: G1 with the range term from G2
-/

/-- **The d = 2 pilot bound.** -/
theorem RebuildBound.Pilot : RebuildBound.Spec.Pilot_statement := by
  intro g L TA TB lam D rule caps S Lf Si So hL hrule hlam hC hlo hS hLf hSi hSo hP
  exact RebuildBound.G1 g L TA TB lam D rule caps S Lf Si So _ hL hrule hlam hC hS hLf hSi hSo hP
    (RebuildBound.G2 g L TA lam D rule S Lf hL hrule hlo)
