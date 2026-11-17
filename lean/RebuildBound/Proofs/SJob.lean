import RebuildBound.Proofs.SG1pfin
import RebuildBound.Proofs.SG2fin

/-! The separated job's bound: SG1p with the range term discharged by SG2. -/

theorem RebuildBound.SJob : RebuildBound.Spec.SJob_statement := by
  intro g L lam D rule K1 K2 hv hl hr hlam hC hI hK1 hK2
  unfold RebuildBound.Spec.sepBound
  exact RebuildBound.SG1p g L lam D rule _ K1 K2 hv hl hr hlam hC hK1 hK2
    (RebuildBound.SG2 g L lam D rule hv hl hr hI)
