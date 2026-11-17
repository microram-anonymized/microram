import RebuildBound.Proofs.G3fin
import RebuildBound.Proofs.TopNum2

/-!
# TopSel2: the selected top finish, at most 0.5845 · 2^-78

G3 at the selected shape with cutoffs 256, then TopNum2's numeric bound on its `topFinishBound`.
-/

open scoped ENNReal NNReal

theorem RebuildBound.TopSel2 : RebuildBound.Spec.TopSel2_statement := by
  intro L unsh hL
  refine (RebuildBound.G3 RebuildBound.Spec.selectedTop L unsh 32 256 256 hL (by decide) (by decide)
    (by decide)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hT := RebuildBound.TopNum2
  unfold RebuildBound.Spec.TopNum2_statement at hT
  have e : RebuildBound.Spec.topFinishBound RebuildBound.Spec.selectedTop.C
      RebuildBound.Spec.selectedTop.SR RebuildBound.Spec.selectedTop.rho
      RebuildBound.Spec.selectedTop.I RebuildBound.Spec.selectedTop.T
      (min RebuildBound.Spec.selectedTop.SMerge RebuildBound.Spec.selectedTop.STier) 256 256
      ((32 : ℝ≥0) : ℝ) = RebuildBound.Spec.topFinishBound 64 128 4 18 (2 ^ 22) 128 256 256 32 := by
    norm_num [RebuildBound.Spec.selectedTop, RebuildBound.Model.TopGeom.SR,
      RebuildBound.Model.TopGeom.T, RebuildBound.Model.TopGeom.SMerge,
      RebuildBound.Model.TopGeom.STier]
  rw [e]
  exact hT
