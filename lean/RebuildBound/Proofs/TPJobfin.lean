import RebuildBound.Proofs.TPJobfin.Generic
import RebuildBound.Proofs.TG1
import RebuildBound.Proofs.TG2
import RebuildBound.Proofs.TPEng
import RebuildBound.Proofs.TP5
import RebuildBound.Proofs.TP6
import RebuildBound.Proofs.TP4fin
import RebuildBound.Proofs.TPNum
import RebuildBound.Proofs.D1

/-!
# The top preparation's and the initialization's bounds, assembled (package TPJobfin)

TPJob and IJob from the pilot bounds (TG1, IG1) with the range term discharged
by TG2 and IG2, and the deterministic theorems TPEngine, TP5, TP6, TP4a, TP4b.
TPSel and ISel apply them at the selected top with TPNum.
-/

open scoped ENNReal NNReal

namespace RebuildBound

open RebuildBound.Spec RebuildBound.Model

theorem TPSel : TPSel_statement := by
  intro L unsh hL
  refine le_trans ?_ TPNum
  exact TPJob selectedTP L unsh 32 1 engineRule 256 256 (by decide) hL D1
    (fun _ => by decide) (by decide) (by decide)

theorem ISel : ISel_statement := by
  intro L input hL
  refine le_trans ?_ TPNum
  have h := IJob selectedTP L input engineRule 256 256 (by decide) hL D1
    (fun _ => by decide) (by decide) (by decide)
  have h32 : ((selectedTP.C / 2 : ℕ) : ℝ≥0) = 32 := by norm_num [selectedTP]
  rwa [h32] at h

end RebuildBound
