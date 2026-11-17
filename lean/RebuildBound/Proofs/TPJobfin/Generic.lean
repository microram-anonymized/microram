import RebuildBound.Proofs.TG1
import RebuildBound.Proofs.TG2
import RebuildBound.Proofs.TPEng
import RebuildBound.Proofs.TP5
import RebuildBound.Proofs.TP6
import RebuildBound.Proofs.TP4fin
import RebuildBound.Proofs.D1

/-! Generic top preparation and initialization probability assembly. Concrete
numerical certificates enter only the selected parent corollaries. -/
open scoped ENNReal NNReal
namespace RebuildBound
open Spec Model

theorem TG1 : TG1_statement := TG1_of TPEngine TP6 TP4a TP4b
theorem IG1 : IG1_statement := IG1_of TPEngine TP6 TP4a TP4b
theorem TG2 : TG2_statement := TG2_of TP5_step TP5_route
theorem IG2 : IG2_statement := IG2_of TP5_step TP5_route

theorem TPJob : TPJob_statement := by
  intro g L unsh lam D rule K1 K2 hg hL hr hI hK1 hK2
  have h := TG1 g L unsh lam D rule ((D : ℝ≥0∞) * tpRangeTerm g lam) K1 K2 hg hL hr hK1 hK2
    (fun hd => TG2 g L unsh lam D rule hg hL hr hd (hI hd))
  simpa [tpBound] using h

theorem IJob : IJob_statement := by
  intro g L input rule K1 K2 hg hL hr hI hK1 hK2
  have h := IG1 g L input rule (tpRangeTerm g ((g.C / 2 : ℕ) : ℝ≥0)) K1 K2 hg hL hr hK1 hK2
    (fun hd => IG2 g L input rule hg hL hr hd (hI hd))
  simpa [tpBound] using h

end RebuildBound
