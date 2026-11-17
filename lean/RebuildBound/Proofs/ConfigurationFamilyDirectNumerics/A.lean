import RebuildBound.Spec.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.Check
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.AKeys
import RebuildBound.Proofs.SelOrd

/-! Direct A histories consume the same exact-shape numerical rows as the
separated jobs. Only the six missing small-radix range shapes add certificates. -/
open scoped ENNReal
namespace RebuildBound
open Model Spec Spec.ConfigurationFamily
namespace ConfigurationFamilyDirectNumericsProof

set_option exponentiation.threshold 512
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem dyadic_le {e : Nat} (he : 100 ≤ e) :
    ENNReal.ofReal (1 / (2 : ℝ) ^ e) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 100) := by
  apply ENNReal.ofReal_le_ofReal
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) he)

theorem a_shape_bound
    (hrest : ConfigurationFamilyRestNumerics_statement)
    (hrange : ConfigurationFamilyRangeNumerics_statement)
    (hextra : ConfigurationFamilyDirectRangeNumerics_statement)
    (x : DirectJob.Geometry × SepGeom) (hx : x ∈ directShapes)
    (hd : 2 ≤ x.1.digit) :
    (if x.1.ranges = .direct then selRest x.2 else selSepBound x.2) ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 99) := by
  obtain ⟨hrestKey, hrangeKey⟩ := aCoverage x hx hd
  obtain ⟨y, hy, hys⟩ := List.any_eq_true.1 hrestKey
  obtain ⟨heq, he⟩ := of_decide_eq_true hys
  have hR : selRest x.2 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 100) := by
    rw [← heq]
    exact (hrest y hy).trans (dyadic_le he)
  split_ifs with hdir
  · exact hR.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  · obtain ⟨z, hz, hzs⟩ := List.any_eq_true.1 (hrangeKey hdir)
    obtain ⟨heq', he'⟩ := of_decide_eq_true hzs
    have hG : selRange x.2 ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 100) := by
      rw [← heq']
      apply le_trans _ (dyadic_le he')
      rcases List.mem_append.1 hz with hz | hz
      · exact hrange z hz
      · exact hextra z hz
    rw [SelOrdAux.selSepBound_eq]
    apply (add_le_add hR hG).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

theorem a_bound
    (hrest : ConfigurationFamilyRestNumerics_statement)
    (hrange : ConfigurationFamilyRangeNumerics_statement)
    (hextra : ConfigurationFamilyDirectRangeNumerics_statement) :
    ConfigurationFamilyDirectANumerics_statement := by
  intro m hm d hd hdn
  have hx := coverage m hm d
    (List.mem_range'.2 ⟨d - 1, by omega, by omega⟩)
  apply a_shape_bound hrest hrange hextra _ hx
  change 2 ≤ (m.direct d).digit
  unfold Member.direct
  dsimp only
  split_ifs <;> exact hd

end ConfigurationFamilyDirectNumericsProof
end RebuildBound
