import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.BU
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.A
import RebuildBound.Proofs.ConfigurationFamilyRest
import RebuildBound.Proofs.NumericsFamilyRange
import RebuildBound.Proofs.NumericsFamilyDirectRange

/-! A common direct-job budget rounds the independently certified B, A and
union terms upward once, before configurations apply their exposure counts. -/
open scoped ENNReal
namespace RebuildBound
open Spec Spec.ConfigurationFamily

theorem ConfigurationFamilyDirectANumerics : ConfigurationFamilyDirectANumerics_statement :=
  ConfigurationFamilyDirectNumericsProof.a_bound ConfigurationFamilyRestNumerics
    ConfigurationFamilyRangeNumerics ConfigurationFamilyDirectRangeNumerics

theorem ConfigurationFamilyDirectNumerics : ConfigurationFamilyDirectNumerics_statement := by
  intro m hm d hd hdn
  obtain ⟨hB, hU⟩ := ConfigurationFamilyDirectBUNumerics m hm d hd hdn
  unfold directBound
  split_ifs with hfirst
  · exact hB.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  · have hA := ConfigurationFamilyDirectANumerics m hm d (by omega) hdn
    apply (add_le_add (add_le_add hB hA) hU).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)

end RebuildBound
