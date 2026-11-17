import RebuildBound.Proofs.ConfigurationFamilyNumerics.Basic
import RebuildBound.Proofs.ConfigurationFamilyNumerics.Check
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.ConfigurationFamilyRest
import RebuildBound.Proofs.NumericsFamilyRange
import RebuildBound.Proofs.ConfigurationFamilyTop
import RebuildBound.Proofs.ConfigurationFamilyPrep

/-! The checked local certificates cover all consumed shapes; their exact
exposure-weighted rational sum meets the initialized family target. -/
namespace RebuildBound
open Model Spec Spec.ConfigurationFamily ConfigurationFamilyNumericsProof

theorem ConfigurationFamilyNumerics : ConfigurationFamilyNumerics_statement := by
  intro m hm
  apply (exposure_le ConfigurationFamilyDirectBUNumerics ConfigurationFamilyDirectANumerics
    ConfigurationFamilyRestNumerics ConfigurationFamilyRangeNumerics ConfigurationFamilyTopNumerics
    ConfigurationFamilyPrepNumerics m hm (covered m hm)).trans
  apply ENNReal.ofReal_le_ofReal
  have h := (Rat.cast_le (K := ℝ)).2 (checked m hm)
  simpa only [dyadic, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h

end RebuildBound
