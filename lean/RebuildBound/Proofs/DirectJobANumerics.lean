import RebuildBound.Spec.DirectJobANumerics
import RebuildBound.Proofs.DirectJobANumerics.Ranges
import RebuildBound.Proofs.DirectJobANumerics.Storage
import RebuildBound.Proofs.SelOrd
import Mathlib.Tactic.IntervalCases

/-! Kernel-checked selected completed-A numerical expressions. The shared
storage bound includes its final-excess summand, giving a conservative A budget.
Input laws and native event correspondence remain separate premises. -/

set_option exponentiation.threshold 512

namespace RebuildBound
open Spec

theorem DirectJobSelectedARange : DirectJobSelectedARange_statement := by
  intro d hlo hhi
  interval_cases d
  · exact DirectJobANumerics.selectedRange2
  · exact DirectJobANumerics.selectedRange3
  · exact DirectJobANumerics.selectedRange4
  · exact DirectJobANumerics.selectedRange5
  · exact DirectJobANumerics.selectedRange6
  · exact DirectJobANumerics.selectedRange7
  · exact DirectJobANumerics.selectedRange8

theorem DirectJobSelectedANumerics : DirectJobSelectedANumerics_statement := by
  intro d hlo hhi
  rw [SelOrdAux.selSepBound_eq]
  calc selRest (selectedDirectSep d) + selRange (selectedDirectSep d)
      ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 108) + ENNReal.ofReal (1 / (2 : ℝ) ^ 103) :=
        add_le_add (DirectJobSelectedAStorage d hlo hhi) (DirectJobSelectedARange d hlo hhi)
    _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 102) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      norm_num

end RebuildBound
