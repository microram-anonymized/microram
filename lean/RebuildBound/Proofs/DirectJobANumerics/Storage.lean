import RebuildBound.Spec.DirectJobANumerics
import RebuildBound.Proofs.SelRest.Sound
import Mathlib.Tactic.IntervalCases

set_option exponentiation.threshold 512
namespace RebuildBound
open Spec

private theorem storage_check (d : Nat) (hlo : 2 ≤ d) (hhi : d ≤ 8) :
    SelRest.selCheck 400 (selectedDirectSep d) ((1 : ℚ) / 2 ^ 108) = true := by
  interval_cases d <;> decide +kernel

theorem DirectJobSelectedAStorage : DirectJobSelectedAStorage_statement := by
  intro d hlo hhi
  have h := SelRest.sel_sound 400 (selectedDirectSep d) ((1 : ℚ) / 2 ^ 108)
    (storage_check d hlo hhi)
  norm_num at h ⊢
  exact h

end RebuildBound
