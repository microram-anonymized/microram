import RebuildBound.Spec.DirectJobSelected
import RebuildBound.Proofs.NumericalPhi
import Mathlib.Tactic.IntervalCases

set_option exponentiation.threshold 512

namespace RebuildBound
open Spec NTop

theorem DirectJobSelectedGeometry : DirectJobSelectedGeometry_statement := by
  constructor
  · intro d hlo hhi
    interval_cases d <;> decide
  · intro d hlo hhi
    interval_cases d <;> decide

theorem DirectJobSelectedAAdapter : DirectJobSelectedAAdapter_statement := by
  intro d hlo hhi
  interval_cases d <;> constructor <;> decide

private theorem producer_check :
    2 ^ 117 * phiNum (2 ^ 400) 100 32 256 16 64 64 32 1 ≤ 2 ^ 400 := by
  decide +kernel

private theorem output_check (d : Nat) (hlo : 1 ≤ d) (hhi : d ≤ 8) :
    2 ^ 112 * phiNum (2 ^ 400) 100 32 256 (d * 16) 64 64 32 1 ≤ 2 ^ 400 := by
  interval_cases d <;> decide +kernel

private theorem checked_bound (n exponent : Nat)
    (hc : 2 ^ exponent * phiNum (2 ^ 400) 100 32 256 n 64 64 32 1 ≤ 2 ^ 400) :
    Phi 256 n 64 32 64 ≤ 1 / (2 : ℝ) ^ exponent := NumericalPhi.single_le 256 n 64 64 exponent hc

theorem DirectJobSelectedExcess : DirectJobSelectedExcess_statement := by
  exact ⟨checked_bound 16 117 producer_check,
    fun d hlo hhi => checked_bound (d * 16) 112 (output_check d hlo hhi)⟩

theorem DirectJobSelectedDensity : DirectJobSelectedDensity_statement := by
  intro d D hlo hhi hD hD2
  calc D * Phi 256 (d * 16) 64 32 64
      ≤ D * (1 / (2 : ℝ) ^ 112) :=
        mul_le_mul_of_nonneg_left (DirectJobSelectedExcess.2 d hlo hhi) hD
    _ ≤ 2 * (1 / (2 : ℝ) ^ 112) := mul_le_mul_of_nonneg_right hD2 (by positivity)
    _ = 1 / (2 : ℝ) ^ 111 := by norm_num

end RebuildBound
