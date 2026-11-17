import RebuildBound.Spec.NativeMatch.Allocation
import RebuildBound.Proofs.ConfigurationFamilyNumerics
import RebuildBound.Proofs.ConfigurationFamilyBound.Exposure
import RebuildBound.Proofs.IdealCapacity.Analytic
import Mathlib.Tactic

namespace RebuildBound
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem NativeMatchFamilyArithmetic : Spec.NativeMatchFamilyArithmetic_statement := by
  unfold Spec.NativeMatchFamilyArithmetic_statement
  decide +kernel
end RebuildBound

namespace RebuildBound.NativeMatchCombinedAllocationProof
open Model Spec Spec.ConfigurationFamily Spec.NativeMatchInventory
open scoped ENNReal


theorem exposure_nonneg (m : Member) : 0 ≤ exposureBudget m := by
  unfold exposureBudget
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact mul_nonneg (Nat.cast_nonneg _) (ConfigurationFamilyNumericsProof.classBudgetQ_nonneg m p.1)

set_option maxHeartbeats 4000000 in
theorem allocation (checked : ∀ m ∈ members, Fits m true ∧ Fits m false) (m : Member) (hm : m ∈ members) (initialized : Bool) :
    (m.config initialized).exposureSum (classBudget m initialized) +
      (weight m initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128 ≤
      ENNReal.ofReal (1 / (2 : ℝ)^64) := by
  have hcapacity := (ConfigurationFamilyBoundProof.exposure_le_initialized m initialized).trans
    (ConfigurationFamilyNumericsProof.exposure_le ConfigurationFamilyDirectBUNumerics
      ConfigurationFamilyDirectANumerics ConfigurationFamilyRestNumerics ConfigurationFamilyRangeNumerics
      ConfigurationFamilyTopNumerics ConfigurationFamilyPrepNumerics m hm
      (ConfigurationFamilyNumericsProof.covered m hm))
  have hnumeric : Fits m initialized := by
    cases initialized
    · exact (checked m hm).2
    · exact (checked m hm).1
  have hreal : (exposureBudget m : ℝ) + (weight m initialized : ℝ) / (2 : ℝ)^128 ≤
      1 / (2 : ℝ)^64 := by
    unfold Fits at hnumeric
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using (Rat.cast_le.mpr hnumeric : ((exposureBudget m + (weight m initialized : ℚ) / 2 ^ 128 : ℚ) : ℝ) ≤ ((1 / 2 ^ 64 : ℚ) : ℝ))
  have hweight : (weight m initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128 =
      ENNReal.ofReal ((weight m initialized : ℝ) / (2 : ℝ)^128) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_pow]
  calc
    _ ≤ ENNReal.ofReal (exposureBudget m : ℝ) +
        (weight m initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128 := add_le_add hcapacity le_rfl
    _ = ENNReal.ofReal ((exposureBudget m : ℝ) +
        (weight m initialized : ℝ) / (2 : ℝ)^128) := by
      rw [hweight, ENNReal.ofReal_add (by exact_mod_cast exposure_nonneg m) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem allocation_chunks (checked : ∀ m ∈ members, Fits m true ∧ Fits m false) (m : Member) (hm : m ∈ members) (initialized : Bool) (h : Nat) :
    (h : ℝ≥0∞) * (m.config initialized).exposureSum (classBudget m initialized) +
      (h : ℝ≥0∞) * ((weight m initialized : ℝ≥0∞) / (2 : ℝ≥0∞)^128) ≤
      (h : ℝ≥0∞) * ENNReal.ofReal (1 / (2 : ℝ)^64) := by
  rw [← mul_add]
  exact mul_le_mul' le_rfl (allocation checked m hm initialized)

end RebuildBound.NativeMatchCombinedAllocationProof
namespace RebuildBound
open Spec Model Model.Hierarchy Model.Online Spec.IdealHierarchy Spec.IdealDirect
open scoped ENNReal

theorem NativeMatchCapacityAllocation :
    NativeMatchCapacityAllocation_statement := by
  intro initialized member hm h hh geo c g S init m width batches fs choose n compiled
    hinit hgeom hE hn hS hcap a
  have hb := IdealCapacityAnalytic initialized member hm h hh c g S init m width batches
    choose hinit hgeom hE hn hS hcap
  exact (add_le_add hb le_rfl).trans
    (NativeMatchCombinedAllocationProof.allocation_chunks NativeMatchFamilyArithmetic member hm initialized h)
end RebuildBound

namespace RebuildBound
theorem NativeMatchCombinedAllocation : Spec.NativeMatchCombinedAllocation_statement :=
  NativeMatchCombinedAllocationProof.allocation NativeMatchFamilyArithmetic
end RebuildBound
