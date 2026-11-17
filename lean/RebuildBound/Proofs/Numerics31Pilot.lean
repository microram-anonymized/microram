import RebuildBound.Spec.Numerics31Pilot
import RebuildBound.Proofs.Numerics31Top
import RebuildBound.Proofs.Numerics31Range

/-! Assembly and exposure arithmetic for the numerical pilot. -/

namespace RebuildBound
open Spec
open scoped ENNReal

/-- The shared range estimate and the two separate drain estimates give the
complete preparation and initialization bounds. -/
theorem TPNum31_of (hrange : TPRange31_statement) (hrest : TPRemainder31_statement) :
    TPNum31_statement := by
  rcases hrest with ⟨hp, hi⟩
  have hr : tpRangeTerm init31 32 ≤ ENNReal.ofReal (1 / 2 ^ 101) := hrange
  constructor
  · unfold tpBound
    have hdfs : prep31.dfs = true := rfl
    simp only [hdfs, ite_true, ENNReal.coe_one, NNReal.coe_one, one_mul]
    calc _ = (prep31.k * ENNReal.ofReal (Phi 576 prep31.T prep31.C 32
          (prep31.stashPages * prep31.C)) +
          ENNReal.ofReal (Phi 576 prep31.T prep31.C 32 (prep31.drainPages * prep31.C))) +
          tpRangeTerm prep31 32 := by
            norm_num only [NNReal.coe_ofNat]
            ac_rfl
      _ ≤ ENNReal.ofReal (1 / 2 ^ 107) + ENNReal.ofReal (1 / 2 ^ 101) :=
        add_le_add hp hrange
      _ ≤ ENNReal.ofReal (1 / 2 ^ 100) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        norm_num
  · unfold tpBound
    have hdfs : init31.dfs = true := rfl
    simp only [hdfs, ite_true, ENNReal.coe_one, NNReal.coe_one, one_mul]
    calc _ = (init31.k * ENNReal.ofReal (Phi 576 init31.T init31.C 32
          (init31.stashPages * init31.C)) +
          ENNReal.ofReal (Phi 576 init31.T init31.C 32 (init31.drainPages * init31.C))) +
          tpRangeTerm init31 32 := by
            norm_num only [NNReal.coe_ofNat]
            ac_rfl
      _ ≤ ENNReal.ofReal (1 / 2 ^ 71) + ENNReal.ofReal (1 / 2 ^ 101) := add_le_add hi hr
      _ ≤ ENNReal.ofReal (3 / 2 ^ 72) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        norm_num

/-- Complete preparation and initialization numerical certificates. -/
theorem TPNum31 : Spec.TPNum31_statement := TPNum31_of TPRange31 TPRemainder31

/-- The pilot rows leave room for the remaining ordinary range and stash terms.
This is rational budget arithmetic, not a bound for unproved rows. -/
theorem pilot_range_budget31 :
    (pilotRangeBudgets31.map fun p =>
      (config31.ordinaryCount p.1.1 p.1.2 : ℚ) * p.2).sum < 1 / 2 ^ 65 := by
  decide +kernel

/-- Separate accounting: initialization occurs once, preparation at each
potential top ordinal. -/
theorem pilot_top_budgets31 :
    (config31.ordinals config31.levels : ℚ) * (9 / (16 * 2 ^ 70)) < 1 / 2 ^ 66 ∧
    (config31.ordinals config31.levels : ℚ) * (1 / 2 ^ 100) + 3 / 2 ^ 72 < 1 / 2 ^ 70 := by
  decide +kernel

/-- The certified top expression, charged at every potential top ordinal. -/
theorem top_family31_of (htop : TopNum31_statement) :
    (config31.ordinals config31.levels : ℝ≥0∞) *
      ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
        (min top31.SMerge top31.STier) 576 576 32) ≤ ENNReal.ofReal (1 / 2 ^ 66) := by
  calc
    _ ≤ (config31.ordinals config31.levels : ℝ≥0∞) *
        ENNReal.ofReal (9 / (16 * 2 ^ 70)) :=
      by
        gcongr
        exact htop
    _ = ENNReal.ofReal ((config31.ordinals config31.levels : ℝ) *
        (9 / (16 * 2 ^ 70))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := (Rat.cast_le (K := ℝ)).2 pilot_top_budgets31.1.le
      push_cast at h
      exact h)

/-- Preparation is charged at each potential top ordinal; initialization once. -/
theorem tp_family31_of (htp : TPNum31_statement) :
    (config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
      tpBound init31 32 1 576 576 ≤ ENNReal.ofReal (1 / 2 ^ 70) := by
  rcases htp with ⟨hp, hi⟩
  calc
    _ ≤ (config31.ordinals config31.levels : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 100) +
        ENNReal.ofReal (3 / 2 ^ 72) := by gcongr
    _ = ENNReal.ofReal ((config31.ordinals config31.levels : ℝ) * (1 / 2 ^ 100) +
        3 / 2 ^ 72) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have h := (Rat.cast_le (K := ℝ)).2 pilot_top_budgets31.2.le
      push_cast at h
      exact h)

end RebuildBound
