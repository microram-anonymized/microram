import RebuildBound.Proofs.RationalBudget
import RebuildBound.Spec.Numerics31Ordinary
import RebuildBound.Proofs.SelOrd
import RebuildBound.Proofs.Numerics31Pilot
import RebuildBound.Proofs.Inventory31
import RebuildBound.Proofs.Numerics31Rest
import RebuildBound.Proofs.Numerics31OrdRange

open scoped ENNReal

namespace RebuildBound.Numerics31Ordinary

export RationalBudget (sum_ofReal_le weighted_sum_le)

open Spec Model

/-- Exact allocation for every ordinary range row, including existing pilots. -/
theorem range_allocation31 :
    (config31.separatedClasses.map fun p =>
      (config31.ordinaryCount p.1 p.2 : ℚ) * ordinaryRangeBudget31 p).sum =
        (891 / 1024) * (1 / 2 ^ 65) := by decide +kernel

/-- Exact allocation of the geometry-dependent remainder envelope. -/
theorem rest_allocation31 :
    (separated31.map fun p => (p.2 : ℚ) * ordinaryRestBudget31 p.1).sum =
      (6095999 / 8388608) * (1 / 2 ^ 77) := by decide +kernel

lemma range_nonneg31 : ∀ p ∈ config31.separatedClasses,
    0 ≤ ordinaryRangeBudget31 p := by decide +kernel

lemma rest_nonneg31 (g : SepGeom) : 0 ≤ ordinaryRestBudget31 g := by
  unfold ordinaryRestBudget31
  split_ifs <;> positivity

/-- Range bounds lifted through the configuration's complete exposure list. -/
theorem range_family31_of (h : Numerics31OrdRange_statement) :
    (separated31.map fun p => (p.2 : ℝ≥0∞) * selRange p.1).sum ≤
      ENNReal.ofReal ((891 / 1024) * (1 / 2 ^ 65)) := by
  have hs := weighted_sum_le config31.separatedClasses
    (fun p => config31.ordinaryCount p.1 p.2)
    (fun p => selRange (separatedGeometry config31 stashPages31 tierPages31 p.1 p.2))
    ordinaryRangeBudget31 range_nonneg31 h
  rw [range_allocation31] at hs
  simpa only [separated31, separatedRows, List.map_map, Function.comp_def,
    Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow] using hs

/-- The complete remainder family, retaining its own smaller budget. -/
theorem rest_family31_of (h : Numerics31Rest_statement) : OrdinaryRest31_statement := by
  have hp : ∀ p ∈ separated31, selRest p.1 ≤ ENNReal.ofReal (ordinaryRestBudget31 p.1 : ℝ) := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact h c hc
  have hs := weighted_sum_le separated31 Prod.snd (fun p => selRest p.1)
    (fun p => ordinaryRestBudget31 p.1) (fun p _ => rest_nonneg31 p.1) hp
  rw [rest_allocation31] at hs
  exact hs.trans (ENNReal.ofReal_le_ofReal (by norm_num))

/-- Range and remainder terms exhaust the existing separated analytic bound. -/
theorem ordinary31_of (hr : Numerics31OrdRange_statement) (hs : Numerics31Rest_statement) :
    OrdinaryNum31_statement := by
  have he : selSum separated31 =
      (separated31.map fun p => (p.2 : ℝ≥0∞) * selRest p.1).sum +
      (separated31.map fun p => (p.2 : ℝ≥0∞) * selRange p.1).sum := by
    simp only [selSum, SelOrdAux.selSepBound_eq, mul_add, List.sum_map_add]
  unfold OrdinaryNum31_statement
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (1 / 2 ^ 77) +
        ENNReal.ofReal ((891 / 1024) * (1 / 2 ^ 65)) :=
      add_le_add (rest_family31_of hs) (range_family31_of hr)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The complete first-horizon analytic allocation, including the existing
coarse direct-cycle contribution. This is an analytic allocation, not a
failure-probability theorem. -/
theorem total31_of (hr : Numerics31OrdRange_statement) (hs : Numerics31Rest_statement) :
    ENNReal.ofReal (directCost31 : ℝ) + selSum separated31 +
      (config31.ordinals config31.levels : ℝ≥0∞) *
        ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
          (min top31.SMerge top31.STier) 576 576 32) +
      ((config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
        tpBound init31 32 1 576 576) ≤ ENNReal.ofReal (1 / 2 ^ 64) := by
  have hd : ENNReal.ofReal (directCost31 : ℝ) ≤ ENNReal.ofReal (1 / 2 ^ 79) := by
    apply ENNReal.ofReal_le_ofReal
    have h := (Rat.cast_le (K := ℝ)).2 Budget31.1.le
    push_cast at h
    exact h
  calc
    _ ≤ ENNReal.ofReal (1 / 2 ^ 79) + ENNReal.ofReal (1 / 2 ^ 65) +
        ENNReal.ofReal (1 / 2 ^ 66) + ENNReal.ofReal (1 / 2 ^ 70) :=
      add_le_add (add_le_add (add_le_add hd (ordinary31_of hr hs))
        (top_family31_of TopNum31)) (tp_family31_of TPNum31)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

end RebuildBound.Numerics31Ordinary

/-- Unconditional exposure-weighted ordinary remainder bound. -/
theorem RebuildBound.OrdinaryRest31 : RebuildBound.Spec.OrdinaryRest31_statement :=
  RebuildBound.Numerics31Ordinary.rest_family31_of RebuildBound.Numerics31Rest

/-- Unconditional complete separated ordinary numerical bound. -/
theorem RebuildBound.OrdinaryNum31 : RebuildBound.Spec.OrdinaryNum31_statement :=
  RebuildBound.Numerics31Ordinary.ordinary31_of
    RebuildBound.Numerics31OrdRange RebuildBound.Numerics31Rest

namespace RebuildBound
open Spec

/-- Complete first-horizon analytic allocation, including the coarse direct
cost. The hierarchy failure event is connected to this total in
`Proofs/Compose31.lean`. -/
theorem numerical_total31 :
    ENNReal.ofReal (directCost31 : ℝ) + selSum separated31 +
      (config31.ordinals config31.levels : ℝ≥0∞) *
        ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
          (min top31.SMerge top31.STier) 576 576 32) +
      ((config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
        tpBound init31 32 1 576 576) ≤ ENNReal.ofReal (1 / 2 ^ 64) :=
  Numerics31Ordinary.total31_of Numerics31OrdRange Numerics31Rest

end RebuildBound
