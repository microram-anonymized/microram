import RebuildBound.Proofs.Numerics31Pilot
import RebuildBound.Proofs.Geometry31

/-! Numerical-pilot boundary checks. All geometry comes from Configuration31. -/

open RebuildBound RebuildBound.Spec RebuildBound.Model
open scoped ENNReal

-- Complete-excess cutoffs must exceed the actual capacities; the shadow
-- cutoff 256 is insufficient for the four-page preparation stash.
example : prep31.stashPages * prep31.C < 576 ∧
    prep31.drainPages * prep31.C < 576 ∧
    init31.drainPages * init31.C < 576 ∧
    top31.C < 576 ∧ min top31.SMerge top31.STier < 576 := by decide +kernel

example : ¬ prep31.stashPages * prep31.C < 256 := by decide +kernel

-- Sharing the range proof must not equate the drains.
example : tpRangeTerm init31 32 = tpRangeTerm prep31 32 := rfl
example : init31.drainPages ≠ prep31.drainPages := by decide +kernel

-- Every pilot coordinate is a real row, and the deepest ordinary pilot
-- and the preparation have depth nine despite their different range bits.
example : ∀ p ∈ pilotRangeBudgets31, p.1 ∈ config31.separatedClasses := by decide +kernel
example : let g := separatedGeometry config31 stashPages31 tierPages31 7 8
    g.k - g.I = 9 := by decide +kernel
example : prep31.k - 1 - prep31.I = 9 ∧ prep31.rangeBits = 10 := by decide +kernel

-- Full analytic bounds follow from the separate range and remainder results.
example : TPRange31_statement → TPRemainder31_statement → TPNum31_statement := TPNum31_of

-- Unconditional numerical results and their actual hierarchy exposure sums.
example : TopNum31_statement := TopNum31
example : TPNum31_statement := TPNum31

example : selRange (geometry31.shapes.sep 7 8) ≤
    ENNReal.ofReal ((3 / 2 ^ 79 : ℚ) : ℝ) := by
  rw [Geometry31.2.1 (7, 8) (by decide +kernel)]
  exact Numerics31Range ((7, 8), 3 / 2 ^ 79) (by decide +kernel)

example : (config31.ordinals config31.levels : ℝ≥0∞) *
    ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
      (min top31.SMerge top31.STier) 576 576 32) ≤ ENNReal.ofReal (1 / 2 ^ 66) :=
  top_family31_of TopNum31

example : (config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
    tpBound init31 32 1 576 576 ≤ ENNReal.ofReal (1 / 2 ^ 70) :=
  tp_family31_of TPNum31
