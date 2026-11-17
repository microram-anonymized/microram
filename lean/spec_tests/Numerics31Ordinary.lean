import RebuildBound.Proofs.Numerics31Ordinary
import RebuildBound.Proofs.Geometry31

/-! Coverage, allocation and cutoff regressions for all ordinary rows. -/
open RebuildBound RebuildBound.Spec RebuildBound.Model
open scoped ENNReal

-- Full class coverage and the largest ordinary population, without building
-- execution tables or enumerating a word space.
example : config31.separatedClasses.length = 38 := by decide +kernel
example : ∀ p ∈ separated31,
    p.1.stashPages * p.1.C < 256 ∧
    min (p.1.stashPages * p.1.C) (p.1.tierPages * p.1.C) < 256 := by decide +kernel
example : let g := separatedGeometry config31 stashPages31 tierPages31 7 8
    g.N = 2 ^ 23 ∧ g.stashPages * g.C = 128 ∧ g.tierPages * g.C = 128 := by decide +kernel

-- The default allocation is positive and exposure-weighted; the one doubled
-- allocation is separate from the four already certified pilot rows.
example : ordinaryRangeBudget31 (7, 4) = 1 / 2 ^ 76 ∧
    ordinaryRangeBudget31 (7, 6) = 1 / 2 ^ 75 := by decide +kernel
example : ∀ p ∈ config31.separatedClasses,
    0 < config31.ordinaryCount p.1 p.2 ∧ 0 < ordinaryRangeBudget31 p := by decide +kernel
example : ∀ p ∈ pilotRangeBudgets31, ordinaryRangeBudget31 p.1 = p.2 := by decide +kernel

-- Both remainder branches occur in actual rows, including the one-page edge.
example : ordinaryRestBudget31
    (separatedGeometry config31 stashPages31 tierPages31 4 8) = 15 / 2 ^ 96 ∧
    ordinaryRestBudget31
    (separatedGeometry config31 stashPages31 tierPages31 7 8) = 1 / 2 ^ 104 := by decide +kernel

-- Exact accounting checks detect count changes even if the coarser family
-- inequality would still hold after such a change.
example : (config31.separatedClasses.map fun p =>
    (config31.ordinaryCount p.1 p.2 : ℚ) * ordinaryRangeBudget31 p).sum =
      (891 / 1024) * (1 / 2 ^ 65) := Numerics31Ordinary.range_allocation31
example : (separated31.map fun p => (p.2 : ℚ) * ordinaryRestBudget31 p.1).sum =
    6095999 / 2 ^ 100 := by decide +kernel

-- The assembly requires the full configuration-wide row statements.
example : Numerics31OrdRange_statement → Numerics31Rest_statement → OrdinaryNum31_statement :=
  Numerics31Ordinary.ordinary31_of

-- Unconditional remainder theorem, and all model rows through Geometry31.
example : OrdinaryRest31_statement := OrdinaryRest31
example (p : Nat × Nat) (hp : p ∈ config31.separatedClasses) :
    selRest (geometry31.shapes.sep p.1 p.2) ≤ ENNReal.ofReal
      (ordinaryRestBudget31 (separatedGeometry config31 stashPages31 tierPages31 p.1 p.2) : ℝ) := by
  rw [Geometry31.2.1 p hp]
  exact Numerics31Rest p hp

-- Unconditional range and complete-family certificates, with no row-bound
-- hypotheses supplied by this regression.
example : OrdinaryNum31_statement := OrdinaryNum31
example (p : Nat × Nat) (hp : p ∈ config31.separatedClasses) :
    selRange (geometry31.shapes.sep p.1 p.2) ≤
      ENNReal.ofReal (ordinaryRangeBudget31 p : ℝ) := by
  rw [Geometry31.2.1 p hp]
  exact Numerics31OrdRange p hp

example : ENNReal.ofReal (directCost31 : ℝ) + selSum separated31 +
    (config31.ordinals config31.levels : ℝ≥0∞) *
      ENNReal.ofReal (topFinishBound top31.C top31.SR top31.rho top31.I top31.T
        (min top31.SMerge top31.STier) 576 576 32) +
    ((config31.ordinals config31.levels : ℝ≥0∞) * tpBound prep31 32 1 576 576 +
      tpBound init31 32 1 576 576) ≤ ENNReal.ofReal (1 / 2 ^ 64) := numerical_total31
