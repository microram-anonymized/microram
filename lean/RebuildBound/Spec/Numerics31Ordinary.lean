import RebuildBound.Spec.Numerics31Pilot

/-!
# Complete ordinary numerical bounds for capacity 2^31

Budgets are functions on the configuration's classes and geometry. Every
separated class must satisfy its bound; no independent row inventory is used.
These statements concern analytic expressions, not hierarchy failure events.
-/

namespace RebuildBound.Spec
open Model
open scoped ENNReal

/-- Keep the certified pilot allocations. Every other row receives the same
exposure-weighted allocation, with twice that allocation for the last level's
digit six. This exception is numerical budget data, not geometry. -/
def ordinaryRangeBudget31 (p : Nat × Nat) : ℚ :=
  ((pilotRangeBudgets31.find? fun x => x.1 == p).map Prod.snd).getD
    ((if p = (config31.levels - 1, 6) then 1 / 2 ^ 71 else 1 / 2 ^ 72) /
      (config31.ordinaryCount p.1 p.2 : ℚ))

/-- A shared remainder allocation depending only on the actual geometry.
One-page stashes use a quadratic population envelope; larger stashes use a
common bound. The row theorem checks the allocation for every actual row. -/
def ordinaryRestBudget31 (g : SepGeom) : ℚ :=
  if g.stashPages = 1 then ((g.k + 1) * g.N ^ 2 : ℚ) / 2 ^ 124 else 1 / 2 ^ 104

def Numerics31OrdRange_statement : Prop :=
  ∀ p ∈ config31.separatedClasses,
    selRange (separatedGeometry config31 stashPages31 tierPages31 p.1 p.2) ≤
      ENNReal.ofReal (ordinaryRangeBudget31 p : ℝ)

def Numerics31Rest_statement : Prop :=
  ∀ p ∈ config31.separatedClasses,
    let g := separatedGeometry config31 stashPages31 tierPages31 p.1 p.2
    selRest g ≤ ENNReal.ofReal (ordinaryRestBudget31 g : ℝ)

/-- Complete exposure-weighted remainder family. -/
def OrdinaryRest31_statement : Prop :=
  (separated31.map fun p => (p.2 : ℝ≥0∞) * selRest p.1).sum ≤
    ENNReal.ofReal (1 / 2 ^ 77)

/-- Complete separated ordinary family, including range, stage stashes,
radix stash, insertion and output-tier terms. -/
def OrdinaryNum31_statement : Prop :=
  selSum separated31 ≤ ENNReal.ofReal (1 / 2 ^ 65)

end RebuildBound.Spec
