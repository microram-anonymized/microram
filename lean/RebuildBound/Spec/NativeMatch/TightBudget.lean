import RebuildBound.Spec.NativeMatch.Allocation

/-! Three rational refinements of existing local analytic bounds. The witness
laws, population cutoffs and geometry remain unchanged. These allocations are
separate from the original family registry. -/
namespace RebuildBound.Spec.NativeMatchTightBudget
open Model ConfigurationFamily

def topShape : TopGeom := ⟨64, 23, 3, 8, 18, true, 4, 2, 4, 3⟩
def rangeShape14 : SepGeom := ⟨64, 14, 0, 5, 8, 9, 2, 2, 1, 2⟩
def rangeShape20 : SepGeom := ⟨64, 20, 0, 5, 9, 14, 2, 2, 2, 2⟩

def topBudget (g : TopGeom) : ℚ :=
  if g = topShape then 83 / (10000 * 2 ^ 64) else ConfigurationFamily.topBudget g

def rangeBudget (g : SepGeom) : ℚ :=
  if g = rangeShape14 then 27 / (50 * 2 ^ 76) else
  if g = rangeShape20 then 27 / (50 * 2 ^ 72) else
  shapeBudget rangeBudgets dyadic g

def sepBudget (g : SepGeom) : ℚ :=
  shapeBudget restBudgets dyadic g + rangeBudget g

def classBudgetQ (m : Member) : JobClass → ℚ :=
  let geo := m.geometry true
  fun c => match c with
  | .ordinary ℓ d => if ℓ = 1 then directBudget d else if d = 1 then 0 else
      ((geo.cfg.sepRow geo.rows ℓ d).map sepBudget).getD 1
  | .topFinish => topBudget geo.top
  | .topPrepare => prepBudget geo.prep
  | .initialization => prepBudget geo.init

def exposureBudget (m : Member) : ℚ :=
  ((m.config true).exposures.map fun p => (p.2 : ℚ) * classBudgetQ m p.1).sum

/-- Exact overflow-plus-matching allocation, independent of a normalization
collision bound. Both starts reserve the initialized overflow envelope. -/
def allocation (m : Member) (initialized : Bool) : ℚ :=
  exposureBudget m + (NativeMatchInventory.weight m initialized : ℚ) / 2 ^ 128

end RebuildBound.Spec.NativeMatchTightBudget

namespace RebuildBound.Spec
open Model ConfigurationFamily NativeMatchTightBudget
open scoped ENNReal

def NativeMatchTightLocalNumerics_statement : Prop :=
  (topFinishBound topShape.C topShape.SR topShape.rho topShape.I topShape.T
      (min topShape.SMerge topShape.STier) 576 576 32 ≤
      (83 : ℝ) / (10000 * 2 ^ 64)) ∧
  (selRange rangeShape14 ≤ ENNReal.ofReal ((27 / (50 * 2 ^ 76) : ℚ) : ℝ)) ∧
  (selRange rangeShape20 ≤ ENNReal.ofReal ((27 / (50 * 2 ^ 72) : ℚ) : ℝ))

def NativeMatchTightExposure_statement : Prop :=
  ∀ m ∈ members, ∀ initialized,
    (m.config initialized).exposureSum (ConfigurationFamily.classBudget m initialized) ≤
      ENNReal.ofReal (NativeMatchTightBudget.exposureBudget m : ℝ)

def NativeMatchTightArithmetic_statement : Prop :=
  ∀ m ∈ members, ∀ initialized : Bool,
    0 ≤ NativeMatchTightBudget.exposureBudget m ∧
    NativeMatchTightBudget.allocation m initialized < 1 / 2 ^ 65

end RebuildBound.Spec
