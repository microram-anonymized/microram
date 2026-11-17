import RebuildBound.Spec.ConfigurationFamilyDirectNumerics
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.Data
import RebuildBound.Spec.ConfigurationFamilyRest
import RebuildBound.Spec.ConfigurationFamilyRange
import RebuildBound.Proofs.NCA5.Class
import RebuildBound.Proofs.ConfigurationFamilyDirectNumerics.A

/-! The numerical registry is keyed by complete geometry; arithmetic reuse
also checks the exact finite-word mass rather than just radix or width. -/
namespace ConfigurationFamilyNumericsTest
open RebuildBound RebuildBound.Model RebuildBound.Spec RebuildBound.Spec.ConfigurationFamily

def smallDirect : DirectJob.Geometry := (directNumericMember 2).direct 3
def smallSep : SepGeom := (directNumericMember 2).directSep 3

example : (smallDirect, smallSep) ∈ directShapes := by decide +kernel

/-- A capacity mutation cannot borrow the checked pair's density/Phi budget. -/
example : ({ smallDirect with outputCapacity := 65 }, smallSep) ∉ directShapes := by decide +kernel
example : (smallDirect, { smallSep with r := 9 }) ∉ directShapes := by decide +kernel

/-- A shape with the same radix but a different range plan has no such row. -/
example : restBudgets.any (fun x => decide (x.1 = smallSep)) = true := by decide +kernel
example : restBudgets.any
    (fun x => decide (x.1 = { smallSep with rangeBits := smallSep.rangeBits + 1 })) = false := by
  decide +kernel

/-- Missing rows and altered budgets are rejected independently of shape validity. -/
example : ((restBudgets.filter (fun x => decide (x.1 ≠ smallSep))).find?
    (fun x => decide (x.1 = smallSep))) = none := by decide +kernel
example : (smallSep, 999) ∉ restBudgets := by decide +kernel

/-- At 61 remaining bits, exactly two radix-seven residue classes are larger. -/
example : qCount 64 3 7 1 = 329406144173384851 := by
  rw [NCA5.qCount_eq (by decide)]
  norm_num
example : qCount 64 3 7 2 = 329406144173384850 := by
  rw [NCA5.qCount_eq (by decide)]
  norm_num

/-- The lower masses at these widths reduce to the same fraction, while the
upper masses do not. The chain reuse premise must distinguish them. -/
example : (2 ^ 61 / 7 : Nat) * 2 ^ 60 = (2 ^ 60 / 7) * 2 ^ 61 := by decide +kernel
example : (2 ^ 61 / 7 + 1 : Nat) * 2 ^ 60 ≠ (2 ^ 60 / 7 + 1) * 2 ^ 61 := by decide +kernel
example : (2 ^ 61 / 7 : Nat) * 2 ^ 61 ≠ (2 ^ 61 / 3) * 2 ^ 61 := by decide +kernel

/-- The finite class coverage includes the lookahead job at zero accesses. -/
example : ({ (directNumericMember 2).config false with horizon := 0 } : Config).ordinals 1 = 1 := by
  decide +kernel

end ConfigurationFamilyNumericsTest
