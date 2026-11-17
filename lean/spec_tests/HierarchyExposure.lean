import RebuildBound.Proofs.HierarchyExposure
import spec_tests.ConfigurationFamilyData

namespace HierarchyExposureTest
open RebuildBound RebuildBound.Model
open scoped ENNReal

def cfg (H : Nat) (initialized : Bool) : Config := ⟨[2], 4, 8, 32, H, initialized⟩

/-- Partial carry periods keep the lookahead ordinal, including at zero accesses. -/
example : (cfg 0 false).exposures =
    [(.ordinary 1 1, 1), (.ordinary 1 2, 0), (.topPrepare, 1), (.topFinish, 1)] := by decide

example : (cfg 513 true).exposures =
    [(.ordinary 1 1, 3), (.ordinary 1 2, 2), (.topPrepare, 3), (.topFinish, 3),
      (.initialization, 1)] := by decide

example : ([0, 127, 128, 129, 255, 256, 257, 513].map fun H =>
    ((cfg H false).ordinaryCount 1 1, (cfg H false).ordinaryCount 1 2,
      (cfg H false).ordinals 2)) =
    [(1,0,1), (1,0,1), (1,1,1), (1,1,1), (1,1,1), (2,1,2), (2,1,2), (3,2,3)] := by decide

/-- One theorem covers the entire manifest, for arbitrary bounds including ∞. -/
example (m : ConfigurationFamilyTest.Member) (B : JobClass → ℝ≥0∞) :
    (m.config true).exposureSum B = (m.config false).exposureSum B + B .initialization ∧
      (m.config false).exposureSum B ≤ (m.config true).exposureSum B :=
  HierarchyExposureBudget (m.config true) B

/-- Dropping the lookahead top preparation/finish is not empty-start accounting. -/
example : (cfg 0 false).exposures ≠
    [(.ordinary 1 1, 1), (.ordinary 1 2, 0)] := by decide

example : (cfg 513 true).exposures ≠ (cfg 513 false).exposures := by decide

end HierarchyExposureTest
