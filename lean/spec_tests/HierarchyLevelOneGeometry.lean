import RebuildBound.Proofs.HierarchyLevelOneChunks
import spec_tests.ConfigurationFamily

/-! The public level-one projection uses the actual 128/256/512-record
incoming populations for every family member, from both starts. Its coordinate
proof transfers to arbitrary horizons through the existing carry arithmetic.
This tests the input-tape law, not a cycle-failure or family capacity bound. -/

namespace HierarchyLevelOneGeometryTest
open RebuildBound RebuildBound.Model RebuildBound.Spec
open ConfigurationFamilyTest

/-- Reuse the family structural checks and the shared horizon transport. -/
theorem members_steps (initialized : Bool) (m : Member) (hm : m ∈ members) (H : Nat) :
    HierarchyLevelOneProof.StepFacts { (m.geometry initialized).cfg with horizon := H } := by
  have F := members_low initialized m hm
  apply HierarchyLevelOneChunksProof.stepFacts_of
  intro ℓ h1 hL
  refine ⟨F.seed ℓ h1 hL, lt_of_lt_of_le (by decide : 0 < 2) (F.fan ℓ h1 hL).1, ?_⟩
  simp only [Config.carryPositions, F.carrySucc ℓ h1 hL]
  ring

/-- Every manifest geometry obtains the new public law at every horizon. -/
theorem members_projection_horizon (initialized : Bool) (m : Member) (hm : m ∈ members)
    (H : Nat) :
    HierarchyLevelOneGeometryFor { (m.geometry initialized).cfg with horizon := H }
      (m.geometry initialized).keyCapacity :=
  HierarchyLevelOneGeometry _ _ (members_steps initialized m hm H)

/-- In particular, both starts retain the standard family horizon. -/
theorem members_projection (initialized : Bool) (m : Member) (hm : m ∈ members) :
    HierarchyLevelOneGeometryFor (m.geometry initialized).cfg (m.geometry initialized).keyCapacity :=
  members_projection_horizon initialized m hm (m.geometry initialized).cfg.horizon

set_option maxRecDepth 32768 in
/-- The family uses all three actual incoming population caps. -/
theorem population_caps (initialized : Bool) :
    (members.map fun m => (m.geometry initialized).cfg.load *
      (m.geometry initialized).cfg.carry1).toFinset = {128, 256, 512} := by
  cases initialized <;> decide +kernel

/-- Replacing the horizon never changes the population bound supplied by the
new interface. -/
theorem population_cap_horizon (initialized : Bool) (m : Member) (H : Nat) :
    ({ (m.geometry initialized).cfg with horizon := H } : Config).load *
        ({ (m.geometry initialized).cfg with horizon := H } : Config).carry1 = 64 * m.r0 := by
  change 32 * (2 * m.r0) = _
  omega

end HierarchyLevelOneGeometryTest
