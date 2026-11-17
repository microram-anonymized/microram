import RebuildBound.Proofs.IdealFreshness
import spec_tests.ApiStructural
import RebuildBound.Proofs.IdealFailure
import spec_tests.HierarchyInitialization

namespace IdealExposureConcreteTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.Adaptive
open IdealKey

/-- Both initialized and empty structural geometries supply the public timing
facts without a probability or key-universe contract. -/
example (initialized : Bool) :
    IdealHierarchy.ExposureGeometry (ApiStructuralTests.geo initialized).cfg :=
  IdealExposureGeometry _ (ApiStructuralTests.structural initialized)

/-- Keep the initialized top published while two requester units complete. -/
def cfg : Config := ⟨[2], 1, 1, 1, 2, true⟩
def sh : Shapes := HierarchyInitializationTest.sh
def online : OnlineGeom := ⟨1, 1⟩
def schedule : Schedule := fun _ => ⟨2, [(2, 1)]⟩
def client : Client 1 := fun rows _ =>
  if rows.isEmpty then ⟨LogicalKey.ofNat (0), 7, false⟩
  else ⟨LogicalKey.ofNat (100 + (rows.headD fun _ => 0) 0), 9, false⟩
def run : AdaptiveRun 1 := ⟨[.probe, .blind], [], fun _ => false, client⟩

def zeroTape : Tape := fun _ => 0
/-- Change one already exposed word; all dummy words remain unchanged. -/
def exposedTape : Tape := fun coordinate =>
  if coordinate = .inl ((2, 1), LogicalKey.ofNat 0) then 1 else 0
/-- Change every word of a still-future family, including unseen keys. -/
def futureTape : Tape := fun coordinate =>
  match coordinate with
  | .inl (family, _) => if family = (2, 2) then 1 else 0
  | .inr _ => 0

def actual (tape : Tape) : OnlineBatch.BatchRun :=
  realized cfg sh online schedule run (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)

theorem schedule_valid : SchedulePremises cfg schedule 2 1 := by
  constructor
  · intro j hj; interval_cases j <;> decide +kernel
  · intro j hj; dsimp [schedule]; decide +kernel
  · intro j hj c hc
    simp only [schedule, List.mem_singleton] at hc
    subst c
    decide +kernel
  · intro j hj; dsimp [schedule]; decide +kernel
  · intro j hj; norm_num [schedule, Tiles, window, cfg, Config.levels, Config.carryPositions, Config.carry]

example : online.unitEntries * online.unitsPerPrefix = cfg.carryPositions 1 := rfl

/-- An active real probe, not an empty observation dimension or forced-zero cell. -/
example : OnlineBatch.isReal cfg sh online (actual zeroTape) schedule
    (IdealHierarchy.words zeroTape) 0 0 = true := by decide +kernel

example : transcript cfg sh online schedule run 2
    (IdealHierarchy.words zeroTape) (IdealHierarchy.dummy zeroTape) 0 0 = 0 ∧
    transcript cfg sh online schedule run 2
    (IdealHierarchy.words exposedTape) (IdealHierarchy.dummy exposedTape) 0 0 = 1 := by
  decide +kernel

/-- Changing an exposed family changes an actual subsequent chosen key. -/
example : (OnlineBatch.slots (actual zeroTape)).map (fun slot => LogicalKey.toNat slot.record.key) = [0, 100] ∧
    (OnlineBatch.slots (actual exposedTape)).map (fun slot => LogicalKey.toNat slot.record.key) = [0, 101] := by
  decide +kernel

/-- The effect reaches a completed trace unit, not just an unconsumed tail. -/
example : (OnlineBatch.traceOf online (actual zeroTape)).units 1 ≠
    (OnlineBatch.traceOf online (actual exposedTape)).units 1 := by
  decide +kernel

/-- Perturbing an entire future family preserves the actual adaptive requests
and completed units through its public cutoff. -/
example : (OnlineBatch.slots (actual zeroTape)).map (fun slot => slot.record) =
    (OnlineBatch.slots (actual futureTape)).map (fun slot => slot.record) ∧
    (OnlineBatch.traceOf online (actual zeroTape)).units 0 =
      (OnlineBatch.traceOf online (actual futureTape)).units 0 ∧
    (OnlineBatch.traceOf online (actual zeroTape)).units 1 =
      (OnlineBatch.traceOf online (actual futureTape)).units 1 := by
  decide +kernel

/-- The perturbation meets the complete-outside equality premise. -/
theorem future_outside (coordinate : IdealKey.Coord)
    (hout : coordinate ∉ IdealHierarchy.familyBlock (2, 2)) :
    zeroTape coordinate = futureTape coordinate := by
  cases coordinate with
  | inl pair =>
    obtain ⟨family, key⟩ := pair
    change ¬ family = (2, 2) at hout
    simp [zeroTape, futureTape, hout]
  | inr pair => rfl

/-- Both completed units lie within the future family's cutoff, whereas the
family producing the observed bucket is strictly earlier. -/
example : cfg.seed 1 + 1 + 1 ≤ time cfg 1 4 ∧ time cfg 2 1 < time cfg 1 4 := by decide +kernel


/-- Completing carries use this actual receiving family, rather than an unused
nonterminal family label. -/
example : familyOf cfg 1 4 = (2, 2) := by decide +kernel

theorem exposure_geometry : IdealHierarchy.ExposureGeometry cfg := by
  constructor
  · intro level h1 hL
    have : level = 1 := by change level < 2 at hL; omega
    subst level
    decide +kernel
  · intro level h1 hL
    have : level = 1 := by change level < 2 at hL; omega
    subst level
    decide +kernel
  · intro level h1 hL
    change level ≤ 2 at hL
    interval_cases level <;> decide +kernel

/-- This application includes the unit ending exactly at the family cutoff. -/
example : (OnlineBatch.traceOf online (actual zeroTape)).units 1 =
    (OnlineBatch.traceOf online (actual futureTape)).units 1 := by
  exact IdealAdaptiveFamilyFresh cfg sh online schedule 1 run exposure_geometry
    rfl (by decide +kernel) schedule_valid (2, 2) zeroTape futureTape future_outside 1 (by decide +kernel)

/-- Independence is for the actual adaptive prefix and all keys of the
receiving family simultaneously. -/
example : letI : MeasurableSpace (List (List Bucket)) := ⊤
    ProbabilityTheory.IndepFun
      (IdealHierarchy.inputPrefix cfg sh online schedule run (time cfg 2 2))
      (IdealHierarchy.familyBlock (2, 2)).domRestrict tapeLaw := by
  exact IdealInputPrefixIndependent cfg sh online schedule 1 run exposure_geometry
    rfl (by decide +kernel) schedule_valid (2, 2)

end IdealExposureConcreteTests
