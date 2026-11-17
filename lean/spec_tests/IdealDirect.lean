import RebuildBound.Proofs.IdealDirect
import RebuildBound.Proofs.IdealDirectFresh
import spec_tests.IdealExposure

/-! Byte-key direct tests distinguish input causality from output randomness.
The overflow geometry below deliberately has no spare tier and makes no
standard-family or small-error claim. -/
namespace IdealDirectTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.DirectJob MeasureTheory
open scoped ENNReal NNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Exact length distinguishes these empty, leading-zero and long byte keys. -/
def overflowRecords : List Rec :=
  (List.range 66).map fun i => ⟨List.replicate i 0, i, false⟩
def overflowInputs : DirectJob.Inputs := ⟨[], [], [overflowRecords.map some]⟩
def overflowGeometry : DirectJob.Geometry := ⟨0, 1, 1, 0, 0, 0, 0, 0, 0, .direct⟩

example : (overflowRecords.map Rec.key).Nodup := by decide +kernel
example : (overflowRecords[0]!).key = [] ∧ (overflowRecords[1]!).key = [0] ∧
    (overflowRecords[65]!).key.length = 65 := by decide +kernel
example : overflowGeometry.Valid ∧ overflowInputs.Valid overflowGeometry (fun _ => 0) := by
  decide +kernel
example : bExcess overflowGeometry (fun _ => 0) overflowInputs = 2 := by decide +kernel

/-- This is an actual bounded job capacity failure, with all input records
retained by the separate reference continuation. -/
example : runJob overflowGeometry (fun _ => 0) (fun _ => 0) overflowInputs =
    .failed ⟨⟨.produceB, .outputTier, 0⟩, 2, 0⟩ := by rfl

/-- The analytic local theorem applies to the same nonempty overflowing
input, including its 65-byte key. Its arbitrary-load budget is explicit. -/
example (family : IdealKey.Family) :
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | ∃ e, runJob overflowGeometry (fun _ => 0)
        (IdealDirect.familyWords family fresh) overflowInputs = .failed e} ≤
      ENNReal.ofReal (Phi 1 overflowGeometry.U 64 66 overflowGeometry.bCapacity) := by
  apply IdealDirectLocalDigitOne family overflowGeometry overflowInputs (fun _ => 0) 66 1
  all_goals decide +kernel

/-- The empty finite restriction is a normalized law too. -/
example (family : IdealKey.Family) :
    (Measure.infinitePi (fun _ : IdealHierarchy.familyBlock family => IdealKey.wordLaw))
      {fresh | overflowGeometry.bCapacity < bExcess overflowGeometry
        (IdealDirect.familyWords family fresh) ⟨[], [], []⟩} ≤
      ENNReal.ofReal (Phi 1 overflowGeometry.U 64 0 overflowGeometry.bCapacity) := by
  simpa only [Nat.cast_zero] using
    (IdealDirectLocalB family overflowGeometry ⟨[], [], []⟩ 0 1
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- A real one-chunk requester run creates exactly this overloaded input. -/
def cfg : Config := ⟨[2], 1, 1, 66, 66, false⟩
def unionGeometry : DirectJob.Geometry := ⟨0, 2, 2, 0, 0, 0, 0, 0, 0, .direct⟩
def unionSep : SepGeom := ⟨64, 0, 1, 1, 0, 1, 0, 0, 1, 0⟩
def shapes : Shapes := { HierarchyInitializationTest.sh with
  direct := fun d => if d = 1 then overflowGeometry else unionGeometry }
def online : Online.OnlineGeom := ⟨66, 1⟩
def schedule : Online.Schedule := fun _ => ⟨0, []⟩
def client : Adaptive.AdaptiveRun 0 :=
  ⟨[.chunk 66], [], fun _ => false, fun _ i => ⟨List.replicate i 0, i, false⟩⟩
def zeroTape : IdealKey.Tape := fun _ => 0

example (tape : IdealKey.Tape) :
    IdealDirect.trace cfg shapes online schedule client tape =
      IdealDirect.trace cfg shapes online schedule client zeroTape := by rfl

example : levelOneResult cfg shapes (IdealDirect.trace cfg shapes online schedule client zeroTape)
    (IdealHierarchy.words zeroTape) 1 = .failed ⟨⟨.produceB, .outputTier, 0⟩, 2, 0⟩ := by rfl

/-- Reference execution keeps all 66 records after the bounded producer fails. -/
theorem reference_retains : (table cfg shapes (IdealDirect.trace cfg shapes online schedule client zeroTape)
    (IdealHierarchy.words zeroTape) 1 1).records.length = 66 := by
  rw [HierarchyCoveringProof.table_step (by decide +kernel)]
  change (levelOneStep overflowGeometry (fun _ => 0) (fun _ => 0) emptyOutput
    [overflowRecords.map some]).records.length = 66
  decide +kernel

/-- Finite-cylinder positivity proves this is a non-null actual hierarchy
failure, not merely one failing infinite tape of probability zero. -/
theorem actual_failure_positive :
    0 < IdealKey.tapeLaw {tape | jobFails cfg shapes
      (IdealDirect.trace cfg shapes online schedule client tape)
      (IdealHierarchy.words tape) (.ordinary 1 1) = true} := by
  obtain ⟨coordinates, hcoordinates⟩ := IdealJobFailureFiniteRead cfg shapes
    (IdealDirect.trace cfg shapes online schedule client zeroTape) (.ordinary 1 1) zeroTape
  have hpositive : 0 < IdealKey.tapeLaw
      (coordinates.restrict ⁻¹' {coordinates.restrict zeroTape}) := by
    rw [← Measure.map_apply (Finset.measurable_restrict coordinates)
      (measurableSet_singleton _), (IdealKeyRestriction coordinates).2]
    exact pos_iff_ne_zero.mpr (by
      simp [ProbabilityTheory.uniformOn_eq_zero_iff Set.finite_univ])
  apply hpositive.trans_le
  apply measure_mono
  intro tape htape
  have heq := hcoordinates tape (fun c hc => congrFun htape ⟨c, hc⟩)
  change jobFails cfg shapes (IdealDirect.trace cfg shapes online schedule client zeroTape)
    (IdealHierarchy.words tape) (.ordinary 1 1) = true
  dsimp only at heq
  exact heq.trans (by decide +kernel)

theorem exposure_geometry : IdealHierarchy.ExposureGeometry cfg := by
  constructor
  · intro level h1 hL
    simp [cfg, Config.seed]
  · intro level h1 hL
    have : level = 1 := by change level < 2 at hL; omega
    subst level
    decide +kernel
  · intro level h1 hL
    change level ≤ 2 at hL
    interval_cases level <;> decide +kernel

theorem schedule_valid : SchedulePremises cfg schedule (Adaptive.slotCount client.shape) 0 := by
  constructor
  · intro j hj
    simp [schedule, cfg, Config.seed, Online.pos]
  · intro j hj
    simp [schedule]
  · intro j hj c hc
    simp [schedule] at hc
  · intro j hj
    simp [schedule]
  · intro j hj
    simp [schedule, Online.Tiles]

/-- The actual non-null overflow event satisfies the proved canonical-tape
bound with its explicit load 66. No successful-prefix premise is supplied. -/
example : IdealKey.tapeLaw {tape | jobFails cfg shapes
      (IdealDirect.trace cfg shapes online schedule client tape)
      (IdealHierarchy.words tape) (.ordinary 1 1) = true} ≤
    ENNReal.ofReal (Phi 1 overflowGeometry.U 64 cfg.load overflowGeometry.bCapacity) := by
  apply IdealDirectDigitOne cfg shapes online schedule 0 client exposure_geometry
    rfl (by decide +kernel) schedule_valid 1 (by decide +kernel) (by decide +kernel) 1
  all_goals decide +kernel

example : IdealKey.tapeLaw {tape | overflowGeometry.bCapacity <
      bExcess overflowGeometry (jobWord cfg (IdealHierarchy.words tape) 1 1)
        (IdealDirect.inputs cfg shapes online schedule client 1 tape)} ≤
    ENNReal.ofReal (Phi 1 overflowGeometry.U 64 cfg.load overflowGeometry.bCapacity) := by
  apply IdealDirectB cfg shapes online schedule 0 client exposure_geometry
    rfl (by decide +kernel) schedule_valid 1 (by decide +kernel) 1
  all_goals decide +kernel

/-- The next ordinal really consumes the nonempty fallback from the failed
first job, even though its advertised A tier has zero capacity. -/
example : (IdealDirect.inputs cfg shapes online schedule client 2 zeroTape).aRecords.length = 66 := by
  change (table cfg shapes (IdealDirect.trace cfg shapes online schedule client zeroTape)
    (IdealHierarchy.words zeroTape) 1 1).records.length = 66
  exact reference_retains

example (tape : IdealKey.Tape) :
    (IdealDirect.inputs cfg shapes online schedule client 2 tape).bRecords = [] := by rfl

/-- The union bound applies to this continuation after actual overflow; it
does not assume that the predecessor published or that its A tier fits. -/
example : IdealKey.tapeLaw {tape | unionGeometry.outputCapacity <
      (IdealDirect.inputs cfg shapes online schedule client 2 tape).excess unionGeometry
        (jobWord cfg (IdealHierarchy.words tape) 1 2)} ≤
    ENNReal.ofReal (unionSep.curDensity 64 (cfg.load * unionSep.N) *
      Phi 1 unionGeometry.outputHomes 64 cfg.load unionGeometry.outputCapacity) := by
  apply IdealDirectUnion cfg shapes online schedule 0 client exposure_geometry
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) schedule_valid 2 (by decide +kernel) (by decide +kernel) unionSep 1
  all_goals first | decide +kernel | intro word; rfl

/-- Saturated histories permit the raw potential continuation beyond the
configured horizon; the later cycle has no fresh B records. -/
example : cfg.seed 1 + cfg.ordinals 1 < 4 := by decide +kernel
example (tape : IdealKey.Tape) :
    (IdealDirect.inputs cfg shapes online schedule client 4 tape).bRecords = [] := by
  rfl

example : IdealKey.tapeLaw {tape | unionGeometry.outputCapacity <
      (IdealDirect.inputs cfg shapes online schedule client 4 tape).excess unionGeometry
        (jobWord cfg (IdealHierarchy.words tape) 1 4)} ≤
    ENNReal.ofReal (unionSep.curDensity 64 (cfg.load * unionSep.N) *
      Phi 1 unionGeometry.outputHomes 64 cfg.load unionGeometry.outputCapacity) := by
  apply IdealDirectUnion cfg shapes online schedule 0 client exposure_geometry
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rfl (by decide +kernel) schedule_valid 4 (by decide +kernel) (by decide +kernel) unionSep 1
  all_goals first | decide +kernel | intro word; rfl

end IdealDirectTests

namespace IdealDirectFreshTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open IdealExposureConcreteTests

/-- The adopted prior table, B units and every old-family word remain fixed
when the current family is forwarded to a receiving top ordinal. -/
example : IdealDirect.inputs cfg sh online schedule run 4 zeroTape =
      IdealDirect.inputs cfg sh online schedule run 4 futureTape ∧
    jobWord cfg (IdealHierarchy.words zeroTape) 1 3 =
      jobWord cfg (IdealHierarchy.words futureTape) 1 3 := by
  apply IdealDirectInputFresh cfg sh online schedule 1 run exposure_geometry
    rfl (by decide +kernel) schedule_valid 4 (by decide +kernel) zeroTape futureTape
  exact future_outside

/-- Inputs are locally finite on every branch, without a key universe. -/
example : IdealKey.FiniteRead (IdealDirect.inputs cfg sh online schedule run 4) :=
  IdealDirectInputFiniteRead cfg sh online schedule 1 run 4

/-- Earlier observable randomness really changes the actual late input;
resampling independence does not extend to an already exposed family. -/
example : IdealDirect.inputs cfg sh online schedule run 4 zeroTape ≠
    IdealDirect.inputs cfg sh online schedule run 4 exposedTape := by
  intro h
  have hunit := congrArg DirectJob.Inputs.units h
  have hne : (IdealDirect.inputs cfg sh online schedule run 4 zeroTape).units ≠
      (IdealDirect.inputs cfg sh online schedule run 4 exposedTape).units := by
    decide +kernel
  exact hne hunit

end IdealDirectFreshTests
