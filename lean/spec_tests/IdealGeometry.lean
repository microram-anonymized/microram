import RebuildBound.Proofs.IdealGeometry
import RebuildBound.Proofs.IdealGeometryFamily
import spec_tests.IdealCapacity

/-! Generic analytic applicability is exercised outside the certified geometry
inventory by changing declared live capacity to zero or one. Physical geometry,
public shape and analytic budgets stay explicit; no new small-error claim is
made for those nonstandard instances. -/
namespace IdealGeometryTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid online)
open ApiStructuralTests (batches)
open IdealTopPrepFamilyTests (frames choose)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def parameters := IdealGeometry.familyParameters member

def geometry (initialized one : Bool) : HierarchyGeometry :=
  { member.geometry initialized with keyCapacity := if one then 1 else 0 }

/-- These instances genuinely fall outside every member of the inventory. -/
theorem outside_family (initialized one : Bool) :
    ∀ candidate ∈ ConfigurationFamily.members,
      geometry initialized one ≠ candidate.geometry initialized := by
  have hpositive : ∀ candidate ∈ ConfigurationFamily.members,
      1 < (candidate.geometry initialized).keyCapacity := by
    cases initialized <;> decide +kernel
  intro candidate hc heq
  have h := congrArg HierarchyGeometry.keyCapacity heq
  have hp := hpositive candidate hc
  change (if one then 1 else 0) = _ at h
  cases one <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> omega

/-- Only storage capacity changes; all population/probability applicability
conditions still follow from the physical shapes and explicit arithmetic. -/
theorem certificates (initialized one : Bool) :
    (geometry initialized one).Structural ∧ (geometry initialized one).cfg.Valid ∧
      IdealGeometry.Coverage (geometry initialized one) ∧
      IdealGeometry.Analytic (geometry initialized one) parameters ∧
      IdealGeometry.WindowArithmetic (geometry initialized one).cfg := by
  obtain ⟨_, hv, hc, ha, hw, _⟩ := IdealGeometryFamily initialized member member_valid
  refine ⟨?_, hv, ?_, ?_, hw⟩
  · cases initialized <;> cases one <;> decide +kernel
  · cases hc
    constructor <;> assumption
  · cases ha
    constructor <;> assumption

/-- Every certified member supplies exactly the legacy analytic budget. This
checks both starts without introducing a numerical dependency in the bridge. -/
example (initialized : Bool) (candidate : ConfigurationFamily.Member)
    (hc : candidate ∈ ConfigurationFamily.members) :
    IdealGeometry.Analytic (candidate.geometry initialized)
      (IdealGeometry.familyParameters candidate) ∧
    IdealGeometry.classBudget (candidate.geometry initialized)
      (IdealGeometry.familyParameters candidate) =
      ConfigurationFamily.classBudget candidate initialized := by
  have h := IdealGeometryFamily initialized candidate hc
  exact ⟨h.2.2.2.1, h.2.2.2.2.2⟩

/-- A zero route cutoff is rejected even when the rest of the geometry is
valid. Geometry validity does not manufacture an analytic certificate. -/
example (initialized one : Bool) :
    ¬ IdealGeometry.Analytic (geometry initialized one) { parameters with initK1 := 0 } := by
  intro h
  have hc := h.initRoute
  exact Nat.not_lt_zero _ hc

noncomputable def budget (initialized one : Bool) : ℝ≥0∞ :=
  (geometry initialized one).cfg.exposureSum
    (IdealGeometry.classBudget (geometry initialized one) parameters)

def run (initialized one : Bool) : Adaptive.AdaptiveRun 3 :=
  ApiAdaptive.run codec (geometry initialized one).cfg (geometry initialized one).shapes online
    (syncSchedule (geometry initialized one).cfg) [] frames
    (ApiLegal.adapt (geometry initialized one).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geometry initialized one).cfg) (choose _ _ _))

def observe (initialized one : Bool) (tape : IdealKey.Tape) : Fin 2 → Fin 3 → Nat :=
  Adaptive.transcript (geometry initialized one).cfg (geometry initialized one).shapes online
    (syncSchedule (geometry initialized one).cfg) (run initialized one) 2
    (words tape) (dummy tape)

noncomputable def simulator (initialized one : Bool) : Measure (Fin 2 → Fin 3 → Nat) :=
  simLaw (geometry initialized one).cfg
    (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape frames))
      (syncSchedule (geometry initialized one).cfg))
    (Adaptive.shapePattern (ApiAdaptive.shape frames)) 2 3

theorem online_matches (initialized one : Bool) :
    online.unitEntries * online.unitsPerPrefix =
      (geometry initialized one).cfg.carryPositions 1 := by
  cases initialized <;> rfl

theorem schedule_valid (initialized one : Bool) :
    SchedulePremises (geometry initialized one).cfg
      (syncSchedule (geometry initialized one).cfg) 2 3 :=
  SyncScheduleLemmas.syncSchedule_premises _
    (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
    (by change 0 < 128; decide +kernel) _

theorem live (initialized one : Bool)
    (t : ApiLegal.Prefix (geometry initialized one).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geometry initialized one).cfg) 3 2) :
    ApiCapacity.LiveCapacity (geometry initialized one).keyCapacity (Api.stateOf codec []) []
      ((ApiAdaptive.requestGroups
        (ApiLegal.adapt (geometry initialized one).cfg (ApiAdaptive.shape frames)
          (syncSchedule (geometry initialized one).cfg) (choose _ _ _))
        (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap Group.lanes) := by
  have hm : ApiCapacity.LiveCapacity 0 (Api.stateOf codec []) []
      ((ApiAdaptive.requestGroups
        (ApiLegal.adapt (geometry initialized one).cfg (ApiAdaptive.shape frames)
          (syncSchedule (geometry initialized one).cfg) (choose _ _ _))
        (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap Group.lanes) :=
    ApiMissCapacity [_, _]
  exact ⟨hm.1, fun k hk => (hm.2 k hk).trans (Nat.zero_le _)⟩

/-- The same adaptive empty/long-key run receives correctness, exact simulation
and capacity conclusions, even at zero live capacity and outside the inventory. -/
theorem api (initialized one : Bool) :
    (∀ tape, let qs := (ApiAdaptive.requestGroups
        (ApiLegal.adapt (geometry initialized one).cfg (ApiAdaptive.shape frames)
          (syncSchedule (geometry initialized one).cfg) (choose _ _ _))
        (Adaptive.rowsOf (observe initialized one tape) 2) frames).flatMap Group.lanes
      ApiRunCorrect (geometry initialized one) codec online
        (Adaptive.realized (geometry initialized one).cfg (geometry initialized one).shapes online
          (syncSchedule (geometry initialized one).cfg) (run initialized one)
          (words tape) (dummy tape))
        (syncSchedule (geometry initialized one).cfg) qs) ∧
    Measurable (observe initialized one) ∧
    IdealKey.tapeLaw.map (observe initialized one) = simulator initialized one ∧
    IdealKey.tapeLaw {tape | Fails (geometry initialized one).cfg (geometry initialized one).shapes
      (trace (geometry initialized one).cfg (geometry initialized one).shapes online
        (syncSchedule (geometry initialized one).cfg) (run initialized one) tape) (words tape)} ≤
      budget initialized one := by
  obtain ⟨hs, hv, hc, ha, _⟩ := certificates initialized one
  exact IdealGeometryApi (geometry initialized one) parameters hs hv hc ha _ le_rfl
    codec online (syncSchedule (geometry initialized one).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized one) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel) (schedule_valid initialized one) (live initialized one)

/-- Observation transfer charges the explicit analytic budget on the actual
nonstandard reference run, without conditioning it on successful execution. -/
example (initialized one : Bool) (event : Set Nat) (hevent : MeasurableSet event) :
    IdealKey.tapeLaw ((fun tape => observe initialized one tape 0 0) ⁻¹' event) ≤
      (simulator initialized one).map (fun t => t 0 0) event + budget initialized one ∧
    (simulator initialized one).map (fun t => t 0 0) event ≤
      IdealKey.tapeLaw ((fun tape => observe initialized one tape 0 0) ⁻¹' event) +
        budget initialized one := by
  obtain ⟨hs, hv, hc, ha, _⟩ := certificates initialized one
  have hm := (measurable_pi_apply (0 : Fin 3)).comp
    ((measurable_pi_apply (0 : Fin 2)).comp (api initialized one).2.1)
  exact IdealGeometryOblivious (geometry initialized one) parameters hs hv hc ha _ le_rfl
    codec online (syncSchedule (geometry initialized one).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized one) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel) (schedule_valid initialized one) (live initialized one)
    Nat (fun tape => observe initialized one tape 0 0) (fun (t : Fin 2 → Fin 3 → Nat) => t 0 0)
    hm (by fun_prop) (fun _ _ => rfl) event hevent

/-- A capacity-one client chooses arbitrarily long keys using a private seed
with unbounded positive-mass support. No common finite dictionary is supplied. -/
theorem seeded_churn (initialized : Bool) :
    (IdealSeedTests.coins.prod IdealKey.tapeLaw)
      (ApiSeed.failure codec (geometry initialized true).cfg (geometry initialized true).shapes
        online (syncSchedule (geometry initialized true).cfg) (fun _ : Nat => []) 3 1
        IdealCapacitySeedTests.batches (IdealCapacitySeedTests.choose initialized)) ≤
      budget initialized true := by
  obtain ⟨hs, hv, hc, ha, _⟩ := certificates initialized true
  exact IdealGeometrySeedCapacity Nat IdealSeedTests.coins (geometry initialized true)
    parameters hs hv hc ha _ le_rfl codec online (syncSchedule (geometry initialized true).cfg)
    (fun _ : Nat => []) 3 1 IdealCapacitySeedTests.batches (IdealCapacitySeedTests.choose initialized)
    (fun _ => by simp [ApiCapacity.InitialStateValid]) (online_matches initialized true)
    (by decide +kernel) (by change 2 ≤ 2 ^ 32; decide +kernel)
    (schedule_valid initialized true)
    (fun seed _ => by
      change ApiCapacity.LiveCapacity 1 (Api.stateOf codec []) []
        [⟨IdealSeedTests.key seed, .write seed⟩, ⟨IdealSeedTests.key seed, .erase⟩]
      exact ApiChurnCapacity [IdealSeedTests.key seed] seed)

example (dictionary : Finset LogicalKey) :
    ∃ seed, (IdealCapacitySeedTests.choose true seed 0 0 (fun t => Fin.elim0 t) 0).1 ∉ dictionary ∧
      0 < IdealSeedTests.coins {seed} := IdealSeedTests.no_dictionary dictionary

/-- The explicit base-window certificate scales to three windows while the
execution uses that longer horizon. This checks the window adapter outside the
family inventory as well as the direct declared-horizon endpoint. -/
theorem three_windows (initialized : Bool) :
    let geo := (geometry initialized false).chunk 3
    let a := ApiAdaptive.run codec geo.cfg geo.shapes online (syncSchedule geo.cfg) [] frames
      (ApiLegal.adapt geo.cfg (ApiAdaptive.shape frames) (syncSchedule geo.cfg) (choose _ _ _))
    IdealKey.tapeLaw {tape | Fails geo.cfg geo.shapes
      (trace geo.cfg geo.shapes online (syncSchedule geo.cfg) a tape) (words tape)} ≤
      (3 : ℝ≥0∞) * budget initialized false := by
  obtain ⟨hs, hv, hc, ha, hw⟩ := certificates initialized false
  apply IdealGeometryWindows (geometry initialized false) parameters hs hv hc ha hw
    _ le_rfl 3 (by decide +kernel) codec online _ [] 3 64 batches (choose _ _ _)
  · simp [ApiCapacity.InitialStateValid]
  · cases initialized <;> rfl
  · decide +kernel
  · change 2 ≤ 3 * 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · intro t
    exact ApiMissCapacity [_, _]

end IdealGeometryTests
