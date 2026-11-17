import RebuildBound.Proofs.NativeError
import spec_tests.IdealCapacity

/-! The stop term is necessary even with no capacity/encoding/collision errors.
Canonical family capacity bounds plug directly into the same composition. -/
namespace NativeErrorTests
open RebuildBound RebuildBound.Spec NativeError MeasureTheory
open scoped ENNReal

def zeroBudget : Budget := ⟨0, 0, 0, 0, 0, 0⟩
def stopBudget : Budget := { zeroBudget with stopped := 1 }
def stopEvents : Events Unit := ⟨∅, ∅, ∅, Set.univ, ∅⟩

example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    stopEvents.BoundedBy μ stopBudget := by
  simp [Events.BoundedBy, stopEvents, stopBudget, zeroBudget]

/-- Certain refusal cannot be assigned a zero bad-event budget. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    ¬ stopEvents.BoundedBy μ zeroBudget := by
  simp [Events.BoundedBy, stopEvents, zeroBudget]

/-- Omitting stop would assert a false zero failure bound in this experiment. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    ¬ μ (Set.univ : Set Unit) ≤ zeroBudget.total := by
  simp [Budget.total, Budget.ideal, zeroBudget]

/-- Recording refusal as true distinguishes it perfectly from an always
completed reference. Ignoring the stop bit would hide this discrepancy. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    μ ((fun _ : Unit => true) ⁻¹' ({true} : Set Bool)) = 1 ∧
      μ ((fun _ : Unit => false) ⁻¹' ({true} : Set Bool)) = 0 := by
  simp

example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    μ (Set.univ : Set Unit) ≤ min 1 stopBudget.total := by
  apply NativeFailureBound μ μ stopEvents stopBudget Set.univ Set.univ
  · simp [Events.BoundedBy, stopEvents, stopBudget, zeroBudget]
  · simp [Events.bad, stopEvents]
  · simp [stopBudget, zeroBudget]

/-- A bound larger than one is clipped, including infinite allowances. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] :
    μ (Set.univ : Set Unit) ≤ min 1 ({ stopBudget with crypto := ⊤ } : Budget).total := by
  simp [Budget.total, Budget.ideal, stopBudget, zeroBudget]

/-- For public views, a certain stop may change every observation. The same
eventwise theorem handles this without conditioning on successful completion. -/
example {Ω View : Type} [MeasurableSpace Ω] [MeasurableSpace View]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (native simulator : Measure View) [IsProbabilityMeasure native]
    [IsProbabilityMeasure simulator] (reference observed : Ω → View)
    (href : Measurable reference) (hlaw : μ.map reference = simulator)
    (event : Set View) (hevent : MeasurableSet event)
    (hhybrid : native event = μ (observed ⁻¹' event)) :
    native event ≤ min 1 (simulator event + stopBudget.total) ∧
      simulator event ≤ min 1 (native event + stopBudget.total) := by
  apply NativeObservationBound μ native simulator reference observed
    ⟨∅, ∅, ∅, Set.univ, ∅⟩ stopBudget href hlaw
  · simp [Events.BoundedBy, stopBudget, zeroBudget]
  · simp [Events.bad]
  · exact hevent
  · simp [stopBudget, zeroBudget, hhybrid]

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online
open IdealHierarchy IdealDirect
open IdealSepUnionTests (geo online)
open IdealTopPrepFamilyTests (run)

def capacityEvents (initialized : Bool) : Events IdealKey.Tape :=
  ⟨∅, ∅, ∅, ∅, {tape | Fails (geo initialized).cfg (geo initialized).shapes
    (trace (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) (run initialized) tape) (words tape)}⟩

noncomputable def capacityBudget : Budget :=
  { zeroBudget with capacity := ENNReal.ofReal (1 / (2 : ℝ) ^ 64) }

theorem capacity_bounds (initialized : Bool) :
    (capacityEvents initialized).BoundedBy IdealKey.tapeLaw capacityBudget := by
  refine ⟨by simp [capacityEvents, capacityBudget, zeroBudget],
    by simp [capacityEvents, capacityBudget, zeroBudget],
    by simp [capacityEvents, capacityBudget, zeroBudget],
    by simp [capacityEvents, capacityBudget, zeroBudget], ?_⟩
  exact IdealCapacityTests.both_starts initialized

/-- The actual canonical family theorem, from either start, supplies the
capacity term directly. No run-wide key universe or conditional tape is added. -/
theorem canonical_transfer (initialized : Bool)
    {Native : Type} [MeasurableSpace Native] (native : Measure Native)
    [IsProbabilityMeasure native] (bad : Set Native) (idealBad : Set IdealKey.Tape)
    (hsub : idealBad ⊆ (capacityEvents initialized).bad)
    (hhybrid : native bad ≤ IdealKey.tapeLaw idealBad) :
    native bad ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have ht := NativeFailureBound IdealKey.tapeLaw native (capacityEvents initialized)
    capacityBudget idealBad bad (capacity_bounds initialized) hsub
    (by simpa [capacityBudget, zeroBudget] using hhybrid)
  exact (le_trans ht (min_le_right _ _)).trans_eq
    (by simp [Budget.total, Budget.ideal, capacityBudget, zeroBudget])

open IdealCapacityObservationTests (observe simulator family_components)

/-- Arbitrary agreeing adapters use the actual canonical transcript law, with
a separate tested-event hybrid. Both starts and adaptive byte keys are covered. -/
example (initialized : Bool)
    (native : Measure (Fin 2 → Fin 3 → Nat)) [IsProbabilityMeasure native]
    (observed : IdealKey.Tape → Fin 2 → Fin 3 → Nat)
    (hagree : ∀ tape, tape ∉ (capacityEvents initialized).bad →
      observed tape = observe initialized tape)
    (event : Set (Fin 2 → Fin 3 → Nat)) (hevent : MeasurableSet event)
    (δ : ℝ≥0∞)
    (hhybrid : native event ≤ IdealKey.tapeLaw (observed ⁻¹' event) + δ ∧
      IdealKey.tapeLaw (observed ⁻¹' event) ≤ native event + δ) :
    native event ≤ min 1 (simulator initialized event + (capacityBudget.ideal + δ)) ∧
      simulator initialized event ≤ min 1 (native event + (capacityBudget.ideal + δ)) := by
  have hp := family_components initialized
  have : IsProbabilityMeasure (simulator initialized) := by rw [← hp.2.1]; infer_instance
  exact NativeObservationBound IdealKey.tapeLaw native (simulator initialized)
    (observe initialized) observed (capacityEvents initialized)
    { capacityBudget with crypto := δ } hp.1 hp.2.1
    (capacity_bounds initialized) hagree event hevent hhybrid

/-- The identical failure endpoint accepts the independent-seed churn bound;
there is no separate seeded native model or common key dictionary. -/
example (initialized : Bool)
    {Native : Type} [MeasurableSpace Native] (native : Measure Native)
    [IsProbabilityMeasure native] (bad : Set Native)
    (hhybrid : native bad ≤ (IdealSeedTests.coins.prod IdealKey.tapeLaw)
      (ApiSeed.failure ApiTests.codec (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 3 1
        IdealCapacitySeedTests.batches (IdealCapacitySeedTests.choose initialized))) :
    native bad ≤ min 1 capacityBudget.total := by
  let failure := ApiSeed.failure ApiTests.codec (geo initialized).cfg (geo initialized).shapes
    online (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 3 1
    IdealCapacitySeedTests.batches (IdealCapacitySeedTests.choose initialized)
  apply NativeFailureBound (IdealSeedTests.coins.prod IdealKey.tapeLaw) native
    ⟨∅, ∅, ∅, ∅, failure⟩ capacityBudget failure bad
  · refine ⟨by simp [capacityBudget, zeroBudget], by simp [capacityBudget, zeroBudget],
      by simp [capacityBudget, zeroBudget], by simp [capacityBudget, zeroBudget], ?_⟩
    exact IdealCapacitySeedTests.churn_capacity initialized
  · simp [Events.bad]
  · simpa [capacityBudget, zeroBudget] using hhybrid

end NativeErrorTests
