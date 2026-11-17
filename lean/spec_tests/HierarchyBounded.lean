import RebuildBound.Proofs.HierarchyBounded
import spec_tests.HierarchyApi

/-! Bounded transfer outside the numerical family, from both starts. The
five-slot batch exercises duplicate forwarding and tombstones; the adaptive
client changes keys with observed buckets. Corrupted answers, addresses and
histories are rejected by the conclusion, not assumed correct by an adapter. -/

open MeasureTheory

namespace HierarchyBoundedTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.Adaptive
open AdaptiveSemanticsTest (geometry structural online)
open HierarchyApiTest (U run schedule setting words dummy)

def scalarOp : Op := .probe ⟨LogicalKey.ofNat (0), 9, false⟩
def scalarRun : OnlineRun := ⟨[scalarOp], [], fun _ => false⟩

theorem scalar_setting (initialized : Bool) :
    UniverseOnlineSetting (geometry initialized) U online scalarRun
      (syncSchedule (geometry initialized).cfg) 1 2 := by
  have frozen : (stateAt online scalarRun scalarRun.ops.length).frozen = [] := by decide +kernel
  refine ⟨?_, ?_, by decide +kernel, ?_, ?_⟩
  · intro k hk
    simp only [U, Finset.mem_singleton] at hk
    subst k
    decide +kernel
  · change 1 ≤ 1024; decide +kernel
  · refine ⟨⟨rfl, by decide +kernel⟩, by change 1 ≤ 2 ^ 32; decide +kernel, ?_, ?_, ?_⟩
    · intro o ho
      simp only [scalarRun, List.mem_singleton] at ho
      subst o
      decide +kernel
    · exact { nodup := by intro i u hu; simp [traceOf, frozen] at hu
              load := by intro i; simp [traceOf, frozen, DirectMasks.records]
              keys := by intro i x hx; simp [traceOf, frozen, DirectMasks.records] at hx
              initNodup := by simp [traceOf, scalarRun]
              initKeys := by simp [traceOf, scalarRun] }
    · intro w o _ r _ h
      simp [earlyDrop, traceOf, scalarRun] at h
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel) (by change 0 < 128; decide +kernel) 1

/-- A nonempty scalar run supplies all setting and start premises. -/
theorem scalar_reference_bound (initialized : Bool) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : Ω → Words) (d : Ω → Nat → Nat → Nat) :
    let geo := geometry initialized
    let S := syncSchedule geo.cfg
    let actual := fun ω => Probe.scalar geo.cfg geo.shapes online scalarRun S (w ω) (d ω)
    μ {ω | ¬ OnlineResultsCorrect geo online scalarRun S 1 (w ω) (d ω) (actual ω)} ≤
      μ {ω | Fails geo.cfg geo.shapes (traceOf online scalarRun) (w ω)} := by
  exact (HierarchyBoundedOnline _ (structural initialized) U online scalarRun _ 1 2
    (scalar_setting initialized) (fun _ => rfl) μ w d _ (fun _ _ _ _ => rfl)).2

def wrongValue : Nat → Probe.Result := fun _ => ⟨some ⟨LogicalKey.ofNat (0), 999, false⟩, []⟩
def wrongAddress : Nat → Probe.Result := fun _ => ⟨none, [1]⟩

/-- The batch adapter may return arbitrary results on failure. No tape law is
needed to bound any incorrect value/address in the five-slot prefix. -/
theorem batch_bound (initialized omitTop : Bool) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : Ω → Words) (d : Ω → Nat → Nat → Nat) :
    let geo := geometry initialized
    let S := schedule initialized omitTop
    ∀ actual : Ω → Nat → Probe.Result,
      (∀ ω, ¬ Fails geo.cfg geo.shapes (OnlineBatch.traceOf online run) (w ω) →
        ∀ t < 5, actual ω t = Probe.batch geo.cfg geo.shapes online run S (w ω) (d ω) t) →
      μ {ω | ¬ BatchResultsCorrect geo online run S 5 (w ω) (d ω) (actual ω)} ≤
        μ {ω | Fails geo.cfg geo.shapes (OnlineBatch.traceOf online run) (w ω)} := by
  dsimp only
  intro actual hagree
  exact (HierarchyBoundedBatch _ (structural initialized) U online run _ 5 2
    (setting initialized omitTop) (fun _ => rfl) μ w d actual hagree).2

/-- Corrupting a scalar answer is detected. -/
theorem reject_scalar_value (initialized : Bool) :
    ¬ OnlineResultsCorrect (geometry initialized) online scalarRun
      (syncSchedule (geometry initialized).cfg) 1 words dummy wrongValue := by
  intro h
  have hv := (h 0 scalarOp (by decide +kernel) rfl rfl).1
  change some 999 = none at hv
  cases hv

/-- Corrupting a batch answer is detected even on the empty history. -/
theorem reject_batch_value (initialized omitTop : Bool) :
    ¬ BatchResultsCorrect (geometry initialized) online run
      (schedule initialized omitTop) 5 words dummy wrongValue := by
  intro h
  have hv := (h 0 ⟨0, 0, ApiTests.tomb 0 true, true⟩ (by decide +kernel) rfl rfl).1
  change some 999 = none at hv
  cases hv

/-- Correct absence does not excuse a wrong address. -/
theorem reject_address : ¬ BatchResultsCorrect (geometry false) online run
    (schedule false true) 5 words dummy wrongAddress := by
  intro h
  have ha := (h 0 ⟨0, 0, ApiTests.tomb 0 true, true⟩ (by decide +kernel) rfl rfl).2 0
  change 1 = 0 at ha
  omega

def wrongHistory : OnlineBatch.BatchRun := { run with init := [⟨LogicalKey.ofNat (0), 7, false⟩] }

/-- Keeping reference probe results while changing the actual history is
insufficient. Adaptive transfer must also require agreement of the issued run. -/
theorem reject_changed_history (initialized omitTop : Bool) :
    ¬ BatchResultsCorrect (geometry initialized) online wrongHistory
      (schedule initialized omitTop) 5 words dummy
      (Probe.batch (geometry initialized).cfg (geometry initialized).shapes
        online run (schedule initialized omitTop) words dummy) := by
  intro h
  have hv := (h 0 ⟨0, 0, ApiTests.tomb 0 true, true⟩ (by decide +kernel) rfl rfl).1
  rw [HierarchyApiTest.first_found] at hv
  have expected : Probe.latestValue (LogicalKey.ofNat 0) wrongHistory.init = some 7 := by
    decide +kernel
  change none = Probe.latestValue (LogicalKey.ofNat 0) wrongHistory.init at hv
  rw [expected] at hv
  cases hv

/-- This client changes its second key with its first observed bucket. Actual
histories and results can both deviate on failure; agreement is required only
on success. Both starts use the same all-branch setting and fixed universe. -/
theorem adaptive_bound (initialized : Bool) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (w : Ω → Words) (d : Ω → Nat → Nat → Nat) :
    let geo := geometry initialized
    let S := syncSchedule geo.cfg
    let a := AdaptiveSemanticsTest.run
    ∀ (runs : Ω → OnlineBatch.BatchRun) (actual : Ω → Nat → Probe.Result),
      (∀ ω, ¬ AdaptiveFails geo.cfg geo.shapes online S a (w ω) (d ω) →
        runs ω = realized geo.cfg geo.shapes online S a (w ω) (d ω) ∧
        ∀ t < 2, actual ω t = Probe.batch geo.cfg geo.shapes online (runs ω) S (w ω) (d ω) t) →
      μ {ω | ¬ BatchResultsCorrect geo online (runs ω) S 2 (w ω) (d ω) (actual ω)} ≤
        μ {ω | AdaptiveFails geo.cfg geo.shapes online S a (w ω) (d ω)} := by
  dsimp only
  intro runs actual hagree
  exact (HierarchyBoundedAdaptive _ (structural initialized) AdaptiveSemanticsTest.U online 2
    AdaptiveSemanticsTest.run _ 2 (AdaptiveSemanticsTest.setting initialized)
    (fun _ => rfl) μ w d runs actual hagree).2

end HierarchyBoundedTest
