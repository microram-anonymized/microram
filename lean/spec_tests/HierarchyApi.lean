import RebuildBound.Proofs.HierarchyApi
import RebuildBound.Proofs.AdaptiveFoundMem
import spec_tests.AdaptiveSemantics
import spec_tests.ApiCorrectness

/-! Non-vacuous API/flag regression outside the numerical family. A duplicate-key
chunk erases an absent key, writes it, reads it, erases it and reads the tombstone.
Both starts are exercised, including empty plans and plans with the empty top.
The unshadowed promise is derived from API construction, never supplied. -/

namespace HierarchyApiTest
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.Adaptive RebuildBound.Model.Api
open AdaptiveSemanticsTest (geometry structural online)
open ApiTests (codec live tomb)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def requests : List Request :=
  [⟨LogicalKey.ofNat (0), .erase⟩, ⟨LogicalKey.ofNat (0), .write 10⟩, ⟨LogicalKey.ofNat (0), .read⟩, ⟨LogicalKey.ofNat (0), .erase⟩, ⟨LogicalKey.ofNat (0), .read⟩]
def records : List Rec := [tomb 0 true, live 0 10, live 0 10, tomb 0 false, tomb 0 false]
def run : OnlineBatch.BatchRun := ⟨[.batch records], [], fun r => codec.flag r.val⟩
def U : Finset LogicalKey := {LogicalKey.ofNat 0}
def words : Words := fun _ _ _ => 0
def dummy : Nat → Nat → Nat := fun _ _ => 0

def schedule (initialized omitTop : Bool) : Schedule :=
  if initialized || !omitTop then syncSchedule (geometry initialized).cfg else fun _ => ⟨0, []⟩

theorem sched (initialized omitTop : Bool) :
    SchedulePremises (geometry initialized).cfg (schedule initialized omitTop) 5 2 := by
  have sync := SyncScheduleLemmas.syncSchedule_premises (geometry initialized).cfg
    (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
    (by change 0 < 128; decide +kernel) 5
  cases initialized <;> cases omitTop
  · exact sync
  · constructor
    · intro j _; simp [schedule, geometry, Config.seed, pos]
    · intro j _; simp [schedule]
    · intro j _ c hc; simp [schedule] at hc
    · intro j _; simp [schedule]
    · intro j _; rfl
  · exact sync
  · exact sync

theorem trace (initialized : Bool) :
    UniverseTracePremises (geometry initialized).cfg U (OnlineBatch.traceOf online run) := by
  apply RequesterTrace _ U online run rfl (by decide +kernel)
  · intro s hs
    simp [run, records, OnlineBatch.slots, OnlineBatch.Op.lanes] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · decide +kernel
  · simp [run]

/-- The first selection is absent without assuming lookup or flag soundness. -/
theorem first_found (initialized omitTop : Bool) :
    (Probe.batch (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) words dummy 0).found = none := by
  cases hf : (Probe.batch (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) words dummy 0).found with
  | none => rfl
  | some f =>
    have hm := AdaptiveFoundMemProof.foundMemFor (geometry initialized)
      (AdaptiveSemanticsTest.low initialized) online run (schedule initialized omitTop) 2
      rfl (by decide +kernel) (AdaptiveFoundMemProof.tracePremises_of_universe (trace initialized))
      (sched initialized omitTop) words dummy 0 ⟨0, 0, tomb 0 true, true⟩ f rfl hf
    simpa [run] using hm.2

theorem implementation (initialized omitTop : Bool) :
    Implements codec (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) words dummy requests := by
  constructor
  · rfl
  · intro t q s hq hs
    have ht : t < 5 := by simpa [requests] using (List.getElem?_eq_some_iff.mp hq).1
    interval_cases t <;>
      simp [requests, run, records, OnlineBatch.slots, OnlineBatch.Op.lanes] at hq hs <;>
      subst q <;> subst s
    · rw [first_found]; decide +kernel
    all_goals cases initialized <;> cases omitTop <;> decide +kernel

theorem setting (initialized omitTop : Bool) :
    UniverseBatchSetting (geometry initialized) U online run (schedule initialized omitTop) 5 2 := by
  apply HierarchyApiAdmissible _ (structural initialized) U online run _ 2 codec words dummy requests
  · intro _; rfl
  · intro k hk
    simp only [U, Finset.mem_singleton] at hk
    subst k
    decide +kernel
  · change 1 ≤ 1024; decide +kernel
  · rfl
  · decide +kernel
  · change 5 ≤ 2 ^ 32; decide +kernel
  · decide +kernel
  · simp [run]
  · intro q hq; simp [requests] at hq; rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · exact sched initialized omitTop
  · intro r; rfl
  · exact implementation initialized omitTop

/-- The first erase is flagged; the erased formerly live value is not. -/
example : run.unsh (records[0]!) = true ∧ run.unsh (records[3]!) = false := by decide +kernel
example : (schedule false true 0).tables = [] ∧
    (schedule false false 0).tables = [(2, 0)] := by decide +kernel

/-- All-prefix maps, returned values and addresses follow without a promise premise. -/
example (initialized omitTop : Bool) :
    ApiCorrect codec (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) words dummy requests :=
  HierarchyBatchApiCorrectness _ (structural initialized) U online run _ 2
    (setting initialized omitTop) (fun _ => rfl) codec words dummy requests
    (implementation initialized omitTop)

/-- The full selected record is independent of arbitrary routing and dummy words. -/
example (initialized omitTop : Bool) (w w' : Words) (d d' : Nat → Nat → Nat) (t : Nat) (ht : t < 5) :
    (Probe.batch (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) w d t).found =
    (Probe.batch (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) w' d' t).found :=
  HierarchyBatchFound _ (structural initialized) U online run _ 5 2
    (setting initialized omitTop) w w' d d' t ht

/-- A concrete adaptive client, using the same flagged duplicate-key chunk. -/
def adaptive : AdaptiveRun 2 :=
  ⟨[.chunk 5], [], fun r => codec.flag r.val, fun _ i => records[i % 5]!⟩

theorem replay_eq (t : Fin 5 → Fin 2 → Nat) : replay adaptive t = run := by
  rfl

theorem adaptive_setting (initialized omitTop : Bool) :
    AdaptiveSetting (geometry initialized) U online adaptive (schedule initialized omitTop) 5 := by
  apply HierarchyAdaptiveFlagAdmissible _ (structural initialized)
  · intro _; rfl
  · intro k hk
    simp only [U, Finset.mem_singleton] at hk
    subst k
    decide +kernel
  · change 1 ≤ 1024; decide +kernel
  · rfl
  · decide +kernel
  · change 5 ≤ 2 ^ 32; decide +kernel
  · decide +kernel
  · simp [adaptive]
  · intro rows i
    change (records[i % 5]!).key ∈ U
    have hi := Nat.mod_lt i (by decide +kernel : 0 < 5)
    generalize hj : i % 5 = j at *
    interval_cases j <;> decide +kernel
  · exact sched initialized omitTop
  · intro t
    change FlagRule (geometry initialized).cfg (geometry initialized).shapes online run
      (schedule initialized omitTop) words
    exact ApiFlagRule codec _ _ online run _ words dummy requests (fun _ => rfl)
      (implementation initialized omitTop)

/-- The realized run satisfies API semantics; the branch promise is derived above. -/
example (initialized omitTop : Bool) :
    let geo := geometry initialized
    let actual := realized geo.cfg geo.shapes online (schedule initialized omitTop) adaptive words dummy
    ApiCorrect codec geo.cfg geo.shapes online actual (schedule initialized omitTop) words dummy requests := by
  apply HierarchyAdaptiveApiCorrectness _ (structural initialized) U online 2 adaptive
    (schedule initialized omitTop) 5 (adaptive_setting initialized omitTop) (fun _ => rfl)
  change Implements codec (geometry initialized).cfg (geometry initialized).shapes online run
    (schedule initialized omitTop) words dummy requests
  exact implementation initialized omitTop

end HierarchyApiTest
