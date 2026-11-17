import RebuildBound.Proofs.IdealProbe
import spec_tests.ApiSeed

/-! Exact probes need no live-capacity premise. These regressions use active
initialized-top probes, new keys computed from actual earlier bucket reads,
and independent seeds whose byte lengths have unbounded support. -/
namespace IdealProbeTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy
open ApiTests (codec)
open ApiStructuralTests (geo online)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Both writes probe, and each public batch has its own decision point. -/
def batches : List ApiAdaptive.Batch :=
  [⟨false, [⟨.write, true, false⟩]⟩, ⟨false, [⟨.write, true, false⟩]⟩]

def frames := ApiAdaptive.frames 64 online.unitEntries batches

def choose (initialized : Bool) : ApiLegal.Chooser (geo initialized).cfg
    (ApiAdaptive.shape frames) (syncSchedule (geo initialized).cfg) 2 :=
  fun batch count rows _ =>
    (if batch = 0 then [] else
      List.replicate (65 + if h : 0 < count then (rows ⟨0, h⟩ 0).val else 0) 0, 7)

def run (initialized : Bool) :=
  ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) [] frames
    (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geo initialized).cfg) (choose initialized))

def observe (initialized : Bool) (tape : IdealKey.Tape) : Fin 2 → Fin 2 → Nat :=
  Adaptive.transcript (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (run initialized) 2 (words tape) (dummy tape)

/-- The actual first observed bucket changes, and the second actual operation
introduces the corresponding fresh long byte key. The second entry is inactive. -/
example : observe true (fun _ => 0) 0 0 = 0 ∧
    observe true (fun _ => 1) 0 0 = 1 ∧
    observe true (fun _ => 1) 0 1 = 0 ∧
    (OnlineBatch.slots (Adaptive.realized (geo true).cfg (geo true).shapes online
      (syncSchedule (geo true).cfg) (run true) (words (fun _ => 0)) (dummy (fun _ => 0)))).map
        (fun s => s.record.key) = [[], List.replicate 65 0] ∧
    (OnlineBatch.slots (Adaptive.realized (geo true).cfg (geo true).shapes online
      (syncSchedule (geo true).cfg) (run true) (words (fun _ => 1)) (dummy (fun _ => 1)))).map
        (fun s => s.record.key) = [[], List.replicate 66 0] := by
  decide +kernel

/-- The exact law applies although the first insertion already violates the
geometry's declared zero live capacity. This does not claim a capacity bound. -/
theorem exact_without_live_capacity (initialized : Bool) :
    Measurable (observe initialized) ∧ IdealKey.tapeLaw.map (observe initialized) =
      simLaw (geo initialized).cfg
        (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape frames))
          (syncSchedule (geo initialized).cfg))
        (Adaptive.shapePattern (ApiAdaptive.shape frames)) 2 2 := by
  apply IdealApiExact (geo initialized) (ApiStructuralTests.structural initialized)
    codec online (syncSchedule (geo initialized).cfg) [] 2 64 batches (choose initialized)
  · intro _; rfl
  · simp
  · simp
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _

example : ¬ ApiCapacity.LiveCapacity (geo true).keyCapacity (Api.stateOf codec []) []
    [⟨[], .write 7⟩, ⟨List.replicate 65 0, .write 7⟩] := by
  intro h
  have hp := h.2 1 (by decide +kernel)
  change 1 ≤ 0 at hp
  omega

/-- Empty and nonempty byte strings really are different logical identities. -/
example : ([] : LogicalKey) ≠ List.replicate 65 0 ∧
    (List.replicate 65 0 : LogicalKey) ≠ List.replicate 66 0 := by decide +kernel

end IdealProbeTests

namespace IdealProbeSeedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online MeasureTheory
open ApiTests (codec)
open ApiStructuralTests (online)
open ApiSeedTests (geo batches choose observe)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The actual write/erase API transcript is independent of the private
geometric seed, even though that seed chooses an arbitrarily long key. -/
theorem joint_exact (initialized : Bool) :
    let fs := ApiAdaptive.frames 1 online.unitEntries batches
    let simulator := simLaw (geo initialized).cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs))
        (syncSchedule (geo initialized).cfg))
      (Adaptive.shapePattern (ApiAdaptive.shape fs)) 2 2
    Measurable (Function.uncurry (observe initialized)) ∧
    (IdealSeedTests.coins.prod IdealKey.tapeLaw).map
      (fun p => (p.1, observe initialized p.1 p.2)) = IdealSeedTests.coins.prod simulator ∧
    (IdealSeedTests.coins.prod IdealKey.tapeLaw).map
      (Function.uncurry (observe initialized)) = simulator := by
  apply IdealApiSeedExact Nat IdealSeedTests.coins (geo initialized)
    (ApiSeedTests.structural initialized) codec online (syncSchedule (geo initialized).cfg)
    (fun _ : Nat => []) 2 1 batches (choose initialized)
  · intro _ _; rfl
  · intro _; simp
  · intro _; simp
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _

/-- There is no finite dictionary covering the keys chosen with positive
probability by this very client, not merely an unrelated seed read. -/
example (dictionary : Finset LogicalKey) :
    ∃ seed, (choose true seed 0 0 (fun t => Fin.elim0 t) 0).1 ∉ dictionary ∧
      0 < IdealSeedTests.coins {seed} := IdealSeedTests.no_dictionary dictionary

end IdealProbeSeedTests

namespace IdealProbeOverflowTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online MeasureTheory IdealHierarchy
open ApiTests (codec)
open ApiStructuralTests (geo online)

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- 129 distinct byte keys fit the declared initialization shape's load. -/
def initial : List Rec := (List.range 129).map fun n =>
  ⟨List.replicate n 0, codec.pack n false, false⟩

theorem initial_unique : (initial.map Rec.key).Nodup := by
  unfold initial
  rw [List.map_map]
  change ((List.range 129).map (fun n => (List.replicate n 0 : LogicalKey))).Nodup
  apply List.Nodup.map _ List.nodup_range
  intro a b hab
  have := congrArg List.length hab
  simpa only [List.length_replicate] using this

def trace : Trace := ⟨fun _ => [], initial, fun _ => false⟩

/-- Colliding all homes forces a real reference failure; its fallback still
retains every record. Exact simulation below does not exclude this tape. -/
example : (initResult (geo true).cfg (geo true).shapes trace (words (fun _ => 0))).toBool = false ∧
    (initOutput (geo true).cfg (geo true).shapes trace (words (fun _ => 0))).records.length = 129 := by
  decide +kernel

def batches : List ApiAdaptive.Batch := [⟨false, [⟨.read, true, false⟩]⟩]
def frames := ApiAdaptive.frames 64 online.unitEntries batches
def choose : ApiLegal.Chooser (geo true).cfg (ApiAdaptive.shape frames)
    (syncSchedule (geo true).cfg) 2 := fun _ _ _ _ => ([], 0)
def run := ApiAdaptive.run codec (geo true).cfg (geo true).shapes online
  (syncSchedule (geo true).cfg) initial frames
  (ApiLegal.adapt (geo true).cfg (ApiAdaptive.shape frames) (syncSchedule (geo true).cfg) choose)

example : IdealKey.tapeLaw.map (fun tape => Adaptive.transcript (geo true).cfg (geo true).shapes
      online (syncSchedule (geo true).cfg) run 1 (words tape) (dummy tape)) =
    simLaw (geo true).cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape frames))
        (syncSchedule (geo true).cfg))
      (Adaptive.shapePattern (ApiAdaptive.shape frames)) 1 2 := by
  exact (IdealApiExact (geo true) (ApiStructuralTests.structural true)
    codec online (syncSchedule (geo true).cfg) initial 2 64 batches choose
    (by decide +kernel) initial_unique (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)).2

end IdealProbeOverflowTests
