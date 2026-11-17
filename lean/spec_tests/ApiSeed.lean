import RebuildBound.Proofs.ApiSeed
import spec_tests.IdealSeed
import spec_tests.ApiStructural

/-! A fixed public API shape with capacity-one churn and keys of unbounded
byte length under an independent seed with positive mass at every natural. -/
namespace ApiSeedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealKey
open ApiTests (codec)
open ApiStructuralTests (online)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def geo (initialized : Bool) : HierarchyGeometry :=
  { AdaptiveSemanticsTest.geometry initialized with keyCapacity := 1 }

theorem structural (initialized : Bool) : (geo initialized).Structural := by
  cases initialized <;> decide +kernel

def batches : List ApiAdaptive.Batch :=
  [⟨false, [⟨.write, true, false⟩, ⟨.erase, true, false⟩]⟩]

def choose (initialized : Bool) (seed : Nat) :
    ApiLegal.Chooser (geo initialized).cfg
      (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))
      (syncSchedule (geo initialized).cfg) 2 :=
  fun _ _ _ _ => (IdealSeedTests.key seed, seed)

def run (initialized : Bool) (seed : Nat) :=
  ApiSeed.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized) seed

def observe (initialized : Bool) :=
  ApiSeed.transcript codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized)

theorem requests (initialized : Bool) (seed : Nat) (rows : List (Fin 2 → Nat)) :
    (ApiAdaptive.requestGroups (ApiLegal.adapt (geo initialized).cfg
      (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))
      (syncSchedule (geo initialized).cfg) (choose initialized seed)) rows
      (ApiAdaptive.frames 1 online.unitEntries batches)).flatMap Group.lanes =
      [⟨IdealSeedTests.key seed, .write seed⟩,
       ⟨IdealSeedTests.key seed, .erase⟩] := rfl

/-- One public batch splits into two chunks, retaining the same seed choice
and public decision point. Capacity is checked at both lane prefixes. -/
theorem churn (initialized : Bool) (seed : Nat) (tape : Tape) :
    let S := syncSchedule (geo initialized).cfg
    let realized := Adaptive.realized (geo initialized).cfg (geo initialized).shapes
      online S (run initialized seed) (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)
    ApiRunCorrect (geo initialized) codec online realized S
      [⟨IdealSeedTests.key seed, .write seed⟩,
       ⟨IdealSeedTests.key seed, .erase⟩] ∧
      ApiTopPopulations (geo initialized) online realized := by
  have h := ApiSeedLive Nat (geo initialized) (structural initialized) codec online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized)
    (fun _ => by simp [ApiCapacity.InitialStateValid]) rfl (by decide)
    (by change 2 ≤ 2 ^ 32; decide)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide) (by change 0 < 128; decide) _)
    (fun s _ => by
      rw [requests]
      exact ApiChurnCapacity [IdealSeedTests.key s] s) seed tape
  dsimp only at h
  rw [requests] at h
  exact ⟨h.1, h.2.1⟩

example (initialized : Bool) : Measurable (Function.uncurry (observe initialized)) :=
  ApiSeedMeasurable Nat codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized)

/-- Both the transcript and actual capacity-failure event are measurable under
the independent geometric seed, including all arbitrarily long-key slices. -/
example (initialized : Bool) : MeasurableSet
    (ApiSeed.failure codec (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized)) :=
  (ApiSeedFailure Nat IdealSeedTests.coins codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 2 1 batches (choose initialized)).1

/-- Initialization can also depend on seeds with no common finite dictionary.
The empty public request shape preserves each seed's singleton initial map. -/
theorem initialized (seed : Nat) (tape : Tape) :
    let init := fun s => [(⟨IdealSeedTests.key s, codec.pack s false, false⟩ : Rec)]
    let cfg := (geo true).cfg
    let S := syncSchedule cfg
    let choose : Nat → ApiLegal.Chooser cfg [] S 2 := fun _ _ _ _ _ => ([], 0)
    let a := ApiSeed.run codec cfg (geo true).shapes online S init 2 1 [] choose seed
    ApiTopPopulations (geo true) online (Adaptive.realized cfg (geo true).shapes online S a
      (IdealHierarchy.words tape) (IdealHierarchy.dummy tape)) := by
  dsimp only
  have hi (s : Nat) : ApiCapacity.InitialStateValid 1 true
      [(⟨IdealSeedTests.key s, codec.pack s false, false⟩ : Rec)] := by
    simp [ApiCapacity.InitialStateValid, ApiTests.live]
  exact (ApiSeedLive Nat (geo true) (structural true) codec online
    (syncSchedule (geo true).cfg) (fun s => [(⟨IdealSeedTests.key s, codec.pack s false, false⟩ : Rec)])
    2 1 [] (fun _ _ _ _ _ => ([], 0)) hi rfl (by decide) (by decide)
    (SyncScheduleLemmas.syncSchedule_premises _ (by decide) (by decide) _)
    (fun s _ => (ApiInitialCapacity 1 true _ (hi s) codec).2) seed tape).2.1

end ApiSeedTests
