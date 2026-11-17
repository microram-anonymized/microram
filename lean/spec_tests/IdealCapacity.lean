import RebuildBound.Proofs.IdealCapacity
import RebuildBound.Proofs.IdealOblivious
import spec_tests.IdealTopFinish
import spec_tests.ApiSeed

/-! Whole-hierarchy canonical capacity applies to adaptive miss keys and
capacity-one churn under independent geometric seeds. The standard family
geometry and both starts are instantiated; no local failure law is supplied. -/
namespace IdealCapacityTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open IdealTopPrepFamilyTests (frames choose run)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- A first empty key and a subsequent observation-dependent key longer than
64 bytes satisfy the complete hierarchy bound from either start. -/
theorem both_starts (initialized : Bool) :
    IdealKey.tapeLaw {tape | Fails (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape) (words tape)} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have h := IdealCapacity initialized member member_valid 1 (by decide +kernel)
    codec online (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (fun t => by
      have hm : ApiCapacity.LiveCapacity 0 (Api.stateOf codec []) []
          ((ApiAdaptive.requestGroups
            (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
              (syncSchedule (geo initialized).cfg) (choose _ _ _))
            (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap Group.lanes) :=
        ApiMissCapacity [_, _]
      exact ⟨hm.1, fun k hk => (hm.2 k hk).trans (Nat.zero_le _)⟩)
  simpa only [geo, run, frames, Nat.cast_one, one_mul] using h

end IdealCapacityTests

namespace IdealCapacitySeedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi
open MeasureTheory IdealHierarchy
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def batches := ApiSeedTests.batches

def choose (initialized : Bool) (seed : Nat) : ApiLegal.Chooser (geo initialized).cfg
    (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))
    (syncSchedule (geo initialized).cfg) 3 :=
  fun _ _ _ _ => (IdealSeedTests.key seed, seed)

theorem requests (initialized : Bool) (seed : Nat) (rows : List (Fin 3 → Nat)) :
    (ApiAdaptive.requestGroups (ApiLegal.adapt (geo initialized).cfg
      (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))
      (syncSchedule (geo initialized).cfg) (choose initialized seed)) rows
      (ApiAdaptive.frames 1 online.unitEntries batches)).flatMap Group.lanes =
      [⟨IdealSeedTests.key seed, .write seed⟩,
       ⟨IdealSeedTests.key seed, .erase⟩] := rfl

/-- Every lane prefix has at most one live entry even though the seed's
positive-mass support includes keys of every length from 65 onward. -/
theorem churn_capacity (initialized : Bool) :
    (IdealSeedTests.coins.prod IdealKey.tapeLaw)
      (ApiSeed.failure codec (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 3 1 batches
        (choose initialized)) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have h := IdealSeedCapacity Nat IdealSeedTests.coins initialized member member_valid 1
    (by decide +kernel) codec online (syncSchedule (geo initialized).cfg) (fun _ : Nat => [])
    3 1 batches (choose initialized)
    (fun _ => by simp [ApiCapacity.InitialStateValid])
    (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (fun seed _ => by
      change ApiCapacity.LiveCapacity (geo initialized).keyCapacity (Api.stateOf codec []) []
        [⟨IdealSeedTests.key seed, .write seed⟩, ⟨IdealSeedTests.key seed, .erase⟩]
      have hc := ApiChurnCapacity [IdealSeedTests.key seed] seed
      exact ⟨hc.1, fun k hk => (hc.2 k hk).trans
        (by cases initialized <;> decide +kernel)⟩)
  simpa only [geo, Nat.cast_one, one_mul] using h

/-- Changing the seed changes the first actual request's key, and no finite
set contains those keys on every positive-probability seed slice. -/
example (dictionary : Finset LogicalKey) :
    ∃ seed, (choose true seed 0 0 (fun t => Fin.elim0 t) 0).1 ∉ dictionary ∧
      0 < IdealSeedTests.coins {seed} := IdealSeedTests.no_dictionary dictionary

/-- The initial map can also depend on an unbounded-support seed. With no
requested lanes, the whole-hierarchy event still includes initialization. -/
theorem seeded_initialization :
    let init := fun seed => [(⟨IdealSeedTests.key seed, codec.pack seed false, false⟩ : Rec)]
    let S := syncSchedule (geo true).cfg
    let select : Nat → ApiLegal.Chooser (geo true).cfg [] S 3 := fun _ _ _ _ _ => ([], 0)
    (IdealSeedTests.coins.prod IdealKey.tapeLaw)
      (ApiSeed.failure codec (geo true).cfg (geo true).shapes online S init 3 1 [] select) ≤
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  dsimp only
  have hi (seed : Nat) : ApiCapacity.InitialStateValid (geo true).keyCapacity true
      [(⟨IdealSeedTests.key seed, codec.pack seed false, false⟩ : Rec)] := by
    simp [ApiCapacity.InitialStateValid]
    decide +kernel
  have h := IdealSeedCapacity Nat IdealSeedTests.coins true member member_valid 1
    (by decide +kernel) codec online (syncSchedule (geo true).cfg)
    (fun seed => [(⟨IdealSeedTests.key seed, codec.pack seed false, false⟩ : Rec)])
    3 1 [] (fun _ _ _ _ _ => ([], 0)) hi (online_matches true)
    (by decide +kernel) (by decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (fun seed _ => (ApiInitialCapacity _ true _ (hi seed) codec).2)
  convert h using 1 <;> first | rfl | norm_num

end IdealCapacitySeedTests

namespace IdealCapacityObservationTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open IdealTopPrepFamilyTests (frames choose run)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def observe (initialized : Bool) (tape : IdealKey.Tape) : Fin 2 → Fin 3 → Nat :=
  Adaptive.transcript (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (run initialized) 2 (words tape) (dummy tape)

noncomputable def simulator (initialized : Bool) : Measure (Fin 2 → Fin 3 → Nat) :=
  simLaw (geo initialized).cfg
    (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape frames))
      (syncSchedule (geo initialized).cfg))
    (Adaptive.shapePattern (ApiAdaptive.shape frames)) 2 3

theorem schedule_valid (initialized : Bool) :
    SchedulePremises (geo initialized).cfg (syncSchedule (geo initialized).cfg) 2 3 :=
  SyncScheduleLemmas.syncSchedule_premises _
    (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
    (by change 0 < 128; decide +kernel) _

theorem live (initialized : Bool)
    (t : ApiLegal.Prefix (geo initialized).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geo initialized).cfg) 3 2) :
    ApiCapacity.LiveCapacity (geo initialized).keyCapacity (Api.stateOf codec []) []
      ((ApiAdaptive.requestGroups
        (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
          (syncSchedule (geo initialized).cfg) (choose _ _ _))
        (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap Group.lanes) := by
  have hm : ApiCapacity.LiveCapacity 0 (Api.stateOf codec []) []
      ((ApiAdaptive.requestGroups
        (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
          (syncSchedule (geo initialized).cfg) (choose _ _ _))
        (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap Group.lanes) :=
    ApiMissCapacity [_, _]
  exact ⟨hm.1, fun k hk => (hm.2 k hk).trans (Nat.zero_le _)⟩

/-- The combined endpoint supplies exact simulation and capacity on one
concrete adaptive execution; deterministic correctness is its first conclusion. -/
theorem family_components (initialized : Bool) :
    Measurable (observe initialized) ∧
    IdealKey.tapeLaw.map (observe initialized) = simulator initialized ∧
    IdealKey.tapeLaw {tape | Fails (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape) (words tape)} ≤
      ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have h := IdealApiFamily initialized member member_valid 1 (by decide +kernel)
    codec online (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel) (schedule_valid initialized) (live initialized)
  convert h.2 using 1 <;> norm_num <;> rfl

/-- A measurable encoding of the actual probe transcript inherits the stated
simulator error. Here the observation is the first active bucket itself. -/
example (initialized : Bool) (event : Set Nat) (hevent : MeasurableSet event) :
    IdealKey.tapeLaw ((fun tape => observe initialized tape 0 0) ⁻¹' event) ≤
      (simulator initialized).map (fun t => t 0 0) event +
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64) ∧
    (simulator initialized).map (fun t => t 0 0) event ≤
      IdealKey.tapeLaw ((fun tape => observe initialized tape 0 0) ⁻¹' event) +
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  have hm := (measurable_pi_apply (0 : Fin 3)).comp
    ((measurable_pi_apply (0 : Fin 2)).comp (family_components initialized).1)
  have h := IdealApiOblivious initialized member member_valid 1 (by decide +kernel)
    codec online (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
    (by simp [ApiCapacity.InitialStateValid]) (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel) (schedule_valid initialized) (live initialized)
    Nat (fun tape => observe initialized tape 0 0) (fun (t : Fin 2 → Fin 3 → Nat) => t 0 0) hm
    (by fun_prop) (fun _ _ => rfl) event hevent
  convert h using 1 <;> norm_num <;> rfl

end IdealCapacityObservationTests

namespace IdealCapacitySeedTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online RebuildBound.Model.PublicApi MeasureTheory IdealHierarchy
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The observation-transfer endpoint also accepts the real seeded churn
execution with its unbounded-support key choices. -/
example (initialized : Bool) (event : Set (Fin (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))) → Fin 3 → Nat)) (hevent : MeasurableSet event) :
    let reference := ApiSeed.transcript codec (geo initialized).cfg (geo initialized).shapes online
      (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 3 1 batches (choose initialized)
    let fs := ApiAdaptive.frames 1 online.unitEntries batches
    let simulator := simLaw (geo initialized).cfg
      (OnlineBatch.slotSchedule (Adaptive.shapeWidths (ApiAdaptive.shape fs))
        (syncSchedule (geo initialized).cfg))
      (Adaptive.shapePattern (ApiAdaptive.shape fs))
      (Adaptive.slotCount (ApiAdaptive.shape fs)) 3
    (IdealSeedTests.coins.prod IdealKey.tapeLaw) (Function.uncurry reference ⁻¹' event) ≤
      simulator.map id event + ENNReal.ofReal (1 / (2 : ℝ) ^ 64) ∧
    simulator.map id event ≤
      (IdealSeedTests.coins.prod IdealKey.tapeLaw) (Function.uncurry reference ⁻¹' event) +
        ENNReal.ofReal (1 / (2 : ℝ) ^ 64) := by
  let reference := ApiSeed.transcript codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) (fun _ : Nat => []) 3 1 batches (choose initialized)
  have hm : Measurable (Function.uncurry reference) := ApiSeedMeasurable Nat codec
    (geo initialized).cfg (geo initialized).shapes online (syncSchedule (geo initialized).cfg)
    (fun _ : Nat => []) 3 1 batches (choose initialized)
  have h := IdealSeedOblivious Nat IdealSeedTests.coins initialized member member_valid 1
    (by decide +kernel) codec online (syncSchedule (geo initialized).cfg) (fun _ : Nat => [])
    3 1 batches (choose initialized)
    (fun _ => by simp [ApiCapacity.InitialStateValid])
    (online_matches initialized) (by decide +kernel)
    (by change 2 ≤ 2 ^ 32; decide +kernel)
    (SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _)
    (fun seed _ => by
      change ApiCapacity.LiveCapacity (geo initialized).keyCapacity (Api.stateOf codec []) []
        [⟨IdealSeedTests.key seed, .write seed⟩, ⟨IdealSeedTests.key seed, .erase⟩]
      have hc := ApiChurnCapacity [IdealSeedTests.key seed] seed
      exact ⟨hc.1, fun k hk => (hc.2 k hk).trans
        (by cases initialized <;> decide +kernel)⟩)
    (Fin (Adaptive.slotCount (ApiAdaptive.shape (ApiAdaptive.frames 1 online.unitEntries batches))) → Fin 3 → Nat) (Function.uncurry reference) id hm measurable_id
    (fun _ _ => rfl) event hevent
  convert h using 1 <;> norm_num <;> rfl

end IdealCapacitySeedTests
