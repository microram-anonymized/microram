import RebuildBound.Proofs.IdealTopPrep
import spec_tests.HierarchyInitialization
import spec_tests.ApiLegal
import spec_tests.IdealSepUnion

/-! Top-preparation regressions: legal adaptive clients in both starts,
positive-probability failure after reference overflow, two-family sensitivity,
and exact finite old-source restrictions. -/

namespace IdealTopPrepTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy

def cfg : Config := HierarchyInitializationTest.cfg
def prep : TPGeom := ⟨2, 3, 0, 3, 3, 0, 3, false⟩
def initial : TPGeom := ⟨2, 3, 4, 3, 1, 0, 3, false⟩
def sh : Shapes := hierarchyShapesWith cfg [] selectedTop prep initial

def records : List Rec :=
  ([0, 1, 2, 3, 4, 5, 65] : List Nat).map fun n => ⟨List.replicate n 0, n, false⟩
def tr : Trace := ⟨fun _ => [], records, fun _ => false⟩
def zero : LogicalKey → Nat := fun _ => 0
def grouped : LogicalKey → Nat := fun key => key.length % 2
def spread : LogicalKey → Nat := fun key => key.length % 8
def wds (old current : LogicalKey → Nat) : Words := fun level ordinal =>
  if (level, ordinal) = (cfg.levels, cfg.seed cfg.levels) then old else current

def input (old : LogicalKey → Nat) : TPInputs :=
  prepInputs (initOutput cfg sh tr (wds old zero))

/-- This is the actual hierarchy input at the first preparation after the seed. -/
theorem input_actual (old current : LogicalKey → Nat) :
    prepInputsAt cfg sh tr (wds old current) (cfg.seed cfg.levels + 1) = input old := by
  unfold prepInputsAt
  rw [HierarchyCoveringProof.table_base (Or.inr (Or.inr (by omega)))]
  change prepInputs (initOutput cfg sh tr (wds old current)) = input old
  rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The old initialization really fails, while its reference publication keeps
all seven records. Its live keys include the empty string and a 65-byte key. -/
example : initResult cfg sh tr (wds grouped zero) = .error .drain := by
  decide +kernel
example : (input grouped).aAll.length = 7 ∧
    [] ∈ ((input grouped).aAll.map Rec.key) ∧
    List.replicate 65 0 ∈ ((input grouped).aAll.map Rec.key) := by
  decide +kernel

/-- Failure continuation retains the preparation shape and fits the declared
old-tier slot; the failing consumer event is therefore not excluded by fit. -/
example : TPShape prep (fun key => grouped key % prep.T) (input grouped) := by
  constructor <;> decide +kernel
example : prep.Valid ∧ TPTiersFit prep (input grouped) ∧ TPTiersFit prep (input zero) := by
  constructor
  · decide +kernel
  · unfold TPTiersFit
    decide +kernel

/-- Both families matter. Resampling only the old family changes main layout
and removes the stash failure; resampling only the current family also removes it.
This zero-stash geometry is a continuation witness, not a certified small budget. -/
example : (input grouped).aMain ≠ (input zero).aMain ∧
    tpJob engineRule prep (fun _ => false) zero (input grouped) = .error (.stash 0) ∧
    (tpJob engineRule prep (fun _ => false) zero (input zero)).toBool = true ∧
    (tpJob engineRule prep (fun _ => false) spread (input grouped)).toBool = true := by
  decide +kernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A canonical tape whose old family groups records in two homes and whose
new family is zero. All other routing and dummy coordinates are irrelevant. -/
def sample : IdealKey.Tape := fun coordinate =>
  match coordinate with
  | .inl (family, key) =>
      if family = (cfg.levels, cfg.seed cfg.levels) then
        ⟨grouped key, by
          have h := Nat.mod_lt key.length (by decide +kernel : 0 < 2)
          change key.length % 2 < 2 ^ 64
          omega⟩
      else 0
  | .inr _ => 0

theorem sample_words : IdealHierarchy.words sample = wds grouped zero := by
  funext level ordinal key
  simp only [IdealHierarchy.words, sample, wds]
  split <;> rfl

/-- The fitting-input failure occupies a positive finite cylinder, so the
example is not merely one exceptional infinite tape of measure zero. -/
theorem preparation_failure_positive :
    0 < IdealKey.tapeLaw {tape |
      TPTiersFit prep (prepInputsAt cfg sh tr (IdealHierarchy.words tape) 2) ∧
        jobFails cfg sh tr (IdealHierarchy.words tape) (.topPrepare 2) = true} := by
  have hin : IdealKey.FiniteRead (fun tape =>
      prepInputsAt cfg sh tr (IdealHierarchy.words tape) 2) :=
    (IdealMeasurableProof.table_finiteRead cfg sh tr cfg.levels 1).comp prepInputs
  have hf := ((hin.comp (fun inp => TPTiersFit prep inp)).pair
    (IdealJobFailureFiniteRead cfg sh tr (.topPrepare 2))).comp
      (fun p => p.1 ∧ p.2 = true)
  obtain ⟨coordinates, hcoordinates⟩ := hf sample
  have hpositive : 0 < IdealKey.tapeLaw
      (coordinates.restrict ⁻¹' {coordinates.restrict sample}) := by
    rw [← Measure.map_apply (Finset.measurable_restrict coordinates)
      (measurableSet_singleton _), (IdealKeyRestriction coordinates).2]
    exact pos_iff_ne_zero.mpr (by simp [uniformOn_eq_zero_iff Set.finite_univ])
  apply hpositive.trans_le
  apply measure_mono
  intro tape htape
  have heq := hcoordinates tape (fun c hc => congrFun htape ⟨c, hc⟩)
  change (TPTiersFit prep (prepInputsAt cfg sh tr (IdealHierarchy.words tape) 2) ∧
      jobFails cfg sh tr (IdealHierarchy.words tape) (.topPrepare 2) = true) = _ at heq
  change TPTiersFit prep (prepInputsAt cfg sh tr (IdealHierarchy.words tape) 2) ∧
    jobFails cfg sh tr (IdealHierarchy.words tape) (.topPrepare 2) = true
  rw [heq]
  dsimp only
  rw [sample_words]
  change TPTiersFit prep (prepInputsAt cfg sh tr (wds grouped zero) (cfg.seed cfg.levels + 1)) ∧
    jobFails cfg sh tr (wds grouped zero) (.topPrepare (cfg.seed cfg.levels + 1)) = true
  simp only [jobFails, prepResult, input_actual]
  unfold TPTiersFit
  decide +kernel

end IdealTopPrepTests

namespace IdealTopPrepRestrictionTests
open RebuildBound RebuildBound.Spec RebuildBound.Model MeasureTheory
open IdealDirectAProof (freshBlock oldWords currentWords)
open scoped ENNReal

/-- Empty source and A restrictions remain a normalized finite coupling. -/
example (row : TPGeom) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : freshBlock (2, 1) (2, 2) => IdealKey.wordLaw))
      (IdealTopPrepProof.law row ∅ ∅ (fun _ => ⟨[], []⟩)).toFinite
      (IdealTopPrepProof.read (2, 1) (2, 2) ∅ ∅) :=
  IdealTopPrepProof.coupling (2, 1) (2, 2) (by decide +kernel)
    row ∅ ∅ (fun _ => ⟨[], []⟩)

/-- Source keys not surviving in A still belong to the old history. -/
def sourceKeys : Finset LogicalKey := {[], List.replicate 65 0}
def aKeys : Finset LogicalKey := {List.replicate 65 0}

example (fresh : freshBlock (2, 1) (2, 2) → Word64) :
    IdealTopPrepProof.oldWord sourceKeys aKeys
        (IdealTopPrepProof.read (2, 1) (2, 2) sourceKeys aKeys fresh).1 [] =
      oldWords (2, 1) (2, 2) fresh [] := by
  simp [IdealTopPrepProof.oldWord, sourceKeys, aKeys, IdealTopPrepProof.read, oldWords]

/-- The same long key has independent old and current coordinate reads. -/
example (fresh : freshBlock (2, 1) (2, 2) → Word64)
    (key : aKeys) :
    IdealTopPrepProof.oldWord sourceKeys aKeys
        (IdealTopPrepProof.read (2, 1) (2, 2) sourceKeys aKeys fresh).1 key =
      oldWords (2, 1) (2, 2) fresh key ∧
    ((IdealTopPrepProof.read (2, 1) (2, 2) sourceKeys aKeys fresh).2 key).val =
      currentWords (2, 1) (2, 2) fresh key := by
  constructor
  · simp only [IdealTopPrepProof.oldWord, dite_eq_left key.property]
    rfl
  · rfl

/-- The unused old-source coordinate does not change the exact binary-home
marginal, even when all 64 bits become home bits. -/
example (target : aKeys → Fin (2 ^ 64)) :
    (∑ _hist ∈ Finset.univ.filter (fun hist : IdealTopPrepProof.Hist sourceKeys aKeys =>
        ∀ key : aKeys, (hist.1 key).val % 2 ^ 64 = (target key).val),
      (Fintype.card (IdealTopPrepProof.Hist sourceKeys aKeys) : ℝ≥0∞)⁻¹) =
      ((2 ^ 64 : ℝ≥0∞) ^ aKeys.card)⁻¹ :=
  IdealTopPrepProof.density_bits sourceKeys aKeys 64 (by decide +kernel) target

end IdealTopPrepRestrictionTests

namespace IdealTopPrepApiTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open ApiStructuralTests (geo online batches frames)
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def run (initialized : Bool) : Adaptive.AdaptiveRun 2 :=
  ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) [] frames
    (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geo initialized).cfg)
      (ApiLegalTests.choose (geo initialized).cfg (ApiAdaptive.shape frames)
        (syncSchedule (geo initialized).cfg)))
def ordinal (initialized : Bool) : Nat :=
  (geo initialized).cfg.seed (geo initialized).cfg.levels + 1

/-- Actual adaptive misses at zero capacity instantiate the analytic preparation
endpoint from either start. The modeled top prefix may extend beyond this short run. -/
example (initialized : Bool) :
    IdealKey.tapeLaw {tape |
      TPTiersFit (geo initialized).prep (prepInputsAt (geo initialized).cfg
        (geo initialized).shapes (trace (geo initialized).cfg (geo initialized).shapes
          online (syncSchedule (geo initialized).cfg) (run initialized) tape)
        (words tape) (ordinal initialized)) ∧
      (prepResult (geo initialized).cfg (geo initialized).shapes
        (trace (geo initialized).cfg (geo initialized).shapes online
          (syncSchedule (geo initialized).cfg) (run initialized) tape)
        (words tape) (ordinal initialized)).toBool = false} ≤
      tpBound (geo initialized).prep 32 1 576 576 := by
  apply IdealTopPreparation (geo initialized) (ApiStructuralTests.structural initialized)
    codec online (syncSchedule (geo initialized).cfg) [] 2 64 batches
    (ApiLegalTests.choose _ _ _)
  · simp [ApiCapacity.InitialStateValid]
  · rfl
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · intro t
    exact ApiMissCapacity [_, _]
  · cases initialized <;> decide +kernel
  · intro _
    cases initialized <;> decide +kernel
  · cases initialized <;> decide +kernel
  · cases initialized <;> decide +kernel
  · apply (HierarchyTopLawProof.mem_potential_prepare _ _).mpr
    cases initialized <;> decide +kernel

end IdealTopPrepApiTests

namespace IdealTopPrepFamilyTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def frames := ApiAdaptive.frames 64 online.unitEntries batches

def choose (cfg : Config) (shape : List Adaptive.Kind) (S : Schedule) :
    ApiLegal.Chooser cfg shape S 3 := fun batch count rows _ =>
  (if batch = 0 then [] else
    List.replicate (65 + if h : 0 < count then (rows ⟨0, h⟩ 0).val else 0) 0, 0)

def run (initialized : Bool) : Adaptive.AdaptiveRun 3 :=
  ApiAdaptive.run codec (geo initialized).cfg (geo initialized).shapes online
    (syncSchedule (geo initialized).cfg) [] frames
    (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
      (syncSchedule (geo initialized).cfg)
      (choose (geo initialized).cfg (ApiAdaptive.shape frames)
        (syncSchedule (geo initialized).cfg)))
def ordinal (initialized : Bool) : Nat :=
  (geo initialized).cfg.seed (geo initialized).cfg.levels + 1

/-- Both certified starts admit a legal adaptive client whose first key is empty
and whose next byte key is longer than 64 bytes and depends on an earlier bucket. -/
example (initialized : Bool) :
    IdealKey.tapeLaw {tape | JobFailsFirst (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape)
      (words tape) (.topPrepare (ordinal initialized))} ≤
        tpBound (geo initialized).prep 32 1 576 576 := by
  apply IdealTopPreparationFirstFailure initialized member member_valid 1 codec online
    (syncSchedule (geo initialized).cfg) [] 3 64 batches (choose _ _ _)
  · simp [ApiCapacity.InitialStateValid]
  · exact online_matches initialized
  · decide +kernel
  · change 2 ≤ 2 ^ 32
    decide +kernel
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ x ∈ ([2, 8] : List Nat), 0 < x; decide +kernel)
      (by change 0 < 128; decide +kernel) _
  · intro t
    have hm : ApiCapacity.LiveCapacity 0 (Api.stateOf codec []) []
        ((ApiAdaptive.requestGroups
          (ApiLegal.adapt (geo initialized).cfg (ApiAdaptive.shape frames)
            (syncSchedule (geo initialized).cfg) (choose _ _ _))
          (Adaptive.rowsOf (ApiLegal.erase t) 2) frames).flatMap PublicApi.Group.lanes) :=
      ApiMissCapacity [_, _]
    exact ⟨hm.1, fun k hk => (hm.2 k hk).trans (Nat.zero_le _)⟩
  · apply (HierarchyTopLawProof.mem_potential_prepare _ _).mpr
    cases initialized <;> decide +kernel

end IdealTopPrepFamilyTests
