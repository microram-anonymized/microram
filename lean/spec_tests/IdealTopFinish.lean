import RebuildBound.Proofs.IdealTopFinish
import spec_tests.IdealTopPrep

/-! Canonical top-finish regressions: fitting-input failure after an earlier
reference overflow, current-family sensitivity, exact finite restrictions,
and both legal adaptive public endpoints. The small custom zero-tier fixture
is nonstandard and claims no certified numerical budget. -/
namespace IdealTopFinishTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def cfg : Config := HierarchyInitializationTest.cfg
def prep : TPGeom := ⟨64, 2, 1, 1, 1, 0, 2, false⟩
def initial : TPGeom := { prep with drainPages := 0 }
def top : TopGeom := ⟨64, 1, 1, 0, 2, false, 1, 0, 0, 0⟩
def sh : Shapes :=
  { (hierarchyShapesWith cfg [] top prep initial) with
    direct := fun d => ⟨0, d, d, 0, 0, 0, 0, 0, 0, .direct⟩ }
def key (n : Nat) : LogicalKey :=
  if n = 0 then [] else if n = 65 then List.replicate 65 0
    else [⟨n % 256, Nat.mod_lt _ (by decide +kernel)⟩]
def records : List Rec := (List.range 66).map fun n => ⟨key n, n, false⟩
def tr : Trace := ⟨fun _ => [], records, fun _ => false⟩
def zero : LogicalKey → Nat := fun _ => 0
def spread : LogicalKey → Nat := fun key => (key.headD 0).val % 4
/-- The seeded old family remains zero; only the new top family changes. -/
def wds (current : LogicalKey → Nat) : Words := fun level ordinal =>
  if (level, ordinal) = (cfg.levels, cfg.seed cfg.levels + 1) then current else zero

def input (current : LogicalKey → Nat) : TopInputs :=
  finishInputs (prepOutput cfg sh tr (wds current) 2
    (initOutput cfg sh tr (wds current))) ⟨List.replicate 2 (Bucket.empty 64), []⟩

example : initResult cfg sh tr (wds zero) = .error .drain := by decide +kernel
example : (initOutput cfg sh tr (wds zero)).records.length = 66 := by decide +kernel
example : (input zero).aAll.length = 66 ∧
    [] ∈ ((input zero).aAll.map Rec.key) ∧
    List.replicate 65 0 ∈ ((input zero).aAll.map Rec.key) := by decide +kernel
theorem valid_fit : top.Valid ∧ TopTiersFit top (input zero) := by decide +kernel
example : TopShape top (fun _ => false) zero (input zero) := by
  constructor <;> decide +kernel
theorem finish_verdicts : topJob top (fun _ => false) zero (input zero) = .error .drain ∧
    (topJob top (fun _ => false) spread (input spread)).toBool = true := by
  decide +kernel

/-- The compact input is exactly the first finish after initialization. -/
theorem input_actual (current : LogicalKey → Nat) (hc : current = zero ∨ current = spread) :
    finishInputsAt cfg sh tr (wds current) 2 = input current := by
  unfold finishInputsAt
  rw [HierarchyCoveringProof.table_base (Or.inr (Or.inr (by decide +kernel)))]
  change finishInputs (prepOutput cfg sh tr (wds current) 2
    (initOutput cfg sh tr (wds current))) _ = input current
  suffices h : carryOf cfg sh tr (wds current) cfg.levels 2 =
      ⟨List.replicate 2 (Bucket.empty 64), []⟩ by rw [h]; rfl
  unfold carryOf
  change table cfg sh tr (wds current) 1 4 = _
  rw [HierarchyLocalityProof.table_eq]
  change step cfg sh tr (wds current) 1 4
    (table cfg sh tr (wds current) 1 3) DirectJob.emptyOutput = _
  rw [HierarchyLocalityProof.table_eq]
  change step cfg sh tr (wds current) 1 4
    (step cfg sh tr (wds current) 1 3
      (table cfg sh tr (wds current) 1 2) DirectJob.emptyOutput) DirectJob.emptyOutput = _
  rw [HierarchyCoveringProof.table_base (Or.inr (Or.inr (by decide +kernel)))]
  rcases hc with rfl | rfl <;> decide +kernel

end IdealTopFinishTests

namespace IdealTopFinishApiTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open ApiStructuralTests (geo online batches frames)
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open IdealTopPrepApiTests (run ordinal)

/-- Actual adaptive misses at zero capacity instantiate the analytic finish
endpoint from either start. The modeled top prefix may extend beyond this short run. -/
example (initialized : Bool) :
    IdealKey.tapeLaw {tape |
      TopTiersFit (geo initialized).top (finishInputsAt (geo initialized).cfg
        (geo initialized).shapes (trace (geo initialized).cfg (geo initialized).shapes
          online (syncSchedule (geo initialized).cfg) (run initialized) tape)
        (words tape) (ordinal initialized)) ∧
      (finishResult (geo initialized).cfg (geo initialized).shapes
        (trace (geo initialized).cfg (geo initialized).shapes online
          (syncSchedule (geo initialized).cfg) (run initialized) tape)
        (words tape) (ordinal initialized)).toBool = false} ≤
      ENNReal.ofReal (topFinishBound (geo initialized).top.C (geo initialized).top.SR
        (geo initialized).top.rho (geo initialized).top.I (geo initialized).top.T
        (min (geo initialized).top.SMerge (geo initialized).top.STier) 576 576 32) := by
  apply IdealTopFinish (geo initialized) (ApiStructuralTests.structural initialized)
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
  · cases initialized <;> decide +kernel
  · cases initialized <;> decide +kernel
  · apply (HierarchyTopLawProof.mem_potential_finish _ _).mpr
    cases initialized <;> decide +kernel

end IdealTopFinishApiTests

namespace IdealTopFinishFamilyTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.Online MeasureTheory IdealHierarchy IdealDirect
open ApiTests (codec)
open IdealSepUnionTests (member member_valid geo online online_matches)
open ApiStructuralTests (batches)
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open IdealTopPrepFamilyTests (frames choose run ordinal)

/-- Both certified starts admit a legal adaptive client whose first key is empty
and whose next byte key is longer than 64 bytes and depends on an earlier bucket. -/
example (initialized : Bool) :
    IdealKey.tapeLaw {tape | JobFailsFirst (geo initialized).cfg (geo initialized).shapes
      (trace (geo initialized).cfg (geo initialized).shapes online
        (syncSchedule (geo initialized).cfg) (run initialized) tape)
      (words tape) (.topFinish (ordinal initialized))} ≤
        ENNReal.ofReal (topFinishBound (geo initialized).top.C (geo initialized).top.SR
        (geo initialized).top.rho (geo initialized).top.I (geo initialized).top.T
        (min (geo initialized).top.SMerge (geo initialized).top.STier) 576 576 32) := by
  apply IdealTopFinishFirstFailure initialized member member_valid 1 codec online
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
  · apply (HierarchyTopLawProof.mem_potential_finish _ _).mpr
    cases initialized <;> decide +kernel

end IdealTopFinishFamilyTests

namespace IdealTopFinishTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def sample : IdealKey.Tape := fun _ => 0

theorem sample_words : IdealHierarchy.words sample = wds zero := by
  funext level ordinal key
  simp only [IdealHierarchy.words, sample, wds]
  split <;> rfl

def failureEvent (tape : IdealKey.Tape) : Prop :=
  TopTiersFit top (finishInputsAt cfg sh tr (IdealHierarchy.words tape) 2) ∧
    jobFails cfg sh tr (IdealHierarchy.words tape) (.topFinish 2) = true

theorem sample_failure : failureEvent sample := by
  change TopTiersFit top (finishInputsAt cfg sh tr (IdealHierarchy.words sample) 2) ∧
    Bool.not (topJob top (fun _ => false) (jobWord cfg (IdealHierarchy.words sample) cfg.levels 2)
      (finishInputsAt cfg sh tr (IdealHierarchy.words sample) 2)).toBool = true
  rw [sample_words, input_actual zero (Or.inl rfl)]
  change TopTiersFit top (input zero) ∧
    Bool.not (topJob top (fun _ => false) zero (input zero)).toBool = true
  constructor
  · exact valid_fit.2
  · exact congrArg (fun result : Except Test Output => !result.toBool) finish_verdicts.1

theorem fixed_inputs_finiteRead (config : Config) (shapes : Shapes) (trace : Trace)
    (ordinal : Nat) : IdealKey.FiniteRead (fun tape =>
      finishInputsAt config shapes trace (IdealHierarchy.words tape) ordinal) := by
  have hp : IdealKey.FiniteRead (fun tape =>
      prepOutput config shapes trace (IdealHierarchy.words tape) ordinal
        (table config shapes trace (IdealHierarchy.words tape) config.levels (ordinal - 1))) :=
    (IdealMeasurableProof.table_finiteRead config shapes trace config.levels (ordinal - 1)).bind _
      (fun previous => (IdealFailureProof.tp_reference config config.levels ordinal shapes.prep trace.unsh
        (prepInputs previous)).comp TPRun.output)
  exact (hp.pair (IdealMeasurableProof.table_finiteRead config shapes trace (config.levels - 1)
    (ordinal * config.fanout (config.levels - 1)))).comp fun p => finishInputs p.1 p.2

theorem fixed_failure_finiteRead (config : Config) (shapes : Shapes) (trace : Trace)
    (ordinal : Nat) : IdealKey.FiniteRead (fun tape =>
      TopTiersFit shapes.top (finishInputsAt config shapes trace (IdealHierarchy.words tape) ordinal) ∧
        jobFails config shapes trace (IdealHierarchy.words tape) (.topFinish ordinal) = true) :=
  (((fixed_inputs_finiteRead config shapes trace ordinal).comp (fun inp => TopTiersFit shapes.top inp)).pair
    (IdealJobFailureFiniteRead config shapes trace (.topFinish ordinal))).comp
      (fun p => p.1 ∧ p.2 = true)

theorem failure_finiteRead : IdealKey.FiniteRead failureEvent :=
  fixed_failure_finiteRead cfg sh tr 2

theorem finiteRead_positive (event : IdealKey.Tape → Prop) (hf : IdealKey.FiniteRead event)
    (point : IdealKey.Tape) (hpoint : event point) :
    0 < IdealKey.tapeLaw {tape | event tape} := by
  obtain ⟨coordinates, hcoordinates⟩ := hf point
  have hpositive : 0 < IdealKey.tapeLaw
      (coordinates.restrict ⁻¹' {coordinates.restrict point}) := by
    rw [← Measure.map_apply (Finset.measurable_restrict coordinates)
      (measurableSet_singleton _), (IdealKeyRestriction coordinates).2]
    exact pos_iff_ne_zero.mpr (by simp [uniformOn_eq_zero_iff Set.finite_univ])
  apply hpositive.trans_le
  apply measure_mono
  intro tape htape
  have heq : event tape = event point :=
    hcoordinates tape (fun c hc => congrFun htape ⟨c, hc⟩)
  exact heq.mpr hpoint

/-- The actual fitting-input finish failure has positive canonical probability,
even though initialization already failed on its unconditional reference path. -/
theorem finish_failure_positive :
    0 < IdealKey.tapeLaw {tape | failureEvent tape} :=
  finiteRead_positive failureEvent failure_finiteRead sample sample_failure

end IdealTopFinishTests

namespace IdealTopFinishRestrictionTests
open RebuildBound RebuildBound.Spec RebuildBound.Model MeasureTheory
open IdealHierarchy IdealDirect
open scoped ENNReal

/-- Empty populations and source restrictions still give a normalized coupling. -/
example (row : TopGeom) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : familyBlock (2, 2) => IdealKey.wordLaw))
      (IdealTopFinishProof.law row ∅ ∅ ∅ (fun _ => ⟨[], [], [], []⟩)).toFinite
      (IdealTopFinishProof.read (2, 2) ∅ ∅) :=
  IdealTopFinishProof.coupling (2, 2) row ∅ ∅ ∅ (fun _ => ⟨[], [], [], []⟩)

def sourceKeys : Finset LogicalKey := {[], [0], List.replicate 65 0}
def a : Rec := ⟨List.replicate 65 0, 1, false⟩
def b : Rec := ⟨List.replicate 65 0, 2, true⟩
def RA : Finset Rec := {a}
def RB : Finset Rec := {b}
def keys : Finset LogicalKey := RA.image Rec.key ∪ RB.image Rec.key

/-- A tombstone in B and its older live A copy share exactly one fresh key word. -/
example : keys.card = 1 ∧ liveSet RA RB = ∅ := by decide +kernel

example (fresh : familyBlock (2, 2) → Word64) :
    ((IdealTopFinishProof.read (2, 2) sourceKeys keys fresh).2
      ⟨a.key, by simp [keys, RA, a]⟩).val = familyWords (2, 2) fresh b.key := rfl

/-- Earlier source keys no longer in either finish population stay in the finite
history, including the distinction between empty and one-zero-byte keys. -/
example (fresh : familyBlock (2, 2) → Word64) (w : LogicalKey → Nat) :
    IdealTopFinishProof.extend sourceKeys keys
      (IdealTopFinishProof.read (2, 2) sourceKeys keys fresh).1 w [] =
        familyWords (2, 2) fresh [] ∧
    IdealTopFinishProof.extend sourceKeys keys
      (IdealTopFinishProof.read (2, 2) sourceKeys keys fresh).1 w [0] =
        familyWords (2, 2) fresh [0] := by
  constructor <;>
    simp [IdealTopFinishProof.extend, IdealTopFinishProof.read, sourceKeys, keys,
      RA, RB, a, b, familyWords]

/-- Overlap of A and B does not duplicate a random coordinate. Extra source
coordinates are sampled independently of the single input key. -/
example (row : TopGeom) (producer : (LogicalKey → Nat) → TopInputs) :
    FiniteCoupling
      (Measure.infinitePi (fun _ : familyBlock (2, 2) => IdealKey.wordLaw))
      (IdealTopFinishProof.law row sourceKeys RA RB producer).toFinite
      (IdealTopFinishProof.read (2, 2) sourceKeys keys) :=
  IdealTopFinishProof.coupling (2, 2) row sourceKeys RA RB producer

end IdealTopFinishRestrictionTests
