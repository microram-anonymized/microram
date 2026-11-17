import RebuildBound.Proofs.IdealSepUnion
import spec_tests.IdealDirect

/-! The separated current-home bound applies to both starts and to a receiving
family forwarded through a completed carry. Layout changes under resampling
are intentional; only the key populations stay fixed. -/
namespace IdealSepUnionTests
open RebuildBound RebuildBound.Spec RebuildBound.Model RebuildBound.Model.Hierarchy
open RebuildBound.Model.DirectJob MeasureTheory
open scoped ENNReal NNReal

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def member : ConfigurationFamily.Member :=
  ⟨"L3_r2_D8_2.8", 2, [2, 8], [1, 1, 1], [1, 1, 1]⟩

theorem member_valid : member ∈ ConfigurationFamily.members := by
  simp [member, ConfigurationFamily.members]

def geo (initialized : Bool) : HierarchyGeometry := (member.geometry initialized).chunk 1
def online : Online.OnlineGeom := ⟨128, 1⟩

/-- The next batch can introduce long keys computed from an
observed bucket, including a key absent from every preceding batch. -/
def choose : Adaptive.Client 1 := fun rows i =>
  ⟨if rows.isEmpty && i == 0 then []
    else List.replicate (65 + i + (rows.headD fun _ => 0) 0) 0, i, false⟩
def client : Adaptive.AdaptiveRun 1 :=
  ⟨List.replicate 16 (.chunk online.unitEntries), [], fun _ => false, choose⟩
def schedule (initialized : Bool) : Online.Schedule := fun _ =>
  if initialized then ⟨(geo initialized).cfg.seed 1, [(3, 8)]⟩ else ⟨0, []⟩

theorem online_matches (initialized : Bool) :
    online.unitEntries * online.unitsPerPrefix = (geo initialized).cfg.carryPositions 1 := by
  cases initialized <;> rfl

theorem schedule_valid (initialized : Bool) :
    SchedulePremises (geo initialized).cfg (schedule initialized)
      (Adaptive.slotCount client.shape) 1 := by
  cases initialized <;> constructor
  all_goals intro j hj
  all_goals first
    | intro c hc; simp [schedule] at hc; subst c; decide +kernel
    | simp [schedule, geo, member, ConfigurationFamily.Member.geometry,
        ConfigurationFamily.Member.config, HierarchyGeometry.chunk, chunkConfig,
        Config.seed, Config.carryPositions, Config.carry, Config.levels,
        Online.pos, Online.Tiles, Online.window]

example : (choose [] 0).key = [] ∧
    (choose [fun _ => 0] 0).key = List.replicate 65 0 ∧
    (choose [fun _ => 1] 0).key = List.replicate 66 0 := by
  decide +kernel

def digit (forwarded : Bool) : Nat := if forwarded then 8 else 2
def ordinal (initialized forwarded : Bool) : Nat := (geo initialized).cfg.seed 2 + digit forwarded
def row (forwarded : Bool) : SepGeom := (geo false).shapes.sep 2 (digit forwarded)

/-- These are genuine separated jobs, including the completing digit whose
current family is forwarded to the top level. -/
example (initialized : Bool) :
    familyOf (geo initialized).cfg 2 (ordinal initialized true) =
      (3, (geo initialized).cfg.seed 3 + 1) := by
  cases initialized <;> decide +kernel

/-- A small hierarchy isolates the layout change that prevents using a
full-input freshness assertion for separated jobs. -/
def tinyCfg : Config := ⟨[2, 2], 1, 1, 1, 4, false⟩
def tinyDirect (d : Nat) : DirectJob.Geometry :=
  ⟨0, d, d, 0, 0, 0, 0, 0, 0, .direct⟩
def tinySep : SepGeom := ⟨64, 1, 1, 1, 0, 2, 0, 0, 1, 0⟩
def smallRecord (i : Nat) : Rec :=
  ⟨List.replicate (if i = 3 then 65 else i) 0, i, false⟩
def zeroWords : Words := fun _ _ _ => 0
def changedWords : Words := fun level ordinal _ =>
  if (level, ordinal) = (3, 1) then 1 else 0

/-- Two actual direct reference steps form the lower carry. Its finishing
step reads the receiving family's words. -/
def tinyCarry (words : Words) : Output :=
  levelOneStep (tinyDirect 2) (jobWord tinyCfg words 1 3) (jobWord tinyCfg words 1 4)
    (levelOneStep (tinyDirect 1) (fun _ => 0) (jobWord tinyCfg words 1 3)
      emptyOutput [[some (smallRecord 2)]]) [[some (smallRecord 3)]]
def tinyInput (words : Words) : SInputs := sepInputs tinySep emptyOutput (tinyCarry words)

example : familyOf tinyCfg 1 4 = (3, 1) ∧ familyOf tinyCfg 2 2 = (3, 1) := by
  decide +kernel

/-- The carry's physical main changes, so equality of entire inputs is false. -/
example : (tinyInput zeroWords).bMain ≠ (tinyInput changedWords).bMain := by
  decide +kernel

/-- The byte-key populations and their distinctness survive that change. -/
example : ((tinyInput zeroWords).aAll.map Rec.key).toFinset =
      ((tinyInput changedWords).aAll.map Rec.key).toFinset ∧
    ((tinyInput zeroWords).bAll.map Rec.key).toFinset =
      ((tinyInput changedWords).bAll.map Rec.key).toFinset ∧
    ((tinyInput zeroWords).aAll.map Rec.key).Nodup ∧
    ((tinyInput zeroWords).bAll.map Rec.key).Nodup := by
  decide +kernel

/-- A failed direct producer supplies the later separated carry through its
unbounded reference continuation. No small-error claim is made for this
nonstandard load and zero spare tier. -/
def fallbackCarry : Output :=
  levelOneStep (tinyDirect 2) (fun _ => 0) (fun _ => 0)
    (levelOneStep (tinyDirect 1) (fun _ => 0) (fun _ => 0)
      emptyOutput [IdealDirectTests.overflowRecords.map some]) []

example : runJob (tinyDirect 1) (fun _ => 0) (fun _ => 0)
    (adopt emptyOutput [IdealDirectTests.overflowRecords.map some]) =
      .failed ⟨⟨.produceB, .outputTier, 0⟩, 2, 0⟩ := rfl

example : (sepInputs tinySep emptyOutput fallbackCarry).bAll.length = 66 ∧
    List.replicate 65 0 ∈ ((sepInputs tinySep emptyOutput fallbackCarry).bAll.map Rec.key) := by
  decide +kernel

/-- Both nonterminal and forwarded completing jobs instantiate the actual
canonical probability endpoint; potential-job membership is arithmetic. -/
example (initialized forwarded : Bool) :
    IdealKey.tapeLaw {tape |
      min ((row forwarded).stashPages * (row forwarded).C)
          ((row forwarded).tierPages * (row forwarded).C) <
        sHomeExcess (row forwarded)
          (jobWord (geo initialized).cfg (IdealHierarchy.words tape) 2 (ordinal initialized forwarded))
          (sepInputsAt (geo initialized).cfg (geo initialized).shapes
            (IdealDirect.trace (geo initialized).cfg (geo initialized).shapes online
              (schedule initialized) client tape)
            (IdealHierarchy.words tape) 2 (ordinal initialized forwarded))} ≤
      selSepUBound (row forwarded) := by
  apply IdealSepUnion initialized member member_valid 1 online (schedule initialized) 1 client
    (online_matches initialized) (by decide +kernel) (schedule_valid initialized)
    2 (ordinal initialized forwarded) (row forwarded)
  · apply HierarchyCoveringProof.mem_ordinary.mpr
    cases initialized <;> cases forwarded <;> decide +kernel
  · decide +kernel
  · cases initialized <;> cases forwarded <;> decide +kernel
  · cases initialized <;> cases forwarded <;> decide +kernel

end IdealSepUnionTests
