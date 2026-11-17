import RebuildBound.Proofs.ApiExecution
import spec_tests.ApiCorrectness
import spec_tests.AdaptiveSemantics

/-! Physical request construction regressions. These checks exercise the actual
provisional probes, duplicate forwarding, blind writes, and public unit cuts.
In particular, physical flags need not equal chronological reference flags
after top publication drops a tombstone. -/
namespace ApiExecutionTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open ApiTests (codec live tomb)

deriving instance DecidableEq for OnlineBatch.Op

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def localGroups : List (PublicApi.Group Api.Request) :=
  [.blind ⟨LogicalKey.ofNat (7), .blindWrite 10⟩,
   .chunk [⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .write 20⟩, ⟨LogicalKey.ofNat (7), .erase⟩,
     ⟨LogicalKey.ofNat (7), .exchange 30 false⟩, ⟨LogicalKey.ofNat (7), .exchange 40 true⟩, ⟨LogicalKey.ofNat (7), .read⟩]]

def localRun : OnlineBatch.BatchRun :=
  ApiExecution.run codec ApiTests.cfg ApiTests.sh ApiTests.g ApiTests.schedule [] localGroups

example : localRun.ops = ApiTests.localRun.ops := by decide +kernel
example : localGroups.flatMap Group.lanes = ApiTests.localRequests := by decide +kernel
example : (OnlineBatch.slots localRun).map (fun s => s.record) =
    [live 7 10, live 7 10, live 7 20, tomb 7 false,
     tomb 7 false, live 7 40, live 7 40] := by decide +kernel

-- Invalid public probe classifications are rejected by the constructor contract.
example : ¬ ApiExecution.Valid (.blind ⟨LogicalKey.ofNat (7), .read⟩) := by simp [ApiExecution.Valid, Api.Request.probes]
example : ¬ ApiExecution.Valid (.chunk [⟨LogicalKey.ofNat (7), .blindWrite 9⟩]) := by
  simp [ApiExecution.Valid, Api.Request.probes]
example : ApiExecution.Valid (.chunk []) := by simp [ApiExecution.Valid]
example : (ApiExecution.run codec ApiTests.cfg ApiTests.sh ApiTests.g ApiTests.schedule
    [] [.chunk []]).ops = [.batch []] := by rfl

-- The standard 64-position boundary with 62 already occupied positions. The
-- first chunk erases A and writes B; a later miss of A cannot suppress that
-- deletion from the committed unit.
def boundaryCfg : Config := { ApiTests.cfg with carry1 := 32 }
def boundaryGeom : OnlineGeom := ⟨64, 1⟩
def boundaryPrefix : List OnlineBatch.Op := [.batch (List.replicate 62 (live 7 10))]
def boundaryLanes : List Lane :=
  [⟨LogicalKey.ofNat (7), 0, ⟨.erase, false, false⟩⟩,
   ⟨LogicalKey.ofNat (8), 40, ⟨.write, true, false⟩⟩,
   ⟨LogicalKey.ofNat (7), 0, ⟨.read, true, false⟩⟩]
def boundaryGroups : List (PublicApi.Group Api.Request) :=
  (groups 64 64 62 false boundaryLanes).map (Group.map (request false))
def boundaryRun : OnlineBatch.BatchRun :=
  ⟨boundaryPrefix ++ ApiExecution.operations codec boundaryCfg ApiTests.sh boundaryGeom
      ApiTests.schedule [] boundaryPrefix boundaryGroups,
    [], fun r => codec.flag r.val⟩

example : boundaryGeom.unitEntries * boundaryGeom.unitsPerPrefix =
    boundaryCfg.carryPositions 1 := by rfl
example : boundaryGroups.map Group.shape = [(true, 2), (true, 1)] := by decide +kernel
example : boundaryRun.ops.drop 1 =
    [.batch [tomb 7 false, live 8 40], .batch [tomb 7 false]] := by decide +kernel
example : (OnlineBatch.stateAt boundaryGeom boundaryRun 3).frozen.flatMap Bucket.recs =
    [tomb 7 false, live 8 40] := by decide +kernel
example : (OnlineBatch.stateAt boundaryGeom boundaryRun 3).current.recs =
    [tomb 7 false] := by decide +kernel

-- Tiny executable hierarchy: zero tier capacity intentionally permits reference
-- fallback; the constructor is total without assuming successful capacities.
def cfg : Config :=
  { fanouts := [2], carry1 := 1, topDigit := 1, load := 2, horizon := 32,
    initialized := false }
def geom : OnlineGeom := ⟨2, 1⟩
def direct (d : Nat) : DirectJob.Geometry :=
  { K := 0, digit := d, outputHomes := d, outputCapacity := 0,
    aTierCapacity := 0, routeCapacity := 0, radixCapacity := 0,
    insertionCapacity := 0, copyCapacity := 0, ranges := .direct }
def top : TopGeom :=
  { C := 64, k := 1, e := 0, rho := 0, I := 1, dfs := false,
    rPages := 1, bPages := 1, mergePages := 1, tierPages := 1 }
def prep : TPGeom :=
  { C := 64, k := 1, stashPages := 1, aTierPages := 1, drainPages := 1,
    rangeBits := 0, I := 1, dfs := false }
def shapes : Shapes := ⟨direct, fun _ _ => selectedDirectSep 2, top, prep, prep⟩
def schedule : Schedule := fun t => if t < 4 then ⟨0, []⟩ else ⟨2, [(2, 1)]⟩
def publicationGroups : List (PublicApi.Group Api.Request) :=
  [.blind ⟨LogicalKey.ofNat (7), .blindWrite 10⟩, .blind ⟨LogicalKey.ofNat (99), .blindWrite 42⟩,
   .chunk [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (8), .write 40⟩], .chunk [⟨LogicalKey.ofNat (7), .read⟩]]
def publicationRun : OnlineBatch.BatchRun :=
  ApiExecution.run codec cfg shapes geom schedule [] publicationGroups

theorem schedule_valid : SchedulePremises cfg schedule 5 1 := by
  constructor
  · intro j hj
    interval_cases j <;> decide +kernel
  · intro j hj
    interval_cases j <;> decide +kernel
  · intro j hj c hc
    interval_cases j <;> simp [schedule] at hc
    subst c
    decide +kernel
  · intro j hj
    interval_cases j <;> decide +kernel
  · intro j hj
    interval_cases j <;> norm_num [schedule, Tiles, window, cfg, Config.levels,
      Config.carryPositions, Config.carry]

theorem publication_valid : ∀ group ∈ publicationGroups, ApiExecution.Valid group := by
  intro group hg
  simp [publicationGroups] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp [ApiExecution.Valid, Api.Request.probes]

/-- The base constructor theorem discharges every physical local equation,
without any fixed-universe or successful-capacity premise. -/
example : Api.Implements codec cfg shapes geom publicationRun schedule
    (fun _ _ _ => 0) (fun _ _ => 0) (publicationGroups.flatMap Group.lanes) :=
  ApiExecutionImplements codec cfg shapes geom schedule [] publicationGroups 1
    rfl (by decide +kernel) publication_valid schedule_valid

example : FlagRule cfg shapes geom publicationRun schedule (fun _ _ _ => 0) :=
  ApiExecutionFlags codec cfg shapes geom schedule [] publicationGroups 1
    rfl (by decide +kernel) publication_valid schedule_valid

def publicationPrefix : List OnlineBatch.Op :=
  [.blind (live 7 10), .blind (live 99 42), .batch [tomb 7 false, live 8 40]]
def publicationProbe : OnlineBatch.BatchRun :=
  ApiExecution.provisional codec [] publicationPrefix [] ⟨LogicalKey.ofNat (7), .read⟩
def publicationTrace : Trace := OnlineBatch.traceOf geom publicationProbe
def zeroWords : Words := fun _ _ _ => 0

private theorem low_zero : table cfg shapes publicationTrace zeroWords 1 0 =
    DirectJob.emptyOutput := by
  rw [HierarchyInvariantProof.table_base (Or.inr (Or.inr (by decide +kernel))),
    HierarchyInvariantProof.base_low (by decide +kernel)]

private theorem low_one : table cfg shapes publicationTrace zeroWords 1 1 =
    Hierarchy.step cfg shapes publicationTrace zeroWords 1 1
      DirectJob.emptyOutput DirectJob.emptyOutput := by
  rw [HierarchyInvariantProof.table_step (by decide +kernel) (by decide +kernel) (by decide +kernel), low_zero]
  rfl

private theorem low_two : table cfg shapes publicationTrace zeroWords 1 2 =
    Hierarchy.step cfg shapes publicationTrace zeroWords 1 2
      (Hierarchy.step cfg shapes publicationTrace zeroWords 1 1
        DirectJob.emptyOutput DirectJob.emptyOutput) DirectJob.emptyOutput := by
  rw [HierarchyInvariantProof.table_step (by decide +kernel) (by decide +kernel) (by decide +kernel), low_one]
  rfl

private theorem top_one : table cfg shapes publicationTrace zeroWords 2 1 =
    Hierarchy.step cfg shapes publicationTrace zeroWords 2 1
      (base cfg shapes publicationTrace zeroWords 2)
      (Hierarchy.step cfg shapes publicationTrace zeroWords 1 2
        (Hierarchy.step cfg shapes publicationTrace zeroWords 1 1
          DirectJob.emptyOutput DirectJob.emptyOutput) DirectJob.emptyOutput) := by
  rw [HierarchyInvariantProof.table_step (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rw [HierarchyInvariantProof.table_base (v := 0) (Or.inr (Or.inr (by decide +kernel)))]
  change Hierarchy.step cfg shapes publicationTrace zeroWords 2 1 _
    (table cfg shapes publicationTrace zeroWords 1 2) = _
  rw [low_two]

/-- Top publication has removed the deletion, so the physical miss is absent. -/
theorem publication_found :
    (Probe.batch cfg shapes geom publicationProbe schedule zeroWords (fun _ _ => 0) 4).found =
      none := by
  change (Probe.hierarchy cfg shapes publicationTrace zeroWords (fun _ => 0)
    (LogicalKey.ofNat 7) [(2, 1)] none).found = none
  simp only [Probe.hierarchy, Probe.cascade, Probe.cascadeWith]
  rw [top_one]
  decide +kernel

private theorem publication_append (pre : List OnlineBatch.Op)
    (first rest : List (PublicApi.Group Api.Request)) :
    ApiExecution.operations codec cfg shapes geom schedule [] pre (first ++ rest) =
      ApiExecution.operations codec cfg shapes geom schedule [] pre first ++
        ApiExecution.operations codec cfg shapes geom schedule []
          (pre ++ ApiExecution.operations codec cfg shapes geom schedule [] pre first) rest := by
  induction first generalizing pre with
  | nil => simp [ApiExecution.operations]
  | cons group first ih => simp [ApiExecution.operations, ih, List.append_assoc]

/-- The compiler constructs the physical flag from that miss, after the cut. -/
theorem publication_records : publicationRun.ops =
    [.blind (live 7 10), .blind (live 99 42),
     .batch [tomb 7 false, live 8 40], .batch [tomb 7 true]] := by
  have hprefix : ApiExecution.operations codec cfg shapes geom schedule [] []
      (publicationGroups.take 3) = publicationPrefix := by decide +kernel
  change ApiExecution.operations codec cfg shapes geom schedule [] [] publicationGroups = _
  rw [show publicationGroups = publicationGroups.take 3 ++ publicationGroups.drop 3 by rfl,
    publication_append, hprefix]
  change publicationPrefix ++ [.batch [Api.postRecord codec ⟨LogicalKey.ofNat 7, .read⟩
    (Probe.batch cfg shapes geom publicationProbe schedule zeroWords (fun _ _ => 0) 4).found]] = _
  rw [publication_found]
  rfl

example : (Api.referenceRecords codec [] (publicationGroups.flatMap Group.lanes)).getLast? =
    some (tomb 7 false) := by decide +kernel

/-- Requests exercise a nonempty initialized top, blind replacement, deletion,
forwarded tombstones and reinsertion, with the same public shape for both starts. -/
def semanticGroups : List (PublicApi.Group Api.Request) :=
  [.chunk [⟨LogicalKey.ofNat (7), .read⟩], .blind ⟨LogicalKey.ofNat (7), .blindWrite 20⟩,
   .chunk [⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .exchange 40 true⟩]]
def semanticInit (initialized : Bool) : List Rec :=
  if initialized then [live 7 10] else []

theorem both_starts (initialized : Bool) :
    let geo := AdaptiveSemanticsTest.geometry initialized
    let S := syncSchedule geo.cfg
    let run := ApiExecution.run codec geo.cfg geo.shapes AdaptiveSemanticsTest.online S
      (semanticInit initialized) semanticGroups
    ∀ words dummy,
      Api.Implements codec geo.cfg geo.shapes AdaptiveSemanticsTest.online run S words dummy
        (semanticGroups.flatMap Group.lanes) ∧
      ApiCorrect codec geo.cfg geo.shapes AdaptiveSemanticsTest.online run S words dummy
        (semanticGroups.flatMap Group.lanes) := by
  have result := ApiExecutionCorrectness (AdaptiveSemanticsTest.geometry initialized)
    (AdaptiveSemanticsTest.structural initialized) {LogicalKey.ofNat 7} codec AdaptiveSemanticsTest.online
    (syncSchedule (AdaptiveSemanticsTest.geometry initialized).cfg)
    (semanticInit initialized) semanticGroups 2
  apply And.right
  apply result
  · change initialized = false → semanticInit initialized = []
    intro h
    subst initialized
    rfl
  · intro k hk
    have : k = LogicalKey.ofNat 7 := Finset.mem_singleton.mp hk
    subst k
    decide +kernel
  · change 1 ≤ 1024
    decide +kernel
  · rfl
  · decide +kernel
  · change 5 ≤ 2 ^ 32
    decide +kernel
  · cases initialized <;> decide +kernel
  · intro r hr
    cases initialized <;> simp [semanticInit] at hr
    subst r
    decide +kernel
  · intro q hq
    simp [semanticGroups, Group.lanes] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro group hg
    simp [semanticGroups] at hg
    rcases hg with rfl | rfl | rfl <;>
      simp [ApiExecution.Valid, Api.Request.probes]
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) 5

/-- Reinsertion leaves the same live payload for both starts and all tapes. -/
theorem final_value (initialized : Bool)
    (words : Words) (dummy : Nat → Nat → Nat) :
    let geo := AdaptiveSemanticsTest.geometry initialized
    let run := ApiExecution.run codec geo.cfg geo.shapes AdaptiveSemanticsTest.online
      (syncSchedule geo.cfg) (semanticInit initialized) semanticGroups
    Api.stateOf codec (Api.historyAt run 5) (LogicalKey.ofNat 7) = some 40 := by
  have hc := (both_starts initialized words dummy).2
  have state := congrFun (hc.1 5 (by decide +kernel)) (LogicalKey.ofNat 7)
  apply state.trans
  change Api.stateAt (Api.stateOf codec (semanticInit initialized))
    (semanticGroups.flatMap Group.lanes) 5 (LogicalKey.ofNat 7) = some 40
  cases initialized <;> decide +kernel

/-- The first physical read sees the initialized value exactly when one was supplied. -/
theorem first_value (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    let geo := AdaptiveSemanticsTest.geometry initialized
    let S := syncSchedule geo.cfg
    let run := ApiExecution.run codec geo.cfg geo.shapes AdaptiveSemanticsTest.online S
      (semanticInit initialized) semanticGroups
    Api.value codec (Probe.batch geo.cfg geo.shapes AdaptiveSemanticsTest.online run S words dummy 0).found =
      if initialized then some 10 else none := by
  dsimp only
  obtain ⟨hi, hc⟩ := both_starts initialized words dummy
  let run := ApiExecution.run codec (AdaptiveSemanticsTest.geometry initialized).cfg
    (AdaptiveSemanticsTest.geometry initialized).shapes AdaptiveSemanticsTest.online
    (syncSchedule (AdaptiveSemanticsTest.geometry initialized).cfg)
    (semanticInit initialized) semanticGroups
  have ht : 0 < (OnlineBatch.slots run).length := by
    rw [← hi.length]
    decide +kernel
  let s := (OnlineBatch.slots run)[0]
  have hs : (OnlineBatch.slots run)[0]? = some s := List.getElem?_eq_getElem ht
  have hr := (hc.2 0 ⟨LogicalKey.ofNat (7), .read⟩ s rfl hs).1
  change Api.value codec (Probe.batch _ _ _ run _ words dummy 0).found =
    Api.stateOf codec (semanticInit initialized) (LogicalKey.ofNat 7) at hr
  exact hr.trans (by cases initialized <;> decide +kernel)


end ApiExecutionTests
