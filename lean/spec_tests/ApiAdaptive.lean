import RebuildBound.Proofs.ApiAdaptive.Correctness
import spec_tests.ApiExecution

/-! The public client chooses one batch from one prefix, even when unit and
blind/probing cuts emit several internal operations. Later public batches can
use the new observations. Checked correctness uses both starts and all tapes. -/
namespace ApiAdaptiveTests
open RebuildBound RebuildBound.Spec RebuildBound.Model
open RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Model.PublicApi
open RebuildBound.Model.ApiAdaptive
open ApiTests (codec live tomb)

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def batches : List Batch :=
  [⟨false, [⟨.write, false, false⟩]⟩,
   ⟨false, [⟨.read, true, false⟩, ⟨.erase, false, false⟩,
     ⟨.exchange, true, true⟩, ⟨.read, true, false⟩]⟩,
   ⟨false, []⟩,
   ⟨false, [⟨.read, true, false⟩]⟩]

def fs : List Frame := frames 64 2 batches

def choose : ApiAdaptive.Chooser 1 := fun batch rows lane =>
  (LogicalKey.ofNat (7 + (rows.getLastD (fun _ => 0)) 0), 10 + 10 * batch + lane)

def rows : List (Fin 1 → Nat) :=
  [fun _ => 0, fun _ => 3, fun _ => 4, fun _ => 5, fun _ => 6, fun _ => 8]

example : shape fs = [.blind, .chunk 1, .chunk 2, .chunk 1, .chunk 1] := by decide +kernel
example : fs.map Frame.start = [0, 1, 1, 1, 5] := by decide +kernel
example : fs.map Frame.batchIndex = [0, 1, 1, 1, 3] := by decide +kernel
example : ((requestGroups choose rows fs).flatMap Group.lanes).map (fun q => LogicalKey.toNat q.key) =
    [7, 7, 7, 7, 7, 13] := by decide +kernel
-- Passing the new rows directly would change the batch's chosen key.
example : (choose 1 (rows.take 1) 2).1 ≠ (choose 1 (rows.take 3) 2).1 := by decide +kernel
example : Causal 0 fs := (ApiAdaptiveFrames 64 2 batches).1
example : GroupsFit 2 0 (requestGroups choose rows fs) :=
  (ApiAdaptiveFrames 64 2 batches).2.2 1 choose rows |>.2

-- The causal contract rejects a chooser using a future observation prefix.
example : ¬ Causal 0 [⟨0, 1, false, .blind (⟨.write, false, false⟩, 0)⟩] := by
  simp [Causal]
example : ¬ Causal 0 [⟨0, 0, true, .chunk []⟩] := by
  simp [Causal, Frame.kind, Adaptive.Kind.width]

def candidate : Fin (Adaptive.slotCount (shape fs)) → Fin 1 → Nat :=
  fun t => rows.getD t.val (fun _ => 0)

theorem replay_requests :
    Adaptive.replay (run codec ApiExecutionTests.cfg ApiExecutionTests.shapes
      ApiExecutionTests.geom ApiExecutionTests.schedule [] fs choose) candidate =
    ApiExecution.run codec ApiExecutionTests.cfg ApiExecutionTests.shapes
      ApiExecutionTests.geom ApiExecutionTests.schedule []
      (requestGroups choose (Adaptive.rowsOf candidate 6) fs) :=
  ApiAdaptiveReplay codec _ _ _ _ [] 1 fs choose (ApiAdaptiveFrames 64 2 batches).1 candidate

-- Another public batch can be absent without introducing a zero-width operation.
example : frames 64 2 [⟨false, []⟩, ⟨true, []⟩] = [] := by decide +kernel

-- This client chooses different replacement payloads based on observed rows.
-- Keys stay in the explicit legacy universe; that requirement is not erased.
def semanticBatches : List Batch :=
  [⟨false, [⟨.read, true, false⟩]⟩,
   ⟨false, [⟨.write, false, false⟩, ⟨.erase, false, false⟩,
     ⟨.read, true, false⟩, ⟨.exchange, true, true⟩]⟩]

def semanticChoose : ApiAdaptive.Chooser 2 := fun batch rows lane =>
  (LogicalKey.ofNat 7, if batch = 1 && lane = 3 then 40 else 20 + (rows.getLastD (fun _ => 0)) 0)

def semanticFrames := frames 2 AdaptiveSemanticsTest.online.unitEntries semanticBatches

theorem semantic_keys (rs : List (Fin 2 → Nat)) :
    ∀ q ∈ (requestGroups semanticChoose rs semanticFrames).flatMap Group.lanes,
      q.key ∈ ({LogicalKey.ofNat 7} : Finset LogicalKey) := by
  intro q hq
  simp only [requestGroups, List.flatMap_map, List.mem_flatMap] at hq
  obtain ⟨frame, _, hq⟩ := hq
  cases h : frame.group with
  | blind indexed =>
    simp [requests, h, Group.map, Group.lanes] at hq
    subst q
    simp [request, chosenLane, semanticChoose]
  | chunk indexed =>
    simp only [requests, h, Group.map, Group.lanes, List.mem_map] at hq
    obtain ⟨indexed, _, rfl⟩ := hq
    simp [request, chosenLane, semanticChoose]

theorem both_starts (initialized : Bool) :
    let geo := AdaptiveSemanticsTest.geometry initialized
    let S := syncSchedule geo.cfg
    let a := run codec geo.cfg geo.shapes AdaptiveSemanticsTest.online S
      (ApiExecutionTests.semanticInit initialized) semanticFrames semanticChoose
    AdaptiveSetting geo {LogicalKey.ofNat 7} AdaptiveSemanticsTest.online a S 5 ∧
    ∀ words dummy,
      let t := Adaptive.transcript geo.cfg geo.shapes AdaptiveSemanticsTest.online S a 5 words dummy
      let qs := (requestGroups semanticChoose (Adaptive.rowsOf t 5) semanticFrames).flatMap Group.lanes
      let realized := Adaptive.realized geo.cfg geo.shapes AdaptiveSemanticsTest.online S a words dummy
      Api.Implements codec geo.cfg geo.shapes AdaptiveSemanticsTest.online realized S words dummy qs ∧
      ApiCorrect codec geo.cfg geo.shapes AdaptiveSemanticsTest.online realized S words dummy qs := by
  apply ApiAdaptiveCorrectness (AdaptiveSemanticsTest.geometry initialized)
    (AdaptiveSemanticsTest.structural initialized) {LogicalKey.ofNat 7} codec AdaptiveSemanticsTest.online
    (syncSchedule (AdaptiveSemanticsTest.geometry initialized).cfg)
    (ApiExecutionTests.semanticInit initialized) 2 2 semanticBatches semanticChoose
  · change initialized = false → ApiExecutionTests.semanticInit initialized = []
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
    cases initialized <;> simp [ApiExecutionTests.semanticInit] at hr
    subst r
    decide +kernel
  · intro t
    exact semantic_keys _
  · exact SyncScheduleLemmas.syncSchedule_premises _
      (by change ∀ b ∈ ([2] : List Nat), 0 < b; decide +kernel)
      (by change 0 < 128; decide +kernel) 5

-- The final insertion result follows from API correctness, for all tapes.
theorem semantic_requests (rs : List (Fin 2 → Nat)) :
    (requestGroups semanticChoose rs semanticFrames).flatMap Group.lanes =
      [⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .blindWrite (20 + (rs.take 1).getLastD (fun _ => 0) 0)⟩,
       ⟨LogicalKey.ofNat (7), .erase⟩, ⟨LogicalKey.ofNat (7), .read⟩, ⟨LogicalKey.ofNat (7), .exchange 40 true⟩] := by rfl

theorem final_value (initialized : Bool) (words : Words) (dummy : Nat → Nat → Nat) :
    let geo := AdaptiveSemanticsTest.geometry initialized
    let S := syncSchedule geo.cfg
    let a := run codec geo.cfg geo.shapes AdaptiveSemanticsTest.online S
      (ApiExecutionTests.semanticInit initialized) semanticFrames semanticChoose
    Api.stateOf codec (Api.historyAt
      (Adaptive.realized geo.cfg geo.shapes AdaptiveSemanticsTest.online S a words dummy) 5) (LogicalKey.ofNat 7) =
        some 40 := by
  have hc := ((both_starts initialized).2 words dummy).2
  have state := congrFun (hc.1 5 (by rw [semantic_requests]; simp)) (LogicalKey.ofNat 7)
  apply state.trans
  rw [semantic_requests]
  cases initialized <;> simp [Api.stateAt, Api.step, Api.nextValue]

-- The adaptive wrapper retains the physical flag distinction after publication.
def publicationBatches : List Batch :=
  [⟨false, [⟨.write, false, false⟩, ⟨.write, false, false⟩,
    ⟨.erase, false, false⟩, ⟨.write, true, false⟩, ⟨.read, true, false⟩]⟩]
def publicationChoose : ApiAdaptive.Chooser 1 := fun _ _ lane =>
  let pair := [(7, 10), (99, 42), (7, 0), (8, 40), (7, 0)].getD lane (0, 0)
  (LogicalKey.ofNat pair.1, pair.2)
def publicationFrames := frames 64 2 publicationBatches

theorem publication_interaction (words : Words) (dummy : Nat → Nat → Nat) :
    let a := run codec ApiExecutionTests.cfg ApiExecutionTests.shapes ApiExecutionTests.geom
      ApiExecutionTests.schedule [] publicationFrames publicationChoose
    (Adaptive.realized ApiExecutionTests.cfg ApiExecutionTests.shapes ApiExecutionTests.geom
      ApiExecutionTests.schedule a words dummy).ops =
        [.blind (live 7 10), .blind (live 99 42),
          .batch [tomb 7 false, live 8 40], .batch [tomb 7 true]] := by
  have h := ApiAdaptiveInteraction codec ApiExecutionTests.cfg ApiExecutionTests.shapes
    ApiExecutionTests.geom ApiExecutionTests.schedule [] 1 publicationFrames publicationChoose
    (ApiAdaptiveFrames 64 2 publicationBatches).1 words dummy
  apply (congrArg OnlineBatch.BatchRun.ops h).trans
  exact ApiExecutionTests.publication_records

end ApiAdaptiveTests
