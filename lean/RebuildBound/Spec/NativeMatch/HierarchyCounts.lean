import RebuildBound.Spec.NativeMatch.Hierarchy
import RebuildBound.Spec.NativeMatch.Allocation
import RebuildBound.Spec.NativeMatch.Ordinals
import RebuildBound.Spec.ApiLegal

/-! Production job inventories are generated from actual reference states.
The global contracts in the first two interfaces are existing API theorems;
the third interface derives them from the public legal-client premises.
Capacity failure is charged separately on the unconditional experiment.
Original physical pages, direct groups and genuine DFS repartitioning remain
part of the execution construction; public arithmetic is not an execution census. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online NativeMatch NativeMatchTrace NativeMatchHierarchy

/-- Every actual in-horizon potential job obeys its public S_min allocation. -/
def NativeMatchProductionJobInventory_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool),
    member ∈ ConfigurationFamily.members → ∀ h,
    let geo := (member.geometry initialized).chunk h
    let g : OnlineGeom := ⟨64,member.r0⟩
    ∀ (c : Api.Codec) (run : OnlineBatch.BatchRun) (schedule : Schedule) (requests : List Api.Request),
    ApiRunCorrect geo c g run schedule requests → ApiTopPopulations geo g run →
    ∀ (words : Words) (job : JobId), job ∈ geo.cfg.potentialJobs → WithinHorizon geo.cfg job →
    ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words →
    weight 4 ((jobEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words job).map Event.comparison) ≤
      64^4 * NativeMatchInventory.classCharge member (geo.cfg.classOf job)

/-- The finite job prefix is counted by its actual carry ordinals, preserving
its original initialization seed. Future speculative finishes are filtered out. -/
def NativeMatchRebuildInventory_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
    let g : OnlineGeom := ⟨64,member.r0⟩
    ∀ (c : Api.Codec) (run : OnlineBatch.BatchRun) (schedule : Schedule) (requests : List Api.Request),
    ApiRunCorrect geo c g run schedule requests → ApiTopPopulations geo g run →
    ∀ words : Words, ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words →
    weight 4 ((rebuildEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words).map Event.comparison) ≤
      64^4 * h * NativeMatchInventory.sMin member initialized

/-- Actual adaptively chosen API requests supply all structural and live-load
premises through the existing legal-client correctness theorem. No per-job
shape, load, matching count, stored-key independence or agreement is assumed. -/
def NativeMatchAdaptiveRebuildInventory_statement : Prop :=
  ∀ (member : ConfigurationFamily.Member) (initialized : Bool),
    member ∈ ConfigurationFamily.members → ∀ h, 1 ≤ h →
    let geo := (member.geometry initialized).chunk h
    let g : OnlineGeom := ⟨64,member.r0⟩
    ∀ (c : Api.Codec) schedule init transcriptWidth width batches,
    let frames := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiLegal.Chooser geo.cfg (ApiAdaptive.shape frames) schedule transcriptWidth,
    let n := Adaptive.slotCount (ApiAdaptive.shape frames)
    let compiled := ApiLegal.adapt geo.cfg (ApiAdaptive.shape frames) schedule choose
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    n ≤ geo.cfg.horizon → SchedulePremises geo.cfg schedule n transcriptWidth →
    (∀ t : ApiLegal.Prefix geo.cfg (ApiAdaptive.shape frames) schedule transcriptWidth n,
      ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
        ((ApiAdaptive.requestGroups compiled (Adaptive.rowsOf (ApiLegal.erase t) n) frames).flatMap
          PublicApi.Group.lanes)) →
    ∀ words dummy,
    let client := ApiAdaptive.run c geo.cfg geo.shapes g schedule init frames compiled
    let run := Adaptive.realized geo.cfg geo.shapes g schedule client words dummy
    ¬Fails geo.cfg geo.shapes (OnlineBatch.traceOf g run) words →
    weight 4 ((rebuildEvents geo.cfg geo.shapes (OnlineBatch.traceOf g run) words).map Event.comparison) ≤
      64^4 * h * NativeMatchInventory.sMin member initialized

/-- The modeled initialization and top-preparation paths perform no approximate
matching. Their capacity and compiled-execution obligations remain separate. -/
def NativeMatchNoComparisonPaths_statement : Prop :=
  ∀ (cfg : Config) (sh : Shapes) (tr : Trace) (words : Words) (ordinal : Nat),
    jobEvents cfg sh tr words .initialization = [] ∧
    jobEvents cfg sh tr words (.topPrepare ordinal) = []

end RebuildBound.Spec
