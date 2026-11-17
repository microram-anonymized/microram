import RebuildBound.Spec.Model.ApiContinuation
import RebuildBound.Spec.ApiStructural

/-! Physical continuation contracts. The same public schedule and configuration
are used for the original and extended run. Validity of the schedule through
the extended endpoint and room in the public horizon are explicit; neither is
inferred from a shorter run. All reference executions remain unconditional. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.PublicApi Model.ApiContinuation

def ApiIdleShape_statement : Prop :=
  ∀ entries groups extra, 0 < entries →
    (∀ group ∈ groups, ApiExecution.Valid group) → GroupsFit entries 0 groups →
    (extend groups extra).flatMap Group.lanes =
      ApiCapacity.idleExtend (groups.flatMap Group.lanes) extra ∧
    (∀ group ∈ extend groups extra, ApiExecution.Valid group) ∧
    GroupsFit entries 0 (extend groups extra)

/-- Extending requests preserves complete physical operations, metadata, slots,
and every requester state belonging to the original operation prefix. -/
def ApiIdlePrefix_statement : Prop :=
  ∀ c cfg sh g S init groups extra,
    let before := ApiExecution.run c cfg sh g S init groups
    let after := ApiExecution.run c cfg sh g S init (extend groups extra)
    after.ops.take before.ops.length = before.ops ∧
    (OnlineBatch.slots after).take (OnlineBatch.slots before).length =
      OnlineBatch.slots before ∧
    ∀ j, j ≤ before.ops.length →
      OnlineBatch.stateAt g after j = OnlineBatch.stateAt g before j

/-- On every tape, earlier physical selections and bucket observations are
unchanged. No correctness, capacity, flag, or key-universe assumption is used. -/
def ApiIdleObservations_statement : Prop :=
  ∀ c cfg sh g S init groups extra m,
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 → 0 < g.unitEntries →
    SchedulePremises cfg S ((extend groups extra).flatMap Group.lanes).length m →
    let before := ApiExecution.run c cfg sh g S init groups
    let after := ApiExecution.run c cfg sh g S init (extend groups extra)
    ∀ words dummy t, t < (OnlineBatch.slots before).length →
      (Probe.batch cfg sh g before S words dummy t).found =
        (Probe.batch cfg sh g after S words dummy t).found ∧
      ∀ i, OnlineBatch.touched cfg sh g before S words dummy t i =
        OnlineBatch.touched cfg sh g after S words dummy t i

/-- A completed physical endpoint has no partial unit. Every trace cut covering
its frozen units represents the original final map, including initialization. -/
def CompletedApiSnapshot (c : Api.Codec) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (requests : List Api.Request) (units : Nat) : Prop :=
  (OnlineBatch.stateAt g run run.ops.length).current = [] ∧
  (OnlineBatch.stateAt g run run.ops.length).frozen.length = units ∧
  ∀ n, units ≤ n * g.unitsPerPrefix →
    Api.stateOf c (run.init ++ (List.range n).flatMap
      (fun i => DirectMasks.records ((OnlineBatch.traceOf g run).units i))) =
        Api.stateAt (Api.stateOf c run.init) requests requests.length

/-- The constructor derives the flags and every logical prefix before the
completed-cut argument. Capacity is unnecessary for deterministic semantics. -/
def ApiIdleComplete_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ c g S init groups m units,
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    (groups.flatMap Group.lanes).length ≤ units * g.unitEntries →
    units * g.unitEntries ≤ geo.cfg.horizon →
    (∀ group ∈ groups, ApiExecution.Valid group) → GroupsFit g.unitEntries 0 groups →
    SchedulePremises geo.cfg S (units * g.unitEntries) m →
    let extended := complete g.unitEntries units groups
    let run := ApiExecution.run c geo.cfg geo.shapes g S init extended
    ApiRunCorrect geo c g run S (extended.flatMap Group.lanes) ∧
      CompletedApiSnapshot c g run (groups.flatMap Group.lanes) units

/-- Logical capacity survives the physical continuation and supplies all four
top populations, together with the exact final-map snapshot correspondence. -/
def ApiIdleLive_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ c g S init groups m units,
    ApiCapacity.InitialStateValid geo.keyCapacity geo.cfg.initialized init →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 → 0 < g.unitEntries →
    (groups.flatMap Group.lanes).length ≤ units * g.unitEntries →
    units * g.unitEntries ≤ geo.cfg.horizon →
    (∀ group ∈ groups, ApiExecution.Valid group) → GroupsFit g.unitEntries 0 groups →
    SchedulePremises geo.cfg S (units * g.unitEntries) m →
    ApiCapacity.LiveCapacity geo.keyCapacity (Api.stateOf c init) (init.map Rec.key)
      (groups.flatMap Group.lanes) →
    let extended := complete g.unitEntries units groups
    let run := ApiExecution.run c geo.cfg geo.shapes g S init extended
    ApiRunCorrect geo c g run S (extended.flatMap Group.lanes) ∧
      ApiTopPopulations geo g run ∧
      CompletedApiSnapshot c g run (groups.flatMap Group.lanes) units

end RebuildBound.Spec
