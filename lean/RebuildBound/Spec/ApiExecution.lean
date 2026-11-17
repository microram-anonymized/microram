import RebuildBound.Spec.Model.ApiExecution
import RebuildBound.Spec.HierarchyApi

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.PublicApi

/-- Request execution preserves all public group widths, keys and probe bits. -/
def ApiExecutionShape_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init (groups : List (PublicApi.Group Api.Request)),
    (∀ group ∈ groups, ApiExecution.Valid group) →
    let run := ApiExecution.run c cfg sh g S init groups
    OnlineBatch.widths run = groups.map (fun group => group.lanes.length) ∧
    (OnlineBatch.slots run).map (fun s => (s.record.key, s.probes)) =
      (groups.flatMap PublicApi.Group.lanes).map (fun q => (q.key, q.probes))

/-- The constructor derives every physical selection/postrecord equation at
zero tapes. Only public geometry and schedule premises are required; there is
no assumed API implementation, key universe, unshadowed promise or load bound. -/
def ApiExecutionImplements_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init (groups : List (PublicApi.Group Api.Request)) m,
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 →
    0 < g.unitEntries →
    (∀ group ∈ groups, ApiExecution.Valid group) →
    SchedulePremises cfg S (groups.flatMap PublicApi.Group.lanes).length m →
    Api.Implements c cfg sh g (ApiExecution.run c cfg sh g S init groups) S
      (fun _ _ _ => 0) (fun _ _ => 0) (groups.flatMap PublicApi.Group.lanes)

/-- Physical generated flags follow the local rule without a capacity premise. -/
def ApiExecutionFlags_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init (groups : List (PublicApi.Group Api.Request)) m,
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 →
    0 < g.unitEntries →
    (∀ group ∈ groups, ApiExecution.Valid group) →
    SchedulePremises cfg S (groups.flatMap PublicApi.Group.lanes).length m →
    FlagRule cfg sh g (ApiExecution.run c cfg sh g S init groups) S (fun _ _ _ => 0)

/-- Transfer the constructed records to actual tapes under the existing
structural fixed-universe setting. This is not the arbitrary-key capacity
theorem; that is `IdealCapacity_statement` (`Spec/IdealCapacity.lean`). -/
def ApiExecutionTransfer_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ U (c : Api.Codec) g S init (groups : List (PublicApi.Group Api.Request)) m,
      let run := ApiExecution.run c geo.cfg geo.shapes g S init groups
      (∀ group ∈ groups, ApiExecution.Valid group) →
      UniverseBatchSetting geo U g run S (groups.flatMap PublicApi.Group.lanes).length m →
      ∀ words dummy, Api.Implements c geo.cfg geo.shapes g run S words dummy
        (groups.flatMap PublicApi.Group.lanes)

/-- Fresh public lowering feeds the physical constructor without changing keys,
probe shape or the requester-boundary guarantee. A continuation at a nonzero
position must separately supply its preceding operations. -/
def ApiExecutionLowered_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh g S init width found (lanes : List Lane) m,
    g.unitEntries * g.unitsPerPrefix = cfg.carryPositions 1 →
    0 < g.unitEntries → SchedulePremises cfg S lanes.length m →
    let lowered := groups width g.unitEntries 0 found lanes
    let requests := lowered.map (PublicApi.Group.map (request found))
    let run := ApiExecution.run c cfg sh g S init requests
    GroupsFit g.unitEntries 0 lowered ∧
    OnlineBatch.widths run =
      (publicShape width g.unitEntries 0 found (lanes.map Lane.descriptor)).map Prod.snd ∧
    Api.Implements c cfg sh g run S (fun _ _ _ => 0) (fun _ _ => 0)
      (lanes.map (request found))

/-- Complete request-level correctness for the fixed-universe model.
The setting, physical postrecord equations and logical API results are derived
from explicit input/schedule premises. This endpoint is deterministic and
states the fixed-universe contract explicitly; ApiExecutionStructural
provides the universe-free endpoint. -/
def ApiExecutionCorrectness_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (U : Finset LogicalKey) (c : Api.Codec) g S init (groups : List (PublicApi.Group Api.Request)) m,
      (geo.cfg.initialized = false → init = []) →
      (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
      g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
      0 < g.unitEntries → (groups.flatMap PublicApi.Group.lanes).length ≤ geo.cfg.horizon →
      (init.map Rec.key).Nodup → (∀ r ∈ init, r.key ∈ U) →
      (∀ q ∈ groups.flatMap PublicApi.Group.lanes, q.key ∈ U) →
      (∀ group ∈ groups, ApiExecution.Valid group) →
      SchedulePremises geo.cfg S (groups.flatMap PublicApi.Group.lanes).length m →
      let run := ApiExecution.run c geo.cfg geo.shapes g S init groups
      UniverseBatchSetting geo U g run S (groups.flatMap PublicApi.Group.lanes).length m ∧
      ∀ words dummy,
        Api.Implements c geo.cfg geo.shapes g run S words dummy (groups.flatMap PublicApi.Group.lanes) ∧
        ApiCorrect c geo.cfg geo.shapes g run S words dummy (groups.flatMap PublicApi.Group.lanes)

end RebuildBound.Spec
