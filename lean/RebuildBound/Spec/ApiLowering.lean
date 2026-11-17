import RebuildBound.Spec.Model.ApiLowering
import RebuildBound.Spec.ApiCorrectness

/-! The public batch API is reduced to the existing local postrecord contract.
Neither the relation below nor chunk validity assumes logical map correctness. -/
namespace RebuildBound.Model.PublicApi
open Hierarchy Online

/-- Local successful-execution equations. The output equation describes only
requested buffers; an output-free write need not recover a previous value. -/
structure Local (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) (foundOutput : Bool) (lanes : List Lane)
    (returned : Nat → Response) : Prop where
  implementation : Api.Implements c cfg sh g run S words dummy (lanes.map (request foundOutput))
  output : ∀ t l, lanes[t]? = some l →
    returned t = response foundOutput l (Api.value c (Probe.batch cfg sh g run S words dummy t).found)

/-- All prefix maps and all requested outputs satisfy public sequential semantics. -/
def Correct (c : Api.Codec) (run : OnlineBatch.BatchRun) (foundOutput : Bool)
    (lanes : List Lane) (returned : Nat → Response) : Prop :=
  (∀ t, t ≤ lanes.length →
    Api.stateOf c (Api.historyAt run t) = stateAt (Api.stateOf c run.init) lanes t) ∧
  ∀ t l, lanes[t]? = some l →
    returned t = response foundOutput l (stateAt (Api.stateOf c run.init) lanes t l.key)

end RebuildBound.Model.PublicApi

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- Lowering preserves lane order and multiplicity, emits compatible bounded
operations that fit the remaining unit, and its shape depends only on public data. -/
def ApiLoweringStructure_statement : Prop :=
  ∀ width entries position foundOutput (lanes : List PublicApi.Lane),
    (PublicApi.groups width entries position foundOutput lanes).flatMap PublicApi.Group.lanes = lanes ∧
    (∀ group ∈ PublicApi.groups width entries position foundOutput lanes,
      PublicApi.ValidGroup width foundOutput group) ∧
    (PublicApi.groups width entries position foundOutput lanes).map PublicApi.Group.shape =
      PublicApi.publicShape width entries position foundOutput (lanes.map PublicApi.Lane.descriptor) ∧
    PublicApi.GroupsFit entries position (PublicApi.groups width entries position foundOutput lanes)

/-- The internal requests implement precisely the independent public map,
including ReadThenWrite and both probing and output-free Write. -/
def ApiLoweringMap_statement : Prop :=
  ∀ foundOutput (initial : Api.State) lanes t,
    Api.stateAt initial (lanes.map (PublicApi.request foundOutput)) t =
      PublicApi.stateAt initial lanes t

/-- General transfer, also usable with the existing adaptive API theorem on its
realized run. The local equations need no global-correctness assumption. -/
def PublicBatchApiCorrectness_statement : Prop :=
  ∀ (c : Api.Codec) (cfg : Config) (sh : Shapes) (g : OnlineGeom)
    (run : OnlineBatch.BatchRun) (S : Schedule) (words : Words)
    (dummy : Nat → Nat → Nat) foundOutput lanes returned,
    PublicApi.Local c cfg sh g run S words dummy foundOutput lanes returned →
    ApiCorrect c cfg sh g run S words dummy (lanes.map (PublicApi.request foundOutput)) →
    PublicApi.Correct c run foundOutput lanes returned

/-- Conditional on the existing hierarchy setting, local postrecord and requested
output construction suffice for the complete public batch semantics. -/
def PublicBatchApiCorrectness31_statement : Prop :=
  ∀ h, 1 ≤ h → ∀ U g run S m,
    UniverseBatchSetting (geometry31.chunk h) U g run S (OnlineBatch.slots run).length m →
    ∀ (c : Api.Codec) (words : Words) (dummy : Nat → Nat → Nat)
      foundOutput lanes returned,
      PublicApi.Local c (geometry31.chunk h).cfg (geometry31.chunk h).shapes
        g run S words dummy foundOutput lanes returned →
      PublicApi.Correct c run foundOutput lanes returned

end RebuildBound.Spec
