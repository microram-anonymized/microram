import RebuildBound.Spec.Model.RequesterCuts
import RebuildBound.Spec.Model.ApiExecution

/-! Safe public chunk widths imply complete logical prefixes at every frozen
unit and trace cut. This is record chronology, independent of map capacity,
key bounds, routing tapes and success. -/
namespace RebuildBound.Spec
open Model Model.Online Model.OnlineBatch Model.RequesterCuts

/-- Read any frozen prefix from the final requester, even after later requests
repeat its keys. It represents exactly that many logical lane positions. -/
def RequesterUnitCuts_statement : Prop :=
  ∀ (g : OnlineGeom) (run : BatchRun), 0 < g.unitEntries →
    WidthsFit g.unitEntries 0 (widths run) →
    ∀ units, units ≤ (stateAt g run run.ops.length).frozen.length → ∀ key,
    DirectPrefix.latest key (((stateAt g run run.ops.length).frozen.take units).flatMap Bucket.recs) =
      DirectPrefix.latest key (((slots run).take (units * g.unitEntries)).map Slot.record)

/-- Rebuild trace prefixes group whole frozen units, so they inherit exactly
the consumed request prefix, not the map at a later execution time. -/
def RequesterTraceCuts_statement : Prop :=
  ∀ (g : OnlineGeom) (run : BatchRun), 0 < g.unitEntries →
    WidthsFit g.unitEntries 0 (widths run) →
    ∀ n, n * g.unitsPerPrefix ≤ (stateAt g run run.ops.length).frozen.length → ∀ key,
    DirectPrefix.latest key ((List.range n).flatMap
      fun i => DirectMasks.records ((traceOf g run).units i)) =
      DirectPrefix.latest key (((slots run).take
        (n * g.unitsPerPrefix * g.unitEntries)).map Slot.record)

/-- Every trace cut represents a supplied logical prefix, including cuts in
its empty tail. Saturation stops at the final frozen unit, not the final map
when the requester still has a partial current unit. -/
def RequesterTraceSaturatedCuts_statement : Prop :=
  ∀ (g : OnlineGeom) (run : BatchRun), 0 < g.unitEntries →
    WidthsFit g.unitEntries 0 (widths run) → ∀ n,
    traceCutSlots g run n ≤ (slots run).length ∧ ∀ key,
    DirectPrefix.latest key ((List.range n).flatMap
      fun i => DirectMasks.records ((traceOf g run).units i)) =
      DirectPrefix.latest key
        (((slots run).take (traceCutSlots g run n)).map Slot.record)

/-- Public request groups transfer their boundary guarantee through physical
postrecord construction. No selected-record or flag correctness is assumed. -/
def RequesterLoweredFits_statement : Prop :=
  ∀ (c : Api.Codec) cfg sh (g : OnlineGeom) S init
    (groups : List (PublicApi.Group Api.Request)),
    0 < g.unitEntries → PublicApi.GroupsFit g.unitEntries 0 groups →
    WidthsFit g.unitEntries 0
      (widths (ApiExecution.run c cfg sh g S init groups))

end RebuildBound.Spec
