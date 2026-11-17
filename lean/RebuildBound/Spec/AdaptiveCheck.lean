import RebuildBound.Spec.Adaptive.Semantics

/-!
# A check of the adaptive model against fixed runs (not a claim)

Outside the headline
closure: no headline statement references it. It states that the adaptive
model specializes to the fixed-run batch model, so the headline theorems
specialize to the fixed-run ones (C3) at the shape's slot count.
-/

namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.Adaptive

/-- **AdaptiveConstant** (a check of the model, not a claim). The simulator's
public shape is that of every run the client can issue. A client that reads
only how many rows it has seen issues one fixed run, whose view, failure
event and setting are then the transcript, `AdaptiveFails` and
`AdaptiveSetting`. Every fixed run is issued by such a client. -/
def AdaptiveConstant_statement : Prop :=
  (∀ m (a : AdaptiveRun m) n (t : Fin n → Fin m → Nat),
    shapeWidths a.shape = OnlineBatch.widths (replay a t) ∧
      shapePattern a.shape = OnlineBatch.probePattern (replay a t)) ∧
  (∀ (geo : HierarchyGeometry) U g m (a : AdaptiveRun m) S n (t₀ : Fin n → Fin m → Nat),
    (∀ rows rows' : List (Fin m → Nat), rows.length = rows'.length →
      a.client rows = a.client rows') →
    (AdaptiveSetting geo U g a S n ↔
      n = slotCount a.shape ∧ UniverseBatchSetting geo U g (replay a t₀) S n m) ∧
    ∀ words dummy,
      realized geo.cfg geo.shapes g S a words dummy = replay a t₀ ∧
      (AdaptiveFails geo.cfg geo.shapes g S a words dummy ↔
        Fails geo.cfg geo.shapes (OnlineBatch.traceOf g (replay a t₀)) words) ∧
      (AdaptiveSetting geo U g a S n →
        transcript geo.cfg geo.shapes g S a n words dummy =
          OnlineBatch.view geo.cfg geo.shapes g (replay a t₀) S n m words dummy)) ∧
  ∀ m n (run : OnlineBatch.BatchRun), ∃ a : AdaptiveRun m,
    (∀ rows rows' : List (Fin m → Nat), rows.length = rows'.length →
      a.client rows = a.client rows') ∧
    ∀ t : Fin n → Fin m → Nat, replay a t = run

end RebuildBound.Spec
