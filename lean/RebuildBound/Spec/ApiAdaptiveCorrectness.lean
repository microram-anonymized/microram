import RebuildBound.Spec.ApiAdaptive

/-! Request-driven adaptive API correctness in the structural universe
model. The public compiler derives implementation equations and flags; these
are conclusions, not assumptions on an adversarial supplied-record client.
The fixed-universe hypothesis is stated explicitly;
ApiAdaptiveStructural provides the universe-free endpoint. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online Model.ApiAdaptive

def ApiAdaptiveCorrectness_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (U : Finset LogicalKey) (c : Api.Codec) g S init m width batches (choose : Chooser m),
    let fs := frames width g.unitEntries batches
    let n := Adaptive.slotCount (shape fs)
    (geo.cfg.initialized = false → init = []) →
    (∀ k ∈ U, k.toNat < 2 ^ 64) → U.card ≤ geo.keyCapacity →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon →
    (init.map Rec.key).Nodup → (∀ r ∈ init, r.key ∈ U) →
    (∀ (t : Fin n → Fin m → Nat),
      ∀ q ∈ (requestGroups choose (Adaptive.rowsOf t n) fs).flatMap PublicApi.Group.lanes,
        q.key ∈ U) →
    SchedulePremises geo.cfg S n m →
    let a := run c geo.cfg geo.shapes g S init fs choose
    AdaptiveSetting geo U g a S n ∧
    ∀ words dummy,
      let t := Adaptive.transcript geo.cfg geo.shapes g S a n words dummy
      let qs := (requestGroups choose (Adaptive.rowsOf t n) fs).flatMap PublicApi.Group.lanes
      let realized := Adaptive.realized geo.cfg geo.shapes g S a words dummy
      Api.Implements c geo.cfg geo.shapes g realized S words dummy qs ∧
      ApiCorrect c geo.cfg geo.shapes g realized S words dummy qs

end RebuildBound.Spec
