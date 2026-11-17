import RebuildBound.Spec.ApiStructural

/-! One real probe per hash family and key, for request runs with arbitrary
byte keys. The statement is deterministic: it holds for every choice of the
words and of the dummy tape, under the premises of
`ApiAdaptiveStructural_statement`. It has no key universe, no bound on the
number of distinct keys, and no live-capacity or probability premise. -/
namespace RebuildBound.Spec
open Model Model.Hierarchy Model.Online

/-- In the realized run of an adaptive API client, two different real probes
never have the same hash family and the same key. A probe is a slot `t`, which
is one lane of a request batch, together with a position `i` in the table plan
of that slot. It is real when `isReal` holds there and a dummy otherwise.
`familyOf` gives the coordinate whose word function routes a table, so tables
under the same hash have the same `familyOf`. -/
def IdealApiFresh_statement : Prop :=
  ∀ (geo : HierarchyGeometry), geo.Structural →
    ∀ (c : Api.Codec) g S init m width batches,
    let fs := ApiAdaptive.frames width g.unitEntries batches
    ∀ choose : ApiAdaptive.Chooser m,
    let n := Adaptive.slotCount (ApiAdaptive.shape fs)
    (geo.cfg.initialized = false → init = []) →
    (init.map Rec.key).Nodup → init.length ≤ geo.init.C / 2 * geo.init.T →
    g.unitEntries * g.unitsPerPrefix = geo.cfg.carryPositions 1 →
    0 < g.unitEntries → n ≤ geo.cfg.horizon → SchedulePremises geo.cfg S n m →
    ∀ (words : Words) (dummy : Nat → Nat → Nat),
    let a := ApiAdaptive.run c geo.cfg geo.shapes g S init fs choose
    let run := Adaptive.realized geo.cfg geo.shapes g S a words dummy
    ∀ t i t' i' c₁ c₂ s₁ s₂, t < n → i < m → t' < n → i' < m → (t, i) ≠ (t', i') →
      OnlineBatch.isReal geo.cfg geo.shapes g run S words t i = true →
      OnlineBatch.isReal geo.cfg geo.shapes g run S words t' i' = true →
      (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t).tables[i]? = some c₁ →
      (OnlineBatch.slotSchedule (OnlineBatch.widths run) S t').tables[i']? = some c₂ →
      (OnlineBatch.slots run)[t]? = some s₁ → (OnlineBatch.slots run)[t']? = some s₂ →
      (familyOf geo.cfg c₁.1 c₁.2, s₁.record.key) ≠ (familyOf geo.cfg c₂.1 c₂.2, s₂.record.key)

end RebuildBound.Spec
