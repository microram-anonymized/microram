import RebuildBound.Spec.Model.ApiCapacity

/-! Finite logical support and the bridge from decoded snapshots to record
counts. These contracts have no key universe, key range or physical success
premise; records and requests carry exact logical byte keys. -/
namespace RebuildBound.Spec
open Model Model.Api Model.ApiCapacity

def ApiFiniteSupport_statement : Prop :=
  ∀ initial initialKeys requests, Supports initial initialKeys →
    ∀ t, Supports (stateAt initial requests t) (supportAt initial initialKeys requests t)

def ApiSupportStep_statement : Prop :=
  ∀ state keys, Supports state keys → ∀ q,
    let next := step q state
    let nextKeys := support (q.key :: keys) next
    Supports next nextKeys ∧
      nextKeys.length = keys.length - (if (state q.key).isSome then 1 else 0) +
        (if (nextValue q (state q.key)).isSome then 1 else 0)

/-- Initialization has an exact finite map whose count is the supplied count. -/
def ApiInitialCapacity_statement : Prop :=
  ∀ capacity initialized init, InitialStateValid capacity initialized init →
    ∀ c : Codec, Supports (stateOf c init) (init.map Rec.key) ∧
      LiveCapacity capacity (stateOf c init) (init.map Rec.key) []

/-- Unique live snapshots can be counted from their logical map. Without the
uniqueness and live-only hypotheses, map equality does not bound storage. -/
def ApiSnapshotPopulation_statement : Prop :=
  ∀ (c : Codec) initial initialKeys requests t records,
    Supports initial initialKeys → (records.map Rec.key).Nodup →
    (∀ r ∈ records, r.tomb = false) →
    stateOf c records = stateAt initial requests t →
    records.length = (supportAt initial initialKeys requests t).length

/-- Resolved history is unique and live-only, with exactly the original map. -/
def ApiResolvedHistory_statement : Prop :=
  ∀ (c : Codec) history,
    ((liveRecords history).map Rec.key).Nodup ∧
      (∀ r ∈ liveRecords history, r.tomb = false) ∧
      stateOf c (liveRecords history) = stateOf c history

/-- The logical prefix contract supplies the population bound, including after
reference overflow. This is a transfer lemma, not hierarchy applicability. -/
def ApiLivePopulation_statement : Prop :=
  ∀ capacity (c : Codec) initial initialKeys requests t history,
    LiveCapacity capacity initial initialKeys requests → t ≤ requests.length →
    stateOf c history = stateAt initial requests t →
    (liveRecords history).length ≤ capacity

/-- Arbitrarily many distinct misses need no positive live capacity. -/
def ApiMissCapacity_statement : Prop :=
  ∀ keys : List LogicalKey,
    LiveCapacity 0 (fun _ => none) [] (keys.map fun key => (⟨key, .read⟩ : Request))

/-- Arbitrarily many insert/erase pairs need only one live entry. Historical
key count and numeric key magnitudes are unrestricted. -/
def ApiChurnCapacity_statement : Prop :=
  ∀ (keys : List LogicalKey) value,
    LiveCapacity 1 (fun _ => none) []
      (keys.flatMap fun key => [(⟨key, .write value⟩ : Request), ⟨key, .erase⟩])

/-- Canonical idle extension preserves every original prefix and the final
map, and therefore preserves live capacity. Physical horizon/schedule extension
is a separate execution obligation. -/
def ApiCapacityExtension_statement : Prop :=
  ∀ capacity initial initialKeys requests extra,
    LiveCapacity capacity initial initialKeys requests →
    LiveCapacity capacity initial initialKeys (idleExtend requests extra) ∧
      (∀ t, t ≤ requests.length →
        stateAt initial (idleExtend requests extra) t = stateAt initial requests t) ∧
      (∀ t, requests.length ≤ t →
        stateAt initial (idleExtend requests extra) t =
          stateAt initial requests requests.length)

end RebuildBound.Spec
