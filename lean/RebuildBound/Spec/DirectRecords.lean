import RebuildBound.Spec.Model.DirectRecords
import RebuildBound.Spec.DirectProducer
import RebuildBound.Spec.DirectPrefix

namespace RebuildBound.Spec
open Model Model.DirectRecords

/-- Index restoration preserves complete records, including tombstones. -/
def DirectRecordsSource_statement : Prop :=
  ∀ rs : List Rec, (source rs).map (record rs) = DirectPrefix.winners rs

def DirectRecordsFailure_statement : Prop :=
  ∀ (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (chunks : List (List Nat)),
    0 < U → ValidChunks rs chunks →
    (build digit output U word rs chunks = none ↔
      DirectDrain.tierCapacity digit output <
        DirectB.excess 64 (DirectGroups.groups U (home rs word U) (source rs)))

/-- Successful output conserves precisely the newest complete records, has
unique keys, answers every key lookup as the original chronology does, and
has the exact total-excess tier occupancy. No probability premise is used. -/
def DirectRecordsSuccess_statement : Prop :=
  ∀ (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (chunks : List (List Nat)) (main : List (List Rec)) (tier : List Rec),
    0 < U → ValidChunks rs chunks →
    build digit output U word rs chunks = some (main, tier) →
    (main.flatten ++ tier).Perm (DirectPrefix.winners rs) ∧
    ((main.flatten ++ tier).map Rec.key).Nodup ∧
    (∀ key, (main.flatten ++ tier).find? (fun r => r.key == key) =
      DirectPrefix.latest key rs) ∧
    tier.length = DirectB.excess 64
      (DirectGroups.groups U (home rs word U) (source rs)) ∧
    tier.length ≤ DirectDrain.tierCapacity digit output

/-- Exact stable per-home main contents, expressed in records rather than indices. -/
def DirectRecordsMain_statement : Prop :=
  ∀ (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (chunks : List (List Nat)) (main : List (List Rec)) (tier : List Rec),
    0 < U → ValidChunks rs chunks →
    build digit output U word rs chunks = some (main, tier) →
    main = (List.range U).map (fun h =>
      ((DirectPrefix.winners rs).filter
        (fun r => DirectPrefix.cachedHome word U r == h)).take 64)

/-- Changing source chunk boundaries does not change the restored result. -/
def DirectRecordsRechunk_statement : Prop :=
  ∀ (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (first second : List (List Nat)),
    first.flatten = second.flatten →
    build digit output U word rs first = build digit output U word rs second

end RebuildBound.Spec
