import RebuildBound.Spec.Model.DirectPrefix
import Mathlib.Data.List.Nodup

namespace RebuildBound.Spec
open Model Model.DirectPrefix

def DirectPrefixUnique_statement : Prop :=
  ∀ rs : List Rec, ((winners rs).map Rec.key).Nodup

def DirectPrefixKeys_statement : Prop :=
  ∀ (rs : List Rec) (key : LogicalKey),
    key ∈ (winners rs).map Rec.key ↔ key ∈ rs.map Rec.key

def DirectPrefixStable_statement : Prop :=
  ∀ rs : List Rec, (winners rs).Sublist rs

def DirectPrefixLatest_statement : Prop :=
  ∀ (rs : List Rec) (key : LogicalKey),
    (winners rs).find? (fun r => r.key == key) = latest key rs

/-- Appending a fresher prefix removes all shadowed older winners, even if
the fresh record is a tombstone. This also describes chronological chunking. -/
def DirectPrefixAppend_statement : Prop :=
  ∀ older newer : List Rec,
    winners (older ++ newer) =
      (winners older).filter (fun r => r.key ∉ newer.map Rec.key) ++ winners newer

def DirectPrefixUnits_statement : Prop :=
  ∀ (older : List Rec) (units : List (List Rec)),
    (∀ unit ∈ units, (unit.map Rec.key).Nodup) →
    runUnits (winners older) units = winners (older ++ units.flatten)

def DirectPrefixHome_statement : Prop :=
  ∀ (word : LogicalKey → Nat) (U : Nat) (r s : Rec),
    (0 < U → cachedHome word U r < U) ∧
    (r.key = s.key → cachedHome word U r = cachedHome word U s)

end RebuildBound.Spec
