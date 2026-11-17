import RebuildBound.Spec.Model.DirectMaskedRecords
import RebuildBound.Spec.DirectRecords
import RebuildBound.Spec.DirectMasks

namespace RebuildBound.Spec
open Model Model.DirectMaskedRecords

/-- Constructed chunks satisfy the producer's enumeration premise. -/
def DirectMaskedRecordsValid_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    DirectRecords.ValidChunks (DirectMasks.records units)
      (chunks (DirectMasks.run compare [] units))

/-- Restoring each index chunk recovers precisely that surviving unit's full
records, in lane order. Empty chunks and tombstones are retained. -/
def DirectMaskedRecordsRestore_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    (chunks (DirectMasks.run compare [] units)).map
      (List.map (DirectRecords.record (DirectMasks.records units))) =
      (DirectMasks.run compare [] units).map Bucket.recs

def DirectMaskedRecordsFailure_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : LogicalKey → Nat) (units : List Bucket),
    0 < U → DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    (build compare digit output U word units = none ↔
      DirectDrain.tierCapacity digit output < DirectB.excess 64
        (DirectGroups.groups U (DirectRecords.home (DirectMasks.records units) word U)
          (DirectRecords.source (DirectMasks.records units))))

def DirectMaskedRecordsSuccess_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : LogicalKey → Nat) (units : List Bucket) (main : List (List Rec)) (tier : List Rec),
    0 < U → DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    build compare digit output U word units = some (main, tier) →
    (main.flatten ++ tier).Perm (DirectPrefix.winners (DirectMasks.records units)) ∧
    ((main.flatten ++ tier).map Rec.key).Nodup ∧
    (∀ key, (main.flatten ++ tier).find? (fun r => r.key == key) =
      DirectPrefix.latest key (DirectMasks.records units)) ∧
    tier.length = DirectB.excess 64
      (DirectGroups.groups U (DirectRecords.home (DirectMasks.records units) word U)
        (DirectRecords.source (DirectMasks.records units))) ∧
    tier.length ≤ DirectDrain.tierCapacity digit output

def DirectMaskedRecordsMain_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : LogicalKey → Nat) (units : List Bucket) (main : List (List Rec)) (tier : List Rec),
    0 < U → DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    build compare digit output U word units = some (main, tier) →
    main = (List.range U).map (fun h =>
      ((DirectPrefix.winners (DirectMasks.records units)).filter
        (fun r => DirectPrefix.cachedHome word U r == h)).take 64)

/-- Changing unit boundaries preserves the result provided each new unit
still has unique keys. Without that premise the mask pass skips duplicates. -/
def DirectMaskedRecordsRechunk_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : LogicalKey → Nat) (first second : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ first, (unit.recs.map Rec.key).Nodup) →
    (∀ unit ∈ second, (unit.recs.map Rec.key).Nodup) →
    DirectMasks.records first = DirectMasks.records second →
    build compare digit output U word first = build compare digit output U word second

end RebuildBound.Spec
