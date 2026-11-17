import RebuildBound.Spec.Model.DirectAddresses
import RebuildBound.Spec.DirectMaskedRecords

namespace RebuildBound.Spec
open Model Model.DirectAddresses

/-- No grouped-unit/lane position is enumerated twice. -/
def DirectAddressesUnique_statement : Prop :=
  ∀ units : List Bucket, (chunks units).flatten.Nodup

/-- Mask survivors read back their entire payload at the original source
address. This holds for arbitrary comparisons and arbitrary resume states. -/
def DirectAddressesRestore_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (state units : List Bucket),
    (chunks (DirectMasks.run compare state units)).map
      (List.map (lookup (state ++ units))) =
      (DirectMasks.run compare state units).map (fun bucket => bucket.recs.map some)

/-- Dense survivor numbering and source-address enumeration agree per unit. -/
def DirectAddressesChunks_statement : Prop :=
  ∀ masked : List Bucket,
    (DirectMaskedRecords.chunks masked).map (List.map (address masked)) = chunks masked

/-- Every valid logical winner index denotes its original source record. -/
def DirectAddressesDense_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ∀ i, i < (DirectRecords.source (DirectMasks.records units)).length →
      lookup units (address (DirectMasks.run compare [] units) i) =
        some (DirectRecords.record (DirectMasks.records units) i)

/-- Original source addresses restore exactly the chronological winners,
including tombstones, in source order. -/
def DirectAddressesWinners_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ((chunks (DirectMasks.run compare [] units)).flatten.map (lookup units)) =
      (DirectPrefix.winners (DirectMasks.records units)).map some

/-- Computing a home from the original source payload agrees with the logical
producer's home under the same routing-word family. -/
def DirectAddressesHome_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ∀ (word : LogicalKey → Nat) (U i : Nat),
      i < (DirectRecords.source (DirectMasks.records units)).length →
      (lookup units (address (DirectMasks.run compare [] units) i)).map
        (DirectPrefix.cachedHome word U) =
        some (DirectRecords.home (DirectMasks.records units) word U i)

end RebuildBound.Spec
