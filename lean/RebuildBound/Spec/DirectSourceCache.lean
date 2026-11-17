import RebuildBound.Spec.Model.DirectSourceCache
import RebuildBound.Spec.DirectAddresses
import RebuildBound.Spec.DirectCache

namespace RebuildBound.Spec
open Model Model.DirectSourceCache

/-- A valid dense winner's original-source cache encodes its logical home. -/
def DirectSourceCacheEncoding_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ∀ (word : LogicalKey → Nat) (bits i : Nat),
      i < (DirectRecords.source (DirectMasks.records units)).length →
      DirectCache.Encodes bits
        (cache word bits units (DirectMasks.run compare [] units) i)
        (DirectRecords.home (DirectMasks.records units) word (2 ^ bits) i)

/-- Byte comparisons and the logical per-home candidate filter agree for any
chunks of valid survivor indices, including subsets left after earlier clears. -/
def DirectSourceCacheCandidates_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ∀ (word : LogicalKey → Nat) (bits home : Nat) (chunks : List (List Nat)),
      home < 2 ^ bits →
      (∀ i ∈ chunks.flatten, i < (DirectRecords.source (DirectMasks.records units)).length) →
      candidates compare bits word units home chunks =
        DirectScan.candidates (DirectRecords.home (DirectMasks.records units) word (2 ^ bits))
          home chunks

/-- Scanning the source-cache candidates restores the exact stable prefix of
chronological winners at the requested home, for any selection capacity. -/
def DirectSourceCacheSelected_statement : Prop :=
  ∀ (compare : DirectMasks.Comparison) (units : List Bucket),
    DirectMasks.ExactComparison compare →
    (∀ unit ∈ units, (unit.recs.map Rec.key).Nodup) →
    ∀ (word : LogicalKey → Nat) (bits home cap : Nat), home < 2 ^ bits →
      ((DirectScan.run cap (candidates compare bits word units home
        (DirectMaskedRecords.chunks (DirectMasks.run compare [] units)))).selected.map
          (DirectRecords.record (DirectMasks.records units))) =
      ((DirectPrefix.winners (DirectMasks.records units)).filter
        (fun r => DirectPrefix.cachedHome word (2 ^ bits) r == home)).take cap

end RebuildBound.Spec
