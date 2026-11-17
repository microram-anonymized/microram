import RebuildBound.Spec.Model.DirectPrefix
import RebuildBound.Spec.Model.DirectProducer

/-! Restore full chronological winner records after the finite direct producer.
Indices enumerate logical winners in source order; they are not native lane
addresses. A valid chunking contains exactly these indices in order. The total
lookup below has a default only to keep the executable model nondependent;
valid chunking and producer conservation exclude out-of-range output indices.
This is a logical composition, not a native masks/cache/SIMD extraction. -/
namespace RebuildBound.Model.DirectRecords

/-- Positions in the winner list, after exact-key chronological deduplication. -/
def source (rs : List Rec) : List Nat :=
  List.range (DirectPrefix.winners rs).length

def record (rs : List Rec) (i : Nat) : Rec :=
  (DirectPrefix.winners rs)[i]!

def home (rs : List Rec) (word : LogicalKey → Nat) (U i : Nat) : Nat :=
  DirectPrefix.cachedHome word U (record rs i)

/-- Empty chunks are allowed; missing, repeated or reordered indices are not. -/
def ValidChunks (rs : List Rec) (chunks : List (List Nat)) : Prop :=
  chunks.flatten = source rs

def restore (rs : List Rec) (result : List (List Nat) × List Nat) :
    List (List Rec) × List Rec :=
  (result.1.map (List.map (record rs)), result.2.map (record rs))

def build (digit output U : Nat) (word : LogicalKey → Nat) (rs : List Rec)
    (chunks : List (List Nat)) : Option (List (List Rec) × List Rec) :=
  (DirectProducer.build digit output U (home rs word U) chunks).map (restore rs)

end RebuildBound.Model.DirectRecords
