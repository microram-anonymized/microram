import RebuildBound.Spec.Model.DirectMasks
import RebuildBound.Spec.Model.DirectRecords

/-! Construct the logical producer's occurrence chunks from surviving mask
lanes. Each mask unit contributes one chunk, including empty units. Indices
number surviving records densely in source order; they are not native lane
addresses. A unit may abstract an entire multi-bucket native flush unit. The restoration theorem relates them back to the unit payloads.
Native pair scheduling, cached bytes, pdep and publication are not extracted. -/
namespace RebuildBound.Model.DirectMaskedRecords

/-- Consecutive occurrence indices, retaining the supplied chunk lengths. -/
def indexChunks (start : Nat) : List Nat → List (List Nat)
  | [] => []
  | n :: ns => List.range' start n :: indexChunks (start + n) ns

/-- Number the surviving real lanes, keeping each source unit's boundary. -/
def chunks (masked : List Bucket) : List (List Nat) :=
  indexChunks 0 (masked.map (fun b => b.recs.length))

/-- Chronological mask dedup followed by checked direct record production.
The same word family determines every home. Digit one uses the configured
output tier; all other digits use a separate 64-record producer tier. -/
def build (compare : DirectMasks.Comparison) (digit output U : Nat)
    (word : LogicalKey → Nat) (units : List Bucket) :
    Option (List (List Rec) × List Rec) :=
  DirectRecords.build digit output U word (DirectMasks.records units)
    (chunks (DirectMasks.run compare [] units))

end RebuildBound.Model.DirectMaskedRecords
