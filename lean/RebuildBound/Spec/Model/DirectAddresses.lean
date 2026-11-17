import RebuildBound.Spec.Model.DirectMaskedRecords

/-! Source unit/lane addresses for chronological mask survivors. These are
addresses in the abstract grouped-unit input, not native pointers or decoded
multi-bucket offsets. Absent lanes still occupy positions. The enumeration
bridges dense winner indices to these source addresses without moving payloads.
Native layout, scheduler, cache bytes and SIMD correspondence remain separate. -/
namespace RebuildBound.Model.DirectAddresses

abbrev Address := Nat × Nat

/-- Occupied lane addresses in ascending lane order. -/
def lanes (unit : Nat) (bucket : Bucket) : List Address :=
  ((List.range bucket.length).filter (fun lane => bucket[lane]!.isSome)).map
    (fun lane => (unit, lane))

/-- One address chunk per input unit, including empty and cleared units. -/
def chunksFrom (unit : Nat) : List Bucket → List (List Address)
  | [] => []
  | bucket :: rest => lanes unit bucket :: chunksFrom (unit + 1) rest

def chunks (units : List Bucket) : List (List Address) := chunksFrom 0 units

/-- Checked source access: invalid addresses and absent lanes yield none. -/
def lookup (units : List Bucket) (address : Address) : Option Rec :=
  (units[address.1]?.bind (fun bucket => bucket[address.2]?)).bind id

/-- Dense survivor index to original grouped-unit/lane address. The default is
unreachable under the proved bounds; it is not a valid-address assertion. -/
def address (masked : List Bucket) (i : Nat) : Address :=
  (chunks masked).flatten[i]!

end RebuildBound.Model.DirectAddresses
