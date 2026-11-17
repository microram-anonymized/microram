import RebuildBound.Spec.Model.DirectCapacity
/-! Stable per-home selection of already deduplicated home lists.
Native chronological grouping, exact-key correspondence and probability
premises remain separate obligations. -/
namespace RebuildBound.Model.DirectB

def main (cap : Nat) (homes : List (List Nat)) : List (List Nat) :=
  homes.map (List.take cap)
def residual (cap : Nat) (homes : List (List Nat)) : List Nat :=
  (homes.map (List.drop cap)).flatten
def excess (cap : Nat) (homes : List (List Nat)) : Nat :=
  (homes.map (fun xs => xs.length - cap)).sum
def finalHome (word U stride radix : Nat) : Nat :=
  word % (U * stride) + (U * stride) * ((word / (U * stride)) % radix)
end RebuildBound.Model.DirectB
