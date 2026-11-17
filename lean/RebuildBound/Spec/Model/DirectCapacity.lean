import Init
/-! Shared executable capacity policy for the direct producer and checked drain. -/
namespace RebuildBound.Model.DirectCapacity
/-- Digit one uses the configured output tier; later digits use the producer bucket. -/
def producerCapacity (digit cap output : Nat) : Nat :=
  if digit = 1 then output else cap
end RebuildBound.Model.DirectCapacity
