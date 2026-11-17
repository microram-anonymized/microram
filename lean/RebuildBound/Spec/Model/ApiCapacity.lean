import RebuildBound.Spec.Model.Api

/-! Explicit finite support for the existing independent API map. Support is
computed from initial keys and requested keys, then filtered by the logical
state; it is not inferred from physical record populations. Records and requests
use exact byte-string logical keys. -/
namespace RebuildBound.Model.ApiCapacity
open Api

/-- A finite, exact support witness. Zero payloads are live values. -/
def Supports (state : State) (keys : List LogicalKey) : Prop :=
  keys.Nodup ∧ ∀ key, key ∈ keys ↔ (state key).isSome = true

/-- Executable support extraction from a finite list of candidate keys. -/
def support (keys : List LogicalKey) (state : State) : List LogicalKey :=
  keys.eraseDups.filter fun key => (state key).isSome

/-- Candidate keys grow with history; the live support need not grow. -/
def supportAt (initial : State) (initialKeys : List LogicalKey)
    (requests : List Request) (t : Nat) : List LogicalKey :=
  support (initialKeys ++ (requests.take t).map Request.key)
    (stateAt initial requests t)

/-- Initialization counts supplied records, including any low-level tombstones.
The API initialization contract chooses live-only records. -/
def InitialStateValid (capacity : Nat) (initialized : Bool) (init : List Rec) : Prop :=
  (init.map Rec.key).Nodup ∧ init.length ≤ capacity ∧
    (∀ r ∈ init, r.tomb = false) ∧ (initialized = false → init = [])

/-- Capacity holds after every lane prefix, including the initial map. -/
def LiveCapacity (capacity : Nat) (initial : State) (initialKeys : List LogicalKey)
    (requests : List Request) : Prop :=
  Supports initial initialKeys ∧
    ∀ t, t ≤ requests.length → (supportAt initial initialKeys requests t).length ≤ capacity

/-- Resolve newest records before removing tombstones. Reversing that order
would resurrect an older live value. -/
def liveRecords (history : List Rec) : List Rec :=
  (DirectPrefix.winners history).filter fun r => !r.tomb

/-- A canonical logical continuation beyond a finite requested horizon. Reads
preserve the final map even when the chosen key is absent. -/
def idleExtend (requests : List Request) (extra : Nat) : List Request :=
  requests ++ List.replicate extra ⟨[], .read⟩

end RebuildBound.Model.ApiCapacity
