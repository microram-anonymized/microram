import RebuildBound.Spec.Model.Api

/-!
# Normalized hierarchy callback Access semantics

A callback is a pure function of the prior payload (zero on absence) and the
original presence bit. Its result abstracts either normal completion with a
key/value pair or an exception. Keys are exact stored keys and payloads are
codec identities. Native callback side effects, reentrancy, buffer lifetimes,
and byte/key encoding are separate refinement obligations.

The public callback signature determines `Mode`. Value-only success inserts
one probed write. A mutable-key success always erases the source and then blindly
upserts the destination, including when the two keys are equal. An exception
restores the original source through a Read, without a destination write.
-/
namespace RebuildBound.Model.ApiAccess
open Api

inductive Mode where
  | valueOnly
  | mutableKey
  deriving DecidableEq, BEq, Repr

inductive Outcome where
  | success (key : LogicalKey) (value : Nat)
  | exception
  deriving DecidableEq, BEq, Repr

structure Request where
  key : LogicalKey
  mode : Mode
  callback : Nat → Bool → Outcome

/-- The callback receives the original presence separately from its zero-filled
payload input; a present zero and a missing key remain distinguishable. -/
def evaluate (q : Request) (old : Option Nat) : Outcome :=
  q.callback (Api.output old) (Api.present old)

inductive Response where
  | returned (originalPresence : Bool)
  | exception
  deriving DecidableEq, BEq, Repr

def response (q : Request) (old : Option Nat) : Response :=
  match evaluate q old with
  | .success _ _ => .returned (Api.present old)
  | .exception => .exception

/-- Independent map semantics; a destination collision is an overwrite. -/
def step (q : Request) (state : Api.State) : Api.State :=
  match evaluate q (state q.key) with
  | .exception => state
  | .success destination payload =>
    match q.mode with
    | .valueOnly => fun key => if key = q.key then some payload else state key
    | .mutableKey => fun key =>
        if key = destination then some payload else if key = q.key then none else state key

/-- The first lowered access always probes the source. -/
def first (q : Request) (old : Option Nat) : Api.Request :=
  ⟨q.key, match evaluate q old with
    | .exception => .read
    | .success _ payload => match q.mode with
      | .valueOnly => .write payload
      | .mutableKey => .erase⟩

/-- Key-capable callbacks retain the second write even when the key is unchanged. -/
def rest (q : Request) (old : Option Nat) : List Api.Request :=
  match evaluate q old, q.mode with
  | .success destination payload, .mutableKey => [⟨destination, .blindWrite payload⟩]
  | _, _ => []

def lower (q : Request) (old : Option Nat) : List Api.Request :=
  first q old :: rest q old

end RebuildBound.Model.ApiAccess
