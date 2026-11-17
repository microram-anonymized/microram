import RebuildBound.Spec.Model.Adaptive

/-!
# Causal public observations and a record-issuing program

This is an abstract native interface, not a semantics of C++ instructions.
A program already computes each lane's **post-operation record**. Computing
that record from requests, effective selected entries (including forwarded
postrecords and flags), and API responses is a separate adapter obligation.

`metadata` must include the entire fixed public API schedule: scalar/batch
boundaries, lane operation kinds, Exchange's insert flag, and value/presence
output descriptors that determine blind writes and chunk boundaries. Callback
mode and completion shape must also be fixed; secret-dependent exceptions or
callback instruction traces are not hidden by the bucket-view theorem. It is shared
by compared programs, as is the encoding. The encoder receives only the
rows already observed. It may retain all of them, so arbitrary deterministic
causal prefix encodings fit; it cannot inspect either random tape.
-/
namespace RebuildBound.Model.NativeAdapter

open Hierarchy Online Adaptive

/-- An arbitrary causal observation of a row prefix and fixed public metadata. -/
abbrev Encoding (m : Nat) (Public View : Type) := Public → List (Fin m → Nat) → View

/-- A deterministic program choosing postrecords from its public observations.
Private inputs may be closed over by `next`; neither tape is an argument. -/
structure Program (View : Type) where
  shape : List Kind
  init : List Rec
  unsh : Rec → Bool
  next : View → Nat → Rec

/-- Fold the causal public encoding into the adaptive client. -/
def Program.folded {m : Nat} {Public View : Type} (p : Program View)
    (encode : Encoding m Public View) (metadata : Public) : AdaptiveRun m :=
  ⟨p.shape, p.init, p.unsh, fun rows => p.next (encode metadata rows)⟩

/-- An opaque execution state, its public observation, and one operation step.
The implementation of this interface remains outside the Lean model. For a
full native obliviousness claim, `observe` must contain the entire accumulated
adversary-visible trace, including within-step events. A projection into a
smaller `View` certifies only that projection, not omitted instruction,
address, or timing observations. -/
structure Machine (State View : Type) where
  initial : State
  observe : State → View
  step : State → OnlineBatch.Op → State

/-- The machine issues the program's next operation from its actual current
observation. The separately maintained operation list is a proof witness. -/
def Machine.issue {State View : Type} (M : Machine State View) (p : Program View)
    (acc : List OnlineBatch.Op × State) (k : Kind) : List OnlineBatch.Op × State :=
  let op := k.op (p.next (M.observe acc.2))
  (acc.1 ++ [op], M.step acc.2 op)

/-- Execution through the given public operation prefix. -/
def Machine.prefix {State View : Type} (M : Machine State View) (p : Program View)
    (ks : List Kind) : List OnlineBatch.Op × State :=
  ks.foldl (M.issue p) ([], M.initial)

/-- The machine's final public observation. -/
def Machine.observation {State View : Type} (M : Machine State View) (p : Program View) : View :=
  M.observe (M.prefix p p.shape).2

/-- Reference operations and rows through a public operation prefix. -/
def referencePrefix (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule)
    {m : Nat} {Public View : Type} (p : Program View) (encode : Encoding m Public View)
    (metadata : Public) (words : Words) (dummy : Nat → Nat → Nat) (ks : List Kind) :
    List OnlineBatch.Op × List (Fin m → Nat) :=
  ks.foldl (Adaptive.issue cfg sh g S (p.folded encode metadata) words dummy) ([], [])

/-- The same public encoding applied to the complete finite transcript. -/
def transcriptEncoding {n m : Nat} {Public View : Type} (encode : Encoding m Public View)
    (metadata : Public) (t : Fin n → Fin m → Nat) : View :=
  encode metadata (rowsOf t n)

end RebuildBound.Model.NativeAdapter
