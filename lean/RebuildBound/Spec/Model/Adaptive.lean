import RebuildBound.Spec.Model.OnlineBatch

/-!
# Adaptive clients (trusted model)

The batch model (`Spec/Model/OnlineBatch.lean`) with
records chosen by a deterministic client from the buckets touched so far:
it has no other input, so it reads no word of either tape (a randomized
client whose coins are independent of the tapes is a mixture of deterministic
ones, and every bound is uniform in the client). The probe plans, and so the
schedule, are decided by the program, not the client; the public shape
(which operations probe, the chunk widths) is fixed with the schedule. Only
the records are adaptive, and letting the client choose whole records (key,
value, tombstone and unshadowed bits) also covers the program's own
computation of them. Each operation's rows are `touched` on
the run issued so far, so the interaction is causal by construction.
-/

namespace RebuildBound.Model.Adaptive

open Hierarchy Online OnlineBatch

/-- The public kind of one operation. -/
inductive Kind where
  /-- A scalar Read, Write, Erase or Exchange. -/
  | probe
  /-- A scalar `WriteWithoutProbe`. -/
  | blind
  /-- One chunk of `w` lanes. -/
  | chunk (w : Nat)
  deriving DecidableEq, Repr

/-- The lane count of an operation of this kind. -/
def Kind.width : Kind → Nat
  | .probe => 1
  | .blind => 1
  | .chunk w => w

/-- Whether an operation of this kind probes. -/
def Kind.probes : Kind → Bool
  | .blind => false
  | _ => true

/-- The operation of this kind whose lane `i` inserts `rec i`. -/
def Kind.op (k : Kind) (rec : Nat → Rec) : OnlineBatch.Op :=
  match k with
  | .probe => .probe (rec 0)
  | .blind => .blind (rec 0)
  | .chunk w => .batch ((List.range w).map rec)

/-- A client for plans of at most `m` tables: the record of lane `i` of the
next operation from the rows of the earlier operations' slots, oldest first. -/
abbrev Client (m : Nat) : Type := List (Fin m → Nat) → Nat → Rec

/-- An adaptive run: the public shape, the initialization's input, the
unshadowed flag of a record and the client. -/
structure AdaptiveRun (m : Nat) where
  shape : List Kind
  init : List Rec
  unsh : Rec → Bool
  client : Client m

/-- The shape's lane counts. -/
def shapeWidths (shape : List Kind) : List Nat := shape.map Kind.width

/-- The shape's number of slots. -/
def slotCount (shape : List Kind) : Nat := (shapeWidths shape).sum

/-- Whether slot `t` probes, from the public kinds. -/
def shapePattern (shape : List Kind) (t : Nat) : Bool :=
  ((shape.flatMap fun k => List.replicate k.width k.probes)[t]?).getD false

/-- One step of the interaction: issue the next operation of kind `k` and
append its slots' rows, each `touched` on the run issued so far. -/
def issue (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat)
    (acc : List OnlineBatch.Op × List (Fin m → Nat)) (k : Kind) :
    List OnlineBatch.Op × List (Fin m → Nat) :=
  let ops := acc.1 ++ [k.op (a.client acc.2)]
  let run : BatchRun := ⟨ops, a.init, a.unsh⟩
  (ops, acc.2 ++ (List.range k.width).map fun l (i : Fin m) =>
    touched cfg sh g run S words dummy (acc.2.length + l) i)

/-- The interaction: the operations issued and every slot's row. -/
def interact (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat) :
    List OnlineBatch.Op × List (Fin m → Nat) :=
  a.shape.foldl (issue cfg sh g S a words dummy) ([], [])

/-- The run the interaction issued. -/
def realized (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (words : Words) (dummy : Nat → Nat → Nat) : BatchRun :=
  ⟨(interact cfg sh g S a words dummy).1, a.init, a.unsh⟩

/-- The transcript: the rows of the first `n` slots. -/
def transcript (cfg : Config) (sh : Shapes) (g : OnlineGeom) (S : Schedule) {m : Nat}
    (a : AdaptiveRun m) (n : Nat) (words : Words) (dummy : Nat → Nat → Nat) :
    Fin n → Fin m → Nat :=
  fun t i => ((interact cfg sh g S a words dummy).2.getD t fun _ => 0) i

/-- The rows of the first `s` slots, read from a candidate transcript. -/
def rowsOf {n m : Nat} (t : Fin n → Fin m → Nat) (s : Nat) : List (Fin m → Nat) :=
  (List.range s).map fun r i => if h : r < n then t ⟨r, h⟩ i else 0

/-- The operations a client issues for the kinds `ks`, the first at slot `s`,
reading its rows from `t`. -/
def replayOps {n m : Nat} (C : Client m) (t : Fin n → Fin m → Nat) :
    List Kind → Nat → List OnlineBatch.Op
  | [], _ => []
  | k :: ks, s => k.op (C (rowsOf t s)) :: replayOps C t ks (s + k.width)

/-- The run the client issues when it reads its rows from `t`. -/
def replay {n m : Nat} (a : AdaptiveRun m) (t : Fin n → Fin m → Nat) : BatchRun :=
  ⟨replayOps a.client t a.shape 0, a.init, a.unsh⟩

end RebuildBound.Model.Adaptive
