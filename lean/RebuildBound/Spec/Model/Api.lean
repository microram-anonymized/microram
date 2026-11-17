import RebuildBound.Spec.Model.Probe

/-!
# Reference API requests, payloads, and post-operation records

Payloads are abstract natural-number identities, not the `Rec.val` word that
also carries metadata. A codec supplies only payload/flag roundtrips; connecting
it to native byte arrays is a separate refinement obligation. Keys are already
stored exact keys. The exchange proposal is a value, so input/output buffer
aliasing is likewise outside this model.

The internal `write` action is a probed replacement (`ReadThenWrite` in the
current native API); default scalar `Write` lowers to `blindWrite`. Every
probing lane has an internal prior-value answer. Output-bearing batch Write
may return it; scalar replacements discard it through `scalarReply`. An absent prior
value represents a false presence bit and a zero-filled output buffer. Native
initialization must separately ensure tombstone payload bytes are zero.
-/
namespace RebuildBound.Model.Api

/-- Payload and unshadowed metadata in the opaque record-value identity. -/
structure Codec where
  pack : Nat → Bool → Nat
  payload : Nat → Nat
  flag : Nat → Bool
  payload_pack : ∀ v b, payload (pack v b) = v
  flag_pack : ∀ v b, flag (pack v b) = b

/-- Primitive operation kinds after public API lowering. The kind and exchange's
insertion policy are public; `write` is the probed replacement primitive. -/
inductive Action where
  | read
  | write (value : Nat)
  | erase
  | exchange (value : Nat) (insertIfAbsent : Bool)
  | blindWrite (value : Nat)
  deriving DecidableEq, BEq, Repr

structure Request where
  key : LogicalKey
  action : Action
  deriving DecidableEq, BEq, Repr

/-- Blind writes occupy scalar operations in the lowered run. A public batch
splits at output-free Write lanes, leaving only probing lanes in its chunks. -/
def Request.probes (q : Request) : Bool :=
  match q.action with
  | .blindWrite _ => false
  | _ => true

abbrev State := LogicalKey → Option Nat

/-- User-visible payload of a selected record, after tombstone interpretation. -/
def value (c : Codec) (found : Option Rec) : Option Nat :=
  (Probe.decode found).map c.payload

/-- The independent finite-history map used to interpret initialization. -/
def stateOf (c : Codec) (history : List Rec) : State :=
  fun key => value c (DirectPrefix.latest key history)

/-- Logical effect at the requested key; Read preserves absence as well as presence. -/
def nextValue (q : Request) (old : Option Nat) : Option Nat :=
  match q.action with
  | .read => old
  | .write v | .blindWrite v => some v
  | .erase => none
  | .exchange v insert => if old.isSome || insert then some v else none

/-- One standard map operation, preserving every other key. -/
def step (q : Request) (state : State) : State :=
  fun key => if key = q.key then nextValue q (state q.key) else state key

/-- Reference map after the first `t` requests, in lane order. -/
def stateAt (initial : State) (requests : List Request) (t : Nat) : State :=
  (requests.take t).foldl (fun state q => step q state) initial

/-- Canonical prior-value answer. Blind writes have no prior-value result. -/
def reply (q : Request) (old : Option Nat) : Option Nat :=
  if q.probes then old else none

/-- Presence returned by Read/Erase/Exchange and probing batch lanes. -/
def present (old : Option Nat) : Bool := old.isSome

/-- The scalar or batch output buffer, with zeros on absence. -/
def output (old : Option Nat) : Nat := old.getD 0

/-- Scalar Write and WriteWithoutProbe have no return value. Read/Erase/Exchange
expose prior presence and, where requested, the prior payload. -/
inductive ScalarReply where
  | unit
  | previous (old : Option Nat)
  deriving DecidableEq, BEq, Repr

def scalarReply (q : Request) (old : Option Nat) : ScalarReply :=
  match q.action with
  | .write _ | .blindWrite _ => .unit
  | _ => .previous old

/-- `NoOlderLiveCopy`, before conjoining the inserted tombstone bit. -/
def noOlderLiveCopy (c : Codec) : Option Rec → Bool
  | none => true
  | some r => r.tomb && c.flag r.val

/-- The inserted record, including a zero payload on every tombstone and the
engine's inherited unshadowed qualifier. A blind write is always live. -/
def postRecord (c : Codec) (q : Request) (found : Option Rec) : Rec :=
  let next := nextValue q (value c found)
  let tomb := next.isNone
  ⟨q.key, c.pack (next.getD 0) (tomb && noOlderLiveCopy c found), tomb⟩

/-- A concrete sequential reference history; each request is answered from its
preceding history, then appends the explicitly constructed record. -/
def referenceRecords (c : Codec) : List Rec → List Request → List Rec
  | _, [] => []
  | history, q :: qs =>
    let r := postRecord c q (DirectPrefix.latest q.key history)
    r :: referenceRecords c (history ++ [r]) qs

/-- History of supplied slot records before slot `t`. -/
def historyAt (run : OnlineBatch.BatchRun) (t : Nat) : List Rec :=
  run.init ++ ((OnlineBatch.slots run).take t).map OnlineBatch.Slot.record

/-- Local implementation obligations, not a history-correctness assumption.
Requests have the same key/probe shape as the slots, and each inserted record
is constructed from that slot's effective selected record (including earlier
lanes of its chunk). No response or final-map equality is assumed. -/
structure Implements (c : Codec) (cfg : Config) (sh : Hierarchy.Shapes)
    (g : Online.OnlineGeom) (run : OnlineBatch.BatchRun) (S : Online.Schedule)
    (words : Hierarchy.Words) (dummy : Nat → Nat → Nat) (requests : List Request) : Prop where
  length : requests.length = (OnlineBatch.slots run).length
  slot : ∀ t q s, requests[t]? = some q → (OnlineBatch.slots run)[t]? = some s →
    s.record.key = q.key ∧ s.probes = q.probes ∧
      s.record = postRecord c q (Probe.batch cfg sh g run S words dummy t).found

end RebuildBound.Model.Api
