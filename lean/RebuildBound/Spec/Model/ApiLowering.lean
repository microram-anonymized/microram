import RebuildBound.Spec.Model.Api

/-!
# Public batch descriptors and their internal lowering

This is the successful, sequential API contract, over normalized stored keys and
payload identities. The public descriptor includes whether each value output
exists and whether the call requests presence outputs. These fields determine
blind writes and chunk boundaries; keys, values, selected entries and results do
not. The public requester position and unit size also constrain chunk boundaries.
The positive native width and unit size are represented by `max 1 width` and
`max 1 entries`; a pending full unit is normalized before the next chunk.
Byte buffers, overlap, key conversion, failure and concurrent calls remain
separate refinement obligations.
-/
namespace RebuildBound.Model.PublicApi

variable {α β : Type}

inductive Kind where
  | read | write | erase | exchange | readThenWrite
  deriving DecidableEq, BEq, Repr

/-- Public per-lane controls. The insertion policy matters only to Exchange. -/
structure Descriptor where
  kind : Kind
  valueOutput : Bool := false
  insertIfAbsent : Bool := false
  deriving DecidableEq, BEq, Repr

structure Lane where
  key : LogicalKey
  value : Nat
  descriptor : Descriptor
  deriving DecidableEq, BEq, Repr

/-- Exactly the engine's public blind-write test. ReadThenWrite always probes. -/
def probes (foundOutput : Bool) (d : Descriptor) : Bool :=
  match d.kind with
  | .write => d.valueOutput || foundOutput
  | _ => true

/-- Translate public names to the existing internal action model. In particular
internal `Api.Action.write` means a probing write, not default scalar Write. -/
def request (foundOutput : Bool) (l : Lane) : Api.Request :=
  ⟨l.key, match l.descriptor.kind with
    | .read => .read
    | .write => if probes foundOutput l.descriptor then .write l.value else .blindWrite l.value
    | .erase => .erase
    | .exchange => .exchange l.value l.descriptor.insertIfAbsent
    | .readThenWrite => .write l.value⟩

/-- Independent public operation semantics, without referring to the lowering. -/
def nextValue (l : Lane) (old : Option Nat) : Option Nat :=
  match l.descriptor.kind with
  | .read => old
  | .write | .readThenWrite => some l.value
  | .erase => none
  | .exchange => if old.isSome || l.descriptor.insertIfAbsent then some l.value else none

def step (l : Lane) (state : Api.State) : Api.State :=
  fun key => if key = l.key then nextValue l (state l.key) else state key

def stateAt (initial : Api.State) (lanes : List Lane) (t : Nat) : Api.State :=
  (lanes.take t).foldl (fun state lane => step lane state) initial

/-- Only requested buffers are exposed. `some 0` is a written zero payload;
`none` means no buffer. Presence distinguishes an absent value from live zero. -/
structure Response where
  value : Option Nat
  found : Option Bool
  deriving DecidableEq, BEq, Repr

def response (foundOutput : Bool) (l : Lane) (old : Option Nat) : Response :=
  ⟨if l.descriptor.valueOutput then some (Api.output old) else none,
   if foundOutput then some (Api.present old) else none⟩

/-- A blind lane is one scalar operation. Every lane of a chunk probes. -/
inductive Group (α : Type) where
  | blind (lane : α)
  | chunk (lanes : List α)
  deriving DecidableEq, BEq, Repr

def Group.lanes : Group α → List α
  | .blind lane => [lane]
  | .chunk lanes => lanes

def Group.map (f : α → β) : Group α → Group β
  | .blind lane => .blind (f lane)
  | .chunk lanes => .chunk (lanes.map f)

/-- The Boolean is the probe bit; the natural is the operation's lane count. -/
def Group.shape : Group α → Bool × Nat
  | .blind _ => (false, 1)
  | .chunk lanes => (true, lanes.length)

/-- Maximal additional probing lanes after the first lane of a chunk, up to
width minus one. An intervening blind write always ends the chunk. -/
def tailChunk (width : Nat) (p : α → Bool) (lanes : List α) : List α :=
  (lanes.takeWhile p).take (width - 1)

/-- Available public lane positions before the next frozen unit. The remainder
normalizes a pending full unit; real/superseded masks do not affect position. -/
def unitRemaining (entries position : Nat) : Nat :=
  max 1 entries - position % max 1 entries

/-- The whole deduplication job, including every participant, fits this width. -/
def chunkWidth (width entries position : Nat) : Nat :=
  min (max 1 width) (unitRemaining entries position)

/-- Fuel is the remaining input length. Each step consumes at least one lane.
Position advances for blind, superseded and non-real lanes alike. -/
def partitionAux (width entries : Nat) (p : α → Bool) :
    Nat → Nat → List α → List (Group α)
  | _, 0, _ => []
  | _, _ + 1, [] => []
  | position, fuel + 1, lane :: lanes =>
    if p lane then
      let tail := tailChunk (chunkWidth width entries position) p lanes
      .chunk (lane :: tail) ::
        partitionAux width entries p (position + (tail.length + 1)) fuel (lanes.drop tail.length)
    else
      .blind lane :: partitionAux width entries p (position + 1) fuel lanes

def partition (width entries position : Nat) (p : α → Bool) (lanes : List α) :
    List (Group α) :=
  partitionAux width entries p position lanes.length lanes

def groups (width entries position : Nat) (foundOutput : Bool) (lanes : List Lane) :
    List (Group Lane) :=
  partition width entries position (fun l => probes foundOutput l.descriptor) lanes

/-- Shape uses public descriptors, unit size and position, before any lookup. -/
def publicShape (width entries position : Nat) (foundOutput : Bool)
    (descriptors : List Descriptor) : List (Bool × Nat) :=
  (partition width entries position (probes foundOutput) descriptors).map Group.shape

/-- Every operation stops at or before the next unit boundary. No deduplication
job can suppress a record across an already committed cut. -/
def GroupsFit (entries : Nat) : Nat → List (Group α) → Prop
  | _, [] => True
  | position, group :: rest =>
      0 < group.lanes.length ∧ group.lanes.length ≤ unitRemaining entries position ∧
      GroupsFit entries (position + group.lanes.length) rest

/-- Valid shape and internal request probes, for each emitted operation. -/
def ValidGroup (width : Nat) (foundOutput : Bool) : Group Lane → Prop
  | .blind lane => (request foundOutput lane).probes = false
  | .chunk lanes => lanes ≠ [] ∧ lanes.length ≤ max 1 width ∧
      ∀ l ∈ lanes, (request foundOutput l).probes = true

end RebuildBound.Model.PublicApi
