import RebuildBound.Spec.Model.SepContract
import RebuildBound.Spec.Model.DirectMaskedRecords

/-! Core-only direct-job contract. Capacities count records; mathematical
words and slot capacities intentionally generalize machine words/page-aligned
native stores. Source order supplies version ranks. This module does not
execute later-digit A preparation or finish (see `DirectJobA.lean` and
`DirectJobFinish.lean`). -/
namespace RebuildBound.Model.DirectJob

inductive RangePlan where
  | direct
  | dfs (indexBits rangeBits poolCapacity : Nat)
  deriving Repr, DecidableEq, BEq

structure Geometry where
  K : Nat
  digit : Nat
  outputHomes : Nat
  outputCapacity : Nat
  aTierCapacity : Nat
  routeCapacity : Nat
  radixCapacity : Nat
  insertionCapacity : Nat
  copyCapacity : Nat
  ranges : RangePlan
  deriving Repr, DecidableEq

def Geometry.U (g : Geometry) : Nat := 2 ^ g.K

def Geometry.poolCapacity (g : Geometry) : Nat :=
  if g.digit = 1 then 0 else
  (g.K + val2 g.digit) * g.routeCapacity +
    (if 1 < g.digit / 2 ^ val2 g.digit then g.radixCapacity else 0) + g.aTierCapacity

def Geometry.Valid (g : Geometry) : Prop :=
  1 ≤ g.digit ∧ g.digit ≤ 8 ∧ g.outputHomes = g.digit * g.U ∧
  g.outputCapacity ≤ g.insertionCapacity ∧ g.outputCapacity ≤ g.copyCapacity ∧
  (g.digit = 1 → g.aTierCapacity = 0) ∧
  match g.ranges with
  | .direct => g.outputHomes ≤ 8 ∨ g.poolCapacity = 0
  | .dfs i r p => 8 < g.outputHomes ∧ g.outputHomes ≤ 2 ^ (i + r) ∧ p = g.poolCapacity ∧ 0 < p

instance (g : Geometry) : Decidable g.Valid := by
  unfold Geometry.Valid
  split <;> infer_instance

def Geometry.home (g : Geometry) (word : Nat) : Nat := digitHome g.K g.digit word

def Geometry.bCapacity (g : Geometry) : Nat :=
  DirectDrain.tierCapacity g.digit g.outputCapacity

/-- Units are chronological logical flush units, possibly empty or multi-bucket.
Holes are retained. Every B occurrence is newer than every A record; ranks are
derived from list order, never supplied separately by the caller. -/
structure Inputs where
  aMain : List Bucket
  aTier : List Rec
  units : List Bucket
  deriving Repr, DecidableEq

def Inputs.aRecords (inp : Inputs) : List Rec := inp.aMain.flatMap Bucket.recs ++ inp.aTier

def Inputs.bRecords (inp : Inputs) : List Rec := DirectMasks.records inp.units

/-- Structural assumptions, with separate previous-family words for A's old
placement. Current words are supplied once per key to every phase. -/
def Inputs.Valid (g : Geometry) (oldWord : LogicalKey → Nat) (inp : Inputs) : Prop :=
  inp.aMain.length = (g.digit - 1) * g.U ∧
  (∀ b ∈ inp.aMain, b.length = 64) ∧
  inp.aTier.length ≤ g.aTierCapacity ∧
  (inp.aRecords.map Rec.key).Nodup ∧
  (∀ u ∈ inp.units, (u.recs.map Rec.key).Nodup) ∧
  (∀ ib ∈ inp.aMain.zipIdx, ∀ x ∈ ib.1.recs,
    digitHome g.K (g.digit - 1) (oldWord x.key) = ib.2)

instance (g : Geometry) (oldWord : LogicalKey → Nat) (inp : Inputs) :
    Decidable (inp.Valid g oldWord) := by unfold Inputs.Valid; infer_instance

inductive Phase where
  | prepareA | produceB | distributeA | finish | drain | publish
  deriving Repr, DecidableEq, BEq

/-- Logical identity, not an instruction/fused task index. DFS node identity
remains reference-local until a native traversal adapter is proved. -/
inductive Site where
  | route (bit : Nat) (continuation : Bool)
  | radix | bTier | outputTier
  | dfs (depth pre : Nat)
  | insertion
  deriving Repr, DecidableEq, BEq

structure CheckId where
  phase : Phase
  site : Site
  /-- Zero-based ordinal. B uses chronological unit ordinals, including empty
  and cleared units. Native bucket/chunk ordinals need an explicit adapter. -/
  ordinal : Nat
  deriving Repr, DecidableEq, BEq

structure CheckEvent where
  id : CheckId
  occupancy : Nat
  capacity : Nat
  deriving Repr, DecidableEq, BEq

def CheckEvent.passed (e : CheckEvent) : Bool := e.occupancy ≤ e.capacity

/-- Compact publication for the B branch: main has implicit trailing holes.
Later-digit routed lanes must receive a separate lane-preserving output type. -/
structure Table where
  main : List (List Rec)
  tier : List Rec
  deriving Repr, DecidableEq, BEq

inductive Rejection where
  | geometry | inputs | requiresLaterPhases
  deriving Repr, DecidableEq, BEq

inductive Result where
  | rejected (reason : Rejection)
  | failed (event : CheckEvent)
  | published (table : Table)
  deriving Repr, DecidableEq, BEq

/-- One shared scalar update/check; analytical execution keeps the updated
state after overflow, while bounded execution stops at that event. -/
def appendTransition {α : Type} (id : CheckId) (capacity : Nat)
    (state chunk : List α) : List α × CheckEvent :=
  let next := state ++ chunk
  (next, ⟨id, next.length, capacity⟩)

def drainBounded {α : Type} (phase : Phase) (site : Site) (capacity : Nat) :
    Nat → List α → List (List α) → Except CheckEvent (List α)
  | _, state, [] => .ok state
  | ordinal, state, chunk :: rest =>
    let step := appendTransition ⟨phase, site, ordinal⟩ capacity state chunk
    if step.2.passed then drainBounded phase site capacity (ordinal + 1) step.1 rest
    else .error step.2

/-- Unlimited continuation is deliberately distinct from publishable Table. -/
structure AnalyticalDrain (α : Type) where
  records : List α
  trace : List CheckEvent

def drainAnalytical {α : Type} (phase : Phase) (site : Site) (capacity : Nat) :
    Nat → List α → List (List α) → AnalyticalDrain α
  | _, state, [] => ⟨state, []⟩
  | ordinal, state, chunk :: rest =>
    let step := appendTransition ⟨phase, site, ordinal⟩ capacity state chunk
    let tail := drainAnalytical phase site capacity (ordinal + 1) step.1 rest
    ⟨tail.records, step.2 :: tail.trace⟩

def firstFailure (trace : List CheckEvent) : Option CheckEvent :=
  trace.find? (fun e => !e.passed)

/-- Nonempty witnesses include shared versions, holes and a newest tombstone. -/
def exampleGeometry (digit : Nat) : Geometry :=
  ⟨0, digit, digit, 64, if digit = 1 then 0 else 64, 64, 64, 64, 64, .direct⟩

def exampleInputs (digit : Nat) : Inputs :=
  { aMain := if digit = 1 then [] else
      ((some ⟨LogicalKey.ofNat 7, 10, false⟩) :: List.replicate 63 none) ::
        List.replicate (digit - 2) (Bucket.empty 64)
    aTier := []
    units := [[some ⟨LogicalKey.ofNat 7, 20, false⟩, none], [], [some ⟨LogicalKey.ofNat 7, 30, true⟩]] }

end RebuildBound.Model.DirectJob
