import RebuildBound.Spec.Model.Key

/-!
# Records, lane buckets and selection rules (trusted model)

Core/Std only: the model modules and the oracle never import Mathlib, so the
oracle executable links without Mathlib and the model stays small to review.

* `Rec`: a record carries its key, its value identity and its tombstone flag,
  never its own routing word. Which version of a key is newer is structural:
  a merge's fresher source (B) beats its older source (A).
* `Bucket`: a lane array. Lane `l` is entry `l` of the list; a main bucket has
  exactly `C` lanes. "Lane order" is list order.
* `fill`: place records, in order, into the lowest free lanes; the records that
  find no free lane are returned. Every allocation in the job is a `fill`.
* `CapRule`: the selection rule of one binary merge-split, a parameter of the
  model. It sees the two buckets (keys, values, lanes) and the routing bit of
  each record, and nothing else of the words; that is the rule's blindness.
  `engineRule` is the engine's `PlanMergePair`.
-/

namespace RebuildBound.Model

/-- One record: key, value identity and tombstone flag. A tombstone is a live
record of the ordinary merge; it is never dropped. -/
structure Rec where
  key : LogicalKey
  val : Nat
  tomb : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A lane array: lane `l` is entry `l`, `none` a free lane. -/
abbrev Bucket := List (Option Rec)

namespace Bucket

/-- The records of a bucket in lane order. -/
def recs (B : Bucket) : List Rec := B.filterMap id

/-- The empty bucket with `C` lanes. -/
def empty (C : Nat) : Bucket := List.replicate C none

/-- The keys of a bucket's records, in lane order. -/
def keys (B : Bucket) : List LogicalKey := B.recs.map Rec.key

/-- Free the lanes whose record's key satisfies `p`; other lanes keep their
records. -/
def clear (p : LogicalKey → Bool) (B : Bucket) : Bucket :=
  B.map fun s => s.filter fun r => !p r.key

end Bucket

/-- The number of occupied lanes. -/
def occupied {α : Type} (B : List (Option α)) : Nat := B.countP (·.isSome)

/-- Place the records of `L`, in order, into the free lanes of `B`, lowest lane
first. Returns the filled lanes and the records of `L` that found no free
lane (a suffix of `L`). -/
def fill {α : Type} : List (Option α) → List α → List (Option α) × List α
  | [], L => ([], L)
  | some r :: B, L => let p := fill B L; (some r :: p.1, p.2)
  | none :: B, [] => (none :: B, [])
  | none :: B, r :: L => let p := fill B L; (some r :: p.1, p.2)

/-- Fill the free lanes of a growable store, then append the rest at the end.
Stashes and tiers are stores whose capacity is tested separately. -/
def appendFill {α : Type} (B : List (Option α)) (L : List α) : List (Option α) :=
  let p := fill B L
  p.1 ++ p.2.map some

/-- The selection rule of one binary merge-split of buckets `(first, second)`
with bucket capacity `C`: records with `dir r = false` go to the first output,
those with `dir r = true` to the second; each output keeps at most `C`
records and the rest are shed, in the returned order. The rule's contract
(`CapRule.Valid`, package S3) is a permutation, the routing direction and the
count `min C arrivals` per output. -/
structure CapRule where
  split : (C : Nat) → (dir : Rec → Bool) → (first second : Bucket) →
    Bucket × Bucket × List Rec

/-- Walk the records `S` in lane order, keeping the first `n0` with
`dir = false` and the first `n1` with `dir = true`. Returns the kept records
of each direction and the shed records, in lane order. -/
def pick (dir : Rec → Bool) : Nat → Nat → List Rec → List Rec × List Rec × List Rec
  | _, _, [] => ([], [], [])
  | n0, n1, r :: S =>
    if dir r then
      match n1 with
      | 0 => let p := pick dir n0 0 S; (p.1, p.2.1, r :: p.2.2)
      | n1 + 1 => let p := pick dir n0 n1 S; (p.1, r :: p.2.1, p.2.2)
    else
      match n0 with
      | 0 => let p := pick dir 0 n1 S; (p.1, p.2.1, r :: p.2.2)
      | n0 + 1 => let p := pick dir n0 n1 S; (r :: p.1, p.2.1, p.2.2)

/-- The engine's rule (`PlanMergePair`): in each direction the first bucket's
records keep their lane numbers; the second bucket's records of that direction
fill the lowest lanes left free, in lane order; only the second bucket's
surplus is shed, in lane order. The first bucket never sheds. -/
def engineSplit (_C : Nat) (dir : Rec → Bool) (F S : Bucket) : Bucket × Bucket × List Rec :=
  let F0 := F.map fun s => s.filter fun r => !dir r
  let F1 := F.map fun s => s.filter dir
  let p := pick dir (F0.countP (·.isNone)) (F1.countP (·.isNone)) (Bucket.recs S)
  ((fill F0 p.1).1, (fill F1 p.2.1).1, p.2.2)

/-- The engine's selection rule. -/
def engineRule : CapRule := ⟨engineSplit⟩

end RebuildBound.Model
