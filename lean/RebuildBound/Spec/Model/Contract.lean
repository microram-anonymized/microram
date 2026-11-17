import RebuildBound.Spec.Model.Job

/-!
# Input contract, rule contract and reference events (trusted)

Core Lean only, like the model.

* `CapRule.Valid`: the contract of a selection rule. The kept and shed records are a permutation of
  the arrivals; each output keeps `min C arrivals` records of its own
  direction in `C` lanes; and the rule reads the routing bit only of the
  records it is given (its permitted view: keys, values, lanes and the bit of
  the stage). Package D1 proves it for `engineRule`.
* `InputShape`: the structural input contract of one job for one word
  assignment. `wOld` is A's old
  family, `w` the merge family (B's family). B is fresher than A by
  construction of the model; that the two families differ is a matter of the
  probability law, not of this contract. It holds on every outcome, including
  reference inputs after an earlier failure.
* `TiersFit`: the tiers are within their public capacities, which holds only
  when no producer failed. `InputValid` is the conjunction of the two; the
  deterministic theorems assume it.
* `winners`: the newest version of every key of A ∪ B.
* **Reference events** on one word assignment, all read off the reference
  execution or the complete populations, so they are defined whether or not
  the bounded job fails earlier:
  - `rawStageExcess j`: the excess `Σ_v (X_{j,v} - C)₊` of the complete A
    population at the raw destinations after the stage that reads bit `j`;
  - `refCoarse R`: the coarse count of range `R`: the early A list (old tier,
    then the sheds of the stages that read bits `< lo`), truncated to its
    public bound `P` in that bit-blind order, plus the later sheds;
  - `homeExcess`: `Σ_v (X_v - C)₊` over the complete union's current homes.
-/

namespace RebuildBound.Model

/-- The contract of a selection rule. Buckets have `C` lanes. -/
structure CapRule.Valid (rule : CapRule) : Prop where
  /-- Kept and shed records together are a permutation of the arrivals. -/
  perm : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    List.Perm ((rule.split C dir F S).1.recs ++ (rule.split C dir F S).2.1.recs ++
      (rule.split C dir F S).2.2) (F.recs ++ S.recs)
  /-- Both outputs have `C` lanes. -/
  lanes : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    (rule.split C dir F S).1.length = C ∧ (rule.split C dir F S).2.1.length = C
  /-- The first output holds only records with `dir = false`. -/
  dir_first : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    ∀ r ∈ (rule.split C dir F S).1.recs, dir r = false
  /-- The second output holds only records with `dir = true`. -/
  dir_second : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    ∀ r ∈ (rule.split C dir F S).2.1.recs, dir r = true
  /-- The first output keeps `min C arrivals` of its direction. -/
  count_first : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    (rule.split C dir F S).1.recs.length = min C ((F.recs ++ S.recs).countP fun r => !dir r)
  /-- The second output keeps `min C arrivals` of its direction. -/
  count_second : ∀ (C : Nat) (dir : Rec → Bool) (F S : Bucket), F.length = C → S.length = C →
    (rule.split C dir F S).2.1.recs.length = min C ((F.recs ++ S.recs).countP dir)
  /-- The rule reads the routing bit only of the records it is given. -/
  local_dir : ∀ (C : Nat) (dir dir' : Rec → Bool) (F S : Bucket),
    (∀ r ∈ F.recs ++ S.recs, dir r = dir' r) → rule.split C dir F S = rule.split C dir' F S

namespace Inputs

/-- A's records: main (bucket order, lane order), then the old tier. -/
def aAll (inp : Inputs) : List Rec := inp.aMain.flatMap Bucket.recs ++ inp.aTier

/-- B's records: main, then tier. -/
def bAll (inp : Inputs) : List Rec := inp.bMain.flatMap Bucket.recs ++ inp.bTier

/-- The newest version of every key of A ∪ B: all of B, and A's records whose
key B lacks. -/
def winners (inp : Inputs) : List Rec :=
  inp.bAll ++ inp.aAll.filter fun r => !(inp.bAll.map Rec.key).contains r.key

end Inputs

/-- The structural input contract of one d = 2 job, for one word assignment.
It holds on every outcome of the ideal-word space, including those on which an
earlier job failed: the inputs are then the producers' reference outputs,
whose tiers may exceed their public capacities. -/
structure InputShape (g : Geom) (wOld w : LogicalKey → Nat) (inp : Inputs) : Prop where
  /-- A's main has `U` buckets of `C` lanes. -/
  aLen : inp.aMain.length = g.U
  aLanes : ∀ B ∈ inp.aMain, B.length = g.C
  /-- B's main has `U` buckets of `C` lanes. -/
  bLen : inp.bMain.length = g.U
  bLanes : ∀ B ∈ inp.bMain, B.length = g.C
  /-- A's main and old tier together are distinct by key; so are B's. -/
  aNodup : (inp.aAll.map Rec.key).Nodup
  bNodup : (inp.bAll.map Rec.key).Nodup
  /-- A's main records sit at their old homes, under A's old family. -/
  aHome : ∀ i < g.U, ∀ r ∈ (inp.aMain.getD i []).recs, wOld r.key % g.U = i
  /-- B's main records sit at their carry homes, under the merge family. -/
  bHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i
  /-- Every A tier record names a full old home. -/
  aTierFull : ∀ r ∈ inp.aTier, (inp.aMain.getD (wOld r.key % g.U) []).recs.length = g.C
  /-- Every B tier record names a full carry home. -/
  bTierFull : ∀ r ∈ inp.bTier, (inp.bMain.getD (w r.key % g.U) []).recs.length = g.C

/-- The tiers fit their public capacities `TA`, `TB`. This is guaranteed only
on outcomes where the producers of A and B did not fail. -/
def TiersFit (TA TB : Nat) (inp : Inputs) : Prop :=
  inp.aTier.length ≤ TA ∧ inp.bTier.length ≤ TB

/-- The input contract of one d = 2 job for one word assignment: the structural
contract (`InputShape`) and tiers within their public capacities `TA`, `TB`
(`TiersFit`). -/
structure InputValid (g : Geom) (TA TB : Nat) (wOld w : LogicalKey → Nat) (inp : Inputs) : Prop where
  /-- A's main has `U` buckets of `C` lanes. -/
  aLen : inp.aMain.length = g.U
  aLanes : ∀ B ∈ inp.aMain, B.length = g.C
  /-- B's main has `U` buckets of `C` lanes. -/
  bLen : inp.bMain.length = g.U
  bLanes : ∀ B ∈ inp.bMain, B.length = g.C
  /-- A's main and old tier together are distinct by key; so are B's. -/
  aNodup : (inp.aAll.map Rec.key).Nodup
  bNodup : (inp.bAll.map Rec.key).Nodup
  /-- A's main records sit at their old homes, under A's old family. -/
  aHome : ∀ i < g.U, ∀ r ∈ (inp.aMain.getD i []).recs, wOld r.key % g.U = i
  /-- B's main records sit at their carry homes, under the merge family. -/
  bHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i
  /-- Every A tier record names a full old home. -/
  aTierFull : ∀ r ∈ inp.aTier, (inp.aMain.getD (wOld r.key % g.U) []).recs.length = g.C
  /-- Every B tier record names a full carry home. -/
  bTierFull : ∀ r ∈ inp.bTier, (inp.bMain.getD (w r.key % g.U) []).recs.length = g.C
  /-- The tiers fit their public capacities. -/
  aTierCap : inp.aTier.length ≤ TA
  bTierCap : inp.bTier.length ≤ TB

/-- The structural contract and fitting tiers give the input contract. -/
theorem InputShape.valid {g : Geom} {wOld w : LogicalKey → Nat} {inp : Inputs}
    (h : InputShape g wOld w inp) {TA TB : Nat} (hf : TiersFit TA TB inp) :
    InputValid g TA TB wOld w inp :=
  ⟨h.aLen, h.aLanes, h.bLen, h.bLanes, h.aNodup, h.bNodup, h.aHome, h.bHome, h.aTierFull,
    h.bTierFull, hf.1, hf.2⟩

/-- Every outcome's inputs meet the input contract at their own tier lengths. -/
theorem InputShape.valid_self {g : Geom} {wOld w : LogicalKey → Nat} {inp : Inputs}
    (h : InputShape g wOld w inp) :
    InputValid g inp.aTier.length inp.bTier.length wOld w inp :=
  h.valid ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- The number of records of `L` whose home is `v`. -/
def homeCount (g : Geom) (w : LogicalKey → Nat) (L : List Rec) (v : Nat) : Nat :=
  L.countP fun r => home g w r == v

/-- The complete-home excess `Σ_v (X_v - C)₊` of the complete union A ∪ B
under the merge family. -/
def homeExcess (g : Geom) (w : LogicalKey → Nat) (inp : Inputs) : Nat :=
  ((List.range g.homes).map fun v => homeCount g w inp.winners v - g.C).sum

/-- The raw destination of A's key `x` after the stage that reads bit `j`: bits
`≤ j` from its merge-family word, the others from its embedded old home
`U + (wOld x mod U)`. -/
def rawDest (g : Geom) (wOld w : LogicalKey → Nat) (j : Nat) (x : LogicalKey) : Nat :=
  2 ^ (j + 1) * ((g.U + wOld x % g.U) / 2 ^ (j + 1)) + w x % 2 ^ (j + 1)

/-- The raw excess `Σ_v (X_{j,v} - C)₊` of the complete A population (main and
old tier) at its raw destinations after the stage that reads bit `j`. -/
def rawStageExcess (g : Geom) (wOld w : LogicalKey → Nat) (inp : Inputs) (j : Nat) : Nat :=
  ((List.range g.homes).map fun v =>
    (inp.aAll.countP fun r => rawDest g wOld w j r.key == v) - g.C).sum

/-- The early A list of a run in its bit-blind order: A's old tier (lane order),
then the sheds of the stages that read bits `0, …, lo - 1` (append order). -/
def earlyList (r : Run) (inp : Inputs) (lo : Nat) : List Rec :=
  inp.aTier ++ (r.route.stash.take lo).flatten

/-- The sheds of the stages that read bits `lo, …, k`. -/
def lateSheds (r : Run) (lo : Nat) : List Rec :=
  (r.route.stash.drop lo).flatten

/-- The reference coarse count of range `R`: the early list truncated to its
public bound `P`, plus the later sheds, counted in range `R` (before any
deletion against B). -/
def refCoarse (g : Geom) (w : LogicalKey → Nat) (r : Run) (inp : Inputs) (P R : Nat) : Nat :=
  ((earlyList r inp g.lo).take P ++ lateSheds r g.lo).countP fun x => rangeOf g w x == R

/-- The sum of the first `n` values of `f`. -/
def sumUpTo (f : Nat → Nat) (n : Nat) : Nat := ((List.range n).map f).sum

/-- A schedule of A's pair operations is valid when it runs each operation of
the model's schedule once, and two operations of different stages that touch
a common bucket run in stage order. -/
def ValidSchedule (g : Geom) (ops : List (Nat × Nat)) : Prop :=
  List.Perm ops (canonicalOps g) ∧
  ∀ a ∈ ops, ∀ b ∈ ops, a.1 < b.1 →
    (a.2 = b.2 ∨ a.2 = b.2 + 2 ^ b.1 ∨ a.2 + 2 ^ a.1 = b.2 ∨ a.2 + 2 ^ a.1 = b.2 + 2 ^ b.1) →
    ops.idxOf a < ops.idxOf b

end RebuildBound.Model
