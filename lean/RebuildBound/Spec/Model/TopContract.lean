import RebuildBound.Spec.Model.Top

/-!
# The top finish's input contract and reference quantities (trusted)

Core Lean only, like the model.

* `TopShape`: the structural contract of one top finish for one word
  assignment of the current family (`REPORT.tex`, premises (P1)–(P2) of
  `prop:top-resolution` and R's fullness identity of
  `cor:top-finish-separated`). B's tier may name any home: neither the engine
  nor any statement relies on its fullness (`ENGINE_TOP.md`, section 10). It holds on **every** outcome: after an earlier
  failure the inputs are the producers' reference outputs, whose retained
  carry and tier may exceed their public capacities. Premise (P3), the pool
  dedup of R against B's tier, is performed by the model itself.
  "Nothing older than A and B is live" is not a property of these inputs; it
  is why the model may drop a winning tombstone, and it is built into
  `TopInputs.live`. The one clause about the unshadowed flag `unsh` is the
  flag's promise (`ENGINE_TOP.md`, section 7) where the engine relies on it: a
  flagged tombstone of B's tier has no live copy in C. The engine drops it
  before the resolution, so it never clears C's copy; the report's premises
  (P1)–(P3) omit this (`ENGINE_TOP.md`, section 9, item 2).
* `TopTiersFit`: the retained carry and B's tier fit their public
  capacities. It holds only when the producers did not fail, so it belongs
  to the first-failure event, never to the law.
* **Reference quantities**, functions of the inputs and the words, defined on
  every outcome:
  - `topExcess`: `E_f = Σ_v (X_v - C)₊`, `X_v` the resolved live winners at
    home `v` (`prop:top-excess`);
  - `rangeExcessA r`: `R_r = Σ_{v ∈ J_r} (Y^A_v - C)₊`, `Y^A_v` A's records
    (C and R, tombstones included) at home `v`, and `J_r` the `2^I` homes of
    coarse range `r` (`cor:top-finish-separated`, item 1).
-/

namespace RebuildBound.Model

/-- The structural contract of one top finish, for one word assignment `w`
of the top's current family. -/
structure TopShape (g : TopGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TopInputs) :
    Prop where
  /-- C has `T` buckets of `C` lanes (so at most `C` records each). -/
  cLen : inp.cMain.length = g.T
  cLanes : ∀ B ∈ inp.cMain, B.length = g.C
  /-- B's main has `U` buckets of `C` lanes. -/
  bLen : inp.bMain.length = g.U
  bLanes : ∀ B ∈ inp.bMain, B.length = g.C
  /-- A = C ⊔ R is distinct by key; so is B (main and tier). B is the fresher
  source by construction of the model. -/
  aNodup : (inp.aAll.map Rec.key).Nodup
  bNodup : (inp.bAll.map Rec.key).Nodup
  /-- C's records sit at their homes under the current family. -/
  cHome : ∀ v < g.T, ∀ r ∈ (inp.cMain.getD v []).recs, topHome g w r = v
  /-- B's main records sit at their carry buckets under the current family. -/
  bHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i
  /-- R's fullness identity: every R record names a full home of C. -/
  carryFull : ∀ r ∈ inp.carry, (inp.cMain.getD (topHome g w r) []).recs.length = g.C
  /-- The unshadowed flag's promise: a flagged tombstone of B's tier has no
  live copy in C. -/
  tierUnsh : ∀ r ∈ inp.bTier, earlyDrop unsh r = true →
    ∀ c ∈ inp.cMain.flatMap Bucket.recs, c.key = r.key → c.tomb = true

/-- The retained carry and B's tier fit their public capacities. Guaranteed
only on outcomes where their producers did not fail. -/
def TopTiersFit (g : TopGeom) (inp : TopInputs) : Prop :=
  inp.carry.length ≤ g.SR ∧ inp.bTier.length ≤ g.SB

instance (g : TopGeom) (inp : TopInputs) : Decidable (TopTiersFit g inp) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The number of records of `L` at home `v`. -/
def topCount (g : TopGeom) (w : LogicalKey → Nat) (L : List Rec) (v : Nat) : Nat :=
  L.countP fun r => topHome g w r == v

/-- `E_f = Σ_v (X_v - C)₊` over the resolved live set. -/
def topExcess (g : TopGeom) (w : LogicalKey → Nat) (inp : TopInputs) : Nat :=
  ((List.range g.T).map fun v => topCount g w inp.live v - g.C).sum

/-- `R_r = Σ_{v ∈ J_r} (Y^A_v - C)₊`: A's complete-home excess restricted to
coarse range `r`, whose homes are `r 2^I, …, r 2^I + 2^I - 1`. -/
def rangeExcessA (g : TopGeom) (w : LogicalKey → Nat) (inp : TopInputs) (r : Nat) : Nat :=
  ((List.range (2 ^ g.I)).map fun i => topCount g w inp.aAll (r * 2 ^ g.I + i) - g.C).sum

end RebuildBound.Model
