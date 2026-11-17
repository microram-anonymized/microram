import RebuildBound.Spec.Model.SepContract

/-!
# Deterministic theorems about the general-digit model (trusted statements)

The general-digit versions of T0–T2 and
T4–T6 (`Spec/T.lean` at d = 2), for the model `Spec/Model/Sep.lean`. All
assume only the structural contract `SInputShape` (with `STiersFit` where a
tier capacity is used), a valid selection rule and a geometry in the model's
domain; none mentions probability. Every statement is for every valid
schedule of A's binary operations, the engine's included (`SEngine`).

* **SEngine.** The engine's schedule is valid.
* **ST0.** The bounded job succeeds iff no test of the reference trace fails,
  and then publishes the reference output.
* **ST1, conservation.** Main and tier together hold exactly the newest
  version of every key of A ∪ B, once each, tombstones included.
* **ST2, placement and counts.** The output main has `N` buckets of `C`
  lanes; every main record sits at its home; home `v` holds `min(X_v, C)`
  records; every tier record names a full home.
* **ST4a, the route and the DFS.** A first failure at a stage stash implies
  that the raw stage excess of the complete A population exceeds the stash; at
  the radix stash, that A's complete-home excess does; at a DFS node, that
  some reference coarse count exceeds a leaf's capacity `C`, provided A's tier
  fits (the early list then fits its bound `P`).
* **ST4b, insertion and output tier.** A first failure at the insertion stash
  or the output tier implies the complete union's home excess exceeds it.
* **ST5, blindness.** A stage of the stage-by-stage schedule reads only the
  routing bit of the records present; the route through stage `n ≤ k` depends
  only on the bits below `n` of A's main keys; the radix pass reads only the
  class of the records present.
* **ST6, schedule independence.** Every valid schedule gives the stage-by-stage
  schedule's buckets and radix stash, its stage stashes up to order, and its
  verdict.
-/

namespace RebuildBound.Spec

open RebuildBound.Model

/-- **SEngine.** The engine's schedule is a valid schedule. -/
def SEngine_statement : Prop :=
  ∀ g : SepGeom, g.Valid → SValidSched g (engineOps g)

/-- **ST0.** -/
def ST0_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat))
    (out : Output),
    sJobWith rule g w inp ops = .ok out ↔
      sFirstFailure g (sReferenceWith rule g w inp ops).trace = none ∧
        out = (sReferenceWith rule g w inp ops).output

/-- **ST1, conservation.** -/
def ST1_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → SInputShape g wOld w inp → SValidSched g ops →
    List.Perm ((sReferenceWith rule g w inp ops).output.main.flatMap Bucket.recs ++
      (sReferenceWith rule g w inp ops).output.tier.filterMap id) inp.winners

/-- **ST2, placement and counts.** -/
def ST2_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → SInputShape g wOld w inp → SValidSched g ops →
    let out := (sReferenceWith rule g w inp ops).output
    out.main.length = g.N ∧
    (∀ B ∈ out.main, B.length = g.C) ∧
    (∀ v < g.N, ∀ x ∈ (out.main.getD v []).recs, sHome g w x = v) ∧
    (∀ v < g.N, (out.main.getD v []).recs.length = min (sHomeCount g w inp.winners v) g.C) ∧
    (∀ x ∈ out.tier.filterMap id, (out.main.getD (sHome g w x) []).recs.length = g.C)

/-- **ST4a, the route and the DFS.** -/
def ST4a_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → SInputShape g wOld w inp → SValidSched g ops →
    let run := sReferenceWith rule g w inp ops
    (∀ (j : Nat) (c : Bool), sFirstFailure g run.trace = some (.stash j c) →
      g.stashPages * g.C < sRawStageExcess g wOld w inp j) ∧
    (sFirstFailure g run.trace = some .radix → g.stashPages * g.C < sAHomeExcess g w inp) ∧
    (∀ dd c : Nat, sFirstFailure g run.trace = some (.dfs dd c) → STiersFit g inp →
      ∃ v < g.ranges, g.C < sRefCoarse g w run inp g.earlyCap v)

/-- **ST4b, insertion and output tier.** -/
def ST4b_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → SInputShape g wOld w inp → SValidSched g ops →
    let run := sReferenceWith rule g w inp ops
    (sFirstFailure g run.trace = some .insertion → g.stashPages * g.C < sHomeExcess g w inp) ∧
    (sFirstFailure g run.trace = some .drain → g.tierPages * g.C < sHomeExcess g w inp)

/-- The stage of the stage-by-stage schedule that reads bit `j`. -/
def sStageOps (g : SepGeom) (j : Nat) : List (Nat × Nat) :=
  g.canonicalOps.filter fun o => o.1 = j

/-- **ST5, blindness.** One stage reads only bit `j` of the records present; the
route through stage `n ≤ k` reads only the bits below `n` of A's main keys;
the radix pass reads only the class of the records present. -/
def ST5_statement : Prop :=
  (∀ (rule : CapRule) (g : SepGeom) (w w' : LogicalKey → Nat) (j : Nat) (st : SRoute),
    rule.Valid →
    (∀ B ∈ st.main, ∀ x ∈ B.recs, (w x.key).testBit j = (w' x.key).testBit j) →
    runSOps rule g w (sStageOps g j) st = runSOps rule g w' (sStageOps g j) st) ∧
  (∀ (rule : CapRule) (g : SepGeom) (wOld w w' : LogicalKey → Nat) (inp : SInputs) (n : Nat),
    rule.Valid → g.Valid → SInputShape g wOld w inp → n ≤ g.k →
    (∀ x ∈ inp.aMain.flatMap Bucket.recs, ∀ i < n, (w x.key).testBit i = (w' x.key).testBit i) →
    sRouteUpTo rule g w inp.aMain n = sRouteUpTo rule g w' inp.aMain n) ∧
  (∀ (g : SepGeom) (w w' : LogicalKey → Nat) (st : SRoute),
    (∀ B ∈ st.main, ∀ x ∈ B.recs, g.cls (w x.key) = g.cls (w' x.key)) →
    radixPass g w st = radixPass g w' st)

/-- **ST6, schedule independence.** -/
def ST6_statement : Prop :=
  ∀ (rule : CapRule) (g : SepGeom) (wOld w : LogicalKey → Nat) (inp : SInputs) (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → SInputShape g wOld w inp → SValidSched g ops →
    (sRouteWith rule g w inp.aMain ops).main = (sRouteWith rule g w inp.aMain g.canonicalOps).main ∧
    (∀ j, List.Perm ((sRouteWith rule g w inp.aMain ops).stash.getD j [])
      ((sRouteWith rule g w inp.aMain g.canonicalOps).stash.getD j [])) ∧
    (sRouteWith rule g w inp.aMain ops).radix = (sRouteWith rule g w inp.aMain g.canonicalOps).radix ∧
    (sJobWith rule g w inp ops).toBool = (sJobWith rule g w inp g.canonicalOps).toBool

end RebuildBound.Spec
