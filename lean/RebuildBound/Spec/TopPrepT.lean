import RebuildBound.Spec.Model.TopPrepContract

/-!
# Deterministic theorems about the top preparation's model (trusted statements)

The counterparts of
T1, T2 and T4–T6 (`Spec/T.lean`) for `Spec/Model/TopPrep.lean`. None mentions
probability. They need only the selection rule's contract, the geometry's
domain and the lane shape of A's main; T4 also needs the starting buckets
(`TPShape`). They hold for every unshadowed flag `unsh` (an initialization is
the case `unsh = fun _ => false` with the scattered input).

* **TPEngine.** The engine's schedule (two half-blocks, each the butterfly
  recursion on bits `0 … k - 2`) is a valid schedule of the route.
* **TP12, conservation, placement and counts**, for every valid schedule: main
  and the drain target together hold exactly the surviving records (A minus
  its flagged tombstones), each once; main has `T` buckets of `C` lanes; every
  main record sits at its home; home `v` holds `min(X_v, C)` records; every
  drained record names a full home. So the drain holds `Σ_v (X_v - C)₊`.
* **TP4, first-failure inventory**, for every valid schedule: a first failure
  at the stash of bit `j` implies the raw stage excess of the surviving
  population at bit `j` exceeds the stash; a first failure at a DFS node
  implies, when A's old tier fits its slot, that some leaf's reference coarse
  count exceeds `C` (containment, `eq:dfs-capacity`; `cor:top-dfs-transfer`);
  a first failure at the drain implies the complete-home excess exceeds the
  drain target. `TPTest` has exactly these kinds.
* **TP5, blindness.** A stage reads only the routing bit of the records
  present; the route through stage `n ≤ k - 1` reads only the bits below `n` of
  A's main keys.
* **TP6, schedule independence.** Every valid schedule gives the stage-by-stage
  buckets, the same stashes up to order, and the same verdict of the job.
-/

namespace RebuildBound.Spec

open RebuildBound.Model

/-- A's main has `T` buckets of `C` lanes. -/
def TPLanes (g : TPGeom) (inp : TPInputs) : Prop :=
  inp.aMain.length = g.T ∧ ∀ B ∈ inp.aMain, B.length = g.C

/-- **TPEngine.** The engine's schedule is valid. -/
def TPEngine_statement : Prop :=
  ∀ g : TPGeom, g.Valid → TPValidSchedule g (tpEngineOps g)

/-- **TP12, conservation, placement and counts.** -/
def TP12_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs)
    (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → TPLanes g inp → TPValidSchedule g ops →
    let out := (tpReferenceWith rule g unsh w inp ops).output
    List.Perm (out.main.flatMap Bucket.recs ++ out.tier.filterMap id) (inp.survivors unsh) ∧
    out.main.length = g.T ∧
    (∀ B ∈ out.main, B.length = g.C) ∧
    (∀ v < g.T, ∀ r ∈ (out.main.getD v []).recs, tpHome g w r = v) ∧
    (∀ v < g.T,
      (out.main.getD v []).recs.length = min (tpHomeCount g w (inp.survivors unsh) v) g.C) ∧
    (∀ r ∈ out.tier.filterMap id, (out.main.getD (tpHome g w r) []).recs.length = g.C)

/-- **TP4a, the stashes and the DFS.** -/
def TP4a_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (pos w : LogicalKey → Nat) (inp : TPInputs)
    (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → TPShape g pos inp → TPValidSchedule g ops →
    (∀ j, tpFirstFailure g (tpReferenceWith rule g unsh w inp ops).trace = some (.stash j) →
      g.stashPages * g.C < tpRawStageExcess g unsh pos w inp j) ∧
    (∀ dd c, TPTiersFit g inp →
      tpFirstFailure g (tpReferenceWith rule g unsh w inp ops).trace = some (.dfs dd c) →
      ∃ R < g.ranges,
        g.C < tpRefCoarse g unsh w (tpReferenceWith rule g unsh w inp ops) inp g.earlyCap R)

/-- **TP4b, the drain.** -/
def TP4b_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs)
    (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → TPLanes g inp → TPValidSchedule g ops →
    tpFirstFailure g (tpReferenceWith rule g unsh w inp ops).trace = some .drain →
    g.drainPages * g.C < tpHomeExcess g unsh w inp

/-- **TP5, blindness of one stage.** The stage that reads bit `j` depends on the
words only through bit `j` of the records present. -/
def TP5_step_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (w w' : LogicalKey → Nat) (j : Nat) (st : TPRoute),
    rule.Valid →
    (∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) →
    runTPOps rule g w (tpStageOps g j) st = runTPOps rule g w' (tpStageOps g j) st

/-- **TP5, blindness of the route.** Word assignments that agree below bit `n` on
A's main keys give the same transcript through stage `n ≤ k - 1`, when A's main
has `T` buckets of `C` lanes (the rule's contract constrains it on such buckets
only). -/
def TP5_route_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w w' : LogicalKey → Nat) (aMain : List Bucket)
    (n : Nat), rule.Valid → n ≤ g.k - 1 → aMain.length = g.T → (∀ B ∈ aMain, B.length = g.C) →
    (∀ r ∈ aMain.flatMap Bucket.recs, ∀ i < n, (w r.key).testBit i = (w' r.key).testBit i) →
    tpRouteUpTo rule g unsh w aMain n = tpRouteUpTo rule g unsh w' aMain n

/-- **TP6, schedule independence.** -/
def TP6_statement : Prop :=
  ∀ (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : LogicalKey → Nat) (inp : TPInputs)
    (ops : List (Nat × Nat)),
    rule.Valid → g.Valid → TPLanes g inp → TPValidSchedule g ops →
    (tpReferenceWith rule g unsh w inp ops).route.main =
        (tpReferenceWith rule g unsh w inp g.canonicalOps).route.main ∧
    (∀ j, List.Perm ((tpReferenceWith rule g unsh w inp ops).route.stash.getD j [])
      ((tpReferenceWith rule g unsh w inp g.canonicalOps).route.stash.getD j [])) ∧
    (tpJobWith rule g unsh w inp ops).toBool = (tpJobWith rule g unsh w inp g.canonicalOps).toBool

end RebuildBound.Spec
