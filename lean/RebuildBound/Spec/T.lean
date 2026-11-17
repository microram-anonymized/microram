import RebuildBound.Spec.Model.Contract

/-!
# Deterministic theorems about the d = 2 model (trusted statements)

Packages D1–D6. All assume only `InputValid` and a
valid selection rule; none mentions probability. T1 and T2 are stated for the
reference execution's output, which is the bounded job's output whenever the
job succeeds (`T0`).

* **D1.** The engine's rule meets the `CapRule` contract.
* **T0.** The bounded job succeeds exactly when no capacity test of the
  reference trace fails, and then publishes the reference output (prefix
  agreement is built into the model).
* **T1, conservation.** Main and tier together hold exactly the newest version
  of every key of A ∪ B, once each, tombstones included.
* **T2, placement and counts.** The output main has `2U` buckets of `C` lanes;
  every main record sits at its home; home `v` holds `min(X_v, C)` records;
  every tier record names a full home. With T1 the tier therefore holds
  `Σ_v (X_v - C)₊` records.
* **T4, first-failure inventory.** Each possible first failure implies its
  reference event on the same words: a stage-stash failure, the raw stage
  excess of the complete A population; a DFS failure, some reference coarse
  count above the leaf capacity (containment, `eq:dfs-capacity`); an insertion
  or output-tier failure, the complete-home excess. The inventory is complete
  because `Test` has exactly these four kinds.
* **T5, blindness.** A stage reads only the routing bit of the records present;
  so two word assignments that agree below bit `n` on A's keys give the same
  route transcript (buckets, stashes, trace) through stage `n`.
* **T6, schedule independence.** Every valid schedule of A's pair operations
  gives the same buckets, the same stash contents up to order, and the same
  verdict of the whole job.
-/

namespace RebuildBound.Spec

open RebuildBound.Model

/-- **D1.** The engine's `PlanMergePair` rule meets the `CapRule` contract. -/
def D1_statement : Prop := engineRule.Valid

/-- **T0.** The bounded job succeeds iff no test of the reference trace fails,
and then publishes the reference output. -/
def T0_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (caps : Caps) (w : LogicalKey → Nat) (inp : Inputs) (out : Output),
    job rule g caps w inp = .ok out ↔
      firstFailure g caps (reference rule g w inp).trace = none ∧
        out = (reference rule g w inp).output

/-- **T1, conservation.** -/
def T1_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (TA TB : Nat) (wOld w : LogicalKey → Nat) (inp : Inputs),
    rule.Valid → InputValid g TA TB wOld w inp →
    List.Perm ((reference rule g w inp).output.main.flatMap Bucket.recs ++
      (reference rule g w inp).output.tier.filterMap id) inp.winners

/-- **T2, placement and counts.** -/
def T2_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (TA TB : Nat) (wOld w : LogicalKey → Nat) (inp : Inputs),
    rule.Valid → InputValid g TA TB wOld w inp →
    let out := (reference rule g w inp).output
    out.main.length = g.homes ∧
    (∀ B ∈ out.main, B.length = g.C) ∧
    (∀ v < g.homes, ∀ r ∈ (out.main.getD v []).recs, home g w r = v) ∧
    (∀ v < g.homes,
      (out.main.getD v []).recs.length = min (homeCount g w inp.winners v) g.C) ∧
    (∀ r ∈ out.tier.filterMap id, (out.main.getD (home g w r) []).recs.length = g.C)

/-- **T4a, stage stashes and the DFS.** A first failure at a stage stash implies
the raw stage excess of the complete A population exceeds its capacity. A
first failure at a DFS node implies some reference coarse count exceeds the
leaf capacity `L`, provided the pool's slots hold every stage stash and A's
tier at their public capacities; the early list is truncated to
`P = T_A + Σ_{j < lo} S_j`. -/
def T4a_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (caps : Caps) (TA TB : Nat) (wOld w : LogicalKey → Nat)
    (inp : Inputs), rule.Valid → InputValid g TA TB wOld w inp →
    (∀ (j S : Nat), caps.stash j = some S →
      firstFailure g caps (reference rule g w inp).trace = some (.stash j) →
      S < rawStageExcess g wOld w inp j) ∧
    (∀ (d c L : Nat) (Ss : Nat → Nat), caps.leaf = some L →
      (∀ j < g.stages, caps.stash j = some (Ss j)) →
      TA + sumUpTo Ss g.stages ≤ g.poolSlots →
      firstFailure g caps (reference rule g w inp).trace = some (.dfs d c) →
      ∃ R < g.ranges,
        L < refCoarse g w (reference rule g w inp) inp (TA + sumUpTo Ss g.lo) R)

/-- **T4b, insertion and output tier.** A first failure at the insertion stash
or at the output tier implies the complete-home excess exceeds that
capacity. Hence either implies `homeExcess > min(S_insert, S_output)`. -/
def T4b_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (caps : Caps) (TA TB : Nat) (wOld w : LogicalKey → Nat)
    (inp : Inputs), rule.Valid → InputValid g TA TB wOld w inp →
    (∀ S : Nat, caps.ins = some S →
      firstFailure g caps (reference rule g w inp).trace = some .insertion →
      S < homeExcess g w inp) ∧
    (∀ S : Nat, caps.out = some S →
      firstFailure g caps (reference rule g w inp).trace = some .drain →
      S < homeExcess g w inp)

/-- **T5, blindness of one stage.** The stage that reads bit `j` depends on the
words only through bit `j` of the records present. -/
def T5_step_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (w w' : LogicalKey → Nat) (j : Nat) (st : RouteState),
    rule.Valid →
    (∀ B ∈ st.main, ∀ r ∈ B.recs, (w r.key).testBit j = (w' r.key).testBit j) →
    stageStep rule g w j st = stageStep rule g w' j st

/-- **T5, blindness of the route.** Word assignments that agree below bit `n` on
A's main keys give the same transcript through stage `n ≤ k + 1`. (Past the
last stage the pairs leave the network, where a rule is unconstrained.) -/
def T5_route_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (TA TB : Nat) (wOld w w' : LogicalKey → Nat) (inp : Inputs)
    (n : Nat), rule.Valid → InputValid g TA TB wOld w inp → n ≤ g.stages →
    (∀ r ∈ inp.aMain.flatMap Bucket.recs, ∀ i < n, (w r.key).testBit i = (w' r.key).testBit i) →
    routeUpTo rule g w inp.aMain n = routeUpTo rule g w' inp.aMain n

/-- **T6, schedule independence.** -/
def T6_statement : Prop :=
  ∀ (rule : CapRule) (g : Geom) (caps : Caps) (TA TB : Nat) (wOld w : LogicalKey → Nat)
    (inp : Inputs) (ops : List (Nat × Nat)),
    rule.Valid → InputValid g TA TB wOld w inp → ValidSchedule g ops →
    (routeWith rule g w inp.aMain ops).main = (routeA rule g w inp.aMain).main ∧
    (∀ j, List.Perm ((routeWith rule g w inp.aMain ops).stash.getD j [])
      ((routeA rule g w inp.aMain).stash.getD j [])) ∧
    (jobWith rule g caps w inp ops).toBool = (job rule g caps w inp).toBool

end RebuildBound.Spec
