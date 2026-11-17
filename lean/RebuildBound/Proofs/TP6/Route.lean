import RebuildBound.Proofs.RouteCore.Basic
import RebuildBound.Spec.TopPrepT

/-!
# TP6: the top preparation's route under a valid schedule

The general-digit counterpart of `D6/Route.lean`.

* `tpPairStep` on disjoint pairs commutes up to stash order (`TPREq`).
* A valid schedule (`TPValidSchedule`) agrees with `canonicalOps` on every
  conflicting pair, so by the shared exchange argument (`Exchange.ExchHyp.sched`)
  its binary route is `TPREq` to the stage-by-stage one.
* The route trace fails iff some touched stage stash's final length fails.
-/

namespace RebuildBound.TP6Aux

open RebuildBound.Model RebuildBound.D6 RebuildBound.Exchange

/-- The stage of bit `j` of the stage-by-stage schedule. -/
def tpStage (g : TPGeom) (j : Nat) : List (Nat × Nat) :=
  ((List.range g.T).filter fun i => !i.testBit j).map fun i => (j, i)

theorem canonicalOps_eq (g : TPGeom) : g.canonicalOps = (List.range (g.k - 1)).flatMap (tpStage g) := rfl

theorem mem_tpStage (g : TPGeom) (j : Nat) (o : Nat × Nat) :
    o ∈ tpStage g j ↔ o.1 = j ∧ o.2 < g.T ∧ o.2.testBit j = false := by
  obtain ⟨a, b⟩ := o
  simp only [tpStage, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq,
    Bool.not_eq_true']
  constructor
  · rintro ⟨i, ⟨hi, hb⟩, rfl, rfl⟩
    exact ⟨rfl, hi, hb⟩
  · rintro ⟨rfl, hb, ht⟩
    exact ⟨b, ⟨hb, ht⟩, rfl, rfl⟩

theorem mem_canonical (g : TPGeom) (o : Nat × Nat) :
    o ∈ g.canonicalOps ↔
      o.1 < g.k - 1 ∧ o.2 < g.T ∧ o.2.testBit o.1 = false := by
  rw [canonicalOps_eq]
  simp only [List.mem_flatMap, List.mem_range, mem_tpStage]
  constructor
  · rintro ⟨j, hj, rfl, h1, h2⟩
    exact ⟨hj, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨o.1, h0, rfl, h1, h2⟩

theorem tpStage_fst (g : TPGeom) (j : Nat) (o : Nat × Nat) (h : o ∈ tpStage g j) : o.1 = j :=
  ((mem_tpStage g j o).mp h).1

theorem nodup_tpStage (g : TPGeom) (j : Nat) : (tpStage g j).Nodup := by
  unfold tpStage
  refine List.Nodup.map (fun a b h => by simpa using h) ?_
  exact (List.nodup_range).filter _

/-! ### The pair operation on `TPRoute` -/

section Pair

variable (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat)

/-- The merge-split of pair `(j, i)` on main `m`. -/
def tpSplitAt (j i : Nat) (m : List Bucket) : Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w j) (m.getD i []) (m.getD (i + 2 ^ j) [])

/-- The main buckets after pair `(j, i)`. -/
def tpPairMain (j i : Nat) (m : List Bucket) : List Bucket :=
  (m.set i (tpSplitAt rule g w j i m).1).set (i + 2 ^ j) (tpSplitAt rule g w j i m).2.1

theorem tpPairStep_main (j i : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).main = tpPairMain rule g w j i st.main := rfl

theorem tpPairStep_stash (j i : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).stash =
      st.stash.set j (st.stash.getD j [] ++ (tpSplitAt rule g w j i st.main).2.2) := rfl

theorem tpPairStep_trace (j i : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).trace =
      st.trace ++ [(TPTest.stash j,
        (st.stash.getD j [] ++ (tpSplitAt rule g w j i st.main).2.2).length)] := rfl

theorem tpPairStep_stash_length (j i : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).stash.length = st.stash.length := by
  simp [tpPairStep_stash]

theorem tpPairStep_main_length (j i : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).main.length = st.main.length := by
  simp [tpPairStep_main, tpPairMain]

theorem tpPairStep_stash_getD (j i j' : Nat) (st : TPRoute) :
    (tpPairStep rule g w j i st).stash.getD j' [] =
      if j = j' ∧ j < st.stash.length then
        st.stash.getD j' [] ++ (tpSplitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] :=
  RouteCore.coreStash_getD j i j' (st.main, st.stash)

/-- Route states with the same buckets, the same radix stash and the same stage
stash contents up to order. -/
structure TPREq (s t : TPRoute) : Prop where
  main : s.main = t.main
  len : s.stash.length = t.stash.length
  perm : ∀ j, (s.stash.getD j []).Perm (t.stash.getD j [])

theorem TPREq.refl (s : TPRoute) : TPREq s s := ⟨rfl, rfl, fun _ => List.Perm.refl _⟩

theorem TPREq.symm {s t : TPRoute} (h : TPREq s t) : TPREq t s :=
  ⟨h.main.symm, h.len.symm, fun j => (h.perm j).symm⟩

theorem TPREq.trans {s t u : TPRoute} (h : TPREq s t) (h' : TPREq t u) : TPREq s u :=
  ⟨h.main.trans h'.main, h.len.trans h'.len, fun j => (h.perm j).trans (h'.perm j)⟩

variable {rule g w} in
theorem TPREq.pairStep {s t : TPRoute} (h : TPREq s t) (j i : Nat) :
    TPREq (tpPairStep rule g w j i s) (tpPairStep rule g w j i t) := by
  refine ⟨by rw [tpPairStep_main, tpPairStep_main, h.main], by
    rw [tpPairStep_stash_length, tpPairStep_stash_length, h.len], fun j' => ?_⟩
  rw [tpPairStep_stash_getD, tpPairStep_stash_getD, h.len, h.main]
  split_ifs
  · exact (h.perm j').append_right _
  · exact h.perm j'

/-- Operations on disjoint bucket pairs commute up to stash order. -/
theorem tpPairStep_comm (a b : Nat × Nat) (hab : ¬Conflict a b) (s : TPRoute) :
    TPREq (tpPairStep rule g w a.1 a.2 (tpPairStep rule g w b.1 b.2 s))
      (tpPairStep rule g w b.1 b.2 (tpPairStep rule g w a.1 a.2 s)) := by
  have h := RouteCore.coreStep_comm (rule := rule) (C := g.C) (w := w) a b hab (s.main, s.stash)
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The step function of `runTPOps`. -/
def tpStep (o : Nat × Nat) (st : TPRoute) : TPRoute := tpPairStep rule g w o.1 o.2 st

theorem runTPOps_eq (ops : List (Nat × Nat)) (st : TPRoute) :
    runTPOps rule g w ops st = runL (tpStep rule g w) ops st := rfl

theorem tpExchHyp : ExchHyp (tpStep rule g w) TPREq where
  refl := TPREq.refl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h h' => h.trans h'
  pres := fun o _ _ h => h.pairStep o.1 o.2
  comm := fun a b s h => tpPairStep_comm rule g w a b h s

theorem runTPOps_cons (o : Nat × Nat) (l : List (Nat × Nat)) (st : TPRoute) :
    runTPOps rule g w (o :: l) st = runTPOps rule g w l (tpPairStep rule g w o.1 o.2 st) := rfl

end Pair

/-- **Part 1.** The binary route under a valid schedule equals the
stage-by-stage one up to stage stash order. -/
theorem binRoute_TPREq (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (ops : List (Nat × Nat))
    (hv : TPValidSchedule g ops) (st : TPRoute) :
    TPREq (runTPOps rule g w ops st) (runTPOps rule g w g.canonicalOps st) := by
  rw [runTPOps_eq, runTPOps_eq]
  exact (tpExchHyp rule g w).sched (tpStage_fst g) (fun j o h => ((mem_tpStage g j o).mp h).2.2)
    (nodup_tpStage g) (g.k - 1) ops hv.1 hv.2 st

/-! ### The route trace -/

/-- The route trace records running stage stash lengths. -/
def TPTraceOK (st : TPRoute) : Prop :=
  (∀ x ∈ st.trace, ∃ j, x.1 = TPTest.stash j ∧ x.2 ≤ (st.stash.getD j []).length) ∧
  (∀ j n, (TPTest.stash j, n) ∈ st.trace →
    (TPTest.stash j, (st.stash.getD j []).length) ∈ st.trace)

theorem TPTraceOK.step {rule : CapRule} {g : TPGeom} {w : Model.LogicalKey → Nat} {st : TPRoute}
    (h : TPTraceOK st) (j i : Nat) (hj : j < st.stash.length) :
    TPTraceOK (tpPairStep rule g w j i st) := by
  have hget : ∀ j', (tpPairStep rule g w j i st).stash.getD j' [] =
      if j = j' then st.stash.getD j' [] ++ (tpSplitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] := by
    intro j'
    rw [tpPairStep_stash_getD]
    by_cases hjj : j = j'
    · rw [ite_eq_left ⟨hjj, hj⟩, ite_eq_left hjj]
    · rw [ite_eq_right (fun h => hjj h.1), ite_eq_right hjj]
  have hle : ∀ j', (st.stash.getD j' []).length ≤
      ((tpPairStep rule g w j i st).stash.getD j' []).length := by
    intro j'
    rw [hget]
    split_ifs <;> simp
  constructor
  · intro x hx
    rw [tpPairStep_trace, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨j', h1, h2⟩ := h.1 x hx
      exact ⟨j', h1, h2.trans (hle j')⟩
    · refine ⟨j, rfl, ?_⟩
      rw [hget, ite_eq_left rfl]
  · intro j' n hx
    rw [tpPairStep_trace, List.mem_append, List.mem_singleton] at hx
    by_cases hjj : j = j'
    · subst hjj
      rw [tpPairStep_trace, List.mem_append, List.mem_singleton]
      right
      rw [hget, ite_eq_left rfl]
    · rcases hx with hx | hx
      · have hc' := h.2 j' n hx
        rw [tpPairStep_trace, List.mem_append]
        left
        rw [hget, ite_eq_right hjj]
        exact hc'
      · simp only [Prod.mk.injEq, TPTest.stash.injEq] at hx
        exact absurd hx.1.symm hjj

theorem runTPOps_stash_length (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : TPRoute),
      (runTPOps rule g w l st).stash.length = st.stash.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runTPOps_cons, runTPOps_stash_length rule g w l, tpPairStep_stash_length]

theorem runTPOps_main_length (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : TPRoute),
      (runTPOps rule g w l st).main.length = st.main.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runTPOps_cons, runTPOps_main_length rule g w l, tpPairStep_main_length]

theorem runTPOps_traceOK (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : TPRoute), (∀ o ∈ l, o.1 < st.stash.length) →
      TPTraceOK st → TPTraceOK (runTPOps rule g w l st)
  | [], _, _, h => h
  | o :: l, st, hl, h => by
    rw [runTPOps_cons]
    refine runTPOps_traceOK rule g w l _ ?_ (h.step o.1 o.2 (hl o List.mem_cons_self))
    intro o' ho'
    rw [tpPairStep_stash_length]
    exact hl o' (List.mem_cons_of_mem _ ho')

theorem runTPOps_trace_stage (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (j : Nat) :
    ∀ (l : List (Nat × Nat)) (st : TPRoute),
      (∃ n, (TPTest.stash j, n) ∈ (runTPOps rule g w l st).trace) ↔
        (∃ n, (TPTest.stash j, n) ∈ st.trace) ∨ ∃ o ∈ l, o.1 = j
  | [], st => by simp [runTPOps]
  | o :: l, st => by
    rw [runTPOps_cons, runTPOps_trace_stage rule g w j l, tpPairStep_trace]
    constructor
    · rintro (⟨n, hn⟩ | ⟨o', ho', h'⟩)
      · rw [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | hn
        · exact Or.inl ⟨n, hn⟩
        · simp only [Prod.mk.injEq, TPTest.stash.injEq] at hn
          exact Or.inr ⟨o, List.mem_cons_self, hn.1.symm⟩
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h'⟩
    · rintro (⟨n, hn⟩ | ⟨o', ho', h'⟩)
      · exact Or.inl ⟨n, List.mem_append_left _ hn⟩
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · subst h'
          exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · exact Or.inr ⟨o', ho', h'⟩

/-- Some test of a trace fails. -/
def TPFails (g : TPGeom) (tr : List (TPTest × Nat)) : Prop :=
  ∃ x ∈ tr, g.capOf x.1 < x.2

theorem tpFails_append (g : TPGeom) (a b : List (TPTest × Nat)) :
    TPFails g (a ++ b) ↔ TPFails g a ∨ TPFails g b := by
  simp only [TPFails, List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, hf⟩
    · exact Or.inl ⟨x, hx, hf⟩
    · exact Or.inr ⟨x, hx, hf⟩
  · rintro (⟨x, hx, hf⟩ | ⟨x, hx, hf⟩)
    · exact ⟨x, Or.inl hx, hf⟩
    · exact ⟨x, Or.inr hx, hf⟩

theorem tpFails_of_traceOK (g : TPGeom) {st : TPRoute} (h : TPTraceOK st) :
    TPFails g st.trace ↔ ∃ j, (∃ n, (TPTest.stash j, n) ∈ st.trace) ∧
      g.stashPages * g.C < (st.stash.getD j []).length := by
  constructor
  · rintro ⟨x, hx, hf⟩
    obtain ⟨j, h1, h2⟩ := h.1 x hx
    obtain ⟨t, n⟩ := x
    simp only at h1 h2 hf
    subst h1
    exact ⟨j, ⟨n, hx⟩, lt_of_lt_of_le hf h2⟩
  · rintro ⟨j, ⟨n, hn⟩, hf⟩
    exact ⟨_, h.2 j n hn, hf⟩

theorem tpRouteInit_traceOK (g : TPGeom) (aMain : List Bucket) :
    TPTraceOK (tpRouteInit g aMain) := by
  constructor <;> simp [tpRouteInit]

/-- **Binary route verdict.** -/
theorem binRoute_fails_iff (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (ops : List (Nat × Nat)) (hv : TPValidSchedule g ops) :
    TPFails g (runTPOps rule g w ops (tpRouteInit g aMain)).trace ↔
      TPFails g (runTPOps rule g w g.canonicalOps (tpRouteInit g aMain)).trace := by
  have hst : ∀ o ∈ g.canonicalOps, o.1 < (tpRouteInit g aMain).stash.length := by
    intro o ho
    have := ((mem_canonical g o).mp ho).1
    simp only [tpRouteInit, List.length_replicate]
    omega
  have hst' : ∀ o ∈ ops, o.1 < (tpRouteInit g aMain).stash.length :=
    fun o ho => hst o (hv.1.subset ho)
  have t1 := runTPOps_traceOK rule g w ops _ hst' (tpRouteInit_traceOK g aMain)
  have t2 := runTPOps_traceOK rule g w g.canonicalOps _ hst (tpRouteInit_traceOK g aMain)
  have hr := binRoute_TPREq rule g w ops hv (tpRouteInit g aMain)
  rw [tpFails_of_traceOK g t1, tpFails_of_traceOK g t2]
  have hstage : ∀ j, (∃ n, (TPTest.stash j, n) ∈
        (runTPOps rule g w ops (tpRouteInit g aMain)).trace) ↔
      (∃ n, (TPTest.stash j, n) ∈
        (runTPOps rule g w g.canonicalOps (tpRouteInit g aMain)).trace) := by
    intro j
    rw [runTPOps_trace_stage, runTPOps_trace_stage]
    simp only [tpRouteInit, List.not_mem_nil, exists_false, false_or]
    exact ⟨fun ⟨o, ho, h⟩ => ⟨o, hv.1.subset ho, h⟩,
      fun ⟨o, ho, h⟩ => ⟨o, hv.1.symm.subset ho, h⟩⟩
  simp only [hstage, (hr.perm _).length_eq]

end RebuildBound.TP6Aux
