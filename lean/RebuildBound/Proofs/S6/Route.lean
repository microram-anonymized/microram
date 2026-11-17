import RebuildBound.Proofs.RouteCore.Basic
import RebuildBound.Spec.SepT

/-!
# S6: A's binary route under a valid schedule

The general-digit counterpart of `D6/Route.lean`.

* `sPairStep` on disjoint pairs commutes up to stash order (`SREq`).
* A valid schedule (`SValidSched`) agrees with `canonicalOps` on every
  conflicting pair, so by the shared exchange argument (`Exchange.ExchHyp.sched`)
  its binary route is `SREq` to the stage-by-stage one.
* The route trace fails iff some touched stage stash's final length fails.
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6 RebuildBound.Exchange

/-- The stage of bit `j` of the stage-by-stage schedule. -/
def sStage (g : SepGeom) (j : Nat) : List (Nat × Nat) :=
  ((List.range g.N).filter fun i => !i.testBit j && decide (g.U ≤ i + 2 ^ j)).map fun i => (j, i)

theorem canonicalOps_eq (g : SepGeom) : g.canonicalOps = (List.range g.k).flatMap (sStage g) := rfl

theorem mem_sStage (g : SepGeom) (j : Nat) (o : Nat × Nat) :
    o ∈ sStage g j ↔ o.1 = j ∧ o.2 < g.N ∧ o.2.testBit j = false ∧ g.U ≤ o.2 + 2 ^ j := by
  obtain ⟨a, b⟩ := o
  simp only [sStage, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hb, hu⟩, rfl, rfl⟩
    exact ⟨rfl, hi, hb, hu⟩
  · rintro ⟨rfl, hb, ht, hu⟩
    exact ⟨b, ⟨hb, ht, hu⟩, rfl, rfl⟩

theorem mem_canonical (g : SepGeom) (o : Nat × Nat) :
    o ∈ g.canonicalOps ↔
      o.1 < g.k ∧ o.2 < g.N ∧ o.2.testBit o.1 = false ∧ g.U ≤ o.2 + 2 ^ o.1 := by
  rw [canonicalOps_eq]
  simp only [List.mem_flatMap, List.mem_range, mem_sStage]
  constructor
  · rintro ⟨j, hj, rfl, h1, h2, h3⟩
    exact ⟨hj, h1, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨o.1, h0, rfl, h1, h2, h3⟩

theorem sStage_fst (g : SepGeom) (j : Nat) (o : Nat × Nat) (h : o ∈ sStage g j) : o.1 = j :=
  ((mem_sStage g j o).mp h).1

theorem nodup_sStage (g : SepGeom) (j : Nat) : (sStage g j).Nodup := by
  unfold sStage
  refine List.Nodup.map (fun a b h => by simpa using h) ?_
  exact (List.nodup_range).filter _

/-! ### The pair operation on `SRoute` -/

section Pair

variable (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat)

/-- The merge-split of pair `(j, i)` on main `m`. -/
def sSplitAt (j i : Nat) (m : List Bucket) : Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w j) (m.getD i []) (m.getD (i + 2 ^ j) [])

/-- The main buckets after pair `(j, i)`. -/
def sPairMain (j i : Nat) (m : List Bucket) : List Bucket :=
  (m.set i (sSplitAt rule g w j i m).1).set (i + 2 ^ j) (sSplitAt rule g w j i m).2.1

theorem sPairStep_main (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).main = sPairMain rule g w j i st.main := rfl

theorem sPairStep_stash (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).stash =
      st.stash.set j (st.stash.getD j [] ++ (sSplitAt rule g w j i st.main).2.2) := rfl

theorem sPairStep_radix (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).radix = st.radix := rfl

theorem sPairStep_trace (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).trace =
      st.trace ++ [(STest.stash j (decide (i < 2 ^ j)),
        (st.stash.getD j [] ++ (sSplitAt rule g w j i st.main).2.2).length)] := rfl

theorem sPairStep_stash_length (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).stash.length = st.stash.length := by
  simp [sPairStep_stash]

theorem sPairStep_main_length (j i : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).main.length = st.main.length := by
  simp [sPairStep_main, sPairMain]

theorem sPairStep_stash_getD (j i j' : Nat) (st : SRoute) :
    (sPairStep rule g w j i st).stash.getD j' [] =
      if j = j' ∧ j < st.stash.length then
        st.stash.getD j' [] ++ (sSplitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] :=
  RouteCore.coreStash_getD j i j' (st.main, st.stash)

/-- Route states with the same buckets, the same radix stash and the same stage
stash contents up to order. -/
structure SREq (s t : SRoute) : Prop where
  main : s.main = t.main
  len : s.stash.length = t.stash.length
  perm : ∀ j, (s.stash.getD j []).Perm (t.stash.getD j [])
  radix : s.radix = t.radix

theorem SREq.refl (s : SRoute) : SREq s s := ⟨rfl, rfl, fun _ => List.Perm.refl _, rfl⟩

theorem SREq.symm {s t : SRoute} (h : SREq s t) : SREq t s :=
  ⟨h.main.symm, h.len.symm, fun j => (h.perm j).symm, h.radix.symm⟩

theorem SREq.trans {s t u : SRoute} (h : SREq s t) (h' : SREq t u) : SREq s u :=
  ⟨h.main.trans h'.main, h.len.trans h'.len, fun j => (h.perm j).trans (h'.perm j),
    h.radix.trans h'.radix⟩

variable {rule g w} in
theorem SREq.pairStep {s t : SRoute} (h : SREq s t) (j i : Nat) :
    SREq (sPairStep rule g w j i s) (sPairStep rule g w j i t) := by
  refine ⟨by rw [sPairStep_main, sPairStep_main, h.main], by
    rw [sPairStep_stash_length, sPairStep_stash_length, h.len], fun j' => ?_, h.radix⟩
  rw [sPairStep_stash_getD, sPairStep_stash_getD, h.len, h.main]
  split_ifs
  · exact (h.perm j').append_right _
  · exact h.perm j'

/-- Operations on disjoint bucket pairs commute up to stash order. -/
theorem sPairStep_comm (a b : Nat × Nat) (hab : ¬Conflict a b) (s : SRoute) :
    SREq (sPairStep rule g w a.1 a.2 (sPairStep rule g w b.1 b.2 s))
      (sPairStep rule g w b.1 b.2 (sPairStep rule g w a.1 a.2 s)) := by
  have h := RouteCore.coreStep_comm (rule := rule) (C := g.C) (w := w) a b hab (s.main, s.stash)
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

/-- The step function of `runSOps`. -/
def sStep (o : Nat × Nat) (st : SRoute) : SRoute := sPairStep rule g w o.1 o.2 st

theorem runSOps_eq (ops : List (Nat × Nat)) (st : SRoute) :
    runSOps rule g w ops st = runL (sStep rule g w) ops st := rfl

theorem sExchHyp : ExchHyp (sStep rule g w) SREq where
  refl := SREq.refl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h h' => h.trans h'
  pres := fun o _ _ h => h.pairStep o.1 o.2
  comm := fun a b s h => sPairStep_comm rule g w a b h s

theorem runSOps_cons (o : Nat × Nat) (l : List (Nat × Nat)) (st : SRoute) :
    runSOps rule g w (o :: l) st = runSOps rule g w l (sPairStep rule g w o.1 o.2 st) := rfl

end Pair

/-- **Part 1.** The binary route under a valid schedule equals the
stage-by-stage one up to stage stash order. -/
theorem binRoute_SREq (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (ops : List (Nat × Nat))
    (hv : SValidSched g ops) (st : SRoute) :
    SREq (runSOps rule g w ops st) (runSOps rule g w g.canonicalOps st) := by
  rw [runSOps_eq, runSOps_eq]
  exact (sExchHyp rule g w).sched (sStage_fst g) (fun j o h => ((mem_sStage g j o).mp h).2.2.1)
    (nodup_sStage g) g.k ops hv.1 hv.2 st

/-! ### The route trace -/

/-- The route trace records running stage stash lengths. -/
def STraceOK (st : SRoute) : Prop :=
  (∀ x ∈ st.trace, ∃ j c, x.1 = STest.stash j c ∧ x.2 ≤ (st.stash.getD j []).length) ∧
  (∀ j c n, (STest.stash j c, n) ∈ st.trace →
    ∃ c', (STest.stash j c', (st.stash.getD j []).length) ∈ st.trace)

theorem STraceOK.step {rule : CapRule} {g : SepGeom} {w : Model.LogicalKey → Nat} {st : SRoute}
    (h : STraceOK st) (j i : Nat) (hj : j < st.stash.length) :
    STraceOK (sPairStep rule g w j i st) := by
  have hget : ∀ j', (sPairStep rule g w j i st).stash.getD j' [] =
      if j = j' then st.stash.getD j' [] ++ (sSplitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] := by
    intro j'
    rw [sPairStep_stash_getD]
    by_cases hjj : j = j'
    · rw [ite_eq_left ⟨hjj, hj⟩, ite_eq_left hjj]
    · rw [ite_eq_right (fun h => hjj h.1), ite_eq_right hjj]
  have hle : ∀ j', (st.stash.getD j' []).length ≤
      ((sPairStep rule g w j i st).stash.getD j' []).length := by
    intro j'
    rw [hget]
    split_ifs <;> simp
  constructor
  · intro x hx
    rw [sPairStep_trace, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨j', c, h1, h2⟩ := h.1 x hx
      exact ⟨j', c, h1, h2.trans (hle j')⟩
    · refine ⟨j, _, rfl, ?_⟩
      rw [hget, ite_eq_left rfl]
  · intro j' c n hx
    rw [sPairStep_trace, List.mem_append, List.mem_singleton] at hx
    by_cases hjj : j = j'
    · subst hjj
      refine ⟨decide (i < 2 ^ j), ?_⟩
      rw [sPairStep_trace, List.mem_append, List.mem_singleton]
      right
      rw [hget, ite_eq_left rfl]
    · rcases hx with hx | hx
      · obtain ⟨c', hc'⟩ := h.2 j' c n hx
        refine ⟨c', ?_⟩
        rw [sPairStep_trace, List.mem_append]
        left
        rw [hget, ite_eq_right hjj]
        exact hc'
      · simp only [Prod.mk.injEq, STest.stash.injEq] at hx
        exact absurd hx.1.1.symm hjj

theorem runSOps_stash_length (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : SRoute),
      (runSOps rule g w l st).stash.length = st.stash.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runSOps_cons, runSOps_stash_length rule g w l, sPairStep_stash_length]

theorem runSOps_main_length (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : SRoute),
      (runSOps rule g w l st).main.length = st.main.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runSOps_cons, runSOps_main_length rule g w l, sPairStep_main_length]

theorem runSOps_radix (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : SRoute), (runSOps rule g w l st).radix = st.radix
  | [], _ => rfl
  | o :: l, st => by
    rw [runSOps_cons, runSOps_radix rule g w l, sPairStep_radix]

theorem runSOps_traceOK (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : SRoute), (∀ o ∈ l, o.1 < st.stash.length) →
      STraceOK st → STraceOK (runSOps rule g w l st)
  | [], _, _, h => h
  | o :: l, st, hl, h => by
    rw [runSOps_cons]
    refine runSOps_traceOK rule g w l _ ?_ (h.step o.1 o.2 (hl o List.mem_cons_self))
    intro o' ho'
    rw [sPairStep_stash_length]
    exact hl o' (List.mem_cons_of_mem _ ho')

theorem runSOps_trace_stage (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j : Nat) :
    ∀ (l : List (Nat × Nat)) (st : SRoute),
      (∃ c n, (STest.stash j c, n) ∈ (runSOps rule g w l st).trace) ↔
        (∃ c n, (STest.stash j c, n) ∈ st.trace) ∨ ∃ o ∈ l, o.1 = j
  | [], st => by simp [runSOps]
  | o :: l, st => by
    rw [runSOps_cons, runSOps_trace_stage rule g w j l, sPairStep_trace]
    constructor
    · rintro (⟨c, n, hn⟩ | ⟨o', ho', h'⟩)
      · rw [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | hn
        · exact Or.inl ⟨c, n, hn⟩
        · simp only [Prod.mk.injEq, STest.stash.injEq] at hn
          exact Or.inr ⟨o, List.mem_cons_self, hn.1.1.symm⟩
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h'⟩
    · rintro (⟨c, n, hn⟩ | ⟨o', ho', h'⟩)
      · exact Or.inl ⟨c, n, List.mem_append_left _ hn⟩
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · subst h'
          exact Or.inl ⟨_, _, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · exact Or.inr ⟨o', ho', h'⟩

/-- Some test of a trace fails. -/
def SFails (g : SepGeom) (tr : List (STest × Nat)) : Prop :=
  ∃ x ∈ tr, g.capOf x.1 < x.2

theorem sFails_append (g : SepGeom) (a b : List (STest × Nat)) :
    SFails g (a ++ b) ↔ SFails g a ∨ SFails g b := by
  simp only [SFails, List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, hf⟩
    · exact Or.inl ⟨x, hx, hf⟩
    · exact Or.inr ⟨x, hx, hf⟩
  · rintro (⟨x, hx, hf⟩ | ⟨x, hx, hf⟩)
    · exact ⟨x, Or.inl hx, hf⟩
    · exact ⟨x, Or.inr hx, hf⟩

theorem sFails_of_traceOK (g : SepGeom) {st : SRoute} (h : STraceOK st) :
    SFails g st.trace ↔ ∃ j, (∃ c n, (STest.stash j c, n) ∈ st.trace) ∧
      g.stashPages * g.C < (st.stash.getD j []).length := by
  constructor
  · rintro ⟨x, hx, hf⟩
    obtain ⟨j, c, h1, h2⟩ := h.1 x hx
    obtain ⟨t, n⟩ := x
    simp only at h1 h2 hf
    subst h1
    exact ⟨j, ⟨c, n, hx⟩, lt_of_lt_of_le hf h2⟩
  · rintro ⟨j, ⟨c, n, hn⟩, hf⟩
    obtain ⟨c', hc'⟩ := h.2 j c n hn
    exact ⟨_, hc', hf⟩

theorem sRouteInit_traceOK (g : SepGeom) (aMain : List Bucket) :
    STraceOK (sRouteInit g aMain) := by
  constructor <;> simp [sRouteInit]

/-- **Binary route verdict.** -/
theorem binRoute_fails_iff (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (ops : List (Nat × Nat)) (hv : SValidSched g ops) :
    SFails g (runSOps rule g w ops (sRouteInit g aMain)).trace ↔
      SFails g (runSOps rule g w g.canonicalOps (sRouteInit g aMain)).trace := by
  have hst : ∀ o ∈ g.canonicalOps, o.1 < (sRouteInit g aMain).stash.length := by
    intro o ho
    simpa [sRouteInit] using ((mem_canonical g o).mp ho).1
  have hst' : ∀ o ∈ ops, o.1 < (sRouteInit g aMain).stash.length :=
    fun o ho => hst o (hv.1.subset ho)
  have t1 := runSOps_traceOK rule g w ops _ hst' (sRouteInit_traceOK g aMain)
  have t2 := runSOps_traceOK rule g w g.canonicalOps _ hst (sRouteInit_traceOK g aMain)
  have hr := binRoute_SREq rule g w ops hv (sRouteInit g aMain)
  rw [sFails_of_traceOK g t1, sFails_of_traceOK g t2]
  have hstage : ∀ j, (∃ c n, (STest.stash j c, n) ∈
        (runSOps rule g w ops (sRouteInit g aMain)).trace) ↔
      (∃ c n, (STest.stash j c, n) ∈
        (runSOps rule g w g.canonicalOps (sRouteInit g aMain)).trace) := by
    intro j
    rw [runSOps_trace_stage, runSOps_trace_stage]
    simp only [sRouteInit, List.not_mem_nil, exists_false, false_or]
    exact ⟨fun ⟨o, ho, h⟩ => ⟨o, hv.1.subset ho, h⟩,
      fun ⟨o, ho, h⟩ => ⟨o, hv.1.symm.subset ho, h⟩⟩
  simp only [hstage, (hr.perm _).length_eq]

end RebuildBound.S6
