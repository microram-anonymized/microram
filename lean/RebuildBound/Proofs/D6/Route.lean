import RebuildBound.Proofs.RouteCore.Basic

/-!
# D6: the route under a valid schedule

* Pair operations on disjoint bucket pairs commute up to stash order (`REq`).
* `pairStep` and `REq` satisfy the shared exchange argument's hypotheses
  (`exchHyp`), so a valid schedule's route is `REq` to the canonical one
  (`Exchange.ExchHyp.sched`).
* The route trace fails iff some touched stash's final length fails.
* The route preserves A's records (`RecInv`), so the pool is key-distinct.
-/

namespace RebuildBound.D6

open RebuildBound.Model RebuildBound.Exchange

section Pair

variable (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat)

/-- The merge-split of pair `(j, i)` on main `m`. -/
def splitAt (j i : Nat) (m : List Bucket) : Bucket × Bucket × List Rec :=
  rule.split g.C (dirBit w j) (m.getD i []) (m.getD (i + 2 ^ j) [])

/-- The main buckets after pair `(j, i)`. -/
def pairMain (j i : Nat) (m : List Bucket) : List Bucket :=
  (m.set i (splitAt rule g w j i m).1).set (i + 2 ^ j) (splitAt rule g w j i m).2.1

theorem pairStep_main (j i : Nat) (st : RouteState) :
    (pairStep rule g w j i st).main = pairMain rule g w j i st.main := rfl

theorem pairStep_stash (j i : Nat) (st : RouteState) :
    (pairStep rule g w j i st).stash =
      st.stash.set j (st.stash.getD j [] ++ (splitAt rule g w j i st.main).2.2) := rfl

theorem pairStep_trace (j i : Nat) (st : RouteState) :
    (pairStep rule g w j i st).trace =
      st.trace ++ [(Test.stash j, (st.stash.getD j [] ++ (splitAt rule g w j i st.main).2.2).length)] :=
  rfl

theorem pairStep_stash_length (j i : Nat) (st : RouteState) :
    (pairStep rule g w j i st).stash.length = st.stash.length := by
  simp [pairStep_stash]

theorem pairStep_main_length (j i : Nat) (st : RouteState) :
    (pairStep rule g w j i st).main.length = st.main.length := by
  simp [pairStep_main, pairMain]

theorem pairStep_stash_getD (j i j' : Nat) (st : RouteState) :
    (pairStep rule g w j i st).stash.getD j' [] =
      if j = j' ∧ j < st.stash.length then
        st.stash.getD j' [] ++ (splitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] :=
  RouteCore.coreStash_getD j i j' (st.main, st.stash)

/-- Route states with the same buckets and the same stash contents up to order. -/
structure REq (s t : RouteState) : Prop where
  main : s.main = t.main
  len : s.stash.length = t.stash.length
  perm : ∀ j, (s.stash.getD j []).Perm (t.stash.getD j [])

theorem REq.refl (s : RouteState) : REq s s := ⟨rfl, rfl, fun _ => List.Perm.refl _⟩

theorem REq.symm {s t : RouteState} (h : REq s t) : REq t s :=
  ⟨h.main.symm, h.len.symm, fun j => (h.perm j).symm⟩

theorem REq.trans {s t u : RouteState} (h : REq s t) (h' : REq t u) : REq s u :=
  ⟨h.main.trans h'.main, h.len.trans h'.len, fun j => (h.perm j).trans (h'.perm j)⟩

variable {rule g w} in
theorem REq.pairStep {s t : RouteState} (h : REq s t) (j i : Nat) :
    REq (pairStep rule g w j i s) (pairStep rule g w j i t) := by
  refine ⟨by rw [pairStep_main, pairStep_main, h.main], by
    rw [pairStep_stash_length, pairStep_stash_length, h.len], fun j' => ?_⟩
  rw [pairStep_stash_getD, pairStep_stash_getD, h.len, h.main]
  split_ifs
  · exact (h.perm j').append_right _
  · exact h.perm j'

theorem runOps_nil (st : RouteState) : runOps rule g w [] st = st := rfl

theorem runOps_cons (o : Nat × Nat) (l : List (Nat × Nat)) (st : RouteState) :
    runOps rule g w (o :: l) st = runOps rule g w l (pairStep rule g w o.1 o.2 st) := rfl

theorem runOps_append (l1 l2 : List (Nat × Nat)) (st : RouteState) :
    runOps rule g w (l1 ++ l2) st = runOps rule g w l2 (runOps rule g w l1 st) := by
  simp [runOps, List.foldl_append]

variable {rule g w} in
theorem REq.runOps {s t : RouteState} (h : REq s t) (l : List (Nat × Nat)) :
    REq (runOps rule g w l s) (runOps rule g w l t) := by
  induction l generalizing s t with
  | nil => exact h
  | cons o l ih => exact ih (h.pairStep o.1 o.2)

/-- Operations on disjoint bucket pairs commute up to stash order. -/
theorem pairStep_comm (a b : Nat × Nat) (hab : ¬Conflict a b) (s : RouteState) :
    REq (pairStep rule g w a.1 a.2 (pairStep rule g w b.1 b.2 s))
      (pairStep rule g w b.1 b.2 (pairStep rule g w a.1 a.2 s)) := by
  have h := RouteCore.coreStep_comm (rule := rule) (C := g.C) (w := w) a b hab (s.main, s.stash)
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The hypotheses of the shared exchange argument for `pairStep` and `REq`. -/
theorem exchHyp : ExchHyp (fun o st => pairStep rule g w o.1 o.2 st) REq where
  refl := REq.refl
  symm := fun _ _ h => h.symm
  trans := fun _ _ _ h h' => h.trans h'
  pres := fun o _ _ h => h.pairStep o.1 o.2
  comm := fun a b s h => pairStep_comm rule g w a b h s

end Pair

/-! ### The canonical schedule -/

theorem mem_stageOps (g : Geom) (j : Nat) (o : Nat × Nat) :
    o ∈ stageOps g j ↔ o.1 = j ∧ o.2 < g.homes ∧ o.2.testBit j = false := by
  obtain ⟨a, b⟩ := o
  simp only [stageOps, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, ⟨hi, hb⟩, rfl, rfl⟩
    exact ⟨rfl, hi, by simpa using hb⟩
  · rintro ⟨rfl, hb, ht⟩
    exact ⟨b, ⟨hb, by simp [ht]⟩, rfl, rfl⟩

theorem mem_ops_upTo (g : Geom) (n : Nat) (o : Nat × Nat) :
    o ∈ (List.range n).flatMap (stageOps g) ↔
      o.1 < n ∧ o.2 < g.homes ∧ o.2.testBit o.1 = false := by
  simp only [List.mem_flatMap, List.mem_range, mem_stageOps]
  constructor
  · rintro ⟨j, hj, rfl, h1, h2⟩
    exact ⟨hj, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨o.1, h0, rfl, h1, h2⟩

theorem mem_canonical (g : Geom) (o : Nat × Nat) :
    o ∈ canonicalOps g ↔ o.1 < g.stages ∧ o.2 < g.homes ∧ o.2.testBit o.1 = false :=
  mem_ops_upTo g g.stages o

theorem nodup_stageOps (g : Geom) (j : Nat) : (stageOps g j).Nodup := by
  unfold stageOps
  refine List.Nodup.map (fun a b h => by simpa using h) ?_
  exact (List.nodup_range).filter _

/-- **Part 1.** The route under a valid schedule equals the canonical route up to
stash order. -/
theorem route_REq (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) (aMain : List Bucket)
    (ops : List (Nat × Nat)) (hv : ValidSchedule g ops) :
    REq (routeWith rule g w aMain ops) (routeA rule g w aMain) := by
  exact (exchHyp rule g w).sched (fun j o h => ((mem_stageOps g j o).mp h).1)
    (fun j o h => ((mem_stageOps g j o).mp h).2.2) (nodup_stageOps g) g.stages ops hv.1 hv.2 _

/-! ### The route trace -/

/-- The route trace records running stash lengths. -/
def TraceOK (st : RouteState) : Prop :=
  (∀ x ∈ st.trace, ∃ j, x.1 = Test.stash j ∧ x.2 ≤ (st.stash.getD j []).length) ∧
  (∀ j n, (Test.stash j, n) ∈ st.trace →
    (Test.stash j, (st.stash.getD j []).length) ∈ st.trace)

theorem TraceOK.step {rule : CapRule} {g : Geom} {w : Model.LogicalKey → Nat} {st : RouteState}
    (h : TraceOK st) (j i : Nat) (hj : j < st.stash.length) :
    TraceOK (pairStep rule g w j i st) := by
  have hget : ∀ j', (pairStep rule g w j i st).stash.getD j' [] =
      if j = j' then st.stash.getD j' [] ++ (splitAt rule g w j i st.main).2.2
      else st.stash.getD j' [] := by
    intro j'
    rw [pairStep_stash_getD]
    by_cases hjj : j = j'
    · rw [ite_eq_left ⟨hjj, hj⟩, ite_eq_left hjj]
    · rw [ite_eq_right (fun h => hjj h.1), ite_eq_right hjj]
  have hle : ∀ j', (st.stash.getD j' []).length ≤
      ((pairStep rule g w j i st).stash.getD j' []).length := by
    intro j'
    rw [hget]
    split_ifs <;> simp
  constructor
  · intro x hx
    rw [pairStep_trace, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨j', h1, h2⟩ := h.1 x hx
      exact ⟨j', h1, h2.trans (hle j')⟩
    · refine ⟨j, rfl, ?_⟩
      rw [hget, ite_eq_left rfl]
  · intro j' n hx
    rw [pairStep_trace, List.mem_append, List.mem_singleton] at hx ⊢
    by_cases hjj : j = j'
    · subst hjj
      right
      rw [hget, ite_eq_left rfl]
    · rcases hx with hx | hx
      · left
        rw [hget, ite_eq_right hjj]
        exact h.2 j' n hx
      · simp only [Prod.mk.injEq, Test.stash.injEq] at hx
        exact absurd hx.1.symm hjj

theorem runOps_stash_length (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : RouteState),
      (runOps rule g w l st).stash.length = st.stash.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runOps_cons, runOps_stash_length rule g w l, pairStep_stash_length]

theorem runOps_main_length (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : RouteState),
      (runOps rule g w l st).main.length = st.main.length
  | [], _ => rfl
  | o :: l, st => by
    rw [runOps_cons, runOps_main_length rule g w l, pairStep_main_length]

theorem runOps_traceOK (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) :
    ∀ (l : List (Nat × Nat)) (st : RouteState), (∀ o ∈ l, o.1 < st.stash.length) →
      TraceOK st → TraceOK (runOps rule g w l st)
  | [], _, _, h => h
  | o :: l, st, hl, h => by
    rw [runOps_cons]
    refine runOps_traceOK rule g w l _ ?_ (h.step o.1 o.2 (hl o List.mem_cons_self))
    intro o' ho'
    rw [pairStep_stash_length]
    exact hl o' (List.mem_cons_of_mem _ ho')

theorem runOps_trace_stage (rule : CapRule) (g : Geom) (w : Model.LogicalKey → Nat) (j : Nat) :
    ∀ (l : List (Nat × Nat)) (st : RouteState),
      (∃ n, (Test.stash j, n) ∈ (runOps rule g w l st).trace) ↔
        (∃ n, (Test.stash j, n) ∈ st.trace) ∨ ∃ o ∈ l, o.1 = j
  | [], st => by simp [runOps_nil]
  | o :: l, st => by
    rw [runOps_cons, runOps_trace_stage rule g w j l, pairStep_trace]
    constructor
    · rintro (⟨n, hn⟩ | ⟨o', ho', h'⟩)
      · rw [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | hn
        · exact Or.inl ⟨n, hn⟩
        · simp only [Prod.mk.injEq, Test.stash.injEq] at hn
          exact Or.inr ⟨o, List.mem_cons_self, hn.1.symm⟩
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h'⟩
    · rintro (⟨n, hn⟩ | ⟨o', ho', h'⟩)
      · exact Or.inl ⟨n, List.mem_append_left _ hn⟩
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · subst h'
          exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · exact Or.inr ⟨o', ho', h'⟩

/-- Some test of a trace fails. -/
def Fails (g : Geom) (caps : Caps) (tr : List (Test × Nat)) : Prop :=
  ∃ x ∈ tr, exceeds (caps.capOf g x.1) x.2 = true

theorem exceeds_mono {c : Option Nat} {n m : Nat} (h : exceeds c n = true) (hnm : n ≤ m) :
    exceeds c m = true := by
  cases c with
  | none => simp [exceeds] at h
  | some c => simp [exceeds] at h ⊢; omega

theorem fails_of_traceOK (g : Geom) (caps : Caps) {st : RouteState} (h : TraceOK st) :
    Fails g caps st.trace ↔ ∃ j, (∃ n, (Test.stash j, n) ∈ st.trace) ∧
      exceeds (caps.stash j) (st.stash.getD j []).length = true := by
  constructor
  · rintro ⟨x, hx, hf⟩
    obtain ⟨j, h1, h2⟩ := h.1 x hx
    obtain ⟨t, n⟩ := x
    simp only at h1 h2
    subst h1
    exact ⟨j, ⟨n, hx⟩, exceeds_mono hf h2⟩
  · rintro ⟨j, ⟨n, hn⟩, hf⟩
    exact ⟨_, h.2 j n hn, hf⟩

theorem fails_append (g : Geom) (caps : Caps) (a b : List (Test × Nat)) :
    Fails g caps (a ++ b) ↔ Fails g caps a ∨ Fails g caps b := by
  simp only [Fails, List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, hf⟩
    · exact Or.inl ⟨x, hx, hf⟩
    · exact Or.inr ⟨x, hx, hf⟩
  · rintro (⟨x, hx, hf⟩ | ⟨x, hx, hf⟩)
    · exact ⟨x, Or.inl hx, hf⟩
    · exact ⟨x, Or.inr hx, hf⟩

theorem routeInit_traceOK (g : Geom) (aMain : List Bucket) : TraceOK (routeInit g aMain) := by
  constructor <;> simp [routeInit]

/-- **Route verdict.** A valid schedule's route trace fails iff the canonical
one does. -/
theorem route_fails_iff (rule : CapRule) (g : Geom) (caps : Caps) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (ops : List (Nat × Nat)) (hv : ValidSchedule g ops) :
    Fails g caps (routeWith rule g w aMain ops).trace ↔
      Fails g caps (routeA rule g w aMain).trace := by
  have hst : ∀ o ∈ canonicalOps g, o.1 < (routeInit g aMain).stash.length := by
    intro o ho
    simpa [routeInit] using ((mem_canonical g o).mp ho).1
  have hst' : ∀ o ∈ ops, o.1 < (routeInit g aMain).stash.length :=
    fun o ho => hst o (hv.1.subset ho)
  have t1 := runOps_traceOK rule g w ops _ hst' (routeInit_traceOK g aMain)
  have t2 := runOps_traceOK rule g w (canonicalOps g) _ hst (routeInit_traceOK g aMain)
  have hr := route_REq rule g w aMain ops hv
  have eW : routeWith rule g w aMain ops = runOps rule g w ops (routeInit g aMain) := rfl
  have eA : routeA rule g w aMain = runOps rule g w (canonicalOps g) (routeInit g aMain) := rfl
  rw [eW, eA] at hr ⊢
  rw [fails_of_traceOK g caps t1, fails_of_traceOK g caps t2]
  have hstage : ∀ j, (∃ n, (Test.stash j, n) ∈ (runOps rule g w ops (routeInit g aMain)).trace) ↔
      (∃ n, (Test.stash j, n) ∈
        (runOps rule g w (canonicalOps g) (routeInit g aMain)).trace) := by
    intro j
    rw [runOps_trace_stage, runOps_trace_stage]
    simp only [routeInit, List.not_mem_nil, exists_false, false_or]
    exact ⟨fun ⟨o, ho, h⟩ => ⟨o, hv.1.subset ho, h⟩,
      fun ⟨o, ho, h⟩ => ⟨o, hv.1.symm.subset ho, h⟩⟩
  simp only [hstage, (hr.perm _).length_eq]

/-! ### A's records along the route -/

/-- The route keeps every bucket at `C` lanes and conserves the records. -/
def RecInv (C : Nat) (M0 : List Rec) (st : RouteState) : Prop :=
  (∀ B ∈ st.main, B.length = C) ∧ (st.main.flatMap Bucket.recs ++ st.stash.flatten).Perm M0

theorem RecInv.step {rule : CapRule} (hv : rule.Valid) {g : Geom} {w : Model.LogicalKey → Nat}
    {M0 : List Rec} {st : RouteState} (h : RecInv g.C M0 st) (j i : Nat)
    (hi : i + 2 ^ j < st.main.length) (hj : j < st.stash.length) :
    RecInv g.C M0 (pairStep rule g w j i st) := by
  obtain ⟨⟨-, h2, -⟩, h4, -⟩ := RouteCore.coreStep_spec (rule := rule) (w := w) hv
    (ms := (st.main, st.stash)) ⟨rfl, h.1, rfl⟩ hj hi
  exact ⟨h2, h4.trans h.2⟩

theorem runOps_recInv {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → Nat)
    (M0 : List Rec) :
    ∀ (l : List (Nat × Nat)) (st : RouteState),
      (∀ o ∈ l, o.2 + 2 ^ o.1 < st.main.length ∧ o.1 < st.stash.length) →
      RecInv g.C M0 st → RecInv g.C M0 (runOps rule g w l st)
  | [], _, _, h => h
  | o :: l, st, hl, h => by
    rw [runOps_cons]
    have ho := hl o List.mem_cons_self
    refine runOps_recInv hv g w M0 l _ ?_ (h.step hv o.1 o.2 ho.1 ho.2)
    intro o' ho'
    rw [pairStep_stash_length, pairStep_main_length]
    exact hl o' (List.mem_cons_of_mem _ ho')

/-- A pair of a canonical operation lies inside the `2U` buckets. -/
theorem pair_lt_homes (g : Geom) (o : Nat × Nat) (ho : o ∈ canonicalOps g) :
    o.2 + 2 ^ o.1 < g.homes := by
  rw [mem_canonical] at ho
  obtain ⟨j, i⟩ := o
  simp only [Geom.stages, Geom.homes] at ho ⊢
  obtain ⟨hj, hi, hb⟩ := ho
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  -- write i = 2^j * a + b with b < 2^j; bit j of i is a's parity
  have hdm := Nat.div_add_mod i (2 ^ j)
  set a := i / 2 ^ j with ha
  set b := i % 2 ^ j with hb'
  have hbP : b < 2 ^ j := Nat.mod_lt _ hP
  have hpar : a % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [decide_eq_false_iff_not] at hb
    omega
  have hQ : 2 ^ (g.k + 1) = 2 ^ j * 2 ^ (g.k + 1 - j) := by
    rw [← Nat.pow_add]; congr 1; omega
  have haQ : a < 2 ^ (g.k + 1 - j) := by
    rw [ha, Nat.div_lt_iff_lt_mul hP, Nat.mul_comm, ← hQ]
    exact hi
  have hQe : 2 ^ (g.k + 1 - j) % 2 = 0 := by
    have : g.k + 1 - j = (g.k - j) + 1 := by omega
    rw [this, Nat.pow_succ]; simp
  have ha2 : a + 2 ≤ 2 ^ (g.k + 1 - j) := by omega
  have : 2 ^ j * (a + 2) ≤ 2 ^ j * 2 ^ (g.k + 1 - j) := Nat.mul_le_mul_left _ ha2
  rw [← hQ] at this
  have e : i + 2 ^ j = 2 ^ j * (a + 1) + b := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [e]
  have : 2 ^ j * (a + 2) = 2 ^ j * (a + 1) + 2 ^ j := by rw [Nat.mul_add, Nat.mul_add]; ring
  omega

/-- The initial record list of A's route. -/
theorem routeInit_recInv (g : Geom) (aMain : List Bucket) (hl : ∀ B ∈ aMain, B.length = g.C) :
    RecInv g.C (aMain.flatMap Bucket.recs) (routeInit g aMain) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    simp only [routeInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hl B hB
  · have : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro x hx
      rw [List.eq_of_mem_replicate hx]
      simp [Bucket.empty, Bucket.recs]
    simp [routeInit, List.flatMap_append, this]

/-- The canonical route conserves A's main records. -/
theorem routeA_recInv {rule : CapRule} (hv : rule.Valid) (g : Geom) (w : Model.LogicalKey → Nat)
    (aMain : List Bucket) (hlen : aMain.length = g.U) (hl : ∀ B ∈ aMain, B.length = g.C) :
    RecInv g.C (aMain.flatMap Bucket.recs) (routeA rule g w aMain) := by
  unfold routeA routeUpTo routeWith
  refine runOps_recInv hv g w _ _ _ ?_ (routeInit_recInv g aMain hl)
  intro o ho
  have h1 := pair_lt_homes g o ho
  have h2 := ((mem_canonical g o).mp ho).1
  simp only [routeInit, List.length_append, List.length_replicate, hlen]
  refine ⟨?_, h2⟩
  have : g.homes = g.U + g.U := by simp [Geom.homes, Geom.U, Nat.pow_succ]; ring
  omega

end RebuildBound.D6
