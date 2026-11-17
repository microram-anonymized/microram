import Mathlib.Data.List.Nodup

/-!
# The schedule exchange argument

Shared by the routes of D6 (binary model), S6 (separated A route) and TP6
(top preparation). Pair operations are `(j, i)`: stage `j` merges buckets `i`
and `i + 2 ^ j`.

* `ExchHyp.exchange`: for any step function on pair operations and any
  equivalence-like relation that steps preserve and under which steps on
  disjoint bucket pairs commute, two orders of the same distinct operations
  that agree on every conflicting pair give related results.
* `validSched_order`: a permutation of a stage-by-stage schedule that orders
  conflicting operations of different stages by stage agrees with it on every
  conflicting pair.
* `ExchHyp.sched`: the two combined, so such a schedule's result is related to
  the stage-by-stage one.
-/

namespace RebuildBound.Exchange

/-- Two pair operations share a bucket (the disjunction of the valid-schedule
definitions `ValidSchedule`, `SValidSched`, `TPValidSchedule`). -/
def Conflict (a b : Nat × Nat) : Prop :=
  a.2 = b.2 ∨ a.2 = b.2 + 2 ^ b.1 ∨ a.2 + 2 ^ a.1 = b.2 ∨ a.2 + 2 ^ a.1 = b.2 + 2 ^ b.1

theorem Conflict.symm {a b : Nat × Nat} (h : Conflict a b) : Conflict b a := by
  unfold Conflict at *; omega

/-- Removing an element from the middle keeps the relative order of the others. -/
theorem idxOf_mid_iff {α : Type*} [BEq α] [LawfulBEq α] (o a b : α) (ha : a ≠ o) (hb : b ≠ o) :
    ∀ (p s : List α),
      ((p ++ o :: s).idxOf a < (p ++ o :: s).idxOf b ↔ (p ++ s).idxOf a < (p ++ s).idxOf b)
  | [], s => by
    simp only [List.nil_append]
    rw [List.idxOf_cons_ne _ (Ne.symm ha), List.idxOf_cons_ne _ (Ne.symm hb)]
    simp
  | c :: p, s => by
    simp only [List.cons_append]
    by_cases hca : c = a <;> by_cases hcb : c = b
    · subst hca; subst hcb; simp
    · subst hca
      rw [List.idxOf_cons_self, List.idxOf_cons_self, List.idxOf_cons_ne _ hcb,
        List.idxOf_cons_ne _ hcb]
      simp
    · subst hcb
      rw [List.idxOf_cons_self, List.idxOf_cons_self, List.idxOf_cons_ne _ hca,
        List.idxOf_cons_ne _ hca]
      simp
    · rw [List.idxOf_cons_ne _ hca, List.idxOf_cons_ne _ hcb, List.idxOf_cons_ne _ hca,
        List.idxOf_cons_ne _ hcb]
      simpa using idxOf_mid_iff o a b ha hb p s

/-! ### The generic exchange argument -/

section Exchange

variable {σ : Type*} (step : Nat × Nat → σ → σ)

/-- Run a list of operations. -/
def runL (l : List (Nat × Nat)) (s : σ) : σ := l.foldl (fun s o => step o s) s

theorem runL_nil (s : σ) : runL step [] s = s := rfl

theorem runL_cons (o : Nat × Nat) (l : List (Nat × Nat)) (s : σ) :
    runL step (o :: l) s = runL step l (step o s) := rfl

theorem runL_append (l1 l2 : List (Nat × Nat)) (s : σ) :
    runL step (l1 ++ l2) s = runL step l2 (runL step l1 s) := by
  simp [runL, List.foldl_append]

/-- The hypotheses of the exchange argument. -/
structure ExchHyp (R : σ → σ → Prop) : Prop where
  refl : ∀ s, R s s
  symm : ∀ s t, R s t → R t s
  trans : ∀ s t u, R s t → R t u → R s u
  pres : ∀ o s t, R s t → R (step o s) (step o t)
  comm : ∀ a b s, ¬Conflict a b → R (step a (step b s)) (step b (step a s))

variable {step} {R : σ → σ → Prop}

theorem ExchHyp.runL (h : ExchHyp step R) :
    ∀ (l : List (Nat × Nat)) (s t : σ), R s t → R (Exchange.runL step l s) (Exchange.runL step l t)
  | [], _, _, hst => hst
  | o :: l, s, t, hst => h.runL l _ _ (h.pres o s t hst)

theorem ExchHyp.commute (h : ExchHyp step R) (o : Nat × Nat) :
    ∀ (p : List (Nat × Nat)), (∀ x ∈ p, ¬Conflict o x) → ∀ s,
      R (Exchange.runL step (p ++ [o]) s) (Exchange.runL step (o :: p) s)
  | [], _, s => h.refl _
  | x :: p, hp, s => by
    have ih := h.commute o p (fun y hy => hp y (List.mem_cons_of_mem _ hy)) (step x s)
    rw [List.cons_append, runL_cons]
    refine h.trans _ _ _ ih ?_
    rw [runL_cons, runL_cons, runL_cons]
    exact h.runL p _ _ (h.comm o x s (hp x List.mem_cons_self))

/-- **Exchange argument.** -/
theorem ExchHyp.exchange (h : ExchHyp step R) :
    ∀ (l1 l2 : List (Nat × Nat)), l1.Perm l2 → l1.Nodup →
      (∀ a ∈ l1, ∀ b ∈ l1, Conflict a b → (l1.idxOf a < l1.idxOf b ↔ l2.idxOf a < l2.idxOf b)) →
      ∀ s, R (Exchange.runL step l1 s) (Exchange.runL step l2 s) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hp _ _ s
    have : l2 = [] := List.Perm.eq_nil hp.symm
    subst this
    exact h.refl _
  | cons o r ih =>
    intro l2 hp hnd hord s
    have ho : o ∈ l2 := hp.subset List.mem_cons_self
    obtain ⟨p, t, rfl⟩ := List.append_of_mem ho
    have hnd2 : (p ++ o :: t).Nodup := hp.nodup_iff.mp hnd
    have hop : o ∉ p := by
      intro hh
      have := List.nodup_append.mp hnd2
      exact this.2.2 o hh o List.mem_cons_self rfl
    have hor : o ∉ r := (List.nodup_cons.mp hnd).1
    have hpc : ∀ x ∈ p, ¬Conflict o x := by
      intro x hx hc
      have hxl : x ∈ o :: r := hp.symm.subset (List.mem_append_left _ hx)
      have key := (hord x hxl o List.mem_cons_self hc.symm).mpr (by
        rw [List.idxOf_append, List.idxOf_append, ite_eq_left hx, ite_eq_right hop,
          List.idxOf_cons_self]
        simpa using List.idxOf_lt_length_of_mem hx)
      simp at key
    have hperm : r.Perm (p ++ t) := (hp.trans List.perm_middle).cons_inv
    have hord' : ∀ a ∈ r, ∀ b ∈ r, Conflict a b →
        (r.idxOf a < r.idxOf b ↔ (p ++ t).idxOf a < (p ++ t).idxOf b) := by
      intro a ha b hb hc
      have hao : a ≠ o := fun e => hor (e ▸ ha)
      have hbo : b ≠ o := fun e => hor (e ▸ hb)
      have := hord a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hc
      rw [List.idxOf_cons_ne _ (Ne.symm hao), List.idxOf_cons_ne _ (Ne.symm hbo)] at this
      rw [← idxOf_mid_iff o a b hao hbo p t, ← this]
      simp
    have h1 := ih (p ++ t) hperm (List.nodup_cons.mp hnd).2 hord' (step o s)
    rw [runL_cons]
    refine h.trans _ _ _ h1 ?_
    have e1 : Exchange.runL step (p ++ t) (step o s) =
        Exchange.runL step t (Exchange.runL step (o :: p) s) := by
      rw [runL_append, runL_cons]
    have e2 : Exchange.runL step (p ++ o :: t) s =
        Exchange.runL step t (Exchange.runL step (p ++ [o]) s) := by
      rw [← runL_append, List.append_assoc, List.singleton_append]
    rw [e1, e2]
    exact h.runL t _ _ (h.symm _ _ (h.commute o p hpc s))

end Exchange

/-! ### Stages and their order -/

section Stages

variable (stage : Nat → List (Nat × Nat))

/-- Stages listed in order run in bit order. -/
theorem idxOf_flatMap_stages (hst : ∀ j o, o ∈ stage j → o.1 = j) :
    ∀ (n : Nat) (a b : Nat × Nat), a ∈ (List.range n).flatMap stage →
      b ∈ (List.range n).flatMap stage → a.1 < b.1 →
      ((List.range n).flatMap stage).idxOf a < ((List.range n).flatMap stage).idxOf b
  | 0, a, _, ha, _, _ => by simp at ha
  | n + 1, a, b, ha, hb, hab => by
    rw [List.range_succ, List.flatMap_append] at ha hb ⊢
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at ha hb ⊢
    have haL : a ∈ (List.range n).flatMap stage := by
      rcases List.mem_append.mp ha with h | h
      · exact h
      · have e1 := hst n a h
        rcases List.mem_append.mp hb with h' | h'
        · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h'
          have := hst j b hj'
          rw [List.mem_range] at hj
          omega
        · have := hst n b h'; omega
    rw [List.idxOf_append, ite_eq_left haL]
    by_cases hbL : b ∈ (List.range n).flatMap stage
    · rw [List.idxOf_append, ite_eq_left hbL]
      exact idxOf_flatMap_stages hst n a b haL hbL hab
    · rw [List.idxOf_append, ite_eq_right hbL]
      have := List.idxOf_lt_length_of_mem haL
      omega

theorem nodup_flatMap_stages (hst : ∀ j o, o ∈ stage j → o.1 = j) (hnd : ∀ j, (stage j).Nodup)
    (n : Nat) : ((List.range n).flatMap stage).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun j _ => hnd j, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro a b _ _ hab x hxa hxb
  exact hab ((hst a x hxa).symm.trans (hst b x hxb))

/-- Two operations of the same stage on low buckets (bit `j` clear) share a
bucket only if they are equal. -/
theorem same_stage (a b : Nat × Nat) (ha : a.2.testBit a.1 = false)
    (hb : b.2.testBit b.1 = false) (hj : a.1 = b.1) (hc : Conflict a b) : a = b := by
  obtain ⟨ja, ia⟩ := a
  obtain ⟨jb, ib⟩ := b
  simp only at hj ha hb
  subst hj
  unfold Conflict at hc
  simp only at hc
  have bit : ∀ x, x.testBit ja = false → (x + 2 ^ ja).testBit ja = true := by
    intro x hx
    rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, hx]; rfl
  rcases hc with h | h | h | h
  · rw [h]
  · have := bit ib hb; rw [← h, ha] at this; exact absurd this (by simp)
  · have := bit ia ha; rw [h, hb] at this; exact absurd this (by simp)
  · have : ia = ib := by omega
    rw [this]

variable {stage}

/-- A permutation of the stage-by-stage schedule that orders conflicting
operations of different stages by stage agrees with it on every conflicting
pair. -/
theorem validSched_order (hst : ∀ j o, o ∈ stage j → o.1 = j)
    (hbit : ∀ j o, o ∈ stage j → o.2.testBit j = false) (n : Nat) (ops : List (Nat × Nat))
    (hp : ops.Perm ((List.range n).flatMap stage))
    (hv : ∀ a ∈ ops, ∀ b ∈ ops, a.1 < b.1 → Conflict a b → ops.idxOf a < ops.idxOf b) :
    ∀ a ∈ ops, ∀ b ∈ ops, Conflict a b →
      (ops.idxOf a < ops.idxOf b ↔
        ((List.range n).flatMap stage).idxOf a < ((List.range n).flatMap stage).idxOf b) := by
  have hb : ∀ o ∈ (List.range n).flatMap stage, o.2.testBit o.1 = false := by
    intro o ho
    obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp ho
    rw [hst j o hj]
    exact hbit j o hj
  intro a ha b hb' hc
  have haC := hp.subset ha
  have hbC := hp.subset hb'
  by_cases hab : a = b
  · subst hab; simp
  have hj : a.1 ≠ b.1 := fun h => hab (same_stage a b (hb a haC) (hb b hbC) h hc)
  rcases Nat.lt_or_gt_of_ne hj with h | h
  · have h1 := hv a ha b hb' h hc
    have h2 := idxOf_flatMap_stages stage hst n a b haC hbC h
    exact ⟨fun _ => h2, fun _ => h1⟩
  · have h1 := hv b hb' a ha h hc.symm
    have h2 := idxOf_flatMap_stages stage hst n b a hbC haC h
    constructor <;> intro h3 <;> omega

/-- **Schedule independence.** A schedule as in `validSched_order` gives a
result related to the stage-by-stage one. -/
theorem ExchHyp.sched {σ : Type*} {step : Nat × Nat → σ → σ} {R : σ → σ → Prop}
    (h : ExchHyp step R) (hst : ∀ j o, o ∈ stage j → o.1 = j)
    (hbit : ∀ j o, o ∈ stage j → o.2.testBit j = false) (hnd : ∀ j, (stage j).Nodup)
    (n : Nat) (ops : List (Nat × Nat)) (hp : ops.Perm ((List.range n).flatMap stage))
    (hv : ∀ a ∈ ops, ∀ b ∈ ops, a.1 < b.1 → Conflict a b → ops.idxOf a < ops.idxOf b)
    (s : σ) : R (Exchange.runL step ops s) (Exchange.runL step ((List.range n).flatMap stage) s) :=
  h.exchange ops _ hp (hp.nodup_iff.mpr (nodup_flatMap_stages stage hst hnd n))
    (validSched_order hst hbit n ops hp hv) s

end Stages

end RebuildBound.Exchange
