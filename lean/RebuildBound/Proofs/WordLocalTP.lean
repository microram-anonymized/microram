import RebuildBound.Spec.WordLocality

/-!
# Word locality of the top preparation (package WordLocalTP)

`tpJob engineRule` reads its word only at the keys of A's records.

Proof: call a record *good* when the two words agree at its key. Every phase
only moves records (copy, merge-split, pool, leaves, offers, drain), so every
record in every intermediate state is one of A's input records, hence good.
Each step reads the word only at records of its state, so under the invariant
"every record of the state is good" both words give the same step. The whole
reference execution (trace and output) is then the same, and so is the job.
-/

namespace RebuildBound.WordLocalTPProof

open RebuildBound.Model

/-! ### Generic membership facts -/

private theorem mem_recs {B : Bucket} {r : Rec} : r ∈ B.recs ↔ some r ∈ B := by
  simp [Bucket.recs]

private theorem getD_mem {α : Type} (l : List α) (i : Nat) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

private theorem forall_set {α : Type} (P : α → Prop) (l : List α) (i : Nat) (a : α)
    (hl : ∀ x ∈ l, P x) (ha : P a) : ∀ x ∈ l.set i a, P x := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hl x h
  · exact h ▸ ha

private theorem forall_getD {α : Type} (P : α → Prop) (l : List α) (i : Nat) (d : α)
    (hl : ∀ x ∈ l, P x) (hd : P d) : P (l.getD i d) := by
  rcases getD_mem l i d with h | h
  · exact hl _ h
  · rw [h]; exact hd

/-- `fill` places only records of the bucket or of the list. -/
private theorem fill_mem {α : Type} :
    ∀ (B : List (Option α)) (L : List α) (x : α),
      (some x ∈ (fill B L).1 → some x ∈ B ∨ x ∈ L) ∧ (x ∈ (fill B L).2 → x ∈ L)
  | [], L, x => by simp [fill]
  | some r :: B, L, x => by
    have ih := fill_mem B L x
    simp only [fill, List.mem_cons]
    refine ⟨fun h => ?_, ih.2⟩
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases ih.1 h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | none :: B, [], x => by simp [fill]
  | none :: B, r :: L, x => by
    have ih := fill_mem B L x
    simp only [fill, List.mem_cons]
    refine ⟨fun h => ?_, fun h => Or.inr (ih.2 h)⟩
    rcases h with h | h
    · exact Or.inr (Or.inl (Option.some.inj h))
    · rcases ih.1 h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- `pick` returns only records of its input. -/
private theorem pick_mem (dir : Rec → Bool) :
    ∀ (S : List Rec) (n0 n1 : Nat) (x : Rec),
      (x ∈ (pick dir n0 n1 S).1 → x ∈ S) ∧ (x ∈ (pick dir n0 n1 S).2.1 → x ∈ S) ∧
        (x ∈ (pick dir n0 n1 S).2.2 → x ∈ S)
  | [], _, _, x => by simp [pick]
  | r :: S, n0, n1, x => by
    have ih := fun n0 n1 => pick_mem dir S n0 n1 x
    cases hd : dir r
    · cases n0 with
      | zero =>
        simp only [pick, hd, Bool.false_eq_true, ite_false, List.mem_cons]
        exact ⟨fun h => Or.inr ((ih _ _).1 h), fun h => Or.inr ((ih _ _).2.1 h),
          fun h => h.elim Or.inl fun h => Or.inr ((ih _ _).2.2 h)⟩
      | succ n0 =>
        simp only [pick, hd, Bool.false_eq_true, ite_false, List.mem_cons]
        exact ⟨fun h => h.elim Or.inl fun h => Or.inr ((ih _ _).1 h),
          fun h => Or.inr ((ih _ _).2.1 h), fun h => Or.inr ((ih _ _).2.2 h)⟩
    · cases n1 with
      | zero =>
        simp only [pick, hd, ite_true, List.mem_cons]
        exact ⟨fun h => Or.inr ((ih _ _).1 h), fun h => Or.inr ((ih _ _).2.1 h),
          fun h => h.elim Or.inl fun h => Or.inr ((ih _ _).2.2 h)⟩
      | succ n1 =>
        simp only [pick, hd, ite_true, List.mem_cons]
        exact ⟨fun h => Or.inr ((ih _ _).1 h),
          fun h => h.elim Or.inl fun h => Or.inr ((ih _ _).2.1 h),
          fun h => Or.inr ((ih _ _).2.2 h)⟩

private theorem pick_congr (dir dir' : Rec → Bool) :
    ∀ (S : List Rec) (n0 n1 : Nat), (∀ r ∈ S, dir r = dir' r) →
      pick dir n0 n1 S = pick dir' n0 n1 S
  | [], _, _, _ => rfl
  | r :: S, n0, n1, h => by
    have hr := h r List.mem_cons_self
    have ih := fun n0 n1 =>
      pick_congr dir dir' S n0 n1 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases n0 <;> cases n1 <;> simp only [pick, hr, ih]

private theorem filter_bucket_mem (p : Rec → Bool) (F : Bucket) (x : Rec)
    (h : some x ∈ F.map fun s => s.filter p) : some x ∈ F := by
  obtain ⟨s, hs, he⟩ := List.mem_map.1 h
  cases s with
  | none => simp at he
  | some y =>
    simp only [Option.filter] at he
    split at he
    · cases he; exact hs
    · cases he

/-- The engine's merge-split returns only records of its two inputs. -/
private theorem engineSplit_mem (C : Nat) (dir : Rec → Bool) (F S : Bucket) (x : Rec) :
    (some x ∈ (engineSplit C dir F S).1 → some x ∈ F ∨ some x ∈ S) ∧
      (some x ∈ (engineSplit C dir F S).2.1 → some x ∈ F ∨ some x ∈ S) ∧
      (x ∈ (engineSplit C dir F S).2.2 → some x ∈ F ∨ some x ∈ S) := by
  have hp := pick_mem dir (Bucket.recs S)
    ((F.map fun s => s.filter fun r => !dir r).countP (·.isNone))
    ((F.map fun s => s.filter dir).countP (·.isNone)) x
  simp only [engineSplit]
  refine ⟨fun h => ?_, fun h => ?_, fun h => Or.inr (mem_recs.1 (hp.2.2 h))⟩
  · rcases (fill_mem _ _ x).1 h with h | h
    · exact Or.inl (filter_bucket_mem _ _ _ h)
    · exact Or.inr (mem_recs.1 (hp.1 h))
  · rcases (fill_mem _ _ x).1 h with h | h
    · exact Or.inl (filter_bucket_mem _ _ _ h)
    · exact Or.inr (mem_recs.1 (hp.2.1 h))

private theorem engineSplit_congr (C : Nat) (dir dir' : Rec → Bool) (F S : Bucket)
    (hF : ∀ r, some r ∈ F → dir r = dir' r) (hS : ∀ r, some r ∈ S → dir r = dir' r) :
    engineSplit C dir F S = engineSplit C dir' F S := by
  have h0 : F.map (fun s => s.filter fun r => !dir r) =
      F.map (fun s => s.filter fun r => !dir' r) := by
    apply List.map_congr_left
    intro s hs; cases s with
    | none => rfl
    | some x => simp [Option.filter, hF x hs]
  have h1 : F.map (fun s => s.filter dir) = F.map (fun s => s.filter dir') := by
    apply List.map_congr_left
    intro s hs; cases s with
    | none => rfl
    | some x => simp [Option.filter, hF x hs]
  unfold engineSplit
  simp only [h0, h1, pick_congr dir dir' (Bucket.recs S) _ _ (fun r hr => hS r (mem_recs.1 hr))]

/-- `eraseFirst` keeps only records of its input. -/
private theorem eraseFirst_mem (p : Rec → Bool) :
    ∀ (n : Nat) (L : List Rec) (x : Rec), x ∈ eraseFirst p n L → x ∈ L
  | 0, L, x, h => by simpa [eraseFirst] using h
  | _ + 1, [], x, h => by simp [eraseFirst] at h
  | n + 1, y :: L, x, h => by
    simp only [eraseFirst] at h
    split at h
    · exact List.mem_cons_of_mem _ (eraseFirst_mem p n L x h)
    · rcases List.mem_cons.1 h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (eraseFirst_mem p (n + 1) L x h)

private theorem eraseFirst_congr (p p' : Rec → Bool) :
    ∀ (n : Nat) (L : List Rec), (∀ r ∈ L, p r = p' r) → eraseFirst p n L = eraseFirst p' n L
  | 0, L, _ => by simp [eraseFirst]
  | _ + 1, [], _ => by simp [eraseFirst]
  | n + 1, y :: L, h => by
    have hy := h y List.mem_cons_self
    have hL := fun r hr => h r (List.mem_cons_of_mem y hr)
    simp only [eraseFirst, hy, eraseFirst_congr p p' n L hL, eraseFirst_congr p p' (n + 1) L hL]

/-! ### The invariant: every record in the state is good -/

variable (g : TPGeom) (w w' : Model.LogicalKey → Nat)

/-- The two words agree at the record's key. -/
def Good (r : Rec) : Prop := w r.key = w' r.key

/-- Every record of a bucket is good. -/
def GoodB (B : Bucket) : Prop := ∀ r, some r ∈ B → Good w w' r

/-- Every record of the route state is good. -/
def GoodRoute (st : TPRoute) : Prop :=
  (∀ B ∈ st.main, GoodB w w' B) ∧ ∀ L ∈ st.stash, ∀ r ∈ L, Good w w' r

/-- Every record of the finish state is good. -/
def GoodFin (st : TPFin) : Prop :=
  (∀ B ∈ st.main, GoodB w w' B) ∧ (∀ r ∈ st.last, Good w w' r) ∧
    ∀ L ∈ st.leaves, ∀ r ∈ L, Good w w' r

/-- The engine's merge-split under two words agreeing on its inputs: the same
result, made of good records. -/
private theorem split_step (C j : Nat) (F S : Bucket) (hF : GoodB w w' F) (hS : GoodB w w' S) :
    engineRule.split C (dirBit w j) F S = engineRule.split C (dirBit w' j) F S ∧
      GoodB w w' (engineRule.split C (dirBit w j) F S).1 ∧
      GoodB w w' (engineRule.split C (dirBit w j) F S).2.1 ∧
      ∀ r ∈ (engineRule.split C (dirBit w j) F S).2.2, Good w w' r := by
  have hd : ∀ (B : Bucket), GoodB w w' B → ∀ r, some r ∈ B → dirBit w j r = dirBit w' j r :=
    fun B hB r hr => by
      have e : w r.key = w' r.key := hB r hr
      simp only [dirBit, e]
  refine ⟨engineSplit_congr C _ _ F S (hd F hF) (hd S hS), ?_, ?_, ?_⟩
  · intro r hr
    rcases (engineSplit_mem C (dirBit w j) F S r).1 hr with h | h
    · exact hF r h
    · exact hS r h
  · intro r hr
    rcases (engineSplit_mem C (dirBit w j) F S r).2.1 hr with h | h
    · exact hF r h
    · exact hS r h
  · intro r hr
    rcases (engineSplit_mem C (dirBit w j) F S r).2.2 hr with h | h
    · exact hF r h
    · exact hS r h

private theorem goodB_nil : GoodB w w' [] := fun _ h => by simp at h

/-! ### Phase 2: the route -/

private theorem tpPairStep_step (j i : Nat) (st : TPRoute) (h : GoodRoute w w' st) :
    tpPairStep engineRule g w j i st = tpPairStep engineRule g w' j i st ∧
      GoodRoute w w' (tpPairStep engineRule g w j i st) := by
  have hF := forall_getD (GoodB w w') st.main i [] h.1 (goodB_nil w w')
  have hS := forall_getD (GoodB w w') st.main (i + 2 ^ j) [] h.1 (goodB_nil w w')
  obtain ⟨he, h1, h2, h3⟩ := split_step w w' g.C j _ _ hF hS
  refine ⟨?_, ?_, ?_⟩
  · simp only [tpPairStep, he]
  · exact forall_set _ _ _ _ (forall_set _ _ _ _ h.1 h1) h2
  · refine forall_set (fun L => ∀ r ∈ L, Good w w' r) _ _ _ h.2 ?_
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact forall_getD (fun L => ∀ r ∈ L, Good w w' r) _ _ _ h.2 (by simp) r hr
    · exact h3 r hr

private theorem runTPOps_step :
    ∀ (ops : List (Nat × Nat)) (st : TPRoute), GoodRoute w w' st →
      runTPOps engineRule g w ops st = runTPOps engineRule g w' ops st ∧
        GoodRoute w w' (runTPOps engineRule g w ops st)
  | [], st, h => ⟨rfl, h⟩
  | o :: ops, st, h => by
    obtain ⟨he, hg⟩ := tpPairStep_step g w w' o.1 o.2 st h
    have ih := runTPOps_step ops _ hg
    simp only [runTPOps, List.foldl_cons] at ih ⊢
    rw [← he]
    exact ih

/-! ### Phase 5: the last level and the offers -/

private theorem tpOffer_step (b : Nat) (st : TPFin) (h : GoodFin w w' st) :
    tpOffer g w b st = tpOffer g w' b st ∧ GoodFin w w' (tpOffer g w b st) := by
  have hleaf := forall_getD (fun L => ∀ r ∈ L, Good w w' r) st.leaves (b / 2 ^ g.I) []
    h.2.2 (by simp)
  have hhome : ∀ r ∈ st.leaves.getD (b / 2 ^ g.I) [],
      (tpHome g w r == b) = (tpHome g w' r == b) := fun r hr => by
    have e : w r.key = w' r.key := hleaf r hr
    simp only [tpHome, e]
  have hcand : (st.leaves.getD (b / 2 ^ g.I) []).filter (fun r => tpHome g w r == b) =
      (st.leaves.getD (b / 2 ^ g.I) []).filter (fun r => tpHome g w' r == b) :=
    List.filter_congr hhome
  have hB := forall_getD (GoodB w w') st.main b [] h.1 (goodB_nil w w')
  refine ⟨?_, ?_, h.2.1, ?_⟩
  · simp only [tpOffer, hcand, eraseFirst_congr _ _ _ _ hhome]
  · refine forall_set _ _ _ _ h.1 ?_
    intro r hr
    rcases (fill_mem _ _ r).1 hr with hr | hr
    · exact hB r hr
    · exact hleaf r (List.mem_filter.1 hr).1
  · refine forall_set (fun L => ∀ r ∈ L, Good w w' r) _ _ _ h.2.2 ?_
    intro r hr
    exact hleaf r (eraseFirst_mem _ _ _ r hr)

private theorem tpLastStep_step (i : Nat) (st : TPFin) (h : GoodFin w w' st) :
    tpLastStep engineRule g w i st = tpLastStep engineRule g w' i st ∧
      GoodFin w w' (tpLastStep engineRule g w i st) := by
  have hF := forall_getD (GoodB w w') st.main i [] h.1 (goodB_nil w w')
  have hS := forall_getD (GoodB w w') st.main (i + g.half) [] h.1 (goodB_nil w w')
  obtain ⟨he, h1, h2, h3⟩ := split_step w w' g.C (g.k - 1) _ _ hF hS
  let p := engineRule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
    (st.main.getD (i + g.half) [])
  let st1 : TPFin := { st with
    main := (st.main.set i p.1).set (i + g.half) p.2.1
    last := st.last ++ p.2.2
    trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] }
  have hst1 : GoodFin w w' st1 := by
    refine ⟨forall_set _ _ _ _ (forall_set _ _ _ _ h.1 h1) h2, ?_, h.2.2⟩
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h.2.1 r hr
    · exact h3 r hr
  have e1 : tpLastStep engineRule g w i st = tpOffer g w (i + g.half) (tpOffer g w i st1) := rfl
  have e2 : tpLastStep engineRule g w' i st = tpOffer g w' (i + g.half) (tpOffer g w' i st1) := by
    simp only [tpLastStep, st1, p, he]
  obtain ⟨o1, g1⟩ := tpOffer_step g w w' i st1 hst1
  obtain ⟨o2, g2⟩ := tpOffer_step g w w' (i + g.half) _ g1
  rw [e1, e2, ← o1, o2]
  exact ⟨rfl, o2 ▸ g2⟩

private theorem finish_fold :
    ∀ (is : List Nat) (st : TPFin), GoodFin w w' st →
      is.foldl (fun st i => tpLastStep engineRule g w i st) st =
        is.foldl (fun st i => tpLastStep engineRule g w' i st) st
  | [], _, _ => rfl
  | i :: is, st, h => by
    obtain ⟨he, hg⟩ := tpLastStep_step g w w' i st h
    simp only [List.foldl_cons]
    rw [← he]
    exact finish_fold is _ hg

/-! ### The reference execution -/

theorem tpReferenceWith_congr (unsh : Rec → Bool) (inp : TPInputs)
    (ops : List (Nat × Nat)) (h : ∀ x ∈ inp.aAll, w x.key = w' x.key) :
    tpReferenceWith engineRule g unsh w inp ops = tpReferenceWith engineRule g unsh w' inp ops := by
  -- The initial route state is good.
  have hinit : GoodRoute w w' (tpRouteInit g (copyMain unsh inp.aMain)) := by
    refine ⟨?_, ?_⟩
    · intro B hB r hr
      simp only [tpRouteInit, copyMain, List.mem_map] at hB
      obtain ⟨B0, hB0, rfl⟩ := hB
      apply h r
      simp only [TPInputs.aAll, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨B0, hB0, mem_recs.2 (filter_bucket_mem _ _ _ hr)⟩
    · intro L hL r hr
      simp only [tpRouteInit] at hL
      rw [List.eq_of_mem_replicate hL] at hr
      simp at hr
  obtain ⟨hroute, hgood⟩ := runTPOps_step g w w' ops _ hinit
  generalize hR : runTPOps engineRule g w ops (tpRouteInit g (copyMain unsh inp.aMain)) = route
    at hroute hgood
  -- The pool is good.
  have hpool : ∀ r ∈ tpPool g unsh route inp.aTier, Good w w' r := by
    intro r hr
    simp only [tpPool, List.mem_filter, List.mem_append, List.mem_flatten] at hr
    rcases hr.1 with ⟨L, hL, hr⟩ | hr
    · exact hgood.2 L (List.mem_of_mem_take hL) r hr
    · exact h r (List.mem_append_right _ hr)
  generalize hP : tpPool g unsh route inp.aTier = pool at hpool
  have hrange : ∀ r ∈ pool, tpRange g w r = tpRange g w' r := fun r hr => by
    have e : w r.key = w' r.key := hpool r hr
    simp only [tpRange, tpHome, e]
  have hleaves : tpLeaves g w pool = tpLeaves g w' pool := by
    simp only [tpLeaves]
    apply List.map_congr_left
    intro v _
    exact List.filter_congr fun r hr => by rw [hrange r hr]
  have hdfs : tpDfsTrace g w pool = tpDfsTrace g w' pool := by
    unfold tpDfsTrace
    congr 1; funext dd; congr 1; funext c
    have : pool.filter (fun r => tpRange g w r / 2 ^ (g.rangeBits - dd) == c) =
        pool.filter (fun r => tpRange g w' r / 2 ^ (g.rangeBits - dd) == c) :=
      List.filter_congr fun r hr => by rw [hrange r hr]
    rw [this]
  -- The finish starts good.
  have hfin0 : GoodFin w w' (⟨route.main, [], tpLeaves g w pool, []⟩ : TPFin) := by
    refine ⟨hgood.1, by simp, ?_⟩
    intro L hL r hr
    simp only [tpLeaves, List.mem_map] at hL
    obtain ⟨v, _, rfl⟩ := hL
    exact hpool r (List.mem_filter.1 hr).1
  have hfin : tpFinish engineRule g w route.main (tpLeaves g w pool) =
      tpFinish engineRule g w' route.main (tpLeaves g w' pool) := by
    rw [← hleaves]
    exact finish_fold g w w' _ _ hfin0
  simp only [tpReferenceWith]
  rw [← hroute, hR, hP, hfin, hleaves, hdfs]

end RebuildBound.WordLocalTPProof

open RebuildBound.Model RebuildBound.WordLocalTPProof in
theorem RebuildBound.TPJobWordLocal : RebuildBound.Spec.TPJobWordLocal_statement := by
  intro g unsh w w' inp h
  unfold tpJob tpJobWith
  rw [tpReferenceWith_congr g w w' unsh inp _ h]
