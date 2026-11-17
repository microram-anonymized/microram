import Mathlib
import RebuildBound.Spec.Model.SepContract
import RebuildBound.Proofs.ListAux.Lists

/-!
# S4a helpers: what the traces record

* the route trace records only stage-stash and radix tests; the finish trace
  only insertion tests and the drain trace only drain tests;
* every stage-stash entry is at most its stash's final length, and a nonempty
  final stash has its length recorded (`RouteP`);
* the same for the radix stash.
-/

namespace RebuildBound.S4aProof

open RebuildBound.Model
open RebuildBound.D4aProof (getD_set_of_lt)

/-! ### Stage stashes -/

/-- Trace facts of a route state: entries are stage-stash tests bounded by their
stash's length, and every nonempty stash has its length recorded. -/
def RouteP (st : SRoute) : Prop :=
  (∀ e ∈ st.trace, ∃ j c, e.1 = .stash j c) ∧
  (∀ e ∈ st.trace, ∀ j c, e.1 = .stash j c → e.2 ≤ (st.stash.getD j []).length) ∧
  (∀ j, st.stash.getD j [] = [] ∨ ∃ c, (STest.stash j c, (st.stash.getD j []).length) ∈ st.trace)

lemma sPairStep_stash_len (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j i : ℕ) (st : SRoute) :
    (sPairStep rule g w j i st).stash.length = st.stash.length := by
  simp [sPairStep]

lemma sPairStep_radix (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j i : ℕ) (st : SRoute) :
    (sPairStep rule g w j i st).radix = st.radix := rfl

lemma sPairStep_routeP (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (j i : ℕ) (st : SRoute)
    (hj : j < st.stash.length) (h : RouteP st) : RouteP (sPairStep rule g w j i st) := by
  obtain ⟨h1, h2, h3⟩ := h
  set sj := st.stash.getD j [] ++ (rule.split g.C (dirBit w j) (st.main.getD i [])
    (st.main.getD (i + 2 ^ j) [])).2.2 with hsj
  have hst : (sPairStep rule g w j i st).stash = st.stash.set j sj := rfl
  have htr : (sPairStep rule g w j i st).trace =
      st.trace ++ [(STest.stash j (decide (i < 2 ^ j)), sj.length)] := rfl
  have hget : ∀ j', (sPairStep rule g w j i st).stash.getD j' [] =
      if j' = j then sj else st.stash.getD j' [] := by
    intro j'; rw [hst, getD_set_of_lt _ _ _ _ _ hj]
  have hle : (st.stash.getD j []).length ≤ sj.length := by rw [hsj, List.length_append]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [htr] at he
    rcases List.mem_append.mp he with he | he
    · exact h1 e he
    · simp only [List.mem_singleton] at he; subst he; exact ⟨j, _, rfl⟩
  · intro e he j' c hec
    rw [htr] at he
    rw [hget]
    rcases List.mem_append.mp he with he | he
    · have := h2 e he j' c hec
      split_ifs with hjj
      · subst hjj; omega
      · exact this
    · simp only [List.mem_singleton] at he; subst he
      simp only [STest.stash.injEq] at hec
      obtain ⟨rfl, _⟩ := hec
      simp
  · intro j'
    rw [hget, htr]
    by_cases hjj : j' = j
    · rw [hjj]; right; exact ⟨decide (i < 2 ^ j), by simp⟩
    · rw [if_neg hjj]
      rcases h3 j' with h | ⟨c, hc⟩
      · left; exact h
      · right; exact ⟨c, List.mem_append_left _ hc⟩

lemma runSOps_routeP (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → Nat) (ops : List (ℕ × ℕ))
    (hops : ∀ o ∈ ops, o.1 < g.k) :
    ∀ st : SRoute, st.stash.length = g.k → RouteP st →
      RouteP (runSOps rule g w ops st) ∧ (runSOps rule g w ops st).stash.length = g.k ∧
        (runSOps rule g w ops st).radix = st.radix := by
  induction ops with
  | nil => intro st h1 h2; exact ⟨h2, h1, rfl⟩
  | cons o ops ih =>
    intro st h1 h2
    unfold runSOps at *
    rw [List.foldl_cons]
    have hj : o.1 < st.stash.length := by rw [h1]; exact hops o (by simp)
    obtain ⟨a, b, c⟩ := ih (fun o' ho' => hops o' (List.mem_cons_of_mem _ ho'))
      (sPairStep rule g w o.1 o.2 st) (by rw [sPairStep_stash_len]; exact h1)
      (sPairStep_routeP rule g w o.1 o.2 st hj h2)
    exact ⟨a, b, by rw [c]; rfl⟩

lemma routeInit_routeP (g : SepGeom) (aMain : List Bucket) : RouteP (sRouteInit g aMain) := by
  have hst : ∀ j, (sRouteInit g aMain).stash.getD j [] = [] := by
    intro j
    simp only [sRouteInit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  refine ⟨by simp [sRouteInit], by simp [sRouteInit], fun j => Or.inl (hst j)⟩

/-! ### The radix pass -/

lemma radixStep_radix (g : SepGeom) (w : Model.LogicalKey → Nat) (p : ℕ) (st : SRoute) :
    ∃ s, (radixStep g w p st).radix = st.radix ++ s ∧
      (radixStep g w p st).trace = st.trace ++ [(STest.radix, (st.radix ++ s).length)] ∧
      (radixStep g w p st).stash = st.stash :=
  ⟨_, rfl, rfl, rfl⟩

/-- Trace facts of a state after the radix pass: stage entries are untouched,
radix entries are at most the radix stash's length. -/
def RadixP (st : SRoute) : Prop :=
  (∀ e ∈ st.trace, (∃ j c, e.1 = .stash j c) ∨ e.1 = .radix) ∧
  (∀ e ∈ st.trace, e.1 = .radix → e.2 ≤ st.radix.length)

lemma radixStep_radixP (g : SepGeom) (w : Model.LogicalKey → Nat) (p : ℕ) (st : SRoute) (h : RadixP st) :
    RadixP (radixStep g w p st) := by
  obtain ⟨s, h1, h2, h3⟩ := radixStep_radix g w p st
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · intro e he
    rw [h2] at he
    rcases List.mem_append.mp he with he | he
    · exact a e he
    · simp only [List.mem_singleton] at he; subst he; right; rfl
  · intro e he hr
    rw [h2] at he
    rw [h1, List.length_append]
    rcases List.mem_append.mp he with he | he
    · have := b e he hr
      omega
    · simp only [List.mem_singleton] at he; subst he; simp

lemma radixPass_radixP (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SRoute) (h : RadixP st) :
    RadixP (radixPass g w st) := by
  unfold radixPass
  split_ifs
  · refine List.foldlRecOn (motive := RadixP) _ _ h ?_
    intro b hb p _
    exact radixStep_radixP g w p b hb
  · exact h

lemma radixPass_last (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SRoute) (h1 : 1 < g.r) :
    ∃ e ∈ (radixPass g w st).trace, e.1 = .radix ∧ e.2 = (radixPass g w st).radix.length := by
  unfold radixPass
  rw [if_pos h1]
  have hb : g.blk = (g.blk - 1) + 1 := by
    have : 0 < g.blk := by unfold SepGeom.blk; positivity
    omega
  rw [hb, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  obtain ⟨s, h1, h2, h3⟩ := radixStep_radix g w (g.blk - 1)
    ((List.range (g.blk - 1)).foldl (fun st p => radixStep g w p st) st)
  rw [h2, h1]
  exact ⟨(STest.radix, (((List.range (g.blk - 1)).foldl (fun st p => radixStep g w p st) st).radix ++ s).length), by simp, rfl, rfl⟩

lemma radixPass_trace (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SRoute) :
    ∀ e ∈ (radixPass g w st).trace, e ∈ st.trace ∨ e.1 = .radix := by
  unfold radixPass
  split_ifs
  · refine List.foldlRecOn (motive := fun s : SRoute => ∀ e ∈ s.trace, e ∈ st.trace ∨ e.1 = .radix)
      _ _ (fun e he => Or.inl he) ?_
    intro b hb p _ e he
    obtain ⟨s, h1, h2, h3⟩ := radixStep_radix g w p b
    rw [h2] at he
    rcases List.mem_append.mp he with he | he
    · exact hb e he
    · simp only [List.mem_singleton] at he; right; rw [he]
  · intro e he; exact Or.inl he

lemma radixPass_trace_sup (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SRoute) :
    ∀ e ∈ st.trace, e ∈ (radixPass g w st).trace := by
  unfold radixPass
  split_ifs
  · refine List.foldlRecOn (motive := fun s : SRoute => ∀ e ∈ st.trace, e ∈ s.trace)
      _ _ (fun e he => he) ?_
    intro b hb p _ e he
    obtain ⟨s, h1, h2, h3⟩ := radixStep_radix g w p b
    rw [h2]
    exact List.mem_append_left _ (hb e he)
  · intro e he; exact he

lemma mem_sDfsTrace (g : SepGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (e : STest × ℕ)
    (he : e ∈ sDfsTrace g w pool) :
    ∃ d < g.rangeBits + 1, ∃ c < 2 ^ d, e = (.dfs d c,
      (pool.filter fun r => sRange g w r / 2 ^ (g.rangeBits - d) == c).length) := by
  simp only [sDfsTrace, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨d, hd, c, hc, rfl⟩ := he
  exact ⟨d, hd, c, hc, rfl⟩

lemma radixPass_of_not (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SRoute) (h : ¬ 1 < g.r) :
    radixPass g w st = st := by
  unfold radixPass; rw [if_neg h]

/-! ### The later phases -/

lemma sOfferB_trace (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : ℕ) (st : SFin) :
    (sOfferB g w ci st).trace = st.trace := by
  unfold sOfferB
  refine List.foldlRecOn (motive := fun s : SFin => s.trace = st.trace) _ _ rfl ?_
  intro b hb pg _
  rw [← hb]; rfl

lemma sOfferA_trace (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : ℕ) (st : SFin) :
    (sOfferA g w ci st).trace = st.trace := rfl

lemma sInsertBucket_tag (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : ℕ) (st : SFin)
    (h : ∀ e ∈ st.trace, e.1 = .insertion) :
    ∀ e ∈ (sInsertBucket g w bMain i st).trace, e.1 = .insertion := by
  unfold sInsertBucket
  simp only []
  refine (List.foldlRecOn (motive := fun acc : SFin × List Rec =>
    ∀ e ∈ acc.1.trace, e.1 = .insertion) _ _ ?_ ?_)
  · simpa using h
  · intro acc hacc q _
    simp only []
    rw [sOfferB_trace, sOfferA_trace]
    split_ifs with hq
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact hacc e he
      · rw [he]
    · exact hacc

lemma sFinish_tag (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (routed : List Bucket)
    (leaves : List (List Rec)) : ∀ e ∈ (sFinish g w inp routed leaves).trace, e.1 = .insertion := by
  unfold sFinish
  refine List.foldlRecOn (motive := fun s : SFin => ∀ e ∈ s.trace, e.1 = .insertion) _ _
    (by simp) ?_
  intro b hb i _
  exact sInsertBucket_tag g w inp.bMain i b hb

lemma sDrainStep_tag (acc : List (Option (Rec × Bool)) × List (STest × ℕ)) (L : List (Rec × Bool))
    (h : ∀ e ∈ acc.2, e.1 = .drain) : ∀ e ∈ (sDrainStep acc L).2, e.1 = .drain := by
  intro e he
  simp only [sDrainStep, List.mem_append, List.mem_singleton] at he
  rcases he with he | he
  · exact h e he
  · rw [he]

lemma sDrain_tag (st : SFin) : ∀ e ∈ (sDrain st).2, e.1 = .drain := by
  intro e he
  unfold sDrain at he
  refine sDrainStep_tag _ _ ?_ e he
  refine List.foldlRecOn (motive := fun acc : List (Option (Rec × Bool)) × List (STest × ℕ) =>
      ∀ e ∈ acc.2, e.1 = .drain) _ _ (by simp) ?_
  intro b hb L _
  exact sDrainStep_tag b L hb

end RebuildBound.S4aProof
