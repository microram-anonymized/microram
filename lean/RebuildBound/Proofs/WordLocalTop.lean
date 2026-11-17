import RebuildBound.Spec.WordLocality

/-!
# Word locality of the top finish (package WordLocalTop)

`topJob` reads its word only through `topHome`, `topWay` and the DFS's
`rangeOf`, and only at records of the pool (a sublist of R), of the B-tier
copy (a sublist of B's tier), of the leaves and the remaining B-tier
candidates (sublists of those), and of B's main buckets. C's records are
moved and cleared by key, never routed. So the reference execution under two
words that agree on every key of `A ∪ B` is the same run.

The proof carries the invariant `Good`: every leaf candidate and every
remaining B-tier candidate is a record on whose key the two words agree. Each
phase step is equal under both words when `Good` holds, and preserves `Good`
(the sweep only filters the leaves and the B-tier copy).
-/

namespace RebuildBound.WordLocalTopProof
open RebuildBound.Model

/-- A fold whose two step functions agree on states satisfying an invariant
that both preserve gives the same result. -/
private theorem foldl_congr_inv {α β : Type} (P : α → Prop) (f f' : α → β → α) :
    ∀ (l : List β) (a : α), P a →
      (∀ a b, b ∈ l → P a → f a b = f' a b ∧ P (f a b)) →
      l.foldl f a = l.foldl f' a ∧ P (l.foldl f a)
  | [], _, ha, _ => ⟨rfl, ha⟩
  | b :: l, a, ha, h => by
    obtain ⟨e, hp⟩ := h a b List.mem_cons_self ha
    simp only [List.foldl_cons, e] at hp ⊢
    exact foldl_congr_inv P f f' l (f' a b) hp
      (fun a' b' hb' ha' => h a' b' (List.mem_cons_of_mem _ hb') ha')

private theorem mem_getD {α : Type} {x : α} :
    ∀ {l : List (List α)} {n : Nat}, x ∈ l.getD n [] → ∃ L ∈ l, x ∈ L
  | [], _, h => by simp at h
  | L :: l, 0, h => ⟨L, List.mem_cons_self, by simpa using h⟩
  | L :: l, n + 1, h => by
    obtain ⟨L', hL', hx⟩ := mem_getD (l := l) (n := n) (by simpa using h)
    exact ⟨L', List.mem_cons_of_mem _ hL', hx⟩

private theorem mem_getD_recs {r : Rec} :
    ∀ {l : List Bucket} {n : Nat}, r ∈ (l.getD n []).recs → ∃ B ∈ l, r ∈ B.recs
  | [], _, h => by simp [Bucket.recs] at h
  | B :: l, 0, h => ⟨B, List.mem_cons_self, by simpa using h⟩
  | B :: l, n + 1, h => by
    obtain ⟨B', hB', hr⟩ := mem_getD_recs (l := l) (n := n) (by simpa using h)
    exact ⟨B', List.mem_cons_of_mem _ hB', hr⟩

/-- Replacing entry `n` by a filter of itself keeps every record a record of
the original list of lists. -/
private theorem mem_set_filter {α : Type} {x : α} {l : List (List α)} {n : Nat}
    {p : α → Bool} {L : List α} (hL : L ∈ l.set n ((l.getD n []).filter p)) (hx : x ∈ L) :
    ∃ L' ∈ l, x ∈ L' := by
  rcases List.mem_or_eq_of_mem_set hL with h | h
  · exact ⟨L, h, hx⟩
  · subst h
    exact mem_getD (List.mem_filter.1 hx).1

section
variable (g : TopGeom) (w w' : Model.LogicalKey → Nat)

/-- The two words agree on the key of `r`. -/
def Agree (r : Rec) : Prop := w r.key = w' r.key

/-- Every leaf candidate and every remaining B-tier candidate is a record on
whose key the two words agree. -/
def Good (st : FinState) : Prop :=
  (∀ L ∈ st.leaves, ∀ r ∈ L, Agree w w' r) ∧ ∀ r ∈ st.bcopy, Agree w w' r

variable {g w w'}

theorem topHome_eq {r : Rec} (h : Agree w w' r) : topHome g w r = topHome g w' r := by
  unfold topHome; rw [h]

theorem topWay_eq {r : Rec} (h : Agree w w' r) : topWay g w r = topWay g w' r := by
  unfold topWay; rw [topHome_eq h]

theorem rangeOf_eq {G : Geom} {r : Rec} (h : Agree w w' r) : rangeOf G w r = rangeOf G w' r := by
  unfold rangeOf home; rw [h]

/-- `Good` after replacing leaf `R` by a filter of itself and filtering the
B-tier copy. -/
private theorem good_of_filters {st st' : FinState} (h : Good w w' st) (R : Nat)
    (p : Rec → Bool) (hl : st'.leaves = st.leaves.set R ((st.leaves.getD R []).filter p))
    (hb : ∀ r ∈ st'.bcopy, r ∈ st.bcopy) : Good w w' st' := by
  refine ⟨fun L hL r hr => ?_, fun r hr => h.2 r (hb r hr)⟩
  rw [hl] at hL
  obtain ⟨L', hL', hr'⟩ := mem_set_filter hL hr
  exact h.1 L' hL' r hr'

private theorem leaf_agree {st : FinState} (h : Good w w' st) (R : Nat) :
    ∀ r ∈ st.leaves.getD R [], topHome g w r = topHome g w' r := fun r hr => by
  obtain ⟨L, hL, hr⟩ := mem_getD hr
  exact topHome_eq (h.1 L hL r hr)

private theorem bcopy_agree {st : FinState} (h : Good w w' st) :
    ∀ r ∈ st.bcopy, topHome g w r = topHome g w' r := fun r hr => topHome_eq (h.2 r hr)

/-! ### The sweep's steps -/

theorem resolve_congr (ci : Nat) (dk : List Model.LogicalKey) {st : FinState} (h : Good w w' st) :
    topResolve g w ci dk st = topResolve g w' ci dk st := by
  have e1 : (st.leaves.getD (ci / 2 ^ g.I) []).filter
        (fun r => !(topHome g w r == ci && (dk.contains r.key || r.tomb))) =
      (st.leaves.getD (ci / 2 ^ g.I) []).filter
        (fun r => !(topHome g w' r == ci && (dk.contains r.key || r.tomb))) :=
    List.filter_congr fun r hr => by rw [leaf_agree h _ r hr]
  have e2 : st.bcopy.filter (fun r => topHome g w r == ci) =
      st.bcopy.filter (fun r => topHome g w' r == ci) :=
    List.filter_congr fun r hr => by rw [bcopy_agree h r hr]
  have e3 : st.bcopy.filter (fun r => !(topHome g w r == ci && r.tomb)) =
      st.bcopy.filter (fun r => !(topHome g w' r == ci && r.tomb)) :=
    List.filter_congr fun r hr => by rw [bcopy_agree h r hr]
  simp only [topResolve]
  rw [e1, e2, e3]

theorem resolve_good (ci : Nat) (dk : List Model.LogicalKey) {st : FinState} (h : Good w w' st) :
    Good w w' (topResolve g w ci dk st) :=
  good_of_filters h _ _ rfl fun _ hr => (List.mem_filter.1 hr).1

theorem offer_congr (ci : Nat) {st : FinState} (h : Good w w' st) :
    topOffer g w ci st = topOffer g w' ci st := by
  have e1 : (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun r => topHome g w r == ci) =
      (st.leaves.getD (ci / 2 ^ g.I) []).filter (fun r => topHome g w' r == ci) :=
    List.filter_congr fun r hr => by rw [leaf_agree h _ r hr]
  have e2 : st.bcopy.filter (fun r => topHome g w r == ci) =
      st.bcopy.filter (fun r => topHome g w' r == ci) :=
    List.filter_congr fun r hr => by rw [bcopy_agree h r hr]
  simp only [topOffer]
  rw [e1, e2]

theorem offer_good (ci : Nat) {st : FinState} (h : Good w w' st) :
    Good w w' (topOffer g w ci st) :=
  good_of_filters h _ _ rfl fun _ hr => (List.mem_filter.1 hr).1

theorem dest_congr (Bi : Bucket) (hB : ∀ r ∈ Bi.recs, Agree w w' r) (i q : Nat)
    {st : FinState} (h : Good w w' st) :
    topDest g w Bi i q st = topDest g w' Bi i q st ∧ Good w w' (topDest g w Bi i q st).1 := by
  have ed : Bi.recs.filter (fun r => topWay g w r == q) =
      Bi.recs.filter (fun r => topWay g w' r == q) :=
    List.filter_congr fun r hr => by rw [topWay_eq (hB r hr)]
  have hr := resolve_good (g := g) (i + q * g.U)
    ((Bi.recs.filter fun r => topWay g w' r == q).map Rec.key) h
  constructor
  · simp only [topDest]
    rw [ed, resolve_congr _ _ h, offer_congr _ (by rw [← resolve_congr _ _ h]; exact hr)]
  · simp only [topDest]
    rw [ed]
    exact offer_good _ hr

theorem bucket_congr (bMain : List Bucket) (i : Nat)
    (hB : ∀ r ∈ (bMain.getD i []).recs, Agree w w' r) {st : FinState} (h : Good w w' st) :
    topBucket g w bMain i st = topBucket g w' bMain i st ∧
      Good w w' (topBucket g w bMain i st) := by
  let main := (List.range g.D).foldl (fun m q =>
    m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key =>
      (bMain.getD i []).keys.contains key)) st.main
  have hf := foldl_congr_inv (fun acc : FinState × List Rec => Good w w' acc.1)
    (fun acc q => let p := topDest g w (bMain.getD i []) i q acc.1; (p.1, acc.2 ++ p.2))
    (fun acc q => let p := topDest g w' (bMain.getD i []) i q acc.1; (p.1, acc.2 ++ p.2))
    (List.range g.D) ({ st with main := main }, []) h
    (fun acc q _ ha => by
      obtain ⟨e, hg⟩ := dest_congr (g := g) _ hB i q ha
      exact ⟨by simp only [e], hg⟩)
  constructor
  · simp only [topBucket]
    rw [hf.1]
  · exact hf.2

theorem sweep_congr (inp : TopInputs) (hB : ∀ r ∈ inp.bMain.flatMap Bucket.recs, Agree w w' r)
    (leaves : List (List Rec)) (bcopy : List Rec)
    (h0 : Good w w' { main := inp.cMain, ins := [], leaves := leaves, bcopy := bcopy, trace := [] }) :
    topSweep g w inp leaves bcopy = topSweep g w' inp leaves bcopy := by
  have hBi : ∀ i, ∀ r ∈ (inp.bMain.getD i []).recs, Agree w w' r := fun i r hr => by
    obtain ⟨B, hB', hrB⟩ := mem_getD_recs hr
    exact hB r (List.mem_flatMap.2 ⟨B, hB', hrB⟩)
  exact (foldl_congr_inv (Good w w') _ _ (List.range g.U) _ h0
    fun st i _ hs => bucket_congr (g := g) inp.bMain i (hBi i) hs).1

end

theorem topJob_word_congr (g : TopGeom) (unsh : Rec → Bool) (w w' : Model.LogicalKey → Nat)
    (inp : TopInputs) (hw : ∀ x ∈ inp.aAll ++ inp.bAll, w x.key = w' x.key) :
    topJob g unsh w inp = topJob g unsh w' inp := by
  have hpool : ∀ r ∈ topPool unsh inp, Agree w w' r := fun r hr => by
    refine hw r (List.mem_append_left _ (List.mem_append_right _ ?_))
    exact (List.mem_filter.1 (List.mem_filter.1 hr).1).1
  have hcopy : ∀ r ∈ topTierCopy unsh inp, Agree w w' r := fun r hr =>
    hw r (List.mem_append_right _ (List.mem_append_right _ (List.mem_filter.1 hr).1))
  have hB : ∀ r ∈ inp.bMain.flatMap Bucket.recs, Agree w w' r := fun r hr =>
    hw r (List.mem_append_right _ (List.mem_append_left _ hr))
  have hleaves : leavesOf g.toGeom w (topPool unsh inp) =
      leavesOf g.toGeom w' (topPool unsh inp) := by
    unfold leavesOf
    refine List.map_congr_left fun R _ => List.filter_congr fun r hr => ?_
    rw [rangeOf_eq (hpool r hr)]
  have hdfs : topDfsTrace g w (topPool unsh inp) = topDfsTrace g w' (topPool unsh inp) := by
    unfold topDfsTrace dfsTrace
    split
    · congr 1
      funext d
      refine List.map_congr_left fun c _ => ?_
      rw [List.filter_congr fun r hr => by rw [rangeOf_eq (hpool r hr)]]
    · rfl
  have hgood : Good w w' (FinState.mk inp.cMain []
      (leavesOf g.toGeom w' (topPool unsh inp)) (topTierCopy unsh inp) []) := by
    refine ⟨fun L hL r hr => ?_, hcopy⟩
    obtain ⟨R, _, rfl⟩ := List.mem_map.1 hL
    exact hpool r (List.mem_filter.1 hr).1
  have hsweep := sweep_congr (g := g) inp hB _ _ hgood
  simp only [topJob, topReference]
  rw [hleaves, hsweep, hdfs]

end RebuildBound.WordLocalTopProof

open RebuildBound.Model in
theorem RebuildBound.TopJobWordLocal : RebuildBound.Spec.TopJobWordLocal_statement :=
  fun g unsh w w' inp hw => RebuildBound.WordLocalTopProof.topJob_word_congr g unsh w w' inp hw
