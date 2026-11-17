import RebuildBound.Proofs.S6.Offer

/-!
# S6: B's insertion for two leaf orders

`sFinish` runs on the same routed buckets with two lists of leaves that agree
leaf by leaf up to order. B's insertion into a home reads only that home's
routed bucket (cleared of B's keys), so the insertion stash and the insertion
trace coincide; the offers are handled by `s_offer_rel`. The insertion
stash's keys (`sKof`) are keys whose home is full when offered (`sK_full`,
from `SInputShape.bHome` and `homeOf = carry + U · way`).

Homes are offered in the order `i + qU`, carry bucket `i` ascending, way `q`
ascending; `keepNQ n q` tracks the records whose home is not yet offered
before way `q` of bucket `n`, and the insertion stash's keys.
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6

theorem U_pos (g : SepGeom) : 0 < g.U := Nat.two_pow_pos _

/-- A home is its carry bucket plus `U` times its way. -/
theorem homeOf_eq (g : SepGeom) (t : Nat) : g.homeOf t = t % g.U + g.U * g.wayOf t := by
  unfold SepGeom.homeOf SepGeom.wayOf SepGeom.U SepGeom.k
  rw [Nat.pow_add, Nat.mod_mul]
  ring

/-- `h = n + q U` with `n < U` iff `h mod U = n` and `h / U = q`. -/
theorem eq_add_mul_iff (U n q h : Nat) (hn : n < U) :
    h = n + q * U ↔ h % U = n ∧ h / U = q := by
  constructor
  · rintro rfl
    refine ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn], ?_⟩
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hn, Nat.zero_add]
  · rintro ⟨h1, h2⟩
    have := Nat.mod_add_div h U
    rw [h1, h2, Nat.mul_comm] at this
    omega

section Finish

variable (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs)

/-- B's keys of carry bucket `i`. -/
def sBk (i : Nat) : List Model.LogicalKey := (inp.bMain.getD i []).keys

/-- Remove the A copies of B's keys of bucket `i`. -/
def sClr (i : Nat) (B : Bucket) : Bucket := B.clear fun key => (sBk inp i).contains key

/-- B's records of bucket `i` and way `q`. -/
def sLw (i q : Nat) : List Rec :=
  (inp.bMain.getD i []).recs.filter fun x => g.wayOf (w x.key) == q

/-- The clears of bucket `i`. -/
def clearSt (i : Nat) (st : SFin) : SFin :=
  { st with
    main := (List.range g.d).foldl
      (fun m q => m.set (i + q * g.U) (sClr inp i (m.getD (i + q * g.U) []))) st.main }

/-- The insertion test after the last way. -/
def insSt (q : Nat) (sheds : List Rec) (st : SFin) : SFin :=
  if q + 1 = g.d then
    { st with ins := st.ins ++ sheds, trace := st.trace ++ [(.insertion, (st.ins ++ sheds).length)] }
  else st

/-- Replace the main buckets. -/
def withMain (st : SFin) (m : List Bucket) : SFin := { st with main := m }

/-- One way of `sInsertBucket`. -/
def wayStep (i : Nat) (acc : SFin × List Rec) (q : Nat) : SFin × List Rec :=
  (sOfferB g w (i + q * g.U) (sOfferA g w (i + q * g.U)
    (insSt g q (acc.2 ++ (fill (acc.1.main.getD (i + q * g.U) []) (sLw g w inp i q)).2)
      (withMain acc.1 (acc.1.main.set (i + q * g.U)
          (fill (acc.1.main.getD (i + q * g.U) []) (sLw g w inp i q)).1)))),
    acc.2 ++ (fill (acc.1.main.getD (i + q * g.U) []) (sLw g w inp i q)).2)

theorem sInsertBucket_eq (i : Nat) (st : SFin) :
    sInsertBucket g w inp.bMain i st =
      ((List.range g.d).foldl (wayStep g w inp i) (clearSt g inp i st, [])).1 := by
  unfold sInsertBucket wayStep clearSt insSt sClr sBk sLw withMain
  rfl

theorem sClr_nil (i : Nat) : sClr inp i [] = [] := rfl

theorem clearFold_getD (i : Nat) (hi : i < g.U) :
    ∀ (n : Nat) (m : List Bucket) (v : Nat),
      ((List.range n).foldl
        (fun m q => m.set (i + q * g.U) (sClr inp i (m.getD (i + q * g.U) []))) m).getD v [] =
        if v % g.U = i ∧ v / g.U < n then sClr inp i (m.getD v []) else m.getD v []
  | 0, m, v => by simp
  | n + 1, m, v => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set M := (List.range n).foldl
      (fun m q => m.set (i + q * g.U) (sClr inp i (m.getD (i + q * g.U) []))) m
    have ih := clearFold_getD i hi n m
    by_cases hv : v = i + n * g.U
    · have hv' := (eq_add_mul_iff g.U i n v hi).mp hv
      subst hv
      rw [getD_set_self M _ [] (sClr inp i) (sClr_nil inp i), ih]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [getD_set_ne _ _ _ (Ne.symm hv), ih]
      have : ¬ (v % g.U = i ∧ v / g.U = n) := fun h => hv ((eq_add_mul_iff g.U i n v hi).mpr h)
      by_cases h1 : v % g.U = i ∧ v / g.U < n
      · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem clearSt_main_getD (i : Nat) (hi : i < g.U) (st : SFin) (v : Nat) :
    (clearSt g inp i st).main.getD v [] =
      if v % g.U = i ∧ v / g.U < g.d then sClr inp i (st.main.getD v []) else st.main.getD v [] :=
  clearFold_getD g inp i hi g.d st.main v

/-! ### The insertion computed from the routed buckets -/

variable (routed : List Bucket)

/-- B's insertion into home `i + qU`. -/
def FR (i q : Nat) : List (Option Rec) × List Rec :=
  fill (sClr inp i (routed.getD (i + q * g.U) [])) (sLw g w inp i q)

/-- The sheds of ways `< q` of B bucket `i`. -/
def shedsUpTo (i q : Nat) : List Rec := (List.range q).flatMap fun q' => (FR g w inp routed i q').2

/-- The insertion sheds of B bucket `i`. -/
def sInsOf (i : Nat) : List Rec := shedsUpTo g w inp routed i g.d

/-- The keys of the complete insertion stash. -/
def sKof : List Model.LogicalKey := ((List.range g.U).flatMap (sInsOf g w inp routed)).map Rec.key

/-- A key of the insertion stash names a home that was full after B's insertion. -/
theorem sK_full (hbHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    (n q : Nat) (hn : n < g.U) (r : Rec) (hh : sHome g w r = n + q * g.U)
    (hK : (sKof g w inp routed).contains r.key = true) :
    nNone (FR g w inp routed n q).1 = 0 := by
  rw [contains_iff] at hK
  unfold sKof at hK
  simp only [List.mem_map, List.mem_flatMap, List.mem_range, sInsOf, shedsUpTo] at hK
  obtain ⟨b, ⟨i, hi, q', hq', hb⟩, hbr⟩ := hK
  have hbL := mem_fill_snd hb
  unfold sLw at hbL
  rw [List.mem_filter] at hbL
  have h1 := hbHome i hi b hbL.1
  have h2 : g.wayOf (w b.key) = q' := by simpa using hbL.2
  have hhb : sHome g w r = i + q' * g.U := by
    rw [sHome_eq_of_key g w hbr.symm]
    unfold sHome
    rw [homeOf_eq, h1, h2, Nat.mul_comm]
  rw [hh] at hhb
  have e1 := (eq_add_mul_iff g.U n q (n + q * g.U) hn).mp rfl
  rw [hhb] at e1
  have e2 := (eq_add_mul_iff g.U i q' (i + q' * g.U) hi).mp rfl
  have hin : i = n := by omega
  have hqq : q' = q := by omega
  subst hin hqq
  exact fill_full _ _ (List.ne_nil_of_mem hb)

/-- The records still tracked before the offers of B bucket `n`. -/
def keepN (n : Nat) (r : Rec) : Bool :=
  decide (n ≤ sHome g w r % g.U) || (sKof g w inp routed).contains r.key

/-- The records still tracked before way `q` of B bucket `n`. -/
def keepNQ (n q : Nat) (r : Rec) : Bool :=
  decide (n < sHome g w r % g.U) ||
    (decide (sHome g w r % g.U = n) && decide (q ≤ sHome g w r / g.U)) ||
    (sKof g w inp routed).contains r.key

theorem keepNQ_zero (n : Nat) (r : Rec) (h : keepNQ g w inp routed n 0 r = true) :
    keepN g w inp routed n r = true := by
  unfold keepNQ at h
  unfold keepN
  cases hK : (sKof g w inp routed).contains r.key
  · simp only [hK, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    omega
  · simp

theorem keepNQ_d (n : Nat) (r : Rec) (h : keepN g w inp routed (n + 1) r = true) :
    keepNQ g w inp routed n g.d r = true := by
  unfold keepNQ
  unfold keepN at h
  cases hK : (sKof g w inp routed).contains r.key
  · simp only [hK, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    omega
  · simp

theorem keepNQ_succ (n q : Nat) (hn : n < g.U) (r : Rec)
    (h : keepNQ g w inp routed n (q + 1) r = true) :
    sKeepAfter g w (keepNQ g w inp routed n q) (sKof g w inp routed) (n + q * g.U) r = true := by
  have hiff := eq_add_mul_iff g.U n q (sHome g w r) hn
  unfold keepNQ at h
  unfold sKeepAfter keepNQ
  cases hK : (sKof g w inp routed).contains r.key
  · simp only [hK, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      bne_iff_ne, ne_eq] at h ⊢
    refine ⟨fun e => ?_, ?_⟩
    · have := hiff.mp e
      omega
    · omega
  · simp

theorem keepNQ_home (n q : Nat) (hn : n < g.U) (r : Rec) (h : sHome g w r = n + q * g.U) :
    keepNQ g w inp routed n q r = true := by
  have := (eq_add_mul_iff g.U n q (sHome g w r) hn).mp h
  unfold keepNQ
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  left; right
  omega

theorem keepNQ_K (n q : Nat) (r : Rec) (h : (sKof g w inp routed).contains r.key = true) :
    keepNQ g w inp routed n q r = true := by
  unfold keepNQ; rw [h, Bool.or_true]

/-- The invariant of the ways of B bucket `n` before way `q`, for two leaf
orders. -/
structure WayInv (TK : List Model.LogicalKey) (n q : Nat) (ins0 : List Rec) (a1 a2 : SFin × List Rec) :
    Prop where
  sh1 : a1.2 = shedsUpTo g w inp routed n q
  sh2 : a2.2 = shedsUpTo g w inp routed n q
  insLt : q < g.d → a1.1.ins = ins0
  insEq : q = g.d → a1.1.ins = ins0 ++ shedsUpTo g w inp routed n g.d
  ins : a1.1.ins = a2.1.ins
  trace : a1.1.trace = a2.1.trace
  out1 : ∀ v, n < v % g.U → a1.1.main.getD v [] = routed.getD v []
  out2 : ∀ v, n < v % g.U → a2.1.main.getD v [] = routed.getD v []
  in1 : ∀ v, v % g.U = n → q ≤ v / g.U → v / g.U < g.d →
    a1.1.main.getD v [] = sClr inp n (routed.getD v [])
  in2 : ∀ v, v % g.U = n → q ≤ v / g.U → v / g.U < g.d →
    a2.1.main.getD v [] = sClr inp n (routed.getD v [])
  bcopy : a1.1.bcopy = a2.1.bcopy
  bT : ∀ pg, ∀ r ∈ a1.1.bcopy.getD pg [], TK.contains r.key = true
  len : a1.1.leaves.length = a2.1.leaves.length
  rel : ∀ R, LeafRel (keepNQ g w inp routed n q) (a1.1.leaves.getD R []) (a2.1.leaves.getD R [])
  ok1 : LeafOK TK a1.1.leaves
  ok2 : LeafOK TK a2.1.leaves

theorem insSt_facts (q : Nat) (sh : List Rec) (st : SFin) :
    (insSt g q sh st).main = st.main ∧ (insSt g q sh st).leaves = st.leaves ∧
    (insSt g q sh st).bcopy = st.bcopy ∧
    (insSt g q sh st).ins = (if q + 1 = g.d then st.ins ++ sh else st.ins) ∧
    (insSt g q sh st).trace = (if q + 1 = g.d then
      st.trace ++ [(.insertion, (st.ins ++ sh).length)] else st.trace) := by
  unfold insSt
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem WayInv.step {TK : List Model.LogicalKey}
    (hbHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    {n q : Nat} {ins0 : List Rec} {a1 a2 : SFin × List Rec}
    (h : WayInv g w inp routed TK n q ins0 a1 a2) (hn : n < g.U) (hq : q < g.d) :
    WayInv g w inp routed TK n (q + 1) ins0 (wayStep g w inp n a1 q) (wayStep g w inp n a2 q) := by
  set ci := n + q * g.U with hci
  have hcv := (eq_add_mul_iff g.U n q ci hn).mp rfl
  have m1 := h.in1 ci hcv.1 (by omega) (by omega)
  have m2 := h.in2 ci hcv.1 (by omega) (by omega)
  have eF1 : fill (a1.1.main.getD ci []) (sLw g w inp n q) = FR g w inp routed n q := by
    rw [m1]; rfl
  have eF2 : fill (a2.1.main.getD ci []) (sLw g w inp n q) = FR g w inp routed n q := by
    rw [m2]; rfl
  have hsh : shedsUpTo g w inp routed n q ++ (FR g w inp routed n q).2 =
      shedsUpTo g w inp routed n (q + 1) := by
    unfold shedsUpTo
    rw [List.range_succ, List.flatMap_append]
    simp
  have ew : ∀ a : SFin × List Rec, a.1.main.getD ci [] = sClr inp n (routed.getD ci []) →
      a.2 = shedsUpTo g w inp routed n q →
      wayStep g w inp n a q = (sOfferB g w ci (sOfferA g w ci
        (insSt g q (shedsUpTo g w inp routed n (q + 1))
          (withMain a.1 (a.1.main.set ci (FR g w inp routed n q).1)))),
        shedsUpTo g w inp routed n (q + 1)) := by
    intro a hm hs
    have eF : fill (a.1.main.getD ci []) (sLw g w inp n q) = FR g w inp routed n q := by
      rw [hm]; rfl
    unfold wayStep
    rw [← hci, eF, hs, hsh]
  rw [ew a1 m1 h.sh1, ew a2 m2 h.sh2]
  -- the states before the offers
  set p1 := insSt g q (shedsUpTo g w inp routed n (q + 1))
    (withMain a1.1 (a1.1.main.set ci (FR g w inp routed n q).1)) with hp1
  set p2 := insSt g q (shedsUpTo g w inp routed n (q + 1))
    (withMain a2.1 (a2.1.main.set ci (FR g w inp routed n q).1)) with hp2
  obtain ⟨p1m, p1l, p1b, p1i, p1t⟩ := insSt_facts g q (shedsUpTo g w inp routed n (q + 1))
    (withMain a1.1 (a1.1.main.set ci (FR g w inp routed n q).1))
  obtain ⟨p2m, p2l, p2b, p2i, p2t⟩ := insSt_facts g q (shedsUpTo g w inp routed n (q + 1))
    (withMain a2.1 (a2.1.main.set ci (FR g w inp routed n q).1))
  rw [← hp1] at p1m p1l p1b p1i p1t
  rw [← hp2] at p2m p2l p2b p2i p2t
  simp only [withMain] at p1m p1l p1b p1i p1t p2m p2l p2b p2i p2t
  have hp1ci : p1.main.getD ci [] = (FR g w inp routed n q).1 := by
    rw [p1m, ← eF1]
    exact getD_set_self a1.1.main ci [] (fun B => (fill B (sLw g w inp n q)).1) (by rw [fill_nil])
  have hp2ci : p2.main.getD ci [] = (FR g w inp routed n q).1 := by
    rw [p2m, ← eF2]
    exact getD_set_self a2.1.main ci [] (fun B => (fill B (sLw g w inp n q)).1) (by rw [fill_nil])
  have hp1v : ∀ v, v ≠ ci → p1.main.getD v [] = a1.1.main.getD v [] := by
    intro v hv; rw [p1m, getD_set_ne _ _ _ (Ne.symm hv)]
  have hp2v : ∀ v, v ≠ ci → p2.main.getD v [] = a2.1.main.getD v [] := by
    intro v hv; rw [p2m, getD_set_ne _ _ _ (Ne.symm hv)]
  -- the offers
  obtain ⟨qbc, qrel⟩ := s_offer_rel g w (keepNQ g w inp routed n q) (sKof g w inp routed) TK ci
    p1 p2 (by rw [hp1ci, hp2ci]) (by rw [p1b, p2b]; exact h.bcopy) (by rw [p1b]; exact h.bT)
    (by rw [p1l, p2l]; exact h.rel) (by rw [p1l]; exact h.ok1) (by rw [p2l]; exact h.ok2)
    (fun r hr => keepNQ_home g w inp routed n q hn r hr)
    (fun r hr => keepNQ_K g w inp routed n q r hr)
    (fun r hr hk => by rw [hp1ci]; exact sK_full g w inp routed hbHome n q hn r hr hk)
  obtain ⟨t1ins, t1tr, t1main, t1len, t1ok, t1bT⟩ := s_offer_single g w ci TK p1
  obtain ⟨t2ins, t2tr, t2main, t2len, t2ok, t2bT⟩ := s_offer_single g w ci TK p2
  have hins : p1.ins = p2.ins := by rw [p1i, p2i, h.ins]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qbc, ?_, ?_, ?_, ?_, ?_⟩
  · intro hq'
    simp only
    rw [t1ins, p1i, ite_eq_right (by omega), h.insLt hq]
  · intro hq'
    simp only
    rw [t1ins, p1i, ite_eq_left (by omega), h.insLt hq, ← hq']
  · simp only; rw [t1ins, t2ins, hins]
  · simp only; rw [t1tr, t2tr, p1t, p2t, h.ins, h.trace]
  · intro v hv
    have hne : v ≠ ci := fun e => by rw [e] at hv; omega
    simp only
    rw [t1main v hne, hp1v v hne, h.out1 v hv]
  · intro v hv
    have hne : v ≠ ci := fun e => by rw [e] at hv; omega
    simp only
    rw [t2main v hne, hp2v v hne, h.out2 v hv]
  · intro v hv1 hv2 hv3
    have hne : v ≠ ci := fun e => by rw [e] at hv2; omega
    simp only
    rw [t1main v hne, hp1v v hne, h.in1 v hv1 (by omega) hv3]
  · intro v hv1 hv2 hv3
    have hne : v ≠ ci := fun e => by rw [e] at hv2; omega
    simp only
    rw [t2main v hne, hp2v v hne, h.in2 v hv1 (by omega) hv3]
  · exact t1bT (by rw [p1b]; exact h.bT)
  · simp only; rw [t1len, t2len, p1l, p2l, h.len]
  · intro R
    exact (qrel R).mono (keepNQ_succ g w inp routed n q hn)
  · exact t1ok (by rw [p1l]; exact h.ok1)
  · exact t2ok (by rw [p2l]; exact h.ok2)

theorem WayInv.fold {TK : List Model.LogicalKey}
    (hbHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    {n : Nat} (hn : n < g.U) {ins0 : List Rec} {a1 a2 : SFin × List Rec}
    (h : WayInv g w inp routed TK n 0 ins0 a1 a2) :
    ∀ q, q ≤ g.d → WayInv g w inp routed TK n q ins0
      ((List.range q).foldl (wayStep g w inp n) a1) ((List.range q).foldl (wayStep g w inp n) a2)
  | 0, _ => h
  | q + 1, hq => by
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    exact (WayInv.fold hbHome hn h q (by omega)).step g w inp routed hbHome hn (by omega)

/-- The invariant of `sFinish` after B buckets `0, …, n - 1`, for two leaf orders. -/
structure FinInv (TK : List Model.LogicalKey) (n : Nat) (s1 s2 : SFin) : Prop where
  main1 : ∀ v, n ≤ v % g.U → s1.main.getD v [] = routed.getD v []
  main2 : ∀ v, n ≤ v % g.U → s2.main.getD v [] = routed.getD v []
  ins1 : s1.ins = (List.range n).flatMap (sInsOf g w inp routed)
  ins : s1.ins = s2.ins
  bcopy : s1.bcopy = s2.bcopy
  bT : ∀ pg, ∀ r ∈ s1.bcopy.getD pg [], TK.contains r.key = true
  trace : s1.trace = s2.trace
  len : s1.leaves.length = s2.leaves.length
  rel : ∀ R, LeafRel (keepN g w inp routed n) (s1.leaves.getD R []) (s2.leaves.getD R [])
  ok1 : LeafOK TK s1.leaves
  ok2 : LeafOK TK s2.leaves

theorem FinInv.step {TK : List Model.LogicalKey} (hd : 1 ≤ g.d)
    (hbHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    {n : Nat} {s1 s2 : SFin} (h : FinInv g w inp routed TK n s1 s2) (hn : n < g.U) :
    FinInv g w inp routed TK (n + 1) (sInsertBucket g w inp.bMain n s1)
      (sInsertBucket g w inp.bMain n s2) := by
  rw [sInsertBucket_eq, sInsertBucket_eq]
  have h0 : WayInv g w inp routed TK n 0 s1.ins (clearSt g inp n s1, [])
      (clearSt g inp n s2, []) := by
    refine ⟨rfl, rfl, fun _ => rfl, fun h => by omega, h.ins, h.trace, ?_, ?_, ?_, ?_, h.bcopy,
      h.bT, h.len, fun R => (h.rel R).mono (keepNQ_zero g w inp routed n), h.ok1, h.ok2⟩
    · intro v hv
      simp only
      rw [clearSt_main_getD g inp n hn, ite_eq_right (by omega), h.main1 v (by omega)]
    · intro v hv
      simp only
      rw [clearSt_main_getD g inp n hn, ite_eq_right (by omega), h.main2 v (by omega)]
    · intro v hv1 _ hv3
      simp only
      rw [clearSt_main_getD g inp n hn, ite_eq_left ⟨hv1, hv3⟩, h.main1 v (by omega)]
    · intro v hv1 _ hv3
      simp only
      rw [clearSt_main_getD g inp n hn, ite_eq_left ⟨hv1, hv3⟩, h.main2 v (by omega)]
  have hW := WayInv.fold g w inp routed hbHome hn h0 g.d le_rfl
  refine ⟨fun v hv => hW.out1 v (by omega), fun v hv => hW.out2 v (by omega), ?_, hW.ins,
    hW.bcopy, hW.bT, hW.trace, hW.len,
    fun R => (hW.rel R).mono (keepNQ_d g w inp routed n), hW.ok1, hW.ok2⟩
  rw [hW.insEq rfl, h.ins1, List.range_succ, List.flatMap_append]
  simp [sInsOf]

theorem FinInv.fold {TK : List Model.LogicalKey} (hd : 1 ≤ g.d)
    (hbHome : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i)
    {s1 s2 : SFin} (h0 : FinInv g w inp routed TK 0 s1 s2) :
    ∀ n, n ≤ g.U → FinInv g w inp routed TK n
      ((List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st) s1)
      ((List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st) s2)
  | 0, _ => h0
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    exact (FinInv.fold hd hbHome h0 n (by omega)).step g w inp routed hd hbHome (by omega)

end Finish

end RebuildBound.S6
