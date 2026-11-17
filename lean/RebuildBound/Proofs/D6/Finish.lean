import RebuildBound.Proofs.D6.Offer

/-!
# D6: B's insertion for two leaf orders

`finish` runs on the same routed buckets with two lists of leaves that agree
leaf by leaf up to order. B's insertion into a home reads only that home's
routed bucket, so the insertion stash and the insertion trace coincide; the
offers are handled by `offer_rel`. The insertion stash's keys `Kof` are
keys whose home is full when offered (`K_full`, from `InputValid.bHome`).
-/

namespace RebuildBound.D6

open RebuildBound.Model

theorem getD_set_of {α : Type*} (l : List α) (i : Nat) (a d : α)
    (h : ¬ i < l.length → l.getD i d = a) : (l.set i a).getD i d = a := by
  rw [getD_set_eq]
  split_ifs with hh
  · rfl
  · exact h fun hi => hh ⟨rfl, hi⟩

theorem U_pos (g : Geom) : 0 < g.U := Nat.two_pow_pos _

theorem homes_eq (g : Geom) : g.homes = g.U + g.U := by
  simp [Geom.homes, Geom.U, Nat.pow_succ]; ring

theorem home_lt (g : Geom) (w : Model.LogicalKey → Nat) (r : Rec) : home g w r < g.homes :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A home is its carry home plus `U` times bit `k`. -/
theorem mod_homes (g : Geom) (x : Nat) :
    x % g.homes = x % g.U + (if x.testBit g.k then g.U else 0) := by
  simp only [Geom.homes, Geom.U]
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have : x / 2 ^ g.k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : x / 2 ^ g.k % 2 = 0 ∨ x / 2 ^ g.k % 2 = 1) with h | h
  · simp [h]
  · simp [h]

section Finish

variable (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs)

/-- B's keys of carry bucket `i`. -/
def bkOf (i : Nat) : List Model.LogicalKey := (inp.bMain.getD i []).keys

/-- B's records of bucket `i` with bit `k` clear. -/
def L0 (i : Nat) : List Rec := (inp.bMain.getD i []).recs.filter fun r => !dirBit w g.k r

/-- B's records of bucket `i` with bit `k` set. -/
def L1 (i : Nat) : List Rec := (inp.bMain.getD i []).recs.filter fun r => dirBit w g.k r

/-- Remove the A copies of B's keys of bucket `i`. -/
def clr (i : Nat) (B : Bucket) : Bucket := B.clear fun key => (bkOf inp i).contains key

/-- `insertBucket` up to the offers to home `i`. -/
def preIns (i : Nat) (st : FinState) : FinState :=
  { st with
    main := ((st.main.set i (fill (clr inp i (st.main.getD i [])) (L0 g w inp i)).1).set
      (i + g.U) (clr inp i (st.main.getD (i + g.U) []))) }

/-- `insertBucket` from the offers to home `i` to the offers to home `i + U`. -/
def midIns (i : Nat) (sh0 : List Rec) (st : FinState) : FinState :=
  { st with
    main := st.main.set (i + g.U) (fill (st.main.getD (i + g.U) []) (L1 g w inp i)).1
    ins := st.ins ++ sh0 ++ (fill (st.main.getD (i + g.U) []) (L1 g w inp i)).2
    trace := st.trace ++
      [(.insertion, (st.ins ++ sh0 ++ (fill (st.main.getD (i + g.U) []) (L1 g w inp i)).2).length)] }

theorem insertBucket_eq (i : Nat) (st : FinState) :
    insertBucket g w inp.bMain i st =
      offerB g w (i + g.U) (offerA g w (i + g.U)
        (midIns g w inp i (fill (clr inp i (st.main.getD i [])) (L0 g w inp i)).2
          (offerB g w i (offerA g w i (preIns g w inp i st))))) := rfl

theorem clr_nil (i : Nat) : clr inp i [] = [] := rfl

theorem preIns_facts (i : Nat) (st : FinState) :
    (preIns g w inp i st).ins = st.ins ∧ (preIns g w inp i st).trace = st.trace ∧
    (preIns g w inp i st).leaves = st.leaves ∧ (preIns g w inp i st).bcopy = st.bcopy ∧
    (∀ v, v ≠ i → v ≠ i + g.U → (preIns g w inp i st).main.getD v [] = st.main.getD v []) ∧
    (preIns g w inp i st).main.getD i [] = (fill (clr inp i (st.main.getD i [])) (L0 g w inp i)).1 ∧
    (preIns g w inp i st).main.getD (i + g.U) [] = clr inp i (st.main.getD (i + g.U) []) := by
  have hU := U_pos g
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro v h1 h2
    show ((st.main.set i _).set (i + g.U) _).getD v [] = _
    rw [getD_set_ne _ _ _ (Ne.symm h2), getD_set_ne _ _ _ (Ne.symm h1)]
  · show ((st.main.set i _).set (i + g.U) _).getD i [] = _
    rw [getD_set_ne _ _ _ (by omega)]
    exact getD_set_self st.main i [] (fun B => (fill (clr inp i B) (L0 g w inp i)).1)
      (by rw [clr_nil, fill_nil])
  · show ((st.main.set i _).set (i + g.U) _).getD (i + g.U) [] = _
    apply getD_set_of
    intro h
    rw [getD_set_ne _ _ _ (by omega), List.getD_eq_default _ _ (by simp at h; omega)]
    rfl

theorem midIns_facts (i : Nat) (sh0 : List Rec) (st : FinState) :
    (midIns g w inp i sh0 st).ins =
      st.ins ++ sh0 ++ (fill (st.main.getD (i + g.U) []) (L1 g w inp i)).2 ∧
    (midIns g w inp i sh0 st).trace =
      st.trace ++ [(.insertion, (midIns g w inp i sh0 st).ins.length)] ∧
    (midIns g w inp i sh0 st).leaves = st.leaves ∧ (midIns g w inp i sh0 st).bcopy = st.bcopy ∧
    (∀ v, v ≠ i + g.U → (midIns g w inp i sh0 st).main.getD v [] = st.main.getD v []) ∧
    (midIns g w inp i sh0 st).main.getD (i + g.U) [] =
      (fill (st.main.getD (i + g.U) []) (L1 g w inp i)).1 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro v hv
    show (st.main.set (i + g.U) _).getD v [] = _
    rw [getD_set_ne _ _ _ (Ne.symm hv)]
  · show (st.main.set (i + g.U) _).getD (i + g.U) [] = _
    apply getD_set_of
    intro h
    rw [List.getD_eq_default _ _ (by omega), fill_nil]

/-! ### The insertion computed from the routed buckets -/

variable (routed : List Bucket)

/-- B's insertion into home `i`. -/
def F0R (i : Nat) : List (Option Rec) × List Rec :=
  fill (clr inp i (routed.getD i [])) (L0 g w inp i)

/-- B's insertion into home `i + U`. -/
def F1R (i : Nat) : List (Option Rec) × List Rec :=
  fill (clr inp i (routed.getD (i + g.U) [])) (L1 g w inp i)

/-- The insertion sheds of B bucket `i`. -/
def insOf (i : Nat) : List Rec := (F0R g w inp routed i).2 ++ (F1R g w inp routed i).2

/-- The keys of the complete insertion stash. -/
def Kof : List Model.LogicalKey := ((List.range g.U).flatMap (insOf g w inp routed)).map Rec.key

/-- A key of the insertion stash names a home that was full after B's insertion. -/
theorem K_full (hbHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i)
    (n : Nat) (hn : n < g.U) (r : Rec) (hK : (Kof g w inp routed).contains r.key = true) :
    (home g w r = n → nNone (F0R g w inp routed n).1 = 0) ∧
    (home g w r = n + g.U → nNone (F1R g w inp routed n).1 = 0) := by
  rw [contains_iff] at hK
  unfold Kof at hK
  simp only [List.mem_map, List.mem_flatMap, List.mem_range] at hK
  obtain ⟨b, ⟨i, hi, hb⟩, hbr⟩ := hK
  have hhome : home g w r = w b.key % g.homes := by simp [home, hbr]
  unfold insOf at hb
  rcases List.mem_append.mp hb with hb | hb
  · have hbL := mem_fill_snd hb
    unfold L0 at hbL
    rw [List.mem_filter] at hbL
    have h1 := hbHome i hi b hbL.1
    have h2 : (w b.key).testBit g.k = false := by simpa [dirBit] using hbL.2
    have hh : home g w r = i := by rw [hhome, mod_homes, h1, h2]; simp
    have hfull : nNone (F0R g w inp routed i).1 = 0 :=
      fill_full _ _ (List.ne_nil_of_mem hb)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h, hh]; exact hfull
    · omega
  · have hbL := mem_fill_snd hb
    unfold L1 at hbL
    rw [List.mem_filter] at hbL
    have h1 := hbHome i hi b hbL.1
    have h2 : (w b.key).testBit g.k = true := by simpa [dirBit] using hbL.2
    have hh : home g w r = i + g.U := by rw [hhome, mod_homes, h1, h2]; simp
    have hfull : nNone (F1R g w inp routed i).1 = 0 :=
      fill_full _ _ (List.ne_nil_of_mem hb)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · omega
    · have : i = n := by omega
      rw [← this]; exact hfull

/-- The records still tracked after the offers to the homes of B buckets `< n`. -/
def keepN (n : Nat) (r : Rec) : Bool :=
  decide (n ≤ home g w r % g.U) || (Kof g w inp routed).contains r.key

/-- The invariant of `finish` after B buckets `0, …, n - 1`, for two leaf orders. -/
structure FinInv (TK : List Model.LogicalKey) (n : Nat) (s1 s2 : FinState) : Prop where
  main1 : ∀ v, n ≤ v % g.U → s1.main.getD v [] = routed.getD v []
  main2 : ∀ v, n ≤ v % g.U → s2.main.getD v [] = routed.getD v []
  ins1 : s1.ins = (List.range n).flatMap (insOf g w inp routed)
  ins : s1.ins = s2.ins
  bcopy : s1.bcopy = s2.bcopy
  bcopyT : ∀ r ∈ s1.bcopy, TK.contains r.key = true
  trace : s1.trace = s2.trace
  len : s1.leaves.length = s2.leaves.length
  rel : ∀ R, LeafRel (keepN g w inp routed n) (s1.leaves.getD R []) (s2.leaves.getD R [])
  ok1 : LeafOK TK s1.leaves
  ok2 : LeafOK TK s2.leaves

theorem keepN_step (n : Nat) (r : Rec) :
    keepAfter g w (keepAfter g w (keepN g w inp routed n) (Kof g w inp routed) n)
        (Kof g w inp routed) (n + g.U) r = keepN g w inp routed (n + 1) r := by
  have hlt := home_lt g w r
  rw [homes_eq] at hlt
  have hU := U_pos g
  have hmod : home g w r % g.U = if home g w r < g.U then home g w r else home g w r - g.U := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold keepAfter keepN
  cases hK : (Kof g w inp routed).contains r.key
  · simp only [Bool.or_false]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    rw [hmod]
    split_ifs <;> omega
  · simp only [Bool.or_true]

theorem FinInv.step {TK : List Model.LogicalKey}
    (hbHome : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i)
    {n : Nat} {s1 s2 : FinState} (h : FinInv g w inp routed TK n s1 s2) (hn : n < g.U) :
    FinInv g w inp routed TK (n + 1) (insertBucket g w inp.bMain n s1)
      (insertBucket g w inp.bMain n s2) := by
  have hU := U_pos g
  have hnU : n % g.U = n := Nat.mod_eq_of_lt hn
  have hnU' : (n + g.U) % g.U = n := by rw [Nat.add_mod_right, hnU]
  have m1n := h.main1 n (by omega)
  have m2n := h.main2 n (by omega)
  have m1nU := h.main1 (n + g.U) (by omega)
  have m2nU := h.main2 (n + g.U) (by omega)
  rw [insertBucket_eq, insertBucket_eq, m1n, m2n,
    show fill (clr inp n (routed.getD n [])) (L0 g w inp n) = F0R g w inp routed n from rfl]
  -- after the clears and B's first direction
  obtain ⟨p1ins, p1tr, p1lv, p1bc, p1main, p1n, p1nU⟩ := preIns_facts g w inp n s1
  obtain ⟨p2ins, p2tr, p2lv, p2bc, p2main, p2n, p2nU⟩ := preIns_facts g w inp n s2
  rw [m1n] at p1n; rw [m2n] at p2n; rw [m1nU] at p1nU; rw [m2nU] at p2nU
  set p1 := preIns g w inp n s1
  set p2 := preIns g w inp n s2
  -- the offers to home n
  have hK := K_full g w inp routed hbHome n hn
  obtain ⟨qbc, qrel⟩ := offer_rel g w (keepN g w inp routed n) (Kof g w inp routed) TK n p1 p2
    (by rw [p1n, p2n]) (by rw [p1bc, p2bc]; exact h.bcopy) (by rw [p1bc]; exact h.bcopyT)
    (by rw [p1lv, p2lv]; exact h.rel) (by rw [p1lv]; exact h.ok1) (by rw [p2lv]; exact h.ok2)
    (fun r hr => by simp [keepN, hr, hnU])
    (fun r hr => by unfold keepN; rw [hr, Bool.or_true])
    (fun r hr hk => by rw [p1n]; exact (hK r hk).1 hr)
  obtain ⟨q1ins, q1tr, q1main, q1len, q1ok, q1bT⟩ := offer_single g w n TK p1
  obtain ⟨q2ins, q2tr, q2main, q2len, q2ok, q2bT⟩ := offer_single g w n TK p2
  set q1 := offerB g w n (offerA g w n p1)
  set q2 := offerB g w n (offerA g w n p2)
  have q1nU : q1.main.getD (n + g.U) [] = clr inp n (routed.getD (n + g.U) []) := by
    rw [q1main _ (by omega), p1nU]
  have q2nU : q2.main.getD (n + g.U) [] = clr inp n (routed.getD (n + g.U) []) := by
    rw [q2main _ (by omega), p2nU]
  -- B's second direction and the insertion test
  obtain ⟨r1ins, r1tr, r1lv, r1bc, r1main, r1nU⟩ :=
    midIns_facts g w inp n (F0R g w inp routed n).2 q1
  obtain ⟨r2ins, r2tr, r2lv, r2bc, r2main, r2nU⟩ :=
    midIns_facts g w inp n (F0R g w inp routed n).2 q2
  rw [q1nU] at r1ins r1nU
  rw [q2nU] at r2ins r2nU
  set r1 := midIns g w inp n (F0R g w inp routed n).2 q1
  set r2 := midIns g w inp n (F0R g w inp routed n).2 q2
  have hins : r1.ins = r2.ins := by
    rw [r1ins, r2ins, q1ins, q2ins, p1ins, p2ins, h.ins]
  -- the offers to home n + U
  obtain ⟨tbc, trel⟩ := offer_rel g w
    (keepAfter g w (keepN g w inp routed n) (Kof g w inp routed) n) (Kof g w inp routed) TK
    (n + g.U) r1 r2 (by rw [r1nU, r2nU]) (by rw [r1bc, r2bc]; exact qbc)
    (by rw [r1bc]; exact q1bT (by rw [p1bc]; exact h.bcopyT))
    (by rw [r1lv, r2lv]; exact qrel)
    (by rw [r1lv]; exact q1ok (by rw [p1lv]; exact h.ok1))
    (by rw [r2lv]; exact q2ok (by rw [p2lv]; exact h.ok2))
    (fun r hr => by
      have hne : n + g.U ≠ n := by omega
      unfold keepAfter keepN
      rw [hr, hnU']
      simp [hU.ne'])
    (fun r hr => by unfold keepAfter; rw [hr, Bool.or_true])
    (fun r hr hk => by rw [r1nU]; exact (hK r hk).2 hr)
  obtain ⟨t1ins, t1tr, t1main, t1len, t1ok, t1bT⟩ := offer_single g w (n + g.U) TK r1
  obtain ⟨t2ins, t2tr, t2main, t2len, t2ok, t2bT⟩ := offer_single g w (n + g.U) TK r2
  refine ⟨?_, ?_, ?_, ?_, tbc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 : v ≠ n := by intro e; subst e; omega
    have h2 : v ≠ n + g.U := by intro e; subst e; omega
    rw [t1main v h2, r1main v h2, q1main v h1, p1main v h1 h2, h.main1 v (by omega)]
  · intro v hv
    have h1 : v ≠ n := by intro e; subst e; omega
    have h2 : v ≠ n + g.U := by intro e; subst e; omega
    rw [t2main v h2, r2main v h2, q2main v h1, p2main v h1 h2, h.main2 v (by omega)]
  · rw [t1ins, r1ins, q1ins, p1ins, h.ins1, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    rfl
  · rw [t1ins, t2ins, hins]
  · exact t1bT (by rw [r1bc]; exact q1bT (by rw [p1bc]; exact h.bcopyT))
  · rw [t1tr, t2tr, r1tr, r2tr, hins, q1tr, q2tr, p1tr, p2tr, h.trace]
  · rw [t1len, t2len, r1lv, r2lv, q1len, q2len, p1lv, p2lv, h.len]
  · intro R
    exact (trel R).congr (keepN_step g w inp routed n)
  · exact t1ok (by rw [r1lv]; exact q1ok (by rw [p1lv]; exact h.ok1))
  · exact t2ok (by rw [r2lv]; exact q2ok (by rw [p2lv]; exact h.ok2))

end Finish

end RebuildBound.D6
