import RebuildBound.Proofs.HomeFinish.Home
import RebuildBound.Proofs.D23.Route

/-!
# D23: B's insertion with the fused offers, home by home

`parts g w st v` is the share of home `v` in a finish state: main bucket `v`,
the candidates of home `v` in its leaf, the B tier candidates of home `v`,
and the insertion sheds of home `v`. The offers to a home `ci` act on
`parts ci` as `offA`/`offB` and leave every other home's parts alone, because
a record's home is a function of its key (`home_of_key`). Hence
`insertBucket i` acts on homes `i` and `i + U` by `homeStep` and on no other
home (`insertBucket_parts_lo`, `_hi`, `_ne`), and after `finish` every home
holds `homeStep` of its initial parts (`finish_inv`).
-/

namespace RebuildBound.D23

open RebuildBound.Model

/-- The share of home `v` in a finish state. -/
def parts (g : Geom) (w : Model.LogicalKey → Nat) (st : FinState) (v : Nat) : HP :=
  ⟨st.main.getD v [], (st.leaves.getD (v / 2 ^ g.lo) []).filter (fun r => home g w r == v),
   st.bcopy.filter (fun r => home g w r == v), st.ins.filter (fun r => home g w r == v)⟩

theorem home_of_key (g : Geom) (w : Model.LogicalKey → Nat) {r r' : Rec} (h : r.key = r'.key) :
    home g w r = home g w r' := by
  simp [home, h]

/-- Keys of home-`ci` records never match a record of another home. -/
theorem key_not_mem_of_home (g : Geom) (w : Model.LogicalKey → Nat) {ci v : Nat} (hne : v ≠ ci)
    (L : List Rec) (hL : ∀ r ∈ L, home g w r = ci) (r : Rec) (hr : home g w r = v) :
    r.key ∉ L.map Rec.key := by
  intro hk
  obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
  have := home_of_key g w he
  rw [hL r' hr', hr] at this
  exact hne this.symm

theorem not_contains_of_home (g : Geom) (w : Model.LogicalKey → Nat) {ci v : Nat} (hne : v ≠ ci)
    (L : List Rec) (hL : ∀ r ∈ L, home g w r = ci) (r : Rec) (hr : home g w r = v) :
    (!(L.map Rec.key).contains r.key) = true := by
  have := key_not_mem_of_home g w hne L hL r hr
  simpa [List.contains_iff_mem] using this

theorem filter_home_self (g : Geom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, home g w r = v) : L.filter (fun r => home g w r == v) = L := by
  rw [List.filter_eq_self]; intro r hr; simp [h r hr]

theorem filter_home_nil (g : Geom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, home g w r ≠ v) : L.filter (fun r => home g w r == v) = [] := by
  rw [List.filter_eq_nil_iff]; intro r hr; simp [h r hr]

theorem range_lt (g : Geom) {v : Nat} (hv : v < g.homes) : v / 2 ^ g.lo < g.ranges := by
  unfold Geom.ranges Geom.depth
  unfold Geom.homes at hv
  by_cases hl : g.lo ≤ g.k + 1
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rwa [Nat.sub_add_cancel hl]
  · have : v < 2 ^ g.lo := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt this, show g.k + 1 - g.lo = 0 by omega]
    decide

/-! ### The offers -/

theorem offA_with_I (h : HP) (x : List Rec) : offA { h with I := x } = { offA h with I := x } := rfl
theorem offB_with_I (h : HP) (x : List Rec) : offB { h with I := x } = { offB h with I := x } := rfl

theorem offerA_main_length (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerA g w ci st).main.length = st.main.length := by
  simp [offerA]

theorem offerA_leaves_length (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerA g w ci st).leaves.length = st.leaves.length := by
  simp [offerA]

theorem offerB_main_length (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerB g w ci st).main.length = st.main.length := by
  simp [offerB]

theorem offerB_leaves (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerB g w ci st).leaves = st.leaves := rfl

theorem offerA_ins (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerA g w ci st).ins = st.ins := rfl

theorem offerB_ins (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState) :
    (offerB g w ci st).ins = st.ins := rfl

theorem offerA_lrange (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState)
    (h : ∀ R, ∀ r ∈ st.leaves.getD R [], rangeOf g w r = R) :
    ∀ R, ∀ r ∈ (offerA g w ci st).leaves.getD R [], rangeOf g w r = R := by
  intro R r hr
  simp only [offerA] at hr
  by_cases hR : ci / 2 ^ g.lo = R
  · subst hR
    by_cases hl : ci / 2 ^ g.lo < st.leaves.length
    · rw [getD_set_self _ _ _ _ hl] at hr
      exact h _ r (List.mem_filter.1 hr).1
    · rw [List.set_eq_of_length_le (by omega)] at hr
      exact h _ r hr
  · rw [D6.getD_set_ne _ _ _ hR] at hr
    exact h R r hr

theorem offerA_parts_self (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState)
    (hci : ci < st.main.length) (hR : ci / 2 ^ g.lo < st.leaves.length) :
    parts g w (offerA g w ci st) ci = offA (parts g w st ci) := by
  simp only [parts, offerA, offA, getD_set_self _ _ _ _ hci, getD_set_self _ _ _ _ hR,
    HP.mk.injEq, true_and, and_true]
  exact filter_comm _ _ _

theorem offerA_parts_ne (g : Geom) (w : Model.LogicalKey → Nat) (ci v : Nat) (st : FinState) (hne : v ≠ ci) :
    parts g w (offerA g w ci st) v = parts g w st v := by
  simp only [parts, offerA, D6.getD_set_ne _ _ _ (Ne.symm hne), HP.mk.injEq, true_and, and_true]
  apply getD_set_filter
  intro r hr
  have hr' : home g w r = v := by simpa using hr
  apply not_contains_of_home g w hne _ ?_ r hr'
  intro r' hr'
  rcases List.mem_append.1 hr' with h1 | h1
  · have := (List.mem_filter.1 (List.mem_filter.1 h1).1).2; simpa using this
  · have := (List.mem_filter.1 (List.mem_filter.1 (List.mem_of_mem_take h1)).1).2
    simpa using this

theorem offerB_parts_self (g : Geom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : FinState)
    (hci : ci < st.main.length) :
    parts g w (offerB g w ci st) ci = offB (parts g w st ci) := by
  simp only [parts, offerB, offB, getD_set_self _ _ _ _ hci, HP.mk.injEq, true_and, and_true]
  exact filter_comm _ _ _

theorem offerB_parts_ne (g : Geom) (w : Model.LogicalKey → Nat) (ci v : Nat) (st : FinState) (hne : v ≠ ci) :
    parts g w (offerB g w ci st) v = parts g w st v := by
  simp only [parts, offerB, D6.getD_set_ne _ _ _ (Ne.symm hne), HP.mk.injEq, true_and, and_true]
  apply filter_filter_of_imp
  intro r hr
  have hr' : home g w r = v := by simpa using hr
  apply not_contains_of_home g w hne _ ?_ r hr'
  intro r' hr'
  have := (List.mem_filter.1 (List.mem_of_mem_take hr')).2; simpa using this

/-! ### One B bucket -/

theorem home_split (g : Geom) (w : Model.LogicalKey → Nat) (r : Rec) (i : Nat) (h : w r.key % g.U = i) :
    home g w r = if dirBit w g.k r then i + g.U else i := by
  have hb := Nat.testBit_eq_decide_div_mod_eq (i := g.k) (x := w r.key)
  have hlt : w r.key / 2 ^ g.k % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold Geom.U at h ⊢
  unfold home Geom.homes dirBit
  rw [Nat.mod_pow_succ, h, hb]
  rcases (show w r.key / 2 ^ g.k % 2 = 0 ∨ w r.key / 2 ^ g.k % 2 = 1 by omega) with h0 | h0
  · simp [h0]
  · simp [h0]

/-- B's records of bucket `i` for its low output (`dirBit k = false`). -/
def src0 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) : List Rec :=
  (bMain.getD i []).recs.filter fun r => !dirBit w g.k r

/-- B's records of bucket `i` for its high output (`dirBit k = true`). -/
def src1 (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) : List Rec :=
  (bMain.getD i []).recs.filter fun r => dirBit w g.k r

theorem src0_home (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (hB : ∀ r ∈ (bMain.getD i []).recs, w r.key % g.U = i) :
    ∀ r ∈ src0 g w bMain i, home g w r = i := by
  intro r hr
  rw [src0, List.mem_filter] at hr
  rw [home_split g w r i (hB r hr.1)]
  simp at hr; simp [hr.2]

theorem src1_home (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (hB : ∀ r ∈ (bMain.getD i []).recs, w r.key % g.U = i) :
    ∀ r ∈ src1 g w bMain i, home g w r = i + g.U := by
  intro r hr
  rw [src1, List.mem_filter] at hr
  rw [home_split g w r i (hB r hr.1)]
  simp [hr.2]

section ib
variable (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : FinState)

/-- Direction 0's fill. -/
def f0Of : List (Option Rec) × List Rec :=
  fill ((st.main.getD i []).clear (clrOf bMain i)) (src0 g w bMain i)

/-- Output `i + U` after the dedup. -/
def m1Of : Bucket := (st.main.getD (i + g.U) []).clear (clrOf bMain i)

/-- After the dedup and direction 0's insertion. -/
def ib1 : FinState :=
  { st with main := (st.main.set i (f0Of g w bMain i st).1).set (i + g.U) (m1Of g bMain i st) }

/-- After the offers to output `i`. -/
def ib3 : FinState := offerB g w i (offerA g w i (ib1 g w bMain i st))

/-- Direction 1's fill. -/
def f1Of : List (Option Rec) × List Rec :=
  fill ((ib3 g w bMain i st).main.getD (i + g.U) []) (src1 g w bMain i)

/-- After direction 1's insertion and the insertion stash append. -/
def ib4 : FinState :=
  { ib3 g w bMain i st with
    main := (ib3 g w bMain i st).main.set (i + g.U) (f1Of g w bMain i st).1
    ins := (ib3 g w bMain i st).ins ++ (f0Of g w bMain i st).2 ++ (f1Of g w bMain i st).2
    trace := (ib3 g w bMain i st).trace ++ [(.insertion,
      ((ib3 g w bMain i st).ins ++ (f0Of g w bMain i st).2 ++ (f1Of g w bMain i st).2).length)] }

theorem insertBucket_eq :
    insertBucket g w bMain i st = offerB g w (i + g.U) (offerA g w (i + g.U) (ib4 g w bMain i st)) :=
  rfl

variable {g w bMain i st}

theorem ib1_main_length : (ib1 g w bMain i st).main.length = st.main.length := by
  simp [ib1]

theorem ib3_main_length : (ib3 g w bMain i st).main.length = st.main.length := by
  rw [ib3, offerB_main_length, offerA_main_length, ib1_main_length]

theorem ib3_leaves_length : (ib3 g w bMain i st).leaves.length = st.leaves.length := by
  rw [ib3, offerB_leaves, offerA_leaves_length]; rfl

theorem ib4_main_length : (ib4 g w bMain i st).main.length = st.main.length := by
  simp only [ib4, List.length_set]; exact ib3_main_length

theorem ib4_leaves_length : (ib4 g w bMain i st).leaves.length = st.leaves.length :=
  ib3_leaves_length

theorem insertBucket_main_length :
    (insertBucket g w bMain i st).main.length = st.main.length := by
  rw [insertBucket_eq, offerB_main_length, offerA_main_length, ib4_main_length]

theorem insertBucket_leaves_length :
    (insertBucket g w bMain i st).leaves.length = st.leaves.length := by
  rw [insertBucket_eq, offerB_leaves, offerA_leaves_length, ib4_leaves_length]

theorem insertBucket_lrange (h : ∀ R, ∀ r ∈ st.leaves.getD R [], rangeOf g w r = R) :
    ∀ R, ∀ r ∈ (insertBucket g w bMain i st).leaves.getD R [], rangeOf g w r = R := by
  rw [insertBucket_eq, offerB_leaves]
  apply offerA_lrange
  show ∀ R, ∀ r ∈ (ib3 g w bMain i st).leaves.getD R [], rangeOf g w r = R
  rw [ib3, offerB_leaves]
  exact offerA_lrange _ _ _ _ h

theorem HP.ext' {h h' : HP} (hm : h.m = h'.m) (hP : h.P = h'.P) (hT : h.T = h'.T)
    (hI : h.I = h'.I) : h = h' := by
  cases h; cases h'; simp_all

variable (hU : i < g.U) (hlen : st.main.length = g.homes) (hll : st.leaves.length = g.ranges)
  (hB : ∀ r ∈ (bMain.getD i []).recs, w r.key % g.U = i)
include hU hlen

theorem ib1_parts_lo : parts g w (ib1 g w bMain i st) i =
    { parts g w st i with m := (f0Of g w bMain i st).1 } := by
  have h1 : i ≠ i + g.U := by have : 0 < g.U := Nat.two_pow_pos _; omega
  have h2 : i < st.main.length := by rw [hlen, homes_eq]; omega
  simp only [parts, ib1, D6.getD_set_ne _ _ _ (Ne.symm h1), getD_set_self _ _ _ _ h2]

theorem ib1_parts_hi : parts g w (ib1 g w bMain i st) (i + g.U) =
    { parts g w st (i + g.U) with m := m1Of g bMain i st } := by
  have h2 : i + g.U < st.main.length := by rw [hlen, homes_eq]; omega
  simp only [parts, ib1, getD_set_self (st.main.set i (f0Of g w bMain i st).1) (i + g.U)
    (m1Of g bMain i st) [] (by rw [List.length_set]; exact h2)]

omit hU hlen in
theorem ib1_parts_ne (v : Nat) (h1 : v ≠ i) (h2 : v ≠ i + g.U) :
    parts g w (ib1 g w bMain i st) v = parts g w st v := by
  simp only [parts, ib1, D6.getD_set_ne _ _ _ (Ne.symm h1), D6.getD_set_ne _ _ _ (Ne.symm h2)]

include hll in
theorem ib3_parts_lo : parts g w (ib3 g w bMain i st) i =
    offB (offA { parts g w st i with m := (f0Of g w bMain i st).1 }) := by
  have h2 : i < st.main.length := by rw [hlen, homes_eq]; omega
  have hR : i / 2 ^ g.lo < st.leaves.length := by rw [hll]; exact range_lt g (by rw [homes_eq]; omega)
  rw [ib3, offerB_parts_self _ _ _ _ (by rw [offerA_main_length, ib1_main_length]; exact h2),
    offerA_parts_self _ _ _ _ (by rw [ib1_main_length]; exact h2) (by exact hR),
    ib1_parts_lo hU hlen]

omit hU hlen in
theorem ib3_parts_ne (v : Nat) (h1 : v ≠ i) :
    parts g w (ib3 g w bMain i st) v = parts g w (ib1 g w bMain i st) v := by
  rw [ib3, offerB_parts_ne _ _ _ _ _ h1, offerA_parts_ne _ _ _ _ _ h1]

omit hU hlen in
theorem ib3_ins : (ib3 g w bMain i st).ins = st.ins := rfl

theorem f1Of_eq : f1Of g w bMain i st = fill (m1Of g bMain i st) (src1 g w bMain i) := by
  have h1 : i + g.U ≠ i := by have : 0 < g.U := Nat.two_pow_pos _; omega
  have := congrArg HP.m (ib3_parts_ne (g := g) (w := w) (bMain := bMain) (st := st) (i + g.U) h1)
  rw [ib1_parts_hi hU hlen] at this
  unfold f1Of
  rw [show (ib3 g w bMain i st).main.getD (i + g.U) [] = m1Of g bMain i st from this]

omit hU hlen in
include hB in
theorem f0_snd_home : ∀ r ∈ (f0Of g w bMain i st).2, home g w r = i := by
  intro r hr
  rw [f0Of, fill_snd] at hr
  exact src0_home g w bMain i hB r (List.mem_of_mem_drop hr)

omit hU hlen in
include hB in
theorem f1_snd_home : ∀ r ∈ (f1Of g w bMain i st).2, home g w r = i + g.U := by
  intro r hr
  rw [f1Of, fill_snd] at hr
  exact src1_home g w bMain i hB r (List.mem_of_mem_drop hr)

omit hU hlen in
include hB in
theorem ib4_parts (v : Nat) (h2 : v ≠ i + g.U) : parts g w (ib4 g w bMain i st) v =
    { parts g w (ib3 g w bMain i st) v with
      I := (parts g w (ib3 g w bMain i st) v).I ++
        (f0Of g w bMain i st).2.filter (fun r => home g w r == v) } := by
  simp only [parts, ib4, D6.getD_set_ne _ _ _ (Ne.symm h2), List.filter_append]
  rw [filter_home_nil g w v (f1Of g w bMain i st).2 (by
    intro r hr; rw [f1_snd_home hB r hr]; exact Ne.symm h2), List.append_nil]

include hB in
theorem ib4_parts_hi : parts g w (ib4 g w bMain i st) (i + g.U) =
    insP (clrOf bMain i) (src1 g w bMain i) (parts g w st (i + g.U)) := by
  have h1 : i + g.U ≠ i := by have : 0 < g.U := Nat.two_pow_pos _; omega
  have h2 : i + g.U < (ib3 g w bMain i st).main.length := by
    rw [ib3_main_length, hlen, homes_eq]; omega
  have e3 := ib3_parts_ne (g := g) (w := w) (bMain := bMain) (st := st) (i + g.U) h1
  rw [ib1_parts_hi hU hlen] at e3
  apply HP.ext'
  · show ((ib3 g w bMain i st).main.set (i + g.U) (f1Of g w bMain i st).1).getD (i + g.U) [] = _
    rw [getD_set_self _ _ _ _ h2, f1Of_eq hU hlen]; rfl
  · show (((ib3 g w bMain i st).leaves.getD ((i + g.U) / 2 ^ g.lo) []).filter _) = _
    exact congrArg HP.P e3
  · show ((ib3 g w bMain i st).bcopy.filter _) = _
    exact congrArg HP.T e3
  · show ((ib3 g w bMain i st).ins ++ (f0Of g w bMain i st).2 ++ (f1Of g w bMain i st).2).filter _ = _
    rw [List.filter_append, List.filter_append,
      filter_home_nil g w _ (f0Of g w bMain i st).2 (by
        intro r hr; rw [f0_snd_home hB r hr]; exact Ne.symm h1),
      filter_home_self g w _ (f1Of g w bMain i st).2 (f1_snd_home hB), List.append_nil,
      f1Of_eq hU hlen]
    have := congrArg HP.I e3
    simp only [parts] at this
    rw [this]; rfl

include hll hB in
/-- B bucket `i` acts on output `i` by `homeStep`. -/
theorem insertBucket_parts_lo : parts g w (insertBucket g w bMain i st) i =
    homeStep (clrOf bMain i) (src0 g w bMain i) (parts g w st i) := by
  have h1 : i ≠ i + g.U := by have : 0 < g.U := Nat.two_pow_pos _; omega
  rw [insertBucket_eq, offerB_parts_ne _ _ _ _ _ h1, offerA_parts_ne _ _ _ _ _ h1,
    ib4_parts hB i h1, ib3_parts_lo hU hlen hll,
    filter_home_self g w i _ (f0_snd_home hB)]
  rfl

include hll hB in
/-- B bucket `i` acts on output `i + U` by `homeStep`. -/
theorem insertBucket_parts_hi : parts g w (insertBucket g w bMain i st) (i + g.U) =
    homeStep (clrOf bMain i) (src1 g w bMain i) (parts g w st (i + g.U)) := by
  have h2 : i + g.U < (ib4 g w bMain i st).main.length := by
    rw [ib4_main_length, hlen, homes_eq]; omega
  have hR : (i + g.U) / 2 ^ g.lo < (ib4 g w bMain i st).leaves.length := by
    rw [ib4_leaves_length, hll]; exact range_lt g (by rw [homes_eq]; omega)
  rw [insertBucket_eq, offerB_parts_self _ _ _ _ (by rw [offerA_main_length]; exact h2),
    offerA_parts_self _ _ _ _ h2 hR, ib4_parts_hi hU hlen hB]
  rfl

omit hU hlen in
include hB in
/-- B bucket `i` leaves every other home alone. -/
theorem insertBucket_parts_ne (v : Nat) (h1 : v ≠ i) (h2 : v ≠ i + g.U) :
    parts g w (insertBucket g w bMain i st) v = parts g w st v := by
  rw [insertBucket_eq, offerB_parts_ne _ _ _ _ _ h2, offerA_parts_ne _ _ _ _ _ h2,
    ib4_parts hB v h2, ib3_parts_ne v h1, ib1_parts_ne v h1 h2,
    filter_home_nil g w v _ (by intro r hr; rw [f0_snd_home hB r hr]; exact Ne.symm h1),
    List.append_nil]

end ib

/-! ### All B buckets -/

/-- The finish invariant after the first `n` B buckets: homes `i` and `i + U`
with `i < n` hold `homeStep` of their initial parts, the others their initial
parts. -/
structure FInv (g : Geom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (st0 st : FinState) (n : Nat) :
    Prop where
  len : st.main.length = g.homes
  llen : st.leaves.length = g.ranges
  lrange : ∀ R, ∀ r ∈ st.leaves.getD R [], rangeOf g w r = R
  lo : ∀ i < g.U, parts g w st i = if i < n then
    homeStep (clrOf bMain i) (src0 g w bMain i) (parts g w st0 i) else parts g w st0 i
  hi : ∀ i < g.U, parts g w st (i + g.U) = if i < n then
    homeStep (clrOf bMain i) (src1 g w bMain i) (parts g w st0 (i + g.U)) else parts g w st0 (i + g.U)

theorem FInv.step {g : Geom} {w : Model.LogicalKey → Nat} {bMain : List Bucket} {st0 st : FinState} {n : Nat}
    (h : FInv g w bMain st0 st n) (hn : n < g.U)
    (hB : ∀ r ∈ (bMain.getD n []).recs, w r.key % g.U = n) :
    FInv g w bMain st0 (insertBucket g w bMain n st) (n + 1) where
  len := by rw [insertBucket_main_length, h.len]
  llen := by rw [insertBucket_leaves_length, h.llen]
  lrange := insertBucket_lrange h.lrange
  lo := by
    intro i hi
    by_cases hin : i = n
    · subst hin
      rw [insertBucket_parts_lo hn h.len h.llen hB, h.lo i hi]
      simp
    · rw [insertBucket_parts_ne hB i hin (by omega), h.lo i hi]
      by_cases hlt : i < n
      · simp [hlt, show i < n + 1 by omega]
      · simp [hlt, show ¬ i < n + 1 by omega]
  hi := by
    intro i hi
    by_cases hin : i = n
    · subst hin
      rw [insertBucket_parts_hi hn h.len h.llen hB, h.hi i hi]
      simp
    · rw [insertBucket_parts_ne hB (i + g.U) (by omega) (by omega), h.hi i hi]
      by_cases hlt : i < n
      · simp [hlt, show i < n + 1 by omega]
      · simp [hlt, show ¬ i < n + 1 by omega]

theorem finish_inv (g : Geom) (w : Model.LogicalKey → Nat) (inp : Inputs) (routed : List Bucket)
    (leaves : List (List Rec)) (hlen : routed.length = g.homes) (hll : leaves.length = g.ranges)
    (hlr : ∀ R, ∀ r ∈ leaves.getD R [], rangeOf g w r = R)
    (hB : ∀ i < g.U, ∀ r ∈ (inp.bMain.getD i []).recs, w r.key % g.U = i) :
    FInv g w inp.bMain
      { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }
      (finish g w inp routed leaves) g.U := by
  have key : ∀ n ≤ g.U, FInv g w inp.bMain
      { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }
      ((List.range n).foldl (fun st i => insertBucket g w inp.bMain i st)
        { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }) n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨hlen, hll, hlr, fun i _ => by simp, fun i _ => by simp⟩
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (ih (by omega)).step (by omega) (hB n (by omega))
  exact key g.U (Nat.le_refl _)

end RebuildBound.D23
