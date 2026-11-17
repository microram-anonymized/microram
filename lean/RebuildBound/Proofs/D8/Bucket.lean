import RebuildBound.Proofs.D8.Sweep

/-!
# D8: one destination and one B bucket

`topDest` acts on the share of its destination by `hvisit` and on no other
home. `topBucket i` clears the A copies of B bucket `i`'s keys at the homes
`i + qU`, then visits the ways in order.
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {w : Model.LogicalKey → Nat}

section dest
/-- B's direction-`q` records. -/
def dirOf (g : TopGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (q : Nat) : List Rec :=
  Bi.recs.filter fun r => topWay g w r == q

variable (Bi : Bucket) (i q : Nat) (st : FinState)

theorem dest_main_length : (topDest g w Bi i q st).1.main.length = st.main.length := by
  simp [topDest, offer_main_length, resolve_main_length]

theorem dest_leaves_length : (topDest g w Bi i q st).1.leaves.length = st.leaves.length := by
  simp [topDest, offer_leaves_length, resolve_leaves_length]

theorem dest_ins : (topDest g w Bi i q st).1.ins = st.ins := rfl
theorem dest_trace : (topDest g w Bi i q st).1.trace = st.trace := rfl

theorem dest_lrange (h : ∀ R, ∀ r ∈ st.leaves.getD R [], topHome g w r / 2 ^ g.I = R) :
    ∀ R, ∀ r ∈ (topDest g w Bi i q st).1.leaves.getD R [], topHome g w r / 2 ^ g.I = R := by
  unfold topDest
  exact offer_lrange (resolve_lrange h)

variable {Bi i q st}

theorem dest_parts_self {ci : Nat} (hci : ci = i + q * g.U) (hm : ci < st.main.length)
    (hR : ci / 2 ^ g.I < st.leaves.length) :
    parts g w (topDest g w Bi i q st).1 ci =
        (hvisit ((dirOf g w Bi q).map Rec.key)
          ((dirOf g w Bi q).filter fun r => !r.tomb) (parts g w st ci)).1 ∧
      (topDest g w Bi i q st).2 =
        (hvisit ((dirOf g w Bi q).map Rec.key)
          ((dirOf g w Bi q).filter fun r => !r.tomb) (parts g w st ci)).2 := by
  subst hci
  have h1 := resolve_parts_self (g := g) (w := w) (dk := ((dirOf g w Bi q).map Rec.key)) hm hR
  have hm1 : i + q * g.U < (topResolve g w (i + q * g.U)
      ((dirOf g w Bi q).map Rec.key) st).main.length := by
    rw [resolve_main_length]; exact hm
  have hR1 : (i + q * g.U) / 2 ^ g.I < (topResolve g w (i + q * g.U)
      ((dirOf g w Bi q).map Rec.key) st).leaves.length := by
    rw [resolve_leaves_length]; exact hR
  set st1 := topResolve g w (i + q * g.U) ((dirOf g w Bi q).map Rec.key) st with hst1
  set f := fill (st1.main.getD (i + q * g.U) [])
    ((dirOf g w Bi q).filter fun r => !r.tomb) with hf
  have h2 : parts g w { st1 with main := st1.main.set (i + q * g.U) f.1 } (i + q * g.U) =
      ⟨f.1, (parts g w st1 (i + q * g.U)).P, (parts g w st1 (i + q * g.U)).T⟩ := by
    simp only [parts]
    rw [getD_set_self _ _ _ _ hm1]
  have hmf : (i + q * g.U) < ({ st1 with main := st1.main.set (i + q * g.U) f.1 } : FinState).main.length := by
    simp only [List.length_set]; exact hm1
  have hRf : (i + q * g.U) / 2 ^ g.I < ({ st1 with main := st1.main.set (i + q * g.U) f.1 } : FinState).leaves.length := hR1
  have hfm : st1.main.getD (i + q * g.U) [] = (hres ((dirOf g w Bi q).map Rec.key)
      (parts g w st (i + q * g.U))).m := by
    rw [← h1]; rfl
  constructor
  · have := offer_parts_self (g := g) (w := w) (ci := i + q * g.U)
      (st := { st1 with main := st1.main.set (i + q * g.U) f.1 }) hmf hRf
    show parts g w (topOffer g w (i + q * g.U) { st1 with main := st1.main.set (i + q * g.U) f.1 }) _ = _
    rw [this, h2, h1]
    simp only [hvisit, hf, hfm]
  · show f.2 = _
    simp only [hvisit, hf, hfm]

theorem dest_parts_ne {ci v : Nat} (hci : ci = i + q * g.U) (hne : v ≠ ci) :
    parts g w (topDest g w Bi i q st).1 v = parts g w st v := by
  subst hci
  unfold topDest
  rw [offer_parts_ne (by simpa using hne)]
  simp only [parts]
  rw [D6.getD_set_ne _ _ _ (Ne.symm hne)]
  have := resolve_parts_ne (g := g) (w := w) (ci := i + q * g.U)
    (dk := ((dirOf g w Bi q).map Rec.key)) (st := st) hne
  simpa [parts, dirOf] using this

end dest

end RebuildBound.D8

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {w : Model.LogicalKey → Nat}

/-! ### The clear phase of a B bucket -/

/-- Clear the A copies of B bucket `i`'s keys at the first `n` destinations
`i + qU`. -/
def clearMain (g : TopGeom) (Bi : Bucket) (i : Nat) (main : List Bucket) (n : Nat) :
    List Bucket :=
  (List.range n).foldl (fun m q => m.set (i + q * g.U)
    ((m.getD (i + q * g.U) []).clear fun key => Bi.keys.contains key)) main

theorem clearMain_spec (Bi : Bucket) {i : Nat} (hi : i < g.U) (main : List Bucket)
    (hlen : main.length = g.T) : ∀ n, n ≤ g.D →
    (clearMain g Bi i main n).length = g.T ∧
    ∀ v, (clearMain g Bi i main n).getD v [] =
      if v % g.U = i ∧ v / g.U < n then
        (main.getD v []).clear (fun key => Bi.keys.contains key) else main.getD v [] := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨hlen, fun v => by simp [clearMain]⟩
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlt : i + n * g.U < g.T := lt_T_of g hi (by omega)
    have e : clearMain g Bi i main (n + 1) = (clearMain g Bi i main n).set (i + n * g.U)
        (((clearMain g Bi i main n).getD (i + n * g.U) []).clear fun key => Bi.keys.contains key) := by
      unfold clearMain
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [e, List.length_set, ih1], ?_⟩
    intro v
    rw [e]
    by_cases hv : v = i + n * g.U
    · subst hv
      obtain ⟨h1, h2⟩ := mod_div_of g (q := n) hi
      rw [getD_set_self _ _ _ _ (by rw [ih1]; exact hlt), ih2, h1, h2]
      simp
    · rw [D6.getD_set_ne _ _ _ (Ne.symm hv), ih2]
      have : ¬ (v % g.U = i ∧ v / g.U = n) := by
        rintro ⟨h1, h2⟩
        apply hv
        have := split_home g (v := v)
        rw [h1, h2] at this; exact this
      by_cases hc : v % g.U = i ∧ v / g.U < n
      · simp [hc, show v / g.U < n + 1 by omega]
      · have : ¬ (v % g.U = i ∧ v / g.U < n + 1) := by
          rintro ⟨h1, h2⟩
          apply this
          exact ⟨h1, by omega⟩
        simp [hc, this]

/-! ### The ways of a B bucket -/

/-- The first `n` ways of bucket `i`: the state and the sheds so far. -/
def wayFold (g : TopGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat) (st1 : FinState) (n : Nat) :
    FinState × List Rec :=
  (List.range n).foldl (fun acc q =>
    let p := topDest g w Bi i q acc.1
    (p.1, acc.2 ++ p.2)) (st1, [])

theorem div_lt_ranges (hg : g.Valid) {v : Nat} (hv : v < g.T) : v / 2 ^ g.I < g.ranges := by
  obtain ⟨_, h2, _⟩ := hg
  unfold TopGeom.ranges
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  unfold TopGeom.T at hv
  rw [h2]; exact hv

/-- The share of way `q`'s destination after its visit. -/
def visitAt (g : TopGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (q : Nat) (h : HQ) : HQ :=
  (hvisit ((dirOf g w Bi q).map Rec.key) ((dirOf g w Bi q).filter fun r => !r.tomb) h).1

theorem wayFold_spec (hg : g.Valid) (Bi : Bucket) {i : Nat} (hi : i < g.U) (st1 : FinState)
    (hst : Good g w st1) : ∀ n, n ≤ g.D →
    Good g w (wayFold g w Bi i st1 n).1 ∧
    (wayFold g w Bi i st1 n).1.ins = st1.ins ∧
    (wayFold g w Bi i st1 n).1.trace = st1.trace ∧
    (∀ v, ¬ (v % g.U = i ∧ v / g.U < n) →
      parts g w (wayFold g w Bi i st1 n).1 v = parts g w st1 v) ∧
    (∀ q < n, parts g w (wayFold g w Bi i st1 n).1 (i + q * g.U) =
      visitAt g w Bi q (parts g w st1 (i + q * g.U))) ∧
    (wayFold g w Bi i st1 n).2 = (List.range n).flatMap fun q =>
      (hvisit ((dirOf g w Bi q).map Rec.key) ((dirOf g w Bi q).filter fun r => !r.tomb)
        (parts g w st1 (i + q * g.U))).2 := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨hst, rfl, rfl, fun v _ => rfl, fun q hq => by omega, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := ih (by omega)
    have e : wayFold g w Bi i st1 (n + 1) =
        ((topDest g w Bi i n (wayFold g w Bi i st1 n).1).1,
          (wayFold g w Bi i st1 n).2 ++ (topDest g w Bi i n (wayFold g w Bi i st1 n).1).2) := by
      unfold wayFold
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set s := (wayFold g w Bi i st1 n).1 with hs
    have hlt : i + n * g.U < g.T := lt_T_of g hi (by omega)
    have hm : i + n * g.U < s.main.length := by rw [g1.len]; exact hlt
    have hR : (i + n * g.U) / 2 ^ g.I < s.leaves.length := by
      rw [g1.llen]; exact div_lt_ranges hg hlt
    obtain ⟨h1, h2⟩ := mod_div_of g (q := n) hi
    have hps : parts g w s (i + n * g.U) = parts g w st1 (i + n * g.U) :=
      g4 _ (by rintro ⟨_, h⟩; rw [h2] at h; omega)
    obtain ⟨d1, d2⟩ := dest_parts_self (Bi := Bi) (i := i) (q := n) (st := s) rfl hm hR
    rw [e]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · show (topDest g w Bi i n s).1.main.length = _
      rw [dest_main_length, g1.len]
    · show (topDest g w Bi i n s).1.leaves.length = _
      rw [dest_leaves_length, g1.llen]
    · exact dest_lrange Bi i n s g1.lrange
    · exact g2
    · exact g3
    · intro v hv
      have hne : v ≠ i + n * g.U := by
        rintro rfl; apply hv; rw [h1, h2]; exact ⟨rfl, by omega⟩
      show parts g w (topDest g w Bi i n s).1 v = _
      rw [dest_parts_ne (Bi := Bi) (i := i) (q := n) (st := s) rfl hne]
      exact g4 v (fun h => hv ⟨h.1, by omega⟩)
    · intro q hq
      by_cases hqn : q = n
      · subst hqn
        show parts g w (topDest g w Bi i q s).1 _ = _
        rw [d1, hps]; rfl
      · have hne : i + q * g.U ≠ i + n * g.U := by
          intro h
          have := (mod_div_of g (q := q) hi).2
          rw [h, h2] at this
          omega
        show parts g w (topDest g w Bi i n s).1 _ = _
        rw [dest_parts_ne (Bi := Bi) (i := i) (q := n) (st := s) rfl hne]
        exact g5 q (by omega)
    · show (wayFold g w Bi i st1 n).2 ++ (topDest g w Bi i n s).2 = _
      rw [g6, d2, hps, List.range_succ, List.flatMap_append]
      simp

/-! ### One B bucket -/

theorem topBucket_spec (hg : g.Valid) (bMain : List Bucket) {st : FinState} (hst : Good g w st)
    {i : Nat} (hi : i < g.U) :
    Good g w (topBucket g w bMain i st) ∧
    (topBucket g w bMain i st).ins = st.ins ++ (List.range g.D).flatMap (fun q =>
      (hstep (fun key => (bMain.getD i []).keys.contains key)
        ((dirOf g w (bMain.getD i []) q).map Rec.key)
        ((dirOf g w (bMain.getD i []) q).filter fun r => !r.tomb)
        (parts g w st (i + q * g.U))).2) ∧
    (topBucket g w bMain i st).trace =
      st.trace ++ [(.insertion, (topBucket g w bMain i st).ins.length)] ∧
    (∀ v, v % g.U ≠ i → parts g w (topBucket g w bMain i st) v = parts g w st v) ∧
    (∀ q < g.D, parts g w (topBucket g w bMain i st) (i + q * g.U) =
      (hstep (fun key => (bMain.getD i []).keys.contains key)
        ((dirOf g w (bMain.getD i []) q).map Rec.key)
        ((dirOf g w (bMain.getD i []) q).filter fun r => !r.tomb)
        (parts g w st (i + q * g.U))).1) := by
  set Bi := bMain.getD i [] with hBi
  obtain ⟨c1, c2⟩ := clearMain_spec Bi hi st.main hst.len g.D (Nat.le_refl _)
  set st1 : FinState := { st with main := clearMain g Bi i st.main g.D } with hst1
  have hg1 : Good g w st1 := ⟨c1, hst.llen, hst.lrange⟩
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := wayFold_spec hg Bi hi st1 hg1 g.D (Nat.le_refl _)
  have hpar : ∀ q < g.D, parts g w st1 (i + q * g.U) =
      ⟨(parts g w st (i + q * g.U)).m.clear (fun key => Bi.keys.contains key),
        (parts g w st (i + q * g.U)).P, (parts g w st (i + q * g.U)).T⟩ := by
    intro q hq
    obtain ⟨h1, h2⟩ := mod_div_of g (q := q) hi
    simp only [parts, hst1]
    rw [c2, if_pos ⟨h1, by rw [h2]; exact hq⟩]
  have hfold : (topBucket g w bMain i st) =
      { (wayFold g w Bi i st1 g.D).1 with
        ins := (wayFold g w Bi i st1 g.D).1.ins ++ (wayFold g w Bi i st1 g.D).2
        trace := (wayFold g w Bi i st1 g.D).1.trace ++
          [(.insertion, ((wayFold g w Bi i st1 g.D).1.ins ++ (wayFold g w Bi i st1 g.D).2).length)] } := rfl
  have hins : (wayFold g w Bi i st1 g.D).1.ins ++ (wayFold g w Bi i st1 g.D).2 =
      st.ins ++ (List.range g.D).flatMap (fun q =>
      (hstep (fun key => Bi.keys.contains key)
        ((dirOf g w Bi q).map Rec.key)
        ((dirOf g w Bi q).filter fun r => !r.tomb)
        (parts g w st (i + q * g.U))).2) := by
    rw [g2, g6]
    show st.ins ++ _ = _
    congr 1
    apply List.flatMap_congr
    intro q hq
    rw [hpar q (List.mem_range.1 hq)]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfold]; exact ⟨g1.len, g1.llen, g1.lrange⟩
  · rw [hfold]; exact hins
  · rw [hfold]
    show (wayFold g w Bi i st1 g.D).1.trace ++ _ = st.trace ++ [(.insertion, _)]
    rw [g3, hins]
  · intro v hv
    rw [hfold]
    show parts g w (wayFold g w Bi i st1 g.D).1 v = _
    rw [g4 v (fun h => hv h.1)]
    simp only [parts, hst1]
    rw [c2, if_neg (fun h => hv h.1)]
  · intro q hq
    rw [hfold]
    show parts g w (wayFold g w Bi i st1 g.D).1 _ = _
    rw [g5 q hq, hpar q hq]
    rfl

end RebuildBound.D8
