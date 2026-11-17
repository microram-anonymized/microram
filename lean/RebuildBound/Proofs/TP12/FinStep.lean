import RebuildBound.Proofs.TP12.Finish

/-!
# TP12: one pair of the last level preserves `FInv`
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

theorem tpOffer_recs_mem (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) {r : Rec}
    (hr : r ∈ ((tpOffer g w b st).main.getD b []).recs) :
    r ∈ (st.main.getD b []).recs ∨ tpHome g w r = b := by
  rw [tpOffer_main_self g w st hb] at hr
  have hf : List.Perm (Bucket.recs (fill (st.main.getD b []) (offCand g w b st)).1)
      (Bucket.recs (st.main.getD b []) ++
        (offCand g w b st).take (min (nfree (st.main.getD b [])) (offCand g w b st).length)) :=
    fill_recs (st.main.getD b []) (offCand g w b st)
  rcases List.mem_append.1 (hf.mem_iff.1 hr) with h | h
  · exact Or.inl h
  · right
    have := (List.mem_filter.1 ((List.take_subset _ _) h)).2
    simpa using this

/-- The state after the merge-split of pair `i` with the split `p`, before the offers. -/
def splitWith (g : TPGeom) (i : Nat) (st : TPFin) (p : Bucket × Bucket × List Rec) : TPFin :=
  { st with
    main := (st.main.set i p.1).set (i + g.half) p.2.1
    last := st.last ++ p.2.2
    trace := st.trace ++ [(.stash (g.k - 1), (st.last ++ p.2.2).length)] }

theorem tpLastStep_eq' (rule : CapRule) (g : TPGeom) (w : Model.LogicalKey → Nat) (i : Nat) (st : TPFin) :
    tpLastStep rule g w i st = tpOffer g w (i + g.half) (tpOffer g w i
      (splitWith g i st (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD i [])
        (st.main.getD (i + g.half) [])))) := rfl

theorem fInv_step {rule : CapRule} (hv : rule.Valid) {g : TPGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat}
    {M : List Bucket} {pool : List Rec} (hM : MData g w M) {n : Nat} {st : TPFin}
    (hn : n < g.half) (h : FInv g w M pool n st) :
    FInv g w M pool (n + 1) (tpLastStep rule g w n st) := by
  have hT := T_eq g hg
  have hH := half_pos g
  have hnT : n < g.T := by omega
  have hnHT : n + g.half < g.T := by omega
  have hmodn : n % g.half = n := Nat.mod_eq_of_lt hn
  have hmodnH : (n + g.half) % g.half = n := by rw [Nat.add_mod_right]; exact hmodn
  obtain ⟨hF0, hLn⟩ := h.unproc n hnT (by rw [hmodn])
  obtain ⟨hS0, hLnH⟩ := h.unproc (n + g.half) hnHT (by rw [hmodnH])
  have hFl : (st.main.getD n []).length = g.C :=
    h.mlanes _ (getD_mem _ _ _ (by rw [h.mlen]; exact hnT))
  have hSl : (st.main.getD (n + g.half) []).length = g.C :=
    h.mlanes _ (getD_mem _ _ _ (by rw [h.mlen]; exact hnHT))
  have hne : n ≠ n + g.half := by omega
  -- the arrivals
  have hArr : ∀ r ∈ (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs,
      tpHome g w r = n + g.half * (if dirBit w (g.k - 1) r then 1 else 0) := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · rw [hF0] at hr
      have := hM.home n (by omega) r hr
      rwa [hmodn] at this
    · rw [hS0] at hr
      have := hM.home (n + g.half) (by omega) r hr
      rwa [hmodnH] at this
  have hArr0 : ∀ r ∈ (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs,
      dirBit w (g.k - 1) r = false → tpHome g w r = n := by
    intro r hr hd; have := hArr r hr; rw [hd] at this; simpa using this
  have hArr1 : ∀ r ∈ (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs,
      dirBit w (g.k - 1) r = true → tpHome g w r = n + g.half := by
    intro r hr hd; have := hArr r hr; rw [hd] at this; simpa using this
  -- the split
  obtain ⟨hp, hlan1, hlan2⟩ : List.Perm ((rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) [])).1.recs ++
      (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) [])).2.1.recs ++
      (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) [])).2.2)
      ((st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs) ∧
    (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) [])).1.length = g.C ∧
    (rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) [])).2.1.length = g.C :=
    ⟨hv.perm _ _ _ _ hFl hSl, (hv.lanes _ _ _ _ hFl hSl).1, (hv.lanes _ _ _ _ hFl hSl).2⟩
  have hcnt1 := hv.count_first g.C (dirBit w (g.k - 1)) _ _ hFl hSl
  have hcnt2 := hv.count_second g.C (dirBit w (g.k - 1)) _ _ hFl hSl
  have hdir1 := hv.dir_first g.C (dirBit w (g.k - 1)) _ _ hFl hSl
  have hdir2 := hv.dir_second g.C (dirBit w (g.k - 1)) _ _ hFl hSl
  have hsh0 := fun r hr hd => shed_full_false hv g.C (dirBit w (g.k - 1)) _ _ hFl hSl (r := r) hr hd
  have hsh1 := fun r hr hd => shed_full_true hv g.C (dirBit w (g.k - 1)) _ _ hFl hSl (r := r) hr hd
  rw [tpLastStep_eq']
  generalize rule.split g.C (dirBit w (g.k - 1)) (st.main.getD n [])
        (st.main.getD (n + g.half) []) = pr at hp hlan1 hlan2 hcnt1 hcnt2 hdir1 hdir2 hsh0 hsh1 ⊢
  obtain ⟨out1, out2, shed⟩ := pr
  simp only at hp hlan1 hlan2 hcnt1 hcnt2 hdir1 hdir2 hsh0 hsh1
  have hmem_arr : ∀ r, r ∈ out1.recs ∨ r ∈ out2.recs →
      r ∈ (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs := by
    intro r hr
    refine hp.mem_iff.1 ?_
    rcases hr with hr | hr
    · exact List.mem_append_left _ (List.mem_append_left _ hr)
    · exact List.mem_append_left _ (List.mem_append_right _ hr)
  have hmem_arr' : ∀ r ∈ shed,
      r ∈ (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs := by
    intro r hr
    exact hp.mem_iff.1 (List.mem_append_right _ hr)
  have hout1h : ∀ r ∈ out1.recs, tpHome g w r = n := fun r hr =>
    hArr0 r (hmem_arr r (Or.inl hr)) (hdir1 r hr)
  have hout2h : ∀ r ∈ out2.recs, tpHome g w r = n + g.half := fun r hr =>
    hArr1 r (hmem_arr r (Or.inr hr)) (hdir2 r hr)
  have hshedh : ∀ r ∈ shed, (tpHome g w r = n ∧ out1.recs.length = g.C) ∨
      (tpHome g w r = n + g.half ∧ out2.recs.length = g.C) := by
    intro r hr
    cases hd : dirBit w (g.k - 1) r
    · exact Or.inl ⟨hArr0 r (hmem_arr' r hr) hd, hsh0 r hr hd⟩
    · exact Or.inr ⟨hArr1 r (hmem_arr' r hr) hd, hsh1 r hr hd⟩
  -- counts
  set Arr := (st.main.getD n []).recs ++ (st.main.getD (n + g.half) []).recs with hArrdef
  have ha0 : Arr.countP (fun r => !dirBit w (g.k - 1) r) =
      Arr.countP (fun r => tpHome g w r == n) := by
    apply List.countP_congr
    intro r hr
    have := hArr r hr
    cases hd : dirBit w (g.k - 1) r
    · have := hArr0 r hr hd; simp [this]
    · have := hArr1 r hr hd; simp [this]; omega
  have ha1 : Arr.countP (dirBit w (g.k - 1)) =
      Arr.countP (fun r => tpHome g w r == n + g.half) := by
    apply List.countP_congr
    intro r hr
    cases hd : dirBit w (g.k - 1) r
    · have := hArr0 r hr hd; simp [this]; omega
    · have := hArr1 r hr hd; simp [this]
  have hcM : ∀ v ∈ [n, n + g.half], (M.flatMap Bucket.recs).countP (fun r => tpHome g w r == v) =
      Arr.countP (fun r => tpHome g w r == v) := by
    intro v hv'
    have h2 := countP_flatMap_two (fun r => tpHome g w r == v) M n (n + g.half) hne
      (by rw [hM.len]; exact hnT) (by rw [hM.len]; exact hnHT) (by
        intro b hb hb1 hb2 r hr
        have := hM.home b (by rw [hM.len] at hb; exact hb) r hr
        have hbT : b < 2 * g.half := by rw [hM.len] at hb; omega
        have hbm : b % g.half < g.half := Nat.mod_lt _ hH
        have hv2 : v = n ∨ v = n + g.half := by simpa using hv'
        by_contra hcon
        have hcon' : tpHome g w r = v := by simpa using hcon
        have hcase : (if (w r.key).testBit (g.k - 1) then 1 else 0) = 0 ∨
            (if (w r.key).testBit (g.k - 1) then 1 else 0) = 1 := by split_ifs <;> simp
        have hbb : b % g.half = n := by
          rcases hcase with hc | hc <;> rcases hv2 with hv2 | hv2 <;> rw [hc] at this <;> omega
        rcases mod_cases hbT hn hbb with e | e
        · exact hb1 e
        · exact hb2 e)
    rw [h2, hArrdef, hF0, hS0, List.countP_append]
  have hlenOut1 : out1.recs.length = min g.C (Arr.countP (fun r => tpHome g w r == n)) := by
    rw [hcnt1, ha0]
  have hlenOut2 : out2.recs.length = min g.C (Arr.countP (fun r => tpHome g w r == n + g.half)) := by
    rw [hcnt2, ha1]
  have hcMn := hcM n (by simp)
  have hcMnH := hcM (n + g.half) (by simp)
  set st1 := splitWith g n st (out1, out2, shed) with hst1def
  have e1main : st1.main = (st.main.set n out1).set (n + g.half) out2 := rfl
  have e1last : st1.last = st.last ++ shed := rfl
  have e1leaves : st1.leaves = st.leaves := rfl
  have hnl : n < st.main.length := by rw [h.mlen]; exact hnT
  have hnHl : n + g.half < st.main.length := by rw [h.mlen]; exact hnHT
  have m1_n : st1.main.getD n [] = out1 := by
    rw [e1main, D6.getD_set_ne _ _ _ (Ne.symm hne), getD_set_self _ _ _ _ hnl]
  have m1_nH : st1.main.getD (n + g.half) [] = out2 := by
    rw [e1main, getD_set_self _ _ _ _ (by rw [List.length_set]; exact hnHl)]
  have m1_ne : ∀ b, b ≠ n → b ≠ n + g.half → st1.main.getD b [] = st.main.getD b [] := by
    intro b h1 h2
    rw [e1main, D6.getD_set_ne _ _ _ (Ne.symm h2), D6.getD_set_ne _ _ _ (Ne.symm h1)]
  have m1len : st1.main.length = g.T := by
    rw [e1main, List.length_set, List.length_set, h.mlen]
  have m1lanes : ∀ B ∈ st1.main, B.length = g.C := by
    intro B hB
    rw [e1main] at hB
    rcases List.mem_or_eq_of_mem_set hB with hB | rfl
    · rcases List.mem_or_eq_of_mem_set hB with hB | rfl
      · exact h.mlanes B hB
      · exact hlan1
    · exact hlan2
  have hb1 : n < st1.main.length := by rw [m1len]; exact hnT
  have hR1 : n / 2 ^ g.I < st1.leaves.length := by
    rw [e1leaves, h.llen]; exact div_lt_ranges g hg hnT
  set st2 := tpOffer g w n st1 with hst2def
  have hb2 : n + g.half < st2.main.length := by
    rw [hst2def, tpOffer_main_length, m1len]; exact hnHT
  have hR2 : (n + g.half) / 2 ^ g.I < st2.leaves.length := by
    rw [hst2def, tpOffer_leaves_length, e1leaves, h.llen]; exact div_lt_ranges g hg hnHT
  have m2len : st2.main.length = g.T := by rw [hst2def, tpOffer_main_length, m1len]
  have m2lanes : ∀ B ∈ st2.main, B.length = g.C := tpOffer_lanes g w st1 hb1 m1lanes
  set st3 := tpOffer g w (n + g.half) st2 with hst3def
  have m2_nH : st2.main.getD (n + g.half) [] = out2 := by
    rw [hst2def, tpOffer_main_ne g w st1 (Ne.symm hne)]; exact m1_nH
  have m3_n : st3.main.getD n [] = st2.main.getD n [] := by
    rw [hst3def, tpOffer_main_ne g w st2 hne]
  have m3_ne : ∀ b, b ≠ n → b ≠ n + g.half → st3.main.getD b [] = st.main.getD b [] := by
    intro b h1 h2
    rw [hst3def, tpOffer_main_ne g w st2 h2, hst2def, tpOffer_main_ne g w st1 h1]
    exact m1_ne b h1 h2
  have m3len : st3.main.length = g.T := by rw [hst3def, tpOffer_main_length, m2len]
  have m3lanes : ∀ B ∈ st3.main, B.length = g.C := tpOffer_lanes g w st2 hb2 m2lanes
  have l3len : st3.leaves.length = g.ranges := by
    rw [hst3def, tpOffer_leaves_length, hst2def, tpOffer_leaves_length, e1leaves, h.llen]
  have l3mem : ∀ R x, x ∈ st3.leaves.getD R [] → x ∈ st.leaves.getD R [] := by
    intro R x hx
    have := tpOffer_leaves_mem g w st2 hx
    have := tpOffer_leaves_mem g w st1 this
    rwa [e1leaves] at this
  have l2mem : ∀ R x, x ∈ st2.leaves.getD R [] → x ∈ st.leaves.getD R [] := by
    intro R x hx
    have := tpOffer_leaves_mem g w st1 hx
    rwa [e1leaves] at this
  have lr3 : ∀ R, ∀ x ∈ st3.leaves.getD R [], tpRange g w x = R := fun R x hx =>
    h.lrange R x (l3mem R x hx)
  -- candidate counts
  have cand1 : (offCand g w n st1).length = pool.countP (fun r => tpHome g w r == n) := by
    unfold offCand
    rw [← List.countP_eq_length_filter, e1leaves]; exact hLn
  have cand2 : (offCand g w (n + g.half) st2).length =
      pool.countP (fun r => tpHome g w r == n + g.half) := by
    unfold offCand
    rw [← List.countP_eq_length_filter, hst2def, tpOffer_count_ne g w st1 (Ne.symm hne),
      e1leaves]; exact hLnH
  have r2 : (st2.main.getD n []).recs.length =
      min g.C (out1.recs.length + pool.countP (fun r => tpHome g w r == n)) := by
    rw [hst2def, tpOffer_recs_length g w st1 hb1 m1lanes, m1_n, cand1]
  have r3 : (st3.main.getD (n + g.half) []).recs.length =
      min g.C (out2.recs.length + pool.countP (fun r => tpHome g w r == n + g.half)) := by
    rw [hst3def, tpOffer_recs_length g w st2 hb2 m2lanes, m2_nH, cand2]
  have nl : ∀ b, b % g.half < n → b ≠ n ∧ b ≠ n + g.half := by
    intro b hlt
    constructor
    · intro e; rw [e, hmodn] at hlt; omega
    · intro e; rw [e, hmodnH] at hlt; omega
  have nl' : ∀ b, n + 1 ≤ b % g.half → b ≠ n ∧ b ≠ n + g.half := by
    intro b hlt
    constructor
    · intro e; rw [e, hmodn] at hlt; omega
    · intro e; rw [e, hmodnH] at hlt; omega
  -- full-ness of the new buckets
  have hmodcases : ∀ b, b < g.T → b % g.half = n → b = n ∨ b = n + g.half := fun b hb hbm =>
    mod_cases (by omega) hn hbm
  refine ⟨m3len, m3lanes, l3len, lr3, ?_, ?_, ?_, ?_, ?_⟩
  · -- conservation
    have P2 := tpOffer_perm g w st1 hb1 hR1
    have P3 := tpOffer_perm g w st2 hb2 hR2
    have A1 := perm_flatMap_set Bucket.recs st.main n out1 [] hnl
    have A2 := perm_flatMap_set Bucket.recs (st.main.set n out1) (n + g.half) out2 []
      (by rw [List.length_set]; exact hnHl)
    rw [D6.getD_set_ne _ _ _ hne] at A2
    rw [e1main] at P2
    rw [List.perm_iff_count]
    intro x
    have c1 := A1.count_eq x
    have c2 := A2.count_eq x
    have c3 := hp.count_eq x
    have c4 := h.cons.count_eq x
    have c5 := P2.count_eq x
    have c6 := P3.count_eq x
    have e3 : st3.last = st.last ++ shed := rfl
    rw [e3]
    rw [e1leaves, ← hst2def] at c5
    rw [← hst3def] at c6
    simp only [hArrdef, List.count_append] at c1 c2 c3 c4 c5 c6 ⊢
    omega
  · -- unprocessed
    intro b hb hnb
    obtain ⟨h1, h2⟩ := nl' b hnb
    obtain ⟨hMb, hLb⟩ := h.unproc b hb (by omega)
    refine ⟨by rw [m3_ne b h1 h2]; exact hMb, ?_⟩
    rw [hst3def, tpOffer_count_ne g w st2 h2, hst2def, tpOffer_count_ne g w st1 h1, e1leaves]
    exact hLb
  · -- processed
    intro b hb hnb
    by_cases hlt : b % g.half < n
    · obtain ⟨h1, h2⟩ := nl b hlt
      obtain ⟨hh, hl⟩ := h.proc b hb hlt
      rw [m3_ne b h1 h2]; exact ⟨hh, hl⟩
    · have hbm : b % g.half = n := by omega
      rcases hmodcases b hb hbm with rfl | rfl
      · rw [m3_n]
        refine ⟨?_, ?_⟩
        · intro r hr
          rcases tpOffer_recs_mem g w st1 hb1 hr with hr | hr
          · rw [m1_n] at hr; exact hout1h r hr
          · exact hr
        · rw [r2, hlenOut1, ← hcMn]; omega
      · refine ⟨?_, ?_⟩
        · intro r hr
          rcases tpOffer_recs_mem g w st2 hb2 hr with hr | hr
          · rw [m2_nH] at hr; exact hout2h r hr
          · exact hr
        · rw [r3, hlenOut2, ← hcMnH]; omega
  · -- leaves
    intro r hr hrm
    obtain ⟨R', hR', hrR⟩ := mem_flatten_getD _ hr
    have hrange := lr3 R' r hrR
    have hrh := home_lt g w r
    by_cases hlt : tpHome g w r % g.half < n
    · obtain ⟨h1, h2⟩ := nl _ hlt
      rw [m3_ne _ h1 h2]
      exact h.leafFull r (mem_getD_flatten _ R' (l3mem R' r hrR)) hlt
    · have hbm : tpHome g w r % g.half = n := by omega
      have hRe : R' = tpHome g w r / 2 ^ g.I := by rw [← hrange]; rfl
      rcases hmodcases _ hrh hbm with e | e
      · rw [e, m3_n]
        rw [hRe, e, hst3def] at hrR
        have hr2 := tpOffer_leaves_mem g w st2 hrR
        exact tpOffer_leftover_full g w st1 hb1 m1lanes hR1 hr2 e
      · rw [e]
        rw [hRe, e] at hrR
        exact tpOffer_leftover_full g w st2 hb2 m2lanes hR2 hrR e
  · -- last stash
    intro r hr
    have e3 : st3.last = st.last ++ shed := rfl
    rw [e3] at hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨hlt, hfull⟩ := h.lastFull r hr
      obtain ⟨h1, h2⟩ := nl _ hlt
      rw [m3_ne _ h1 h2]
      exact ⟨by omega, hfull⟩
    · rcases hshedh r hr with ⟨e, hf⟩ | ⟨e, hf⟩
      · rw [e, m3_n, hmodn]
        refine ⟨by omega, ?_⟩
        rw [r2, hf]; omega
      · rw [e, hmodnH]
        refine ⟨by omega, ?_⟩
        rw [r3, hf]; omega

end RebuildBound.TP12
