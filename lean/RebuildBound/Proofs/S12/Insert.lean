import RebuildBound.Proofs.S12.Offers

/-!
# S12: B's insertion, bucket by bucket

`sInsertBucket i` first clears the A copies of B bucket `i`'s keys from its
`d` homes `i + qU` (`dedup_fold`), then for each way `q` inserts B's records
of that way into home `i + qU` and makes the offers to it (`wayFn`). Its
sheds wait in the accumulator until the last way; with the sheds passed to
`gparts` explicitly, each way acts on its own home by
`gPages ∘ gOffA ∘ gFill` and on no other home (`wayFn_parts`). So after
`sInsertBucket i` every home `i + qU` holds `gStep` of its parts and the
other homes are unchanged (`sInsertBucket_parts`), and after `sFinish`
every home holds `gStep` of its initial parts (`sFinish_inv`).
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-- B's records of carry bucket `i` and way `q`. -/
def srcW (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i q : Nat) : List Rec :=
  (bMain.getD i []).recs.filter fun x => g.wayOf (w x.key) == q

/-- One step of the dedup pass. -/
def dedStep (g : SepGeom) (bMain : List Bucket) (i : Nat) (m : List Bucket) (q : Nat) :
    List Bucket :=
  m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear (clrOf bMain i))

/-- One way of B's insertion of bucket `i`, with its offers. -/
def wayFn (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (acc : SFin × List Rec)
    (q : Nat) : SFin × List Rec :=
  let ci := i + q * g.U
  let f := fill (acc.1.main.getD ci []) (srcW g w bMain i q)
  let sheds := acc.2 ++ f.2
  let st := { acc.1 with main := acc.1.main.set ci f.1 }
  let st := if q + 1 = g.d then
      let ins := st.ins ++ sheds
      { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
    else st
  (sOfferB g w ci (sOfferA g w ci st), sheds)

theorem sInsertBucket_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (st : SFin) : sInsertBucket g w bMain i st =
      ((List.range g.d).foldl (wayFn g w bMain i)
        ({ st with main := (List.range g.d).foldl (dedStep g bMain i) st.main }, [])).1 := rfl

/-! ### The dedup pass -/

theorem carry_eq (g : SepGeom) {v i n : Nat} (h1 : v % g.U = i) (h2 : v / g.U = n) :
    v = i + n * g.U := by
  have := home_decomp g v; rw [h1, h2] at this; exact this

theorem dedup_fold (g : SepGeom) (bMain : List Bucket) {i : Nat} (hi : i < g.U) (m : List Bucket)
    (hm : m.length = g.N) : ∀ n ≤ g.d,
    ((List.range n).foldl (dedStep g bMain i) m).length = g.N ∧
    ∀ v, ((List.range n).foldl (dedStep g bMain i) m).getD v [] =
      if v % g.U = i ∧ v / g.U < n then (m.getD v []).clear (clrOf bMain i) else m.getD v []
  | 0, _ => ⟨hm, fun v => by simp⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := dedup_fold g bMain hi m hm n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlt := home_carry_lt g hi (show n < g.d by omega)
    refine ⟨by rw [dedStep, List.length_set, h1], fun v => ?_⟩
    rw [dedStep]
    by_cases hv : v = i + n * g.U
    · subst hv
      rw [getD_set_self _ _ _ _ (by rw [h1]; exact hlt), h2, home_carry_mod g hi,
        home_carry_div g hi]
      simp
    · rw [D6.getD_set_ne _ _ _ (Ne.symm hv), h2]
      have : (v % g.U = i ∧ v / g.U < n + 1) ↔ (v % g.U = i ∧ v / g.U < n) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨ha, ?_⟩
          by_contra hc
          exact hv (carry_eq g ha (by omega))
        · rintro ⟨ha, hb⟩; exact ⟨ha, by omega⟩
      by_cases hc : v % g.U = i ∧ v / g.U < n
      · rw [ite_eq_left hc, ite_eq_left (this.2 hc)]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (this.1 h))]

/-! ### One way -/

theorem srcW_home (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) {i q : Nat}
    (hB : ∀ x ∈ (bMain.getD i []).recs, w x.key % g.U = i) :
    ∀ x ∈ srcW g w bMain i q, sHome g w x = i + q * g.U := by
  intro x hx
  rw [srcW, List.mem_filter] at hx
  rw [sHome_carry g w x (hB x hx.1)]
  have : g.wayOf (w x.key) = q := by simpa using hx.2
  rw [this]

theorem gparts_upd (g : SepGeom) (w : Model.LogicalKey → Nat) (st : SFin) (E : List Rec) (v : Nat) (a : List Rec)
    (t : List (STest × Nat)) : gparts g w { st with ins := a, trace := t } E v = gparts g w st E v :=
  rfl

/-- The way-fold invariant of bucket `i` after `n` ways. -/
structure WInv (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat) (st : SFin)
    (acc : SFin × List Rec) (n : Nat) : Prop where
  len : acc.1.main.length = g.N
  llen : acc.1.leaves.length = g.ranges
  lrange : ∀ R, ∀ x ∈ acc.1.leaves.getD R [], sRange g w x = R
  blen : acc.1.bcopy.length = st.bcopy.length
  ins : acc.1.ins = if n = g.d then st.ins ++ acc.2 else st.ins
  parts : ∀ v < g.N, gparts g w acc.1 (st.ins ++ acc.2) v =
    if v % g.U = i ∧ v / g.U < n then
      gStep (clrOf bMain i) (srcW g w bMain i (v / g.U)) (gparts g w st st.ins v)
    else if v % g.U = i then gClr (clrOf bMain i) (gparts g w st st.ins v)
    else gparts g w st st.ins v

theorem wayFn_inv {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {bMain : List Bucket} {i : Nat}
    (hi : i < g.U) (hB : ∀ x ∈ (bMain.getD i []).recs, w x.key % g.U = i) {st : SFin}
    {acc : SFin × List Rec} {n : Nat} (hn : n < g.d) (h : WInv g w bMain i st acc n) :
    WInv g w bMain i st (wayFn g w bMain i acc n) (n + 1) := by
  have hd2 := hg.2.1
  set ci := i + n * g.U with hci
  have hciN : ci < g.N := home_carry_lt g hi hn
  set f := fill (acc.1.main.getD ci []) (srcW g w bMain i n) with hf
  set st' : SFin := { acc.1 with main := acc.1.main.set ci f.1 } with hst'
  set st'' : SFin := (if n + 1 = g.d then
      ({ st' with ins := st'.ins ++ (acc.2 ++ f.2), trace := st'.trace ++ [(STest.insertion, (st'.ins ++ (acc.2 ++ f.2)).length)] } : SFin)
    else st') with hst''
  have hW : wayFn g w bMain i acc n = (sOfferB g w ci (sOfferA g w ci st''), acc.2 ++ f.2) := rfl
  have e_main : st''.main = st'.main := by rw [hst'']; split <;> rfl
  have e_leaves : st''.leaves = acc.1.leaves := by rw [hst'']; split <;> rfl
  have e_bcopy : st''.bcopy = acc.1.bcopy := by rw [hst'']; split <;> rfl
  have e_parts : ∀ E v, gparts g w st'' E v = gparts g w st' E v := by
    intro E v; rw [hst'']; split
    · exact gparts_upd ..
    · rfl
  have hlen'' : st''.main.length = g.N := by rw [e_main, hst', List.length_set, h.len]
  have hfh : ∀ x ∈ f.2, sHome g w x = ci := by
    intro x hx
    rw [hf, fill_snd] at hx
    exact srcW_home g w bMain hB x (List.mem_of_mem_drop hx)
  -- the parts after the insertion
  have p_self : gparts g w st' (st.ins ++ acc.2 ++ f.2) ci =
      gFill (srcW g w bMain i n) (gparts g w acc.1 (st.ins ++ acc.2) ci) := by
    simp only [gparts, gFill, hst', hfil_append, hfil_self g w ci f.2 hfh]
    rw [getD_set_self _ _ _ _ (by rw [h.len]; exact hciN)]
  have p_ne : ∀ v, v ≠ ci → gparts g w st' (st.ins ++ acc.2 ++ f.2) v =
      gparts g w acc.1 (st.ins ++ acc.2) v := by
    intro v hv
    simp only [gparts, hst', hfil_append,
      hfil_nil_of g w v f.2 (fun x hx => by rw [hfh x hx]; exact Ne.symm hv), List.append_nil]
    rw [D6.getD_set_ne _ _ _ (Ne.symm hv)]
  have hA_len : (sOfferA g w ci st'').main.length = g.N := by
    rw [sOfferA_main_length, hlen'']
  have hR : ci / 2 ^ g.I < st''.leaves.length := by
    rw [e_leaves, h.llen]; exact range_lt g hg hciN
  have hOB := sOfferB_inv g w ci (sOfferA g w ci st'') (by rw [hA_len]; exact hciN)
  rw [hW]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hOB.mlen, hA_len]
  · rw [hOB.leaves, sOfferA_leaves_length, e_leaves, h.llen]
  · rw [hOB.leaves]
    apply sOfferA_lrange
    rw [e_leaves]; exact h.lrange
  · rw [hOB.blen, sOfferA_bcopy, e_bcopy, h.blen]
  · rw [hOB.ins, sOfferA_ins]
    have hins := h.ins
    rw [ite_eq_right (show ¬ n = g.d by omega)] at hins
    rw [hst'']
    by_cases hd : n + 1 = g.d
    · rw [ite_eq_left hd, ite_eq_left hd]
      show acc.1.ins ++ (acc.2 ++ f.2) = st.ins ++ (acc.2 ++ f.2)
      rw [hins]
    · rw [ite_eq_right hd, ite_eq_right hd]
      exact hins
  · intro v hv
    simp only
    rw [← List.append_assoc]
    by_cases hvc : v = ci
    · subst hvc
      rw [sOfferB_parts_self _ _ _ _ _ (by rw [hA_len]; exact hciN),
        sOfferA_parts_self _ _ _ _ _ (by rw [hlen'']; exact hciN) hR, e_parts, p_self,
        h.parts _ hciN, home_carry_mod g hi, home_carry_div g hi]
      simp only [Nat.lt_irrefl, and_false, ite_false, true_and, ite_true, Nat.lt_succ_self]
      rw [gStep_eq]
    · rw [sOfferB_parts_ne _ _ _ _ _ (by rw [hA_len]; exact hciN) hvc,
        sOfferA_parts_ne _ _ _ _ _ hvc, e_parts, p_ne v hvc, h.parts v hv]
      have : (v % g.U = i ∧ v / g.U < n + 1) ↔ (v % g.U = i ∧ v / g.U < n) := by
        constructor
        · rintro ⟨ha, hb⟩
          refine ⟨ha, ?_⟩
          by_contra hc
          exact hvc (carry_eq g ha (by omega))
        · rintro ⟨ha, hb⟩; exact ⟨ha, by omega⟩
      by_cases hc : v % g.U = i ∧ v / g.U < n
      · rw [ite_eq_left hc, ite_eq_left (this.2 hc)]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc (this.1 h))]

theorem wayFold_inv {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {bMain : List Bucket} {i : Nat}
    (hi : i < g.U) (hB : ∀ x ∈ (bMain.getD i []).recs, w x.key % g.U = i) {st : SFin}
    (hlen : st.main.length = g.N) (hll : st.leaves.length = g.ranges)
    (hlr : ∀ R, ∀ x ∈ st.leaves.getD R [], sRange g w x = R) : ∀ n ≤ g.d,
    WInv g w bMain i st ((List.range n).foldl (wayFn g w bMain i)
      ({ st with main := (List.range g.d).foldl (dedStep g bMain i) st.main }, [])) n
  | 0, _ => by
    have hd2 := hg.2.1
    obtain ⟨h1, h2⟩ := dedup_fold g bMain hi st.main hlen g.d (Nat.le_refl _)
    refine ⟨h1, hll, hlr, rfl, by rw [ite_eq_right (show ¬ (0 = g.d) by omega)]; rfl, fun v hv => ?_⟩
    simp only [List.range_zero, List.foldl_nil, List.append_nil, Nat.not_lt_zero, and_false,
      ite_false]
    have hvd := div_U_lt g hv
    by_cases hvi : v % g.U = i
    · rw [ite_eq_left hvi]
      simp only [gparts, gClr, h2 v, hvi, hvd, and_self, ite_true]
    · rw [ite_eq_right hvi]
      simp only [gparts, h2 v, hvi, false_and, ite_false]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact wayFn_inv hg hi hB (by omega) (wayFold_inv hg hi hB hlen hll hlr n (by omega))

/-! ### One B bucket -/

/-- The finish invariant after the first `n` B buckets. -/
structure GFInv (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (st0 st : SFin) (n : Nat) :
    Prop where
  len : st.main.length = g.N
  llen : st.leaves.length = g.ranges
  lrange : ∀ R, ∀ x ∈ st.leaves.getD R [], sRange g w x = R
  blen : st.bcopy.length = st0.bcopy.length
  parts : ∀ v < g.N, gparts g w st st.ins v =
    if v % g.U < n then
      gStep (clrOf bMain (v % g.U)) (srcW g w bMain (v % g.U) (v / g.U)) (gparts g w st0 st0.ins v)
    else gparts g w st0 st0.ins v

theorem GFInv.step {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {bMain : List Bucket}
    {st0 st : SFin} {n : Nat} (h : GFInv g w bMain st0 st n) (hn : n < g.U)
    (hB : ∀ x ∈ (bMain.getD n []).recs, w x.key % g.U = n) :
    GFInv g w bMain st0 (sInsertBucket g w bMain n st) (n + 1) := by
  have hW := wayFold_inv hg hn hB h.len h.llen h.lrange g.d (Nat.le_refl _)
  rw [sInsertBucket_eq]
  have hins := hW.ins
  rw [ite_eq_left rfl] at hins
  refine ⟨hW.len, hW.llen, hW.lrange, by rw [hW.blen, h.blen], fun v hv => ?_⟩
  have hp := hW.parts v hv
  rw [← hins] at hp
  rw [hp]
  have hvd := div_U_lt g hv
  by_cases hvn : v % g.U = n
  · rw [ite_eq_left ⟨hvn, hvd⟩, h.parts v hv, ite_eq_right (by omega), ite_eq_left (by omega), hvn]
  · rw [ite_eq_right (fun h => hvn h.1), ite_eq_right hvn, h.parts v hv]
    by_cases hlt : v % g.U < n
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The initial finish state. -/
def fin0 (inp : SInputs) (routed : List Bucket) (leaves : List (List Rec)) : SFin :=
  { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }

theorem sFinish_inv {g : SepGeom} (hg : g.Valid) (w : Model.LogicalKey → Nat) (inp : SInputs)
    (routed : List Bucket) (leaves : List (List Rec)) (hlen : routed.length = g.N)
    (hll : leaves.length = g.ranges) (hlr : ∀ R, ∀ x ∈ leaves.getD R [], sRange g w x = R)
    (hB : ∀ i < g.U, ∀ x ∈ (inp.bMain.getD i []).recs, w x.key % g.U = i) :
    GFInv g w inp.bMain (fin0 inp routed leaves) (sFinish g w inp routed leaves) g.U := by
  have key : ∀ n ≤ g.U, GFInv g w inp.bMain (fin0 inp routed leaves)
      ((List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st)
        (fin0 inp routed leaves)) n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨hlen, hll, hlr, rfl, fun v _ => by simp⟩
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (ih (by omega)).step hg (by omega) (hB n (by omega))
  exact key g.U (Nat.le_refl _)

end RebuildBound.S12
