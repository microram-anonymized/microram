import RebuildBound.Proofs.S4b.Finish

/-!
# S4b, the insertion of one B bucket into its `d` destinations

The destinations of B bucket `i` are the homes `i + q U`, `q < d`. Their
dedup runs first; then the ways are inserted in order, each followed by its
offers. `dn n m v` says that home `v` is done: bucket `v % U < n`, or bucket
`n` and way `v / U < m`.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b (nodup_of_subperm getD_set_self getD_set_of_ne getD_sublist_flatten
  mem_flatten_getD flatten_set_sublist fill_snd fill_of_full fill_recs_perm keys_eq mem_keys
  free_zero_of_full fill_placed_eq mem_getD_set_self' mem_getD_set' length_filter_split
  recs_sublist_flatMap not_mem_keys_clear)

theorem N_eq_d (g : SepGeom) : g.N = g.d * g.U := by
  unfold SepGeom.N SepGeom.d SepGeom.U SepGeom.k
  rw [Nat.pow_add]; ring

theorem U_pos (g : SepGeom) : 0 < g.U := Nat.two_pow_pos _

theorem homeOf_eq (g : SepGeom) (t : Nat) : g.homeOf t = t % g.U + g.U * g.wayOf t := by
  unfold SepGeom.homeOf SepGeom.wayOf SepGeom.U SepGeom.cls SepGeom.k
  rw [Nat.pow_add, Nat.mod_mul]
  ring

theorem sHome_eq_of_way (g : SepGeom) (w : Model.LogicalKey → Nat) (x : Rec) {n m : Nat}
    (h1 : w x.key % g.U = n) (h2 : g.wayOf (w x.key) = m) : sHome g w x = n + m * g.U := by
  unfold sHome
  rw [homeOf_eq, h1, h2, Nat.mul_comm]

/-- Home `v` is done: bucket `v % U < n`, or bucket `n` and way `v / U < m`. -/
def dn (g : SepGeom) (n m v : Nat) : Prop := v % g.U < n ∨ (v % g.U = n ∧ v / g.U < m)

section
variable {g : SepGeom} {w : Model.LogicalKey → Nat} {inp : SInputs} {pool : List Rec}

theorem ci_mod {n m : Nat} (hn : n < g.U) : (n + m * g.U) % g.U = n := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]

theorem ci_div {n m : Nat} (hn : n < g.U) : (n + m * g.U) / g.U = m := by
  rw [Nat.add_mul_div_right _ _ (U_pos g), Nat.div_eq_of_lt hn, Nat.zero_add]

theorem ci_lt {n m : Nat} (hn : n < g.U) (hm : m < g.d) : n + m * g.U < g.N := by
  rw [N_eq_d]
  have : (m + 1) * g.U ≤ g.d * g.U := Nat.mul_le_mul_right _ hm
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem dn_succ {n m v : Nat} (hn : n < g.U) :
    dn g n (m + 1) v ↔ dn g n m v ∨ v = n + m * g.U := by
  unfold dn
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hm : v / g.U < m
      · exact Or.inl (Or.inr ⟨h1, hm⟩)
      · right
        have h3 : v / g.U = m := by omega
        have := Nat.mod_add_div v g.U
        rw [h1, h3, Nat.mul_comm] at this
        omega
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by omega⟩
    · subst h
      exact Or.inr ⟨ci_mod hn, by rw [ci_div hn]; omega⟩

theorem dn_zero {n v : Nat} : dn g n 0 v ↔ v % g.U < n := by
  unfold dn; constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h (Nat.not_lt_zero _)
  · exact Or.inl

theorem nodup_keys_append_sHome {L₁ L₂ : List Rec}
    (h₁ : (L₁.map Rec.key).Nodup) (h₂ : (L₂.map Rec.key).Nodup)
    (h : ∀ x ∈ L₁, ∀ y ∈ L₂, sHome g w x ≠ sHome g w y) :
    ((L₁ ++ L₂).map Rec.key).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨h₁, h₂, ?_⟩
  intro a ha b hb e
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  exact h x hx y hy (by simp [sHome, e])

theorem Bi_sub (cx : Ctx g w inp pool) {i : Nat} (hi : i < g.U) :
    List.Sublist (inp.bMain.getD i []).recs (inp.bMain.flatMap Bucket.recs) := by
  have : inp.bMain.getD i [] ∈ inp.bMain := by
    rw [List.getD_eq_getElem _ _ (by rw [cx.bLen]; exact hi)]; exact List.getElem_mem _
  exact recs_sublist_flatMap this

/-- The insertion fill of one way into home `ci`. -/
theorem ins_fill (cx : Ctx g w inp pool) {n ci : Nat} (hn : n < g.U) {B : Bucket}
    (hok : HomeOK g w inp ci B) {src : List Rec}
    (hsub : List.Sublist src (inp.bMain.getD n []).recs) (hh : ∀ r ∈ src, sHome g w r = ci)
    (hcl : ∀ r ∈ src, r.key ∉ B.keys) :
    HomeOK g w inp ci (fill B src).1 ∧
    (∀ x ∈ (fill B src).2, Blocks g x.key (fill B src).1) ∧
    List.Sublist (fill B src).2 src := by
  have hBi := Bi_sub cx hn
  have hnd : (src.map Rec.key).Nodup := cx.bMnd.sublist ((hsub.trans hBi).map _)
  have hsnd : List.Sublist (fill B src).2 src := by
    rw [fill_snd]; exact List.drop_sublist _ _
  refine ⟨?_, ?_, hsnd⟩
  · refine homeOK_fill hok src ?_ hnd hcl
    intro r hr
    exact ⟨hh r hr, mem_WK_of_b (List.mem_append_left _ ((hsub.trans hBi).subset hr))⟩
  · intro x hx
    have hxs := hsnd.subset hx
    refine blocks_fill hok.len hxs (hcl x hxs) ?_
    rw [fill_snd] at hx
    intro hk
    have hnd2 := hnd
    rw [← List.take_append_drop (min src.length (B.countP (·.isNone))) src,
      List.map_append, List.nodup_append] at hnd2
    exact hnd2.2.2 _ hk _ (List.mem_map_of_mem hx) rfl

theorem GInv.set_ins {Pa : Nat → Prop} {Pb : Nat → Nat → Prop} {Pi : Nat → Prop} {I : List Rec}
    {st : SFin} (h : GInv g w inp pool Pa Pb Pi I st) (ins' : List Rec) (tr' : List (STest × Nat))
    (htr : ∀ e ∈ tr', e.1 = STest.insertion ∧ e.2 ≤ sHomeExcess g w inp) :
    GInv g w inp pool Pa Pb Pi I { st with ins := ins', trace := tr' } where
  len := h.len
  ok := h.ok
  lv := h.lv
  lvnd := h.lvnd
  bc := h.bc
  aD := h.aD
  bD := h.bD
  ins := h.ins
  insnd := h.insnd
  tr := htr

theorem sOfferA_ins' (ci : Nat) (st : SFin) : (sOfferA g w ci st).ins = st.ins := rfl

theorem sOfferB_getD (ci v : Nat) (st : SFin) (h : v ≠ ci) :
    (sOfferB g w ci st).main.getD v [] = st.main.getD v [] := by
  unfold sOfferB
  have key : ∀ m, ((List.range m).foldl (sOfferPage g w ci) st).main.getD v [] =
      st.main.getD v [] := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        sOfferPage_getD ci v m _ h, ih]
  exact key _

theorem sOfferB_ins (ci : Nat) (st : SFin) : (sOfferB g w ci st).ins = st.ins := by
  unfold sOfferB
  have key : ∀ m, ((List.range m).foldl (sOfferPage g w ci) st).ins = st.ins := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ih
  exact key _

end

/-! ### One way of B bucket `i` -/

/-- The body of the per-way loop of `sInsertBucket`. -/
def wayBody (g : SepGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (i : Nat) (acc : SFin × List Rec)
    (q : Nat) : SFin × List Rec :=
  let ci := i + q * g.U
  let f := fill (acc.1.main.getD ci []) (Bi.recs.filter fun x => g.wayOf (w x.key) == q)
  let sheds := acc.2 ++ f.2
  let st := { acc.1 with main := acc.1.main.set ci f.1 }
  let st := if q + 1 = g.d then
      let ins := st.ins ++ sheds
      { st with ins := ins, trace := st.trace ++ [(.insertion, ins.length)] }
    else st
  (sOfferB g w ci (sOfferA g w ci st), sheds)

/-- The dedup of B bucket `i`'s keys from all `d` destinations. -/
def dedupSt (g : SepGeom) (bMain : List Bucket) (i : Nat) (st : SFin) : SFin :=
  { st with
    main := (List.range g.d).foldl
      (fun m q => m.set (i + q * g.U) ((m.getD (i + q * g.U) []).clear fun key =>
        (bMain.getD i []).keys.contains key)) st.main }

theorem sInsertBucket_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (bMain : List Bucket) (i : Nat)
    (st : SFin) :
    sInsertBucket g w bMain i st =
      ((List.range g.d).foldl (wayBody g w (bMain.getD i []) i) (dedupSt g bMain i st, [])).1 :=
  rfl

section
variable {g : SepGeom} {w : Model.LogicalKey → Nat} {inp : SInputs} {pool : List Rec}

theorem dedup_getD {n : Nat} (hn : n < g.U) (bMain : List Bucket) (st : SFin)
    (hlen : st.main.length = g.N) :
    (∀ v, (dedupSt g bMain n st).main.getD v [] =
      if v < g.N ∧ v % g.U = n then
        (st.main.getD v []).clear (fun key => (bMain.getD n []).keys.contains key)
      else st.main.getD v []) ∧ (dedupSt g bMain n st).main.length = g.N := by
  have key : ∀ t, t ≤ g.d →
      (((List.range t).foldl
        (fun m q => m.set (n + q * g.U) ((m.getD (n + q * g.U) []).clear fun key =>
          (bMain.getD n []).keys.contains key)) st.main).length = g.N) ∧
      ∀ v, ((List.range t).foldl
        (fun m q => m.set (n + q * g.U) ((m.getD (n + q * g.U) []).clear fun key =>
          (bMain.getD n []).keys.contains key)) st.main).getD v [] =
        if (∃ q < t, v = n + q * g.U) then
          (st.main.getD v []).clear (fun key => (bMain.getD n []).keys.contains key)
        else st.main.getD v [] := by
    intro t
    induction t with
    | zero => intro _; exact ⟨hlen, fun v => by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨ihl, ihg⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hq : n + t * g.U < g.N := ci_lt hn (by omega)
      refine ⟨by rw [List.length_set, ihl], ?_⟩
      intro v
      by_cases e : v = n + t * g.U
      · subst e
        rw [getD_set_self _ (by rw [ihl]; exact hq), ihg]
        have hno : ¬ ∃ q < t, n + t * g.U = n + q * g.U := by
          rintro ⟨q, hqt, e⟩
          have := Nat.eq_of_mul_eq_mul_right (U_pos g) (Nat.add_left_cancel e)
          omega
        have hyes : ∃ q < t + 1, n + t * g.U = n + q * g.U := ⟨t, by omega, rfl⟩
        rw [if_neg hno, if_pos hyes]
      · rw [getD_set_of_ne _ (Ne.symm e), ihg]
        have : (∃ q < t + 1, v = n + q * g.U) ↔ ∃ q < t, v = n + q * g.U := by
          constructor
          · rintro ⟨q, hqt, h⟩
            have : q ≠ t := fun h' => e (by rw [h, h'])
            exact ⟨q, by omega, h⟩
          · rintro ⟨q, hqt, h⟩
            exact ⟨q, by omega, h⟩
        simp only [this]
  obtain ⟨h1, h2⟩ := key g.d le_rfl
  refine ⟨fun v => ?_, h1⟩
  show ((List.range g.d).foldl _ st.main).getD v [] = _
  rw [h2]
  have : (∃ q < g.d, v = n + q * g.U) ↔ (v < g.N ∧ v % g.U = n) := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨ci_lt hn hq, ci_mod hn⟩
    · rintro ⟨h1, h2⟩
      refine ⟨v / g.U, ?_, ?_⟩
      · rw [N_eq_d] at h1
        exact (Nat.div_lt_iff_lt_mul (U_pos g)).2 h1
      · have := Nat.mod_add_div v g.U
        rw [h2, Nat.mul_comm] at this
        omega
  simp only [this]

theorem ginv_dedup (cx : Ctx g w inp pool) {n : Nat} (hn : n < g.U) {st : SFin}
    {Pa : Nat → Prop} {Pb : Nat → Nat → Prop} {Pi : Nat → Prop} {I : List Rec}
    (h : GInv g w inp pool Pa Pb Pi I st)
    (hPa : ∀ v < g.N, Pa v → v % g.U ≠ n) (hPb : ∀ p, ∀ v < g.N, Pb p v → v % g.U ≠ n)
    (hPi : ∀ v < g.N, Pi v → v % g.U ≠ n) :
    GInv g w inp pool Pa Pb Pi I (dedupSt g inp.bMain n st) := by
  obtain ⟨hd, hl⟩ := dedup_getD hn inp.bMain st h.len
  have hsame : ∀ v < g.N, v % g.U ≠ n →
      (dedupSt g inp.bMain n st).main.getD v [] = st.main.getD v [] := by
    intro v hv hne
    rw [hd, if_neg (fun hh => hne hh.2)]
  refine ⟨hl, ?_, h.lv, h.lvnd, h.bc, ?_, ?_, ?_, h.insnd, h.tr⟩
  · intro v hv
    by_cases hne : v % g.U = n
    · rw [hd, if_pos ⟨hv, hne⟩]
      exact homeOK_clear (h.ok v hv) _
    · rw [hsame v hv hne]; exact h.ok v hv
  · intro R r hr hp
    rw [hsame _ (sHome_lt cx.valid w r) (hPa _ (sHome_lt cx.valid w r) hp)]
    exact h.aD R r hr hp
  · intro p r hr hp
    rw [hsame _ (sHome_lt cx.valid w r) (hPb p _ (sHome_lt cx.valid w r) hp)]
    exact h.bD p r hr hp
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := h.ins x hx
    exact ⟨h1, h2, by
      rw [hsame _ (sHome_lt cx.valid w x) (hPi _ (sHome_lt cx.valid w x) h2)]; exact h3⟩

/-- One way of B bucket `n`: the invariant moves from `m` ways done to `m + 1`. -/
theorem way_step (cx : Ctx g w inp pool) {n m : Nat} (hn : n < g.U) (hm : m < g.d)
    {acc : SFin × List Rec} {I0 : List Rec}
    (h : GInv g w inp pool (dn g n m) (fun _ => dn g n m) (dn g n m) (I0 ++ acc.2) acc.1)
    (hins : acc.1.ins = I0)
    (hdd : ∀ q, m ≤ q → q < g.d → ∀ r ∈ (inp.bMain.getD n []).recs,
      r.key ∉ (acc.1.main.getD (n + q * g.U) []).keys) :
    GInv g w inp pool (dn g n (m + 1)) (fun _ => dn g n (m + 1)) (dn g n (m + 1))
      (I0 ++ (wayBody g w (inp.bMain.getD n []) n acc m).2)
      (wayBody g w (inp.bMain.getD n []) n acc m).1 ∧
    (wayBody g w (inp.bMain.getD n []) n acc m).1.ins =
      (if m + 1 = g.d then I0 ++ (wayBody g w (inp.bMain.getD n []) n acc m).2 else I0) ∧
    (∀ q, m + 1 ≤ q → q < g.d → ∀ r ∈ (inp.bMain.getD n []).recs,
      r.key ∉ ((wayBody g w (inp.bMain.getD n []) n acc m).1.main.getD (n + q * g.U) []).keys) := by
  set Bi := inp.bMain.getD n [] with hBi
  set ci := n + m * g.U with hci
  have hciN : ci < g.N := ci_lt hn hm
  have hcim : ci % g.U = n := ci_mod hn
  have hcid : ci / g.U = m := ci_div hn
  set src := Bi.recs.filter (fun x => g.wayOf (w x.key) == m) with hsrc
  set f := fill (acc.1.main.getD ci []) src with hf
  set s1 : SFin := { acc.1 with main := acc.1.main.set ci f.1 } with hs1
  have hndci : ¬ dn g n m ci := by
    unfold dn; rw [hcim, hcid]; omega
  have hne : ∀ v, dn g n m v → v ≠ ci := fun v hv e => hndci (e ▸ hv)
  have hsrcsub : List.Sublist src Bi.recs := List.filter_sublist
  have hsrch : ∀ r ∈ src, sHome g w r = ci := by
    intro r hr
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hr
    exact sHome_eq_of_way g w r (cx.bHome n hn r h1) (by simpa using h2)
  have hcl : ∀ r ∈ src, r.key ∉ (acc.1.main.getD ci []).keys :=
    fun r hr => hdd m le_rfl hm r (hsrcsub.subset hr)
  obtain ⟨Fok, Fbl, Fsub⟩ := ins_fill cx hn (h.ok ci hciN) hsrcsub hsrch hcl
  have e1c : s1.main.getD ci [] = f.1 :=
    getD_set_self _ (by rw [h.len]; exact hciN) _ _
  have e1o : ∀ v, v ≠ ci → s1.main.getD v [] = acc.1.main.getD v [] :=
    fun v hv => getD_set_of_ne _ (Ne.symm hv) _ _
  have G1 : GInv g w inp pool (dn g n m) (fun _ => dn g n m) (fun v => dn g n m v ∨ v = ci)
      ((I0 ++ acc.2) ++ f.2) s1 := by
    refine ⟨?_, ?_, h.lv, h.lvnd, h.bc, ?_, ?_, ?_, ?_, h.tr⟩
    · show (acc.1.main.set ci f.1).length = g.N
      simp [h.len]
    · intro v hv
      by_cases e : v = ci
      · subst e; rw [e1c]; exact Fok
      · rw [e1o v e]; exact h.ok v hv
    · intro R r hr hp
      rw [e1o _ (hne _ hp)]; exact h.aD R r hr hp
    · intro p r hr hp
      rw [e1o _ (hne _ hp)]; exact h.bD p r hr hp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨h1, h2, h3⟩ := h.ins x hx
        exact ⟨h1, Or.inl h2, by rw [e1o _ (hne _ h2)]; exact h3⟩
      · have hs := Fsub.subset hx
        have hh := hsrch x hs
        refine ⟨(Bi_sub cx hn).subset (List.mem_filter.1 hs).1, Or.inr hh, ?_⟩
        rw [hh, e1c]; exact Fbl x hx
    · refine nodup_keys_append_sHome (g := g) (w := w) h.insnd
        (cx.bMnd.sublist (((Fsub.trans hsrcsub).trans (Bi_sub cx hn)).map _)) ?_
      intro x hx y hy e
      exact hne _ (h.ins x hx).2.1 (e.trans (hsrch y (Fsub.subset hy)))
  set s2 : SFin := if m + 1 = g.d then
      { s1 with ins := s1.ins ++ (acc.2 ++ f.2),
                trace := s1.trace ++ [(.insertion, (s1.ins ++ (acc.2 ++ f.2)).length)] }
    else s1 with hs2
  have hwb : wayBody g w Bi n acc m = (sOfferB g w ci (sOfferA g w ci s2), acc.2 ++ f.2) := rfl
  have G2 : GInv g w inp pool (dn g n m) (fun _ => dn g n m) (fun v => dn g n m v ∨ v = ci)
      ((I0 ++ acc.2) ++ f.2) s2 := by
    by_cases hd : m + 1 = g.d
    · rw [hs2, if_pos hd]
      apply G1.set_ins
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact G1.tr e he
      · rw [List.mem_singleton] at he
        subst he
        refine ⟨rfl, ?_⟩
        show (s1.ins ++ (acc.2 ++ f.2)).length ≤ _
        have h1 : s1.ins = I0 := hins
        rw [h1, ← List.append_assoc]
        exact count_main cx.valid s1.main G1.ok _ G1.insnd
          (fun x hx => ⟨mem_WK_of_b (List.mem_append_left _ (G1.ins x hx).1), (G1.ins x hx).2.2⟩)
    · rw [hs2, if_neg hd]; exact G1
  have G3 := ginv_offerB cx hciN (ginv_offerA cx hciN G2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hwb]
    show GInv g w inp pool _ _ _ (I0 ++ (acc.2 ++ f.2)) _
    rw [← List.append_assoc]
    refine G3.mono cx.valid ?_ ?_ ?_
    · intro v _ hv; exact (dn_succ hn).1 hv
    · intro p r _ hv; exact (dn_succ hn).1 hv
    · intro v _ hv; exact (dn_succ hn).2 hv
  · rw [hwb]
    show (sOfferB g w ci (sOfferA g w ci s2)).ins = if m + 1 = g.d then I0 ++ (acc.2 ++ f.2) else I0
    rw [sOfferB_ins, sOfferA_ins']
    by_cases hd : m + 1 = g.d
    · rw [hs2, if_pos hd, if_pos hd]
      show s1.ins ++ (acc.2 ++ f.2) = _
      rw [show s1.ins = I0 from hins]
    · rw [hs2, if_neg hd, if_neg hd]; exact hins
  · intro q hq hqd r hr
    rw [hwb]
    have hneq : n + q * g.U ≠ ci := by
      intro e
      have := Nat.eq_of_mul_eq_mul_right (U_pos g) (Nat.add_left_cancel e)
      omega
    have hm2 : s2.main = s1.main := by
      rw [hs2]; split_ifs <;> rfl
    show r.key ∉ ((sOfferB g w ci (sOfferA g w ci s2)).main.getD (n + q * g.U) []).keys
    rw [sOfferB_getD _ _ _ hneq, sOfferA_getD _ _ _ hneq, hm2, e1o _ hneq]
    exact hdd q (by omega) hqd r hr

end

end RebuildBound.S4b
