import RebuildBound.Proofs.TG2.Blind

/-!
# TG2 helpers: the reference coarse count against `rRangeCount0`

For words `w` whose low `k - 1` bits on A's keys are `h` and whose class bit
(bit `k - 1`) is `c`, the reference coarse count of leaf `v = a 2^(k - 1 - I) + u`
is `rRangeCount0` of the `RRoute` `tRoute`, with class `a`, the range
`R = u 2^I` and the early set `tearlyK` (the keys of the truncated early list):
the early list and the late binary sheds are counted exactly, and the last
level's sheds are not in the pool. The early set is disjoint from main after
stage `I`, has at most `P` keys and is fixed by the bits below `I` (`TP5_route`).
-/

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

/-! ### Arithmetic of ranges -/

theorem trange_iff {b I : ℕ} (hIb : I ≤ b) (t : ℕ) {a u : ℕ} (hu : u < 2 ^ (b - I)) :
    t % 2 ^ (b + 1) / 2 ^ I = a * 2 ^ (b - I) + u ↔
      t / 2 ^ b % 2 = a ∧ t % 2 ^ b / 2 ^ I = u := by
  have hk : 2 ^ b = 2 ^ I * 2 ^ (b - I) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hIb]
  have hq : t % 2 ^ b / 2 ^ I < 2 ^ (b - I) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hk]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdiv : t % 2 ^ (b + 1) / 2 ^ I = t % 2 ^ b / 2 ^ I + 2 ^ (b - I) * (t / 2 ^ b % 2) := by
    rw [Nat.mod_pow_succ, hk, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  rw [hdiv, div_mod_unique hq hu]

/-- The range predicate of `rRangeCount0` on A's keys is the model's leaf. -/
theorem tpred_iff (g : TPGeom) (hk : 1 ≤ g.k) (hIb : g.I ≤ g.k - 1) {KA : Finset Model.LogicalKey} {w : Model.LogicalKey → ℕ}
    {h : {x // x ∈ KA} → Bits (g.k - 1)} {c : {x // x ∈ KA} → Fin 2}
    (hw : ∀ x : {x // x ∈ KA}, natToBits (g.k - 1) (w x.val) = h x ∧
      w x.val / 2 ^ (g.k - 1) % 2 = (c x : ℕ))
    {a u : ℕ} (ha : a < 2) (hu : u < 2 ^ (g.k - 1 - g.I)) (r : Rec) (hx : r.key ∈ KA) :
    (InRange g.I (natToBits (g.k - 1) (u * 2 ^ g.I)) (h ⟨r.key, hx⟩) ∧
        c ⟨r.key, hx⟩ = ⟨a, ha⟩) ↔
      (tpRange g w r == a * 2 ^ (g.k - 1 - g.I) + u) = true := by
  obtain ⟨h1, h2⟩ := hw ⟨r.key, hx⟩
  simp only at h1 h2
  rw [beq_iff_eq, tpRange, tpHome, T_eq hk, trange_iff hIb _ hu, ← h1,
    inRange_natToBits hIb hu, h2, Fin.ext_iff]
  exact And.comm

/-! ### The reference route -/

theorem canon_filter_self (g : TPGeom) :
    g.canonicalOps.filter (fun o => o.1 < g.k - 1) = g.canonicalOps := by
  apply List.filter_eq_self.2
  intro o ho
  unfold TPGeom.canonicalOps at ho
  obtain ⟨j, hj, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 ho
  simpa using List.mem_range.1 hj

theorem tref_route (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → ℕ)
    (inp : TPInputs) :
    (tpReferenceWith rule g unsh w inp g.canonicalOps).route =
      tpRouteUpTo rule g unsh w inp.aMain (g.k - 1) := by
  simp only [tpReferenceWith, tpRouteUpTo, canon_filter_self]

/-! ### Facts about one old history -/

/-- The truncated early list of the words `wOf h`. -/
noncomputable def tearlyL (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    List Rec :=
  (aTier.filter (fun x => !flagged unsh x) ++
    ((tpRouteUpTo rule g unsh (wOf KA (g.k - 1) h) aMain (g.k - 1)).stash.take g.I).flatten).take P

/-- The early key set of the words `wOf h`. -/
noncomputable def tearlyK (rule : CapRule) (g : TPGeom) (unsh : Rec → Bool) (KA : Finset Model.LogicalKey)
    (aMain : List Bucket) (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    Finset {x // x ∈ KA} :=
  keysOf KA (tearlyL rule g unsh KA aMain aTier P h)

section Facts

variable {rule : CapRule} (hv : rule.Valid) {g : TPGeom} {unsh : Rec → Bool}
  {p : Model.LogicalKey → ℕ} {KA : Finset Model.LogicalKey} {aMain : List Bucket} {aTier : List Rec}
  (hC : TCtx g p KA aMain aTier)

include hv hC

theorem tstash_take_flatten (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) :
    ((tpRouteUpTo rule g unsh w aMain (g.k - 1)).stash.take lo).flatten =
      (List.range lo).flatMap (tShedsAt rule g unsh w aMain) := by
  have e1 := (troute_inv hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w) (g.k - 1)
    le_rfl).2.2
  unfold TStashShape at e1
  rw [e1, List.take_append_of_le_length (by simp; omega), ← List.map_take, List.take_range,
    min_eq_left hlo, List.flatMap_def]

theorem tstash_drop_flatten (w : Model.LogicalKey → ℕ) (lo : ℕ) :
    (((tpRouteUpTo rule g unsh w aMain (g.k - 1)).stash.take (g.k - 1)).drop lo).flatten =
      (List.range' lo (g.k - 1 - lo)).flatMap (tShedsAt rule g unsh w aMain) := by
  rw [troute_stash hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w),
    ← List.map_drop, List.range_eq_range', List.drop_range', List.flatMap_def]
  simp

theorem tlate_sub (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) :
    ((flat (tpRouteUpTo rule g unsh w aMain lo).main : List Rec) : Multiset Rec) =
      (flat (tpRouteUpTo rule g unsh w aMain (g.k - 1)).main : Multiset Rec) +
        ((List.range' lo (g.k - 1 - lo)).flatMap (tShedsAt rule g unsh w aMain) :
          Multiset Rec) := by
  have := tflat_range hv g unsh w p aMain (t_init_inv hC) (t_init_placed hC w) lo (g.k - 1 - lo)
    (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

/-- A's surviving main after `lo` stages, the early sheds and A's surviving tier are
distinct by key. -/
theorem tlo_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) :
    ((flat (tpRouteUpTo rule g unsh w aMain lo).main ++
      ((List.range lo).flatMap (tShedsAt rule g unsh w aMain) ++
        aTier.filter (fun x => !flagged unsh x))).map Rec.key).Nodup := by
  have hp : (flat (copyMain unsh aMain) ++ aTier.filter (fun x => !flagged unsh x)).Perm
      (flat (tpRouteUpTo rule g unsh w aMain lo).main ++
        ((List.range lo).flatMap (tShedsAt rule g unsh w aMain) ++
          aTier.filter (fun x => !flagged unsh x))) := by
    rw [← List.append_assoc]
    exact (perm_of_add (tmain_sub hv hC w hlo)).append_right _
  refine (hp.map Rec.key).nodup_iff.1 ?_
  exact List.Nodup.sublist ((flat_copyMain_sublist.append (List.filter_sublist)).map _) hC.nodup

theorem tlate_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) :
    ((flat (tpRouteUpTo rule g unsh w aMain (g.k - 1)).main ++
      (List.range' lo (g.k - 1 - lo)).flatMap (tShedsAt rule g unsh w aMain)).map
        Rec.key).Nodup :=
  nodup_of_add (tlate_sub hv hC w hlo) (tmain_nodup hv hC w hlo)

theorem tlate_mem (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) {r : Rec}
    (hr : r ∈ (List.range' lo (g.k - 1 - lo)).flatMap (tShedsAt rule g unsh w aMain)) :
    r ∈ flat aMain :=
  tmain_mem hv hC w hlo ((mem_of_add (tlate_sub hv hC w hlo)).2 (Or.inr hr))

theorem tearly_mem_main (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k - 1) {r : Rec}
    (hr : r ∈ (List.range lo).flatMap (tShedsAt rule g unsh w aMain)) : r ∈ flat aMain :=
  flat_copyMain_sub ((mem_of_add (tmain_sub hv hC w hlo)).2 (Or.inr hr))

theorem tearlyL_nodup (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) (hIb : g.I ≤ g.k - 1) :
    ((tearlyL rule g unsh KA aMain aTier P h).map Rec.key).Nodup := by
  have := tlo_nodup hv hC (unsh := unsh) (wOf KA (g.k - 1) h) hIb
  rw [List.map_append] at this
  have h2 := (List.nodup_append.1 this).2.1
  unfold tearlyL
  rw [tstash_take_flatten hv hC _ hIb]
  apply List.Nodup.sublist _ ((List.perm_append_comm.map Rec.key).nodup_iff.1 h2)
  rw [List.map_take]
  exact List.take_sublist _ _

theorem tearlyL_mem (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) (hIb : g.I ≤ g.k - 1) {r : Rec}
    (hr : r ∈ tearlyL rule g unsh KA aMain aTier P h) : r.key ∈ KA := by
  unfold tearlyL at hr
  rw [tstash_take_flatten hv hC _ hIb] at hr
  rcases List.mem_append.1 (List.mem_of_mem_take hr) with h1 | h1
  · exact tkey_mem_of_aTier hC (List.mem_filter.1 h1).1
  · exact tkey_mem_of_aMain hC (tearly_mem_main hv hC _ hIb h1)

theorem tearlyK_disjoint (P : ℕ) (hIb : g.I ≤ g.k - 1) (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    Disjoint (tearlyK rule g unsh KA aMain aTier P h)
      ((tRoute rule g unsh KA aMain).mainAt h g.I) := by
  rw [tRoute_mainAt, min_eq_left hIb]
  have hnd := tlo_nodup hv hC (unsh := unsh) (wOf KA (g.k - 1) h) hIb
  have hd := keysOf_disjoint (KA := KA) hnd
  refine (Disjoint.mono_left ?_ hd.symm)
  intro x hx
  unfold tearlyK tearlyL at hx
  rw [mem_keysOf, tstash_take_flatten hv hC _ hIb] at hx
  rw [mem_keysOf, List.map_append, List.mem_append]
  obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hx
  rcases List.mem_append.1 (List.mem_of_mem_take hr) with h1 | h1
  · right; exact List.mem_map.2 ⟨r, h1, hrx⟩
  · left; exact List.mem_map.2 ⟨r, h1, hrx⟩

omit hv hC in
theorem tearlyK_card (P : ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) :
    (tearlyK rule g unsh KA aMain aTier P h).card ≤ P :=
  (keysOf_card_le _).trans (List.length_take_le _ _)

set_option linter.unusedSectionVars false in
/-- **The only use of `TP5_route`**: the route through stage `n` reads only the bits below
`n` of A's main keys. (The lane facts of A's main, `hC.len` and `hC.lanes`, are at hand
here.) -/
theorem troute_congr (h5r : TP5_route_statement) (w w' : Model.LogicalKey → ℕ) {n : ℕ} (hn : n ≤ g.k - 1)
    (hkeys : ∀ r ∈ aMain.flatMap Bucket.recs, ∀ i < n,
      (w r.key).testBit i = (w' r.key).testBit i) :
    tpRouteUpTo rule g unsh w aMain n = tpRouteUpTo rule g unsh w' aMain n :=
  h5r rule g unsh w w' aMain n hv hn hC.len hC.lanes hkeys

/-- Blindness of the early set, from `TP5_route`: the route through stage `I` reads only
the bits below `I`. -/
theorem tearlyK_blind (h5r : TP5_route_statement) (P : ℕ) (hIb : g.I ≤ g.k - 1)
    (h h' : {x // x ∈ KA} → Bits (g.k - 1)) (hag : AgreeBelow g.I h h') :
    tearlyK rule g unsh KA aMain aTier P h = tearlyK rule g unsh KA aMain aTier P h' := by
  unfold tearlyK tearlyL
  have hkeys : ∀ r ∈ aMain.flatMap Bucket.recs, ∀ i < g.I,
      (wOf KA (g.k - 1) h r.key).testBit i = (wOf KA (g.k - 1) h' r.key).testBit i := by
    intro r hr i hi
    have hx := tkey_mem_of_aMain hC (r := r) hr
    have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨i, by omega⟩
    have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨i, by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    exact hag _ _ hi
  have hr := troute_congr hv hC (unsh := unsh) h5r (wOf KA (g.k - 1) h) (wOf KA (g.k - 1) h') hIb hkeys
  rw [troute_stash_take hv g unsh _ p aMain (t_init_inv hC) (t_init_placed hC _) hIb,
    troute_stash_take hv g unsh _ p aMain (t_init_inv hC) (t_init_placed hC _) hIb, hr]

/-- **The reference coarse count is `rRangeCount0` of the route.** -/
theorem trefCoarse_eq (hk : 1 ≤ g.k) (h5r : TP5_route_statement) (hIb : g.I ≤ g.k - 1)
    (w : Model.LogicalKey → ℕ) (h : {x // x ∈ KA} → Bits (g.k - 1)) (c : {x // x ∈ KA} → Fin 2)
    (hw : ∀ x : {x // x ∈ KA}, natToBits (g.k - 1) (w x.val) = h x ∧
      w x.val / 2 ^ (g.k - 1) % 2 = (c x : ℕ))
    {a u : ℕ} (ha : a < 2) (hu : u < 2 ^ (g.k - 1 - g.I)) (P : ℕ) :
    tpRefCoarse g unsh w (tpReferenceWith rule g unsh w ⟨aMain, aTier⟩ g.canonicalOps)
        ⟨aMain, aTier⟩ P (a * 2 ^ (g.k - 1 - g.I) + u) =
      rRangeCount0 (tRoute rule g unsh KA aMain) g.I
        (tearlyK rule g unsh KA aMain aTier P) (natToBits (g.k - 1) (u * 2 ^ g.I)) ⟨a, ha⟩ h c := by
  set w' := wOf KA (g.k - 1) h
  set v := a * 2 ^ (g.k - 1 - g.I) + u
  set R := natToBits (g.k - 1) (u * 2 ^ g.I)
  have hkeys : ∀ x ∈ aMain.flatMap Bucket.recs, ∀ i < g.k - 1,
      (w x.key).testBit i = (w' x.key).testBit i := by
    intro x hx i hi
    have hxK := tkey_mem_of_aMain hC (r := x) hx
    have e1 := congrFun (hw ⟨x.key, hxK⟩).1 ⟨i, hi⟩
    simp only [natToBits] at e1
    rw [e1]
    exact (testBit_wOf h ⟨x.key, hxK⟩ ⟨i, hi⟩).symm
  have hroute := troute_congr hv hC (unsh := unsh) h5r w w' le_rfl hkeys
  have hpr : ∀ (l : List Rec), (∀ r ∈ l, r.key ∈ KA) →
      ∀ Q : Finset {x // x ∈ KA}, (l.map Rec.key).Nodup → Q = keysOf KA l →
      l.countP (fun x => tpRange g w x == v) =
        (Q.filter (fun x => InRange g.I R (h x) ∧ c x = ⟨a, ha⟩)).card := by
    intro l hl Q hnd hQ
    rw [hQ]
    exact (card_filter_keysOf l hnd hl _ _
      (fun r hr => tpred_iff g hk hIb hw ha hu r (hl r hr))).symm
  unfold tpRefCoarse tpEarlyList tpLateSheds rRangeCount0
  rw [tref_route, hroute, List.countP_append]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact hpr _ (fun r hr => tearlyL_mem hv hC P h hIb hr) _
      (tearlyL_nodup hv hC P h hIb) rfl
  · rw [tstash_drop_flatten hv hC w']
    have hnd := tlate_nodup hv hC (unsh := unsh) w' hIb
    rw [List.map_append] at hnd
    refine hpr _ (fun r hr => tkey_mem_of_aMain hC (tlate_mem hv hC w' hIb hr)) _
      (List.nodup_append.1 hnd).2.1 ?_
    rw [tRoute_mainAt, tRoute_mainAt, min_eq_left hIb, min_self]
    exact keysOf_sdiff (tlate_sub hv hC w' hIb) (tlate_nodup hv hC w' hIb)

end Facts

end RebuildBound.TG2
