import RebuildBound.Proofs.SG2.Radix

/-!
# SG2 helpers: the reference coarse count against `rRangeCount`

For merge-family words `w` whose low `k` bits on A's keys are `h` and whose
radix classes are `c`, the reference coarse count of range
`v = a 2^(k - I) + u` is at most `rRangeCount` of the `RRoute` `sRoute`, with
class `a`, the range `R = u 2^I` and the early set `earlyK` (the keys of the
truncated early list): the early list and the late binary sheds are counted
exactly, and the radix stash holds `Σ_p (class-a arrivals at p - C)₊` records
of the range. The early set is disjoint from main after stage `I`, has at most
`P` keys and is fixed by the bits below `I`.
-/

namespace RebuildBound.SG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2

/-! ### Arithmetic of ranges -/

theorem div_mod_unique {M q c a u : ℕ} (hq : q < M) (hu : u < M) :
    q + M * c = a * M + u ↔ c = a ∧ q = u := by
  constructor
  · intro h
    have hM : 0 < M := by omega
    have h1 : (q + M * c) % M = (a * M + u) % M := by rw [h]
    have h2 : (q + M * c) / M = (a * M + u) / M := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq, Nat.mul_comm a, Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu] at h1
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hq, Nat.zero_add, Nat.mul_comm a,
      Nat.add_comm, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hu, Nat.zero_add] at h2
    exact ⟨h2, h1⟩
  · rintro ⟨rfl, rfl⟩; ring

/-- The coarse range of a raw word: class `a` and in-block bits `≥ I` equal to `u`. -/
theorem range_iff (g : SepGeom) (hIk : g.I ≤ g.k) (t : ℕ) {a u : ℕ}
    (hu : u < 2 ^ (g.k - g.I)) :
    g.homeOf t / 2 ^ g.I = a * 2 ^ (g.k - g.I) + u ↔
      g.cls t = a ∧ t % 2 ^ g.k / 2 ^ g.I = u := by
  have hk : 2 ^ g.k = 2 ^ g.I * 2 ^ (g.k - g.I) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hIk]
  have hq : t % 2 ^ g.k / 2 ^ g.I < 2 ^ (g.k - g.I) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← hk]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdiv : g.homeOf t / 2 ^ g.I = t % 2 ^ g.k / 2 ^ g.I + 2 ^ (g.k - g.I) * g.cls t := by
    unfold SepGeom.homeOf
    rw [hk, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  rw [hdiv, div_mod_unique hq hu]

/-- The range predicate of `rRangeCount` on A's keys is the model's coarse range. -/
theorem pred_iff (g : SepGeom) (hIk : g.I ≤ g.k) {KA : Finset Model.LogicalKey} {w : Model.LogicalKey → ℕ}
    {h : {x // x ∈ KA} → Bits g.k} {c : {x // x ∈ KA} → Fin g.r}
    (hw : ∀ x : {x // x ∈ KA}, natToBits g.k (w x.val) = h x ∧ g.cls (w x.val) = (c x : ℕ))
    {a u : ℕ} (ha : a < g.r) (hu : u < 2 ^ (g.k - g.I)) (r : Rec) (hx : r.key ∈ KA) :
    (InRange g.I (natToBits g.k (u * 2 ^ g.I)) (h ⟨r.key, hx⟩) ∧ c ⟨r.key, hx⟩ = ⟨a, ha⟩) ↔
      (sRange g w r == a * 2 ^ (g.k - g.I) + u) = true := by
  obtain ⟨h1, h2⟩ := hw ⟨r.key, hx⟩
  simp only at h1 h2
  rw [beq_iff_eq, sRange, sHome, range_iff g hIk _ hu, ← h1, inRange_natToBits hIk hu, h2,
    Fin.ext_iff]
  exact And.comm

/-! ### Two sums -/

theorem sum_mod_eq (M : ℕ) {p : ℕ} (hp : p < M) (f : ℕ → ℕ) : ∀ r,
    ∑ u ∈ Finset.range (r * M), (if u % M = p then f u else 0) =
      ∑ i ∈ Finset.range r, f (i * M + p)
  | 0 => by simp
  | r + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_mod_eq M hp f r, Finset.sum_range_succ]
    congr 1
    have : ∀ x ∈ Finset.range M, (if (r * M + x) % M = p then f (r * M + x) else 0) =
        if x = p then f (r * M + x) else 0 := by
      intro x hx
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range M) p, if_pos
      (Finset.mem_range.2 hp), Nat.add_comm]

theorem sum_rangeHomes (k I u : ℕ) (hIk : I ≤ k) (hu : u < 2 ^ (k - I)) (G : Bits k → ℕ) :
    ∑ P ∈ rangeHomes I (natToBits k (u * 2 ^ I)), G P =
      ∑ p ∈ Finset.range (2 ^ k), if p / 2 ^ I = u then G (natToBits k p) else 0 := by
  unfold rangeHomes
  rw [Finset.sum_filter]
  rw [Fintype.sum_equiv (bitsEquiv k) _
    (fun n : Fin (2 ^ k) => if InRange I (natToBits k (u * 2 ^ I)) (natToBits k n) then
      G (natToBits k n) else 0) (fun P => by rw [natToBits_bitsEquiv])]
  rw [Fin.sum_univ_eq_sum_range (fun n => if InRange I (natToBits k (u * 2 ^ I)) (natToBits k n)
    then G (natToBits k n) else 0) (2 ^ k)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : InRange I (natToBits k (u * 2 ^ I)) (natToBits k p) ↔ p / 2 ^ I = u := by
    rw [inRange_natToBits hIk hu, Nat.mod_eq_of_lt (Finset.mem_range.1 hp)]
  exact if_congr e rfl rfl

/-! ### The route at the words of the stages -/

theorem canon_eq (g : SepGeom) : g.canonicalOps = (List.range g.k).flatMap (S05.stageL g) := by
  have := S05.canon_filter g (fun _ => true)
  simpa using this

theorem canon_run (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (aMain : List Bucket) :
    runSOps rule g w g.canonicalOps (sRouteInit g aMain) = sRouteUpTo rule g w aMain g.k := by
  rw [S05.sRouteUpTo_ops _ _ _ _ _ le_rfl, canon_eq]

theorem ref_route (rule : CapRule) (g : SepGeom) (w : Model.LogicalKey → ℕ) (inp : SInputs) :
    (sReferenceWith rule g w inp g.canonicalOps).route =
      radixPass g w (sRouteUpTo rule g w inp.aMain g.k) := by
  simp only [sReferenceWith, sRouteWith, canon_run]

theorem idx_lt (g : SepGeom) {i p : ℕ} (hi : i < g.r) (hp : p < g.blk) : i * g.blk + p < g.N := by
  unfold SepGeom.N
  have h2 : (i + 1) * g.blk ≤ g.r * g.blk := Nat.mul_le_mul_right _ hi
  have h3 : (i + 1) * g.blk = i * g.blk + g.blk := Nat.succ_mul _ _
  have h4 : g.r * g.blk = g.r * 2 ^ g.k := rfl
  omega

theorem rin_getD (g : SepGeom) (st : SRoute) (p : ℕ) {i : ℕ} (hi : i < g.r) :
    (rin g st p).getD i [] = st.main.getD (i * g.blk + p) [] := by
  unfold rin
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_map,
    List.getElem_range]

/-! ### Facts about one old history -/

/-- The truncated early list of the words `wOf h`. -/
noncomputable def earlyL (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits g.k) : List Rec :=
  (aTier ++ ((sRouteUpTo rule g (wOf KA g.k h) aMain g.k).stash.take g.I).flatten).take P

/-- The early key set of the words `wOf h`. -/
noncomputable def earlyK (rule : CapRule) (g : SepGeom) (KA : Finset Model.LogicalKey) (aMain : List Bucket)
    (aTier : List Rec) (P : ℕ) (h : {x // x ∈ KA} → Bits g.k) : Finset {x // x ∈ KA} :=
  keysOf KA (earlyL rule g KA aMain aTier P h)

section Facts

variable {rule : CapRule} (hv : rule.Valid) {g : SepGeom} (hg : g.Valid) {wOld w0 : Model.LogicalKey → ℕ}
  {inp : SInputs} (hI : SInputShape g wOld w0 inp) {KA : Finset Model.LogicalKey}
  (hK : ((inp.aAll).map Rec.key).toFinset = KA)

include hv hg hI

/-- The binary route reads only the bits below `n` of A's main keys. -/
theorem route_congr (w w' : Model.LogicalKey → ℕ) : ∀ n, n ≤ g.k →
    (∀ x ∈ flat inp.aMain, ∀ i < n, (w x.key).testBit i = (w' x.key).testBit i) →
    S05.Inv g (flat inp.aMain) (sRouteUpTo rule g w inp.aMain n) ∧
      sRouteUpTo rule g w inp.aMain n = sRouteUpTo rule g w' inp.aMain n
  | 0, _, _ => by rw [sRouteUpTo_zero, sRouteUpTo_zero]; exact ⟨sinv_init hg hI, rfl⟩
  | n + 1, hn, hk => by
    obtain ⟨ih1, ih2⟩ := route_congr w w' n (by omega) (fun x hx i hi => hk x hx i (by omega))
    rw [S05.sRouteUpTo_succ _ _ _ _ _ hn, S05.sRouteUpTo_succ _ _ _ _ _ hn, ← ih2]
    exact ⟨S05.Inv.stage hv (by omega) ih1, S05.stageL_eq rule hv g w w' n _ (fun B hB r hr =>
      hk r (ih1.recs B hB r hr) n (by omega))⟩

theorem stash_take_flatten (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) :
    ((sRouteUpTo rule g w inp.aMain g.k).stash.take lo).flatten =
      (List.range lo).flatMap (shedsAt rule g w inp.aMain) := by
  rw [route_stash hv g w (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w), ← List.map_take, List.take_range, min_eq_left hlo, List.flatMap_def]

theorem stash_drop_flatten (w : Model.LogicalKey → ℕ) (lo : ℕ) :
    ((sRouteUpTo rule g w inp.aMain g.k).stash.drop lo).flatten =
      (List.range' lo (g.k - lo)).flatMap (shedsAt rule g w inp.aMain) := by
  rw [route_stash hv g w (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w), ← List.map_drop, List.range_eq_range', List.drop_range',
    List.flatMap_def]
  simp

theorem late_sub (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) :
    ((flat (sRouteUpTo rule g w inp.aMain lo).main : List Rec) : Multiset Rec) =
      (flat (sRouteUpTo rule g w inp.aMain g.k).main : Multiset Rec) +
        ((List.range' lo (g.k - lo)).flatMap (shedsAt rule g w inp.aMain) : Multiset Rec) := by
  have := flat_range hv g w (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
    (splaced_init hg hI w) lo (g.k - lo) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

omit hv hg in
theorem aAll_nodup : ((flat inp.aMain ++ inp.aTier).map Rec.key).Nodup := hI.aNodup

/-- A's main after `lo` stages, the early sheds and A's tier are distinct by key. -/
theorem lo_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) :
    ((flat (sRouteUpTo rule g w inp.aMain lo).main ++
      ((List.range lo).flatMap (shedsAt rule g w inp.aMain) ++ inp.aTier)).map Rec.key).Nodup := by
  have hp : (flat inp.aMain ++ inp.aTier).Perm (flat (sRouteUpTo rule g w inp.aMain lo).main ++
      ((List.range lo).flatMap (shedsAt rule g w inp.aMain) ++ inp.aTier)) := by
    rw [← List.append_assoc]
    exact (perm_of_add (main_sub hv hg hI w hlo)).append_right _
  exact (hp.map Rec.key).nodup_iff.1 (aAll_nodup hI)

theorem late_nodup (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) :
    ((flat (sRouteUpTo rule g w inp.aMain g.k).main ++
      (List.range' lo (g.k - lo)).flatMap (shedsAt rule g w inp.aMain)).map Rec.key).Nodup :=
  nodup_of_add (late_sub hv hg hI w hlo) (main_nodup hv hg hI w hlo)

theorem early_mem (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) {r : Rec}
    (hr : r ∈ (List.range lo).flatMap (shedsAt rule g w inp.aMain)) : r ∈ flat inp.aMain :=
  (mem_of_add (main_sub hv hg hI w hlo)).2 (Or.inr hr)

theorem late_mem (w : Model.LogicalKey → ℕ) {lo : ℕ} (hlo : lo ≤ g.k) {r : Rec}
    (hr : r ∈ (List.range' lo (g.k - lo)).flatMap (shedsAt rule g w inp.aMain)) :
    r ∈ flat inp.aMain :=
  main_mem hv hg hI w hlo ((mem_of_add (late_sub hv hg hI w hlo)).2 (Or.inr hr))

include hK

omit hK in
theorem earlyL_nodup (P : ℕ) (h : {x // x ∈ KA} → Bits g.k) (hIk : g.I ≤ g.k) :
    ((earlyL rule g KA inp.aMain inp.aTier P h).map Rec.key).Nodup := by
  have := lo_nodup hv hg hI (wOf KA g.k h) hIk
  rw [List.map_append] at this
  have h2 := (List.nodup_append.1 this).2.1
  unfold earlyL
  rw [stash_take_flatten hv hg hI _ hIk]
  apply List.Sublist.nodup _ ((List.perm_append_comm.map Rec.key).nodup_iff.1 h2)
  rw [List.map_take]
  exact List.take_sublist _ _

theorem earlyL_mem (P : ℕ) (h : {x // x ∈ KA} → Bits g.k) (hIk : g.I ≤ g.k) {r : Rec}
    (hr : r ∈ earlyL rule g KA inp.aMain inp.aTier P h) : r.key ∈ KA := by
  unfold earlyL at hr
  rw [stash_take_flatten hv hg hI _ hIk] at hr
  rcases List.mem_append.1 (List.mem_of_mem_take hr) with h1 | h1
  · exact key_mem_of_aTier hK h1
  · exact key_mem_of_aMain hK (early_mem hv hg hI _ hIk h1)

omit hK in
theorem earlyK_disjoint (P : ℕ) (hIk : g.I ≤ g.k) (h : {x // x ∈ KA} → Bits g.k) :
    Disjoint (earlyK rule g KA inp.aMain inp.aTier P h)
      ((sRoute rule g KA inp.aMain).mainAt h g.I) := by
  rw [sRoute_mainAt, min_eq_left hIk]
  have hnd := lo_nodup hv hg hI (wOf KA g.k h) hIk
  have hd := keysOf_disjoint (KA := KA) hnd
  refine (Disjoint.mono_left ?_ hd.symm)
  intro x hx
  unfold earlyK earlyL at hx
  rw [mem_keysOf, stash_take_flatten hv hg hI _ hIk] at hx
  rw [mem_keysOf, List.map_append, List.mem_append]
  obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hx
  rcases List.mem_append.1 (List.mem_of_mem_take hr) with h1 | h1
  · right; exact List.mem_map.2 ⟨r, h1, hrx⟩
  · left; exact List.mem_map.2 ⟨r, h1, hrx⟩

omit hv hg hI hK in
theorem earlyK_card (P : ℕ) (h : {x // x ∈ KA} → Bits g.k) :
    (earlyK rule g KA inp.aMain inp.aTier P h).card ≤ P :=
  (keysOf_card_le _).trans (List.length_take_le _ _)

theorem earlyK_blind (P : ℕ) (hIk : g.I ≤ g.k) (h h' : {x // x ∈ KA} → Bits g.k)
    (hag : AgreeBelow g.I h h') :
    earlyK rule g KA inp.aMain inp.aTier P h = earlyK rule g KA inp.aMain inp.aTier P h' := by
  unfold earlyK earlyL
  have hkeys : ∀ r ∈ flat inp.aMain, ∀ i < g.I,
      (wOf KA g.k h r.key).testBit i = (wOf KA g.k h' r.key).testBit i := by
    intro r hr i hi
    have hx := key_mem_of_aMain hK hr
    have e1 := testBit_wOf h ⟨r.key, hx⟩ ⟨i, by omega⟩
    have e2 := testBit_wOf h' ⟨r.key, hx⟩ ⟨i, by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    exact hag _ _ hi
  have hr := (route_congr hv hg hI (wOf KA g.k h) (wOf KA g.k h') g.I hIk hkeys).2
  rw [route_stash_take hv g _ (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
      (splaced_init hg hI _) hIk,
    route_stash_take hv g _ (pOf g wOld) (U_le_pOf g wOld) inp.aMain (sinv_init hg hI)
      (splaced_init hg hI _) hIk, hr]

/-- The class-`a` arrivals at the radix node of in-block bucket `p`, as keys and as
records of the final buckets. -/
theorem card_class (hr : 0 < g.r) (w : Model.LogicalKey → ℕ) (h : {x // x ∈ KA} → Bits g.k)
    (c : {x // x ∈ KA} → Fin g.r)
    (hw : ∀ x : {x // x ∈ KA}, natToBits g.k (w x.val) = h x ∧ g.cls (w x.val) = (c x : ℕ))
    {a : ℕ} (ha : a < g.r) {p : ℕ} (hp : p < g.blk) :
    (((sRoute rule g KA inp.aMain).mainAt h g.k).filter
        (fun x => h x = natToBits g.k p ∧ c x = ⟨a, ha⟩)).card =
      ∑ i ∈ Finset.range g.r,
        ((rin g (sRouteUpTo rule g (wOf KA g.k h) inp.aMain g.k) p).getD i []).recs.countP
          (fun x => g.cls (w x.key) == a) := by
  set w' := wOf KA g.k h
  set s := sRouteUpTo rule g w' inp.aMain g.k
  obtain ⟨i1, i2, _, _⟩ := route_inv hv g w' (pOf g wOld) (U_le_pOf g wOld) inp.aMain
    (sinv_init hg hI) (splaced_init hg hI w') g.k le_rfl
  have hblk : g.blk = 2 ^ g.k := rfl
  -- the low bits of a key's word, from its main bucket
  have hlow : ∀ u < g.N, ∀ r ∈ (s.main.getD u []).recs, w r.key % 2 ^ g.k = u % 2 ^ g.k := by
    intro u hu r hr
    have hx : r.key ∈ KA := key_mem_of_aMain hK (main_mem hv hg hI w' le_rfl
      (mem_flat_of_getD hr))
    have e := i2 u hu r hr
    have h1 : natToBits g.k (w r.key) = natToBits g.k (w' r.key) := by
      rw [(hw ⟨r.key, hx⟩).1, natToBits_wOf h ⟨r.key, hx⟩]
    have h2 : w' r.key % 2 ^ g.k = u % 2 ^ g.k := by
      rw [e, vd, Nat.mul_add_mod, Nat.mod_mod]
    rw [← h2]
    rw [← natToBits_mod, ← natToBits_mod g.k (w' r.key)] at h1
    exact natToBits_injOn (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _)) h1
  rw [sRoute_mainAt, min_self]
  rw [card_filter_keysOf _ (main_nodup hv hg hI w' le_rfl)
    (fun r hr => key_mem_of_aMain hK (main_mem hv hg hI w' le_rfl hr)) _
    (fun r => decide (w r.key % 2 ^ g.k = p ∧ g.cls (w r.key) = a))]
  · rw [flat_countP, i1.len]
    have hterm : ∀ u ∈ Finset.range g.N,
        (s.main.getD u []).recs.countP (fun r => decide (w r.key % 2 ^ g.k = p ∧
          g.cls (w r.key) = a)) =
        if u % 2 ^ g.k = p then (s.main.getD u []).recs.countP
          (fun x => g.cls (w x.key) == a) else 0 := by
      intro u hu
      split_ifs with hup
      · apply List.countP_congr
        intro r hr
        rw [hlow u (Finset.mem_range.1 hu) r hr, hup]
        simp
      · rw [List.countP_eq_zero]
        intro r hr hq
        simp only [decide_eq_true_eq] at hq
        exact hup (by rw [← hlow u (Finset.mem_range.1 hu) r hr]; exact hq.1)
    rw [Finset.sum_congr rfl hterm]
    unfold SepGeom.N
    rw [sum_mod_eq (2 ^ g.k) hp (fun u => (s.main.getD u []).recs.countP
      (fun x => g.cls (w x.key) == a)) g.r]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [rin_getD g s p (Finset.mem_range.1 hi)]
    rfl
  · intro r hr
    have hx := key_mem_of_aMain hK (main_mem hv hg hI w' le_rfl hr)
    obtain ⟨h1, h2⟩ := hw ⟨r.key, hx⟩
    simp only at h1 h2
    rw [decide_eq_true_iff, ← h1, Fin.ext_iff, ← h2]
    simp only
    rw [natToBits_eq_iff, bitsEquiv_natToBits, Nat.mod_eq_of_lt (show p < 2 ^ g.k from hp)]

/-- **The reference coarse count is at most the route's `rRangeCount`.** -/
theorem refCoarse_le (hr : 0 < g.r) (hIk : g.I ≤ g.k) (w : Model.LogicalKey → ℕ)
    (h : {x // x ∈ KA} → Bits g.k) (c : {x // x ∈ KA} → Fin g.r)
    (hw : ∀ x : {x // x ∈ KA}, natToBits g.k (w x.val) = h x ∧ g.cls (w x.val) = (c x : ℕ))
    {a u : ℕ} (ha : a < g.r) (hu : u < 2 ^ (g.k - g.I)) (P : ℕ) :
    sRefCoarse g w (sReferenceWith rule g w inp g.canonicalOps) inp P (a * 2 ^ (g.k - g.I) + u) ≤
      rRangeCount (sRoute rule g KA inp.aMain) g.C g.I
        (earlyK rule g KA inp.aMain inp.aTier P) (natToBits g.k (u * 2 ^ g.I)) ⟨a, ha⟩ h c := by
  set w' := wOf KA g.k h
  set v := a * 2 ^ (g.k - g.I) + u
  set R := natToBits g.k (u * 2 ^ g.I)
  have hkeys : ∀ x ∈ flat inp.aMain, ∀ i < g.k, (w x.key).testBit i = (w' x.key).testBit i := by
    intro x hx i hi
    have hxK := key_mem_of_aMain hK hx
    have e1 := congrFun (hw ⟨x.key, hxK⟩).1 ⟨i, hi⟩
    simp only [natToBits] at e1
    rw [e1]
    exact (testBit_wOf h ⟨x.key, hxK⟩ ⟨i, hi⟩).symm
  have hroute := (route_congr hv hg hI w w' g.k le_rfl hkeys).2
  set s := sRouteUpTo rule g w' inp.aMain g.k
  obtain ⟨i1, i2, _, i4⟩ := route_inv hv g w' (pOf g wOld) (U_le_pOf g wOld) inp.aMain
    (sinv_init hg hI) (splaced_init hg hI w') g.k le_rfl
  have hpr : ∀ (l : List Rec), (∀ r ∈ l, r.key ∈ KA) →
      ∀ Q : Finset {x // x ∈ KA}, (l.map Rec.key).Nodup → Q = keysOf KA l →
      l.countP (fun x => sRange g w x == v) =
        (Q.filter (fun x => InRange g.I R (h x) ∧ c x = ⟨a, ha⟩)).card := by
    intro l hl Q hnd hQ
    rw [hQ]
    exact (card_filter_keysOf l hnd hl _ _ (fun r hr => pred_iff g hIk hw ha hu r (hl r hr))).symm
  unfold sRefCoarse sEarlyList sLateSheds rRangeCount
  rw [ref_route, hroute, radixPass_stash, radixPass_radix, i4, List.nil_append,
    List.countP_append, List.countP_append, ← Nat.add_assoc]
  refine Nat.add_le_add (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_)) ?_
  · -- the early list
    exact hpr _ (fun r hr => earlyL_mem hv hg hI hK P h hIk hr) _
      (earlyL_nodup hv hg hI P h hIk) rfl
  · -- the late binary sheds
    rw [stash_drop_flatten hv hg hI w']
    have hnd := late_nodup hv hg hI w' hIk
    rw [List.map_append] at hnd
    refine hpr _ (fun r hr => key_mem_of_aMain hK (late_mem hv hg hI w' hIk hr)) _
      (List.nodup_append.1 hnd).2.1 ?_
    rw [sRoute_mainAt, sRoute_mainAt, min_eq_left hIk, min_self]
    exact keysOf_sdiff (late_sub hv hg hI w' hIk) (late_nodup hv hg hI w' hIk)
  · -- the radix stash
    split_ifs with hr1
    · rw [List.countP_flatMap, S12.list_sum_range, sum_rangeHomes g.k g.I u hIk hu]
      apply le_of_eq
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < g.blk := Finset.mem_range.1 hp
      have hlen : (rin g s p).length = g.r := by simp [rin]
      have hlanes : ∀ B ∈ rin g s p, B.length = g.C := by
        intro B hB
        unfold rin at hB
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hB
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
        have hi' := List.mem_range.1 hi
        apply i1.lanes
        apply getD_mem
        rw [i1.len]
        exact idx_lt g hi' hp'
      -- every shed record of tuple `p` has low bits `p`
      have hlow : ∀ x ∈ rshed g w s p, x.key ∈ KA ∧ w x.key % 2 ^ g.k = p := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := S12.radixSplit_mem _ _ hx
        rw [hlen] at hi
        rw [rin_getD g s p hi] at hxi
        have hidx : i * g.blk + p < g.N := idx_lt g hi hp'
        have hxK : x.key ∈ KA := key_mem_of_aMain hK (main_mem hv hg hI w' le_rfl
          (mem_flat_of_getD hxi))
        refine ⟨hxK, ?_⟩
        have e := i2 _ hidx x hxi
        have h1 : natToBits g.k (w x.key) = natToBits g.k (w' x.key) := by
          rw [(hw ⟨x.key, hxK⟩).1, natToBits_wOf h ⟨x.key, hxK⟩]
        have h2 : w' x.key % 2 ^ g.k = p := by
          have h3 := congrArg (· % 2 ^ g.k) e
          simp only [vd, Nat.mul_add_mod, Nat.mod_mod] at h3
          rw [← h3]
          show (i * 2 ^ g.k + p) % 2 ^ g.k = p
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (show p < 2 ^ g.k from hp')]
        rw [← h2]
        rw [← natToBits_mod, ← natToBits_mod g.k (w' x.key)] at h1
        exact natToBits_injOn (Nat.mod_lt _ (Nat.two_pow_pos _))
          (Nat.mod_lt _ (Nat.two_pow_pos _)) h1
      simp only [Function.comp]
      split_ifs with hpu
      · rw [card_class hv hg hI hK hr w h c hw ha hp']
        have hcount := S12.radixSplit_countP (fun x => g.cls (w x.key)) (rin g s p) g.C hlanes
          (show a < (rin g s p).length by rw [hlen]; exact ha)
        rw [hlen] at hcount
        refine Eq.trans ?_ hcount
        apply List.countP_congr
        intro x hx
        obtain ⟨_, hxp⟩ := hlow x hx
        rw [beq_iff_eq, beq_iff_eq, sRange, sHome, range_iff g hIk _ hu, hxp, hpu]
        simp
      · rw [List.countP_eq_zero]
        intro x hx hq
        obtain ⟨_, hxp⟩ := hlow x hx
        rw [beq_iff_eq, sRange, sHome, range_iff g hIk _ hu, hxp] at hq
        exact hpu hq.2
    · simp
end Facts

end RebuildBound.SG2
