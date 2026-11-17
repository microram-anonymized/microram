import RebuildBound.Proofs.S4b.Insert

/-!
# S4b, the whole finish phase

`GInv` after the insertion of every B bucket: all homes have offered, and every
insertion-trace quantity is at most `sHomeExcess`.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b (nodup_of_subperm getD_set_self getD_set_of_ne getD_sublist_flatten
  mem_flatten_getD flatten_set_sublist fill_snd fill_of_full fill_recs_perm keys_eq mem_keys
  free_zero_of_full fill_placed_eq mem_getD_set_self' mem_getD_set' length_filter_split
  recs_sublist_flatMap not_mem_keys_clear)

/-- The state after `m` ways of the per-way loop. -/
def wayAcc (g : SepGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (n : Nat) (s0 : SFin) (m : Nat) :
    SFin × List Rec :=
  (List.range m).foldl (wayBody g w Bi n) (s0, [])

theorem wayAcc_succ (g : SepGeom) (w : Model.LogicalKey → Nat) (Bi : Bucket) (n : Nat) (s0 : SFin) (m : Nat) :
    wayAcc g w Bi n s0 (m + 1) = wayBody g w Bi n (wayAcc g w Bi n s0 m) m := by
  unfold wayAcc
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

section
variable {g : SepGeom} {w : Model.LogicalKey → Nat} {inp : SInputs} {pool : List Rec}

theorem ginv_insertBucket (cx : Ctx g w inp pool) {n : Nat} (hn : n < g.U) {st : SFin}
    (h : GInv g w inp pool (fun v => v % g.U < n) (fun _ v => v % g.U < n)
      (fun v => v % g.U < n) st.ins st) :
    GInv g w inp pool (fun v => v % g.U < n + 1) (fun _ v => v % g.U < n + 1)
      (fun v => v % g.U < n + 1) (sInsertBucket g w inp.bMain n st).ins
      (sInsertBucket g w inp.bMain n st) := by
  have hd2 : 2 ≤ g.d := cx.valid.2.1
  have G0 := ginv_dedup cx hn h (fun v _ hv => by omega) (fun p v _ hv => by omega)
    (fun v _ hv => by omega)
  have G0' : GInv g w inp pool (dn g n 0) (fun _ => dn g n 0) (dn g n 0)
      (st.ins ++ []) (dedupSt g inp.bMain n st) := by
    rw [List.append_nil]
    exact G0.mono cx.valid (fun v _ hv => dn_zero.1 hv) (fun p r _ hv => dn_zero.1 hv)
      (fun v _ hv => dn_zero.2 hv)
  have key : ∀ m, m ≤ g.d →
      GInv g w inp pool (dn g n m) (fun _ => dn g n m) (dn g n m)
        (st.ins ++ (wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) m).2)
        (wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) m).1 ∧
      (wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) m).1.ins =
        (if m = g.d then
          st.ins ++ (wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) m).2
        else st.ins) ∧
      (∀ q, m ≤ q → q < g.d → ∀ r ∈ (inp.bMain.getD n []).recs,
        r.key ∉ ((wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) m).1.main.getD
          (n + q * g.U) []).keys) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨G0', by rw [if_neg (by omega)]; rfl, ?_⟩
      intro q _ hq r hr
      obtain ⟨hd, _⟩ := dedup_getD hn inp.bMain st h.len
      show r.key ∉ ((dedupSt g inp.bMain n st).main.getD (n + q * g.U) []).keys
      rw [hd, if_pos ⟨ci_lt hn hq, ci_mod hn⟩]
      apply not_mem_keys_clear
      simpa [Bucket.keys] using ⟨r, hr, rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      rw [if_neg (by omega)] at i2
      rw [wayAcc_succ]
      exact way_step cx hn (by omega) i1 i2 i3
  obtain ⟨K1, K2, _⟩ := key g.d le_rfl
  rw [sInsertBucket_eq]
  show GInv g w inp pool _ _ _ (wayAcc g w (inp.bMain.getD n []) n (dedupSt g inp.bMain n st) g.d).1.ins _
  rw [K2, if_pos rfl]
  have hdn : ∀ v < g.N, v % g.U < n + 1 → dn g n g.d v := by
    intro v hv hlt
    unfold dn
    by_cases e : v % g.U < n
    · exact Or.inl e
    · refine Or.inr ⟨by omega, ?_⟩
      rw [N_eq_d] at hv
      exact (Nat.div_lt_iff_lt_mul (U_pos g)).2 hv
  have hdn' : ∀ v, dn g n g.d v → v % g.U < n + 1 := by
    intro v hv; unfold dn at hv; omega
  exact K1.mono cx.valid (fun v hv hh => hdn v hv hh) (fun p r _ hh => hdn _ (sHome_lt cx.valid w r) hh)
    (fun v _ hh => hdn' v hh)

/-- The finish phase's start state. -/
def fin0 (inp : SInputs) (routed : List Bucket) (leaves : List (List Rec)) : SFin :=
  { main := routed, ins := [], leaves := leaves, bcopy := inp.bTier, trace := [] }

theorem sFinish_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (inp : SInputs) (routed : List Bucket)
    (leaves : List (List Rec)) :
    sFinish g w inp routed leaves =
      (List.range g.U).foldl (fun st i => sInsertBucket g w inp.bMain i st)
        (fin0 inp routed leaves) :=
  rfl

theorem ginv_fold (cx : Ctx g w inp pool) (st0 : SFin)
    (h0 : GInv g w inp pool (fun v => v % g.U < 0) (fun _ v => v % g.U < 0)
      (fun v => v % g.U < 0) st0.ins st0) : ∀ n, n ≤ g.U →
    GInv g w inp pool (fun v => v % g.U < n) (fun _ v => v % g.U < n) (fun v => v % g.U < n)
      ((List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st) st0).ins
      ((List.range n).foldl (fun st i => sInsertBucket g w inp.bMain i st) st0)
  | 0, _ => h0
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ginv_insertBucket cx (by omega) (ginv_fold cx st0 h0 n (by omega))

theorem sLeaves_getD (g : SepGeom) (w : Model.LogicalKey → Nat) (pool : List Rec) (R : Nat) {r : Rec}
    (hr : r ∈ (sLeaves g w pool).getD R []) : r ∈ pool ∧ sRange g w r = R := by
  unfold sLeaves at hr
  by_cases hR : R < g.ranges
  · rw [List.getD_eq_getElem _ _ (by simpa using hR)] at hr
    simp only [List.getElem_map, List.getElem_range, List.mem_filter] at hr
    exact ⟨hr.1, by simpa using hr.2⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hr
    simp at hr

theorem sLeaves_nodup (g : SepGeom) (w : Model.LogicalKey → Nat) {pool : List Rec}
    (hp : (pool.map Rec.key).Nodup) : ((sLeaves g w pool).flatten.map Rec.key).Nodup := by
  unfold sLeaves
  rw [List.map_flatten, List.map_map, List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨R, _, rfl⟩ := List.mem_map.1 hl
    exact hp.sublist (List.filter_sublist.map _)
  · rw [List.pairwise_map]
    refine List.nodup_range.pairwise_of_forall_ne ?_
    intro R _ R' _ hne x hx hx'
    simp only [Function.comp, List.mem_map, List.mem_filter] at hx hx'
    obtain ⟨r, ⟨_, hr⟩, rfl⟩ := hx
    obtain ⟨r', ⟨_, hr'⟩, e⟩ := hx'
    have h1 : sRange g w r = R := by simpa using hr
    have h2 : sRange g w r' = R' := by simpa using hr'
    apply hne
    rw [← h1, ← h2]
    simp [sRange, sHome, e]

theorem ginv_init {routed : List Bucket}
    (hlen : routed.length = g.N) (hok : ∀ v < g.N, HomeOK g w inp v (routed.getD v []))
    (hp : (pool.map Rec.key).Nodup) :
    GInv g w inp pool (fun v => v % g.U < 0) (fun _ v => v % g.U < 0) (fun v => v % g.U < 0)
      (fin0 inp routed (sLeaves g w pool)).ins (fin0 inp routed (sLeaves g w pool)) where
  len := hlen
  ok := hok
  lv R r hr := sLeaves_getD g w pool R hr
  lvnd := sLeaves_nodup g w hp
  bc := List.Sublist.refl _
  aD _ _ _ hq := absurd hq (Nat.not_lt_zero _)
  bD _ _ _ hq := absurd hq (Nat.not_lt_zero _)
  ins _ hx := by simp [fin0] at hx
  insnd := by simp [fin0]
  tr _ he := by simp [fin0] at he

/-- The finish phase ends with every home offered and every insertion-trace
quantity at most `sHomeExcess`. -/
theorem ginv_finish (cx : Ctx g w inp pool) {routed : List Bucket}
    (hlen : routed.length = g.N) (hok : ∀ v < g.N, HomeOK g w inp v (routed.getD v []))
    (hp : (pool.map Rec.key).Nodup) :
    GInv g w inp pool (fun _ => True) (fun _ _ => True) (fun _ => True)
      (sFinish g w inp routed (sLeaves g w pool)).ins
      (sFinish g w inp routed (sLeaves g w pool)) := by
  have h := ginv_fold cx _ (ginv_init hlen hok hp) g.U le_rfl
  rw [← sFinish_eq] at h
  refine h.mono cx.valid ?_ ?_ (fun _ _ _ => trivial)
  · intro v _ _
    exact Nat.mod_lt _ (U_pos g)
  · intro p r _ _
    exact Nat.mod_lt _ (U_pos g)

end

end RebuildBound.S4b
