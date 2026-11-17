import RebuildBound.Proofs.S6.Route
import RebuildBound.Proofs.S12.Radix

/-!
# S6: the terminal radix pass and A's records along the route

* `radixPass` reads only the main buckets and the radix stash and appends to
  the trace, so two route states with the same main and radix stash give the
  same main, radix stash and trace suffix (`radixPass_congr`).
* Conservation: the binary route keeps every record (`SRecInv`), and the
  radix stash is a sub-multiset of the routed main's records
  (`radixPass_radix_subperm`). Hence the stage stashes and the radix stash
  together are a sub-multiset of A's main records, so the pool is
  key-distinct.
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6

/-! ### The radix pass reads only main and the radix stash -/

section RadixCongr

variable (g : SepGeom) (w : Model.LogicalKey → Nat)

/-- The buckets of tuple `p`. -/
def rIdx (p : Nat) : List Nat := (List.range g.r).map fun a => a * g.blk + p

/-- The radix split of tuple `p` on main `m`. -/
def rSplit (p : Nat) (m : List Bucket) : List Bucket × List Rec :=
  radixSplit (fun x => g.cls (w x.key)) ((rIdx g p).map fun j => m.getD j [])

/-- The main buckets after tuple `p`. -/
def rMain (p : Nat) (m : List Bucket) : List Bucket :=
  ((rIdx g p).zip (rSplit g w p m).1).foldl (fun m q => m.set q.1 q.2) m

theorem radixStep_main (p : Nat) (st : SRoute) :
    (radixStep g w p st).main = rMain g w p st.main := rfl

theorem radixStep_radix (p : Nat) (st : SRoute) :
    (radixStep g w p st).radix = st.radix ++ (rSplit g w p st.main).2 := rfl

theorem radixStep_stash (p : Nat) (st : SRoute) : (radixStep g w p st).stash = st.stash := rfl

theorem radixStep_trace (p : Nat) (st : SRoute) :
    (radixStep g w p st).trace =
      st.trace ++ [(STest.radix, (st.radix ++ (rSplit g w p st.main).2).length)] := rfl

theorem radixFold_congr :
    ∀ (l : List Nat) (s t : SRoute), s.main = t.main → s.radix = t.radix →
      (l.foldl (fun st p => radixStep g w p st) s).main =
          (l.foldl (fun st p => radixStep g w p st) t).main ∧
        (l.foldl (fun st p => radixStep g w p st) s).radix =
          (l.foldl (fun st p => radixStep g w p st) t).radix ∧
        (l.foldl (fun st p => radixStep g w p st) s).stash = s.stash ∧
        (l.foldl (fun st p => radixStep g w p st) t).stash = t.stash ∧
        ∃ T, (l.foldl (fun st p => radixStep g w p st) s).trace = s.trace ++ T ∧
          (l.foldl (fun st p => radixStep g w p st) t).trace = t.trace ++ T
  | [], s, t, hm, hr => ⟨hm, hr, rfl, rfl, [], by simp, by simp⟩
  | p :: l, s, t, hm, hr => by
    simp only [List.foldl_cons]
    have hm' : (radixStep g w p s).main = (radixStep g w p t).main := by
      rw [radixStep_main, radixStep_main, hm]
    have hr' : (radixStep g w p s).radix = (radixStep g w p t).radix := by
      rw [radixStep_radix, radixStep_radix, hm, hr]
    obtain ⟨h1, h2, h3, h4, T, h5, h6⟩ := radixFold_congr l _ _ hm' hr'
    refine ⟨h1, h2, by rw [h3, radixStep_stash], by rw [h4, radixStep_stash],
      [(STest.radix, (s.radix ++ (rSplit g w p s.main).2).length)] ++ T, ?_, ?_⟩
    · rw [h5, radixStep_trace, List.append_assoc]
    · rw [h6, radixStep_trace, List.append_assoc, hm, hr]

/-- **The radix pass.** It reads only main and the radix stash. -/
theorem radixPass_congr (s t : SRoute) (hm : s.main = t.main) (hr : s.radix = t.radix) :
    (radixPass g w s).main = (radixPass g w t).main ∧
      (radixPass g w s).radix = (radixPass g w t).radix ∧
      (radixPass g w s).stash = s.stash ∧ (radixPass g w t).stash = t.stash ∧
      ∃ T, (radixPass g w s).trace = s.trace ++ T ∧ (radixPass g w t).trace = t.trace ++ T := by
  unfold radixPass
  split_ifs
  · exact radixFold_congr g w _ s t hm hr
  · exact ⟨hm, hr, rfl, rfl, [], by simp, by simp⟩

end RadixCongr

/-! ### The radix stash is a sub-multiset of the routed records -/

theorem foldl_set_getD_ne {α : Type*} (j : Nat) (d : α) :
    ∀ (L : List (Nat × α)) (m : List α), (∀ q ∈ L, q.1 ≠ j) →
      (L.foldl (fun m q => m.set q.1 q.2) m).getD j d = m.getD j d
  | [], _, _ => rfl
  | q :: L, m, h => by
    rw [List.foldl_cons, foldl_set_getD_ne j d L _ fun q' hq' => h q' (List.mem_cons_of_mem _ hq'),
      getD_set_ne _ _ _ (h q List.mem_cons_self)]

section Sub

variable (g : SepGeom) (w : Model.LogicalKey → Nat)

theorem blk_pos : 0 < g.blk := Nat.two_pow_pos _

theorem rIdx_mod (p a : Nat) (hp : p < g.blk) : (a * g.blk + p) % g.blk = p := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]

theorem rMain_getD_ne (p j : Nat) (m : List Bucket) (hp : p < g.blk) (hj : j % g.blk ≠ p) :
    (rMain g w p m).getD j [] = m.getD j [] := by
  unfold rMain
  apply foldl_set_getD_ne
  intro q hq
  have h1 := (List.of_mem_zip hq).1
  unfold rIdx at h1
  obtain ⟨a, _, ha⟩ := List.mem_map.mp h1
  intro e
  apply hj
  rw [← e, ← ha, rIdx_mod g p a hp]

/-- The indices of tuples `< n`. -/
def lowIdx (n : Nat) : List Nat := (List.range g.N).filter fun j => decide (j % g.blk < n)

theorem N_eq : g.N = g.r * g.blk := rfl

theorem lowIdx_succ_perm (n : Nat) (hn : n < g.blk) :
    (lowIdx g (n + 1)).Perm (lowIdx g n ++ rIdx g n) := by
  have hb := blk_pos g
  have hnd1 : (lowIdx g (n + 1)).Nodup := List.nodup_range.filter _
  have hnd2 : (lowIdx g n ++ rIdx g n).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_range.filter _, ?_, ?_⟩
    · unfold rIdx
      refine List.Nodup.map (fun a b h => ?_) List.nodup_range
      have := Nat.add_right_cancel h
      exact Nat.eq_of_mul_eq_mul_right hb this
    · intro a ha b hb' hab
      subst hab
      unfold lowIdx at ha
      unfold rIdx at hb'
      obtain ⟨c, _, hc⟩ := List.mem_map.mp hb'
      have h1 := (List.mem_filter.mp ha).2
      simp only [decide_eq_true_eq] at h1
      rw [← hc, rIdx_mod g n c hn] at h1
      omega
  rw [List.perm_ext_iff_of_nodup hnd1 hnd2]
  intro j
  simp only [lowIdx, rIdx, List.mem_append, List.mem_filter, List.mem_range, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hj, hjn⟩
    by_cases h : j % g.blk < n
    · exact Or.inl ⟨hj, h⟩
    · right
      refine ⟨j / g.blk, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hb]
        rw [N_eq] at hj
        exact hj
      · have := Nat.div_add_mod j g.blk
        rw [Nat.mul_comm] at this
        omega
  · rintro (⟨hj, hjn⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨hj, by omega⟩
    · refine ⟨?_, by rw [rIdx_mod g n a hn]; omega⟩
      rw [N_eq]
      calc a * g.blk + n < a * g.blk + g.blk := by omega
        _ = (a + 1) * g.blk := by ring
        _ ≤ g.r * g.blk := Nat.mul_le_mul_right _ ha

theorem lowIdx_blk : lowIdx g g.blk = List.range g.N := by
  unfold lowIdx
  rw [List.filter_eq_self]
  intro j _
  simpa using Nat.mod_lt j (blk_pos g)

theorem radixFold_sub (st : SRoute) :
    ∀ n, n ≤ g.blk →
      (∀ j, n ≤ j % g.blk →
        ((List.range n).foldl (fun st p => radixStep g w p st) st).main.getD j [] =
          st.main.getD j []) ∧
      ((List.range n).foldl (fun st p => radixStep g w p st) st).radix.Subperm
        (st.radix ++ (lowIdx g n).flatMap fun j => (st.main.getD j []).recs)
  | 0, _ => by
    refine ⟨fun _ _ => rfl, ?_⟩
    simp only [List.range_zero, List.foldl_nil]
    exact (List.sublist_append_left _ _).subperm
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := radixFold_sub st n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set s := (List.range n).foldl (fun st p => radixStep g w p st) st with hs
    have hnb : n < g.blk := by omega
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [radixStep_main, rMain_getD_ne g w n j _ hnb (by omega)]
      exact ih1 j (by omega)
    · rw [radixStep_radix]
      have hX : (rIdx g n).map (fun j => s.main.getD j []) =
          (rIdx g n).map (fun j => st.main.getD j []) := by
        apply List.map_congr_left
        intro j hj
        unfold rIdx at hj
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
        exact ih1 _ (by rw [rIdx_mod g n a hnb])
      have hsh : (rSplit g w n s.main).2.Subperm
          ((rIdx g n).flatMap fun j => (st.main.getD j []).recs) := by
        unfold rSplit
        rw [hX]
        have := (List.sublist_append_right _ _).subperm.trans (S12.radixSplit_perm
          (fun x => g.cls (w x.key)) ((rIdx g n).map fun j => st.main.getD j [])).subperm
        rwa [List.flatMap_map] at this
      have hperm : ((lowIdx g (n + 1)).flatMap fun j => (st.main.getD j []).recs).Perm
          (((lowIdx g n).flatMap fun j => (st.main.getD j []).recs) ++
            (rIdx g n).flatMap fun j => (st.main.getD j []).recs) := by
        rw [← List.flatMap_append]
        exact (lowIdx_succ_perm g n hnb).flatMap_right _
      refine (ih2.append hsh).trans ?_
      rw [List.append_assoc]
      exact (hperm.symm.append_left _).subperm

/-- **The radix stash is a sub-multiset of the records it is applied to.** -/
theorem radixPass_radix_subperm (st : SRoute) (hlen : st.main.length = g.N) :
    (radixPass g w st).radix.Subperm (st.radix ++ st.main.flatMap Bucket.recs) := by
  unfold radixPass
  split_ifs
  · have := (radixFold_sub g w st g.blk le_rfl).2
    rw [lowIdx_blk, ← hlen, ← S12.flatMap_eq_range] at this
    exact this
  · exact (List.sublist_append_left _ _).subperm

end Sub

/-! ### The binary route conserves A's records -/

/-- The route keeps every bucket at `C` lanes and conserves the records. -/
def SRecInv (C : Nat) (M0 : List Rec) (st : SRoute) : Prop :=
  (∀ B ∈ st.main, B.length = C) ∧ (st.main.flatMap Bucket.recs ++ st.stash.flatten).Perm M0

theorem SRecInv.step {rule : CapRule} (hv : rule.Valid) {g : SepGeom} {w : Model.LogicalKey → Nat}
    {M0 : List Rec} {st : SRoute} (h : SRecInv g.C M0 st) (j i : Nat)
    (hi : i + 2 ^ j < st.main.length) (hj : j < st.stash.length) :
    SRecInv g.C M0 (sPairStep rule g w j i st) := by
  obtain ⟨⟨-, h2, -⟩, h4, -⟩ := RouteCore.coreStep_spec (rule := rule) (w := w) hv
    (ms := (st.main, st.stash)) ⟨rfl, h.1, rfl⟩ hj hi
  exact ⟨h2, h4.trans h.2⟩

theorem runSOps_recInv {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (w : Model.LogicalKey → Nat)
    (M0 : List Rec) :
    ∀ (l : List (Nat × Nat)) (st : SRoute),
      (∀ o ∈ l, o.2 + 2 ^ o.1 < st.main.length ∧ o.1 < st.stash.length) →
      SRecInv g.C M0 st → SRecInv g.C M0 (runSOps rule g w l st)
  | [], _, _, h => h
  | o :: l, st, hl, h => by
    rw [runSOps_cons]
    have ho := hl o List.mem_cons_self
    refine runSOps_recInv hv g w M0 l _ ?_ (h.step hv o.1 o.2 ho.1 ho.2)
    intro o' ho'
    rw [sPairStep_stash_length, sPairStep_main_length]
    exact hl o' (List.mem_cons_of_mem _ ho')

/-- If `2^(j+1)` divides `N`, a pair `(i, i + 2^j)` with bit `j` of `i < N` clear
lies below `N`. -/
theorem pair_lt (N i j : Nat) (hN : 2 ^ (j + 1) ∣ N) (hi : i < N) (hb : i.testBit j = false) :
    i + 2 ^ j < N := by
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  obtain ⟨c, rfl⟩ := hN
  have hdm := Nat.div_add_mod i (2 ^ j)
  set a := i / 2 ^ j with ha
  set b := i % 2 ^ j with hb'
  have hbP : b < 2 ^ j := Nat.mod_lt _ hP
  have hpar : a % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    simp only [decide_eq_false_iff_not] at hb
    omega
  have hQ : 2 ^ (j + 1) = 2 ^ j * 2 := by rw [Nat.pow_succ]
  rw [hQ] at hi ⊢
  have haQ : a < 2 * c := by
    rw [ha, Nat.div_lt_iff_lt_mul hP]
    calc i < 2 ^ j * 2 * c := hi
      _ = 2 * c * 2 ^ j := by ring
  have ha2 : a + 2 ≤ 2 * c := by omega
  have : 2 ^ j * (a + 2) ≤ 2 ^ j * (2 * c) := Nat.mul_le_mul_left _ ha2
  have e : i + 2 ^ j = 2 ^ j * (a + 1) + b := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [e]
  have h3 : 2 ^ j * (a + 2) = 2 ^ j * (a + 1) + 2 ^ j := by ring
  have h4 : 2 ^ j * (2 * c) = 2 ^ j * 2 * c := by ring
  omega

theorem pair_lt_N (g : SepGeom) (o : Nat × Nat) (ho : o ∈ g.canonicalOps) :
    o.2 + 2 ^ o.1 < g.N := by
  rw [mem_canonical] at ho
  obtain ⟨hj, hi, hb, _⟩ := ho
  apply pair_lt _ _ _ _ hi hb
  unfold SepGeom.N
  refine Dvd.dvd.mul_left ?_ _
  exact Nat.pow_dvd_pow 2 (by omega)

theorem N_eq_dU (g : SepGeom) : g.N = g.d * g.U := by
  unfold SepGeom.N SepGeom.d SepGeom.U SepGeom.k
  rw [Nat.pow_add]; ring

theorem sRouteInit_recInv (g : SepGeom) (aMain : List Bucket)
    (hl : ∀ B ∈ aMain, B.length = g.C) :
    SRecInv g.C (aMain.flatMap Bucket.recs) (sRouteInit g aMain) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    simp only [sRouteInit, List.mem_append, List.mem_replicate] at hB
    rcases hB with ⟨_, rfl⟩ | hB
    · simp [Bucket.empty]
    · exact hl B hB
  · have : (List.replicate g.U (Bucket.empty g.C)).flatMap Bucket.recs = [] := by
      rw [List.flatMap_eq_nil_iff]
      intro x hx
      rw [List.eq_of_mem_replicate hx]
      simp [Bucket.empty, Bucket.recs]
    simp [sRouteInit, List.flatMap_append, this]

theorem sRouteInit_main_length (g : SepGeom) (hd : 1 ≤ g.d) (aMain : List Bucket)
    (hlen : aMain.length = (g.d - 1) * g.U) : (sRouteInit g aMain).main.length = g.N := by
  simp only [sRouteInit, List.length_append, List.length_replicate, hlen, N_eq_dU]
  have : g.d = (g.d - 1) + 1 := by omega
  conv_rhs => rw [this]
  ring

/-- **Conservation.** The stage stashes and the radix stash of the stage-by-stage
route are a sub-multiset of A's main records. -/
theorem route_sheds_subperm {rule : CapRule} (hv : rule.Valid) (g : SepGeom) (hd : 1 ≤ g.d)
    (w : Model.LogicalKey → Nat) (aMain : List Bucket) (hlen : aMain.length = (g.d - 1) * g.U)
    (hl : ∀ B ∈ aMain, B.length = g.C) :
    ((sRouteWith rule g w aMain g.canonicalOps).stash.flatten ++
      (sRouteWith rule g w aMain g.canonicalOps).radix).Subperm (aMain.flatMap Bucket.recs) := by
  set st := runSOps rule g w g.canonicalOps (sRouteInit g aMain) with hst
  have hlen0 := sRouteInit_main_length g hd aMain hlen
  have hri : SRecInv g.C (aMain.flatMap Bucket.recs) st := by
    refine runSOps_recInv hv g w _ _ _ ?_ (sRouteInit_recInv g aMain hl)
    intro o ho
    rw [hlen0]
    refine ⟨pair_lt_N g o ho, ?_⟩
    simpa [sRouteInit] using ((mem_canonical g o).mp ho).1
  have hmlen : st.main.length = g.N := by rw [hst, runSOps_main_length, hlen0]
  have hr0 : st.radix = [] := by rw [hst, runSOps_radix]; rfl
  have hsub := radixPass_radix_subperm g w st hmlen
  rw [hr0, List.nil_append] at hsub
  obtain ⟨-, -, hstash, -, -⟩ := radixPass_congr g w st st rfl rfl
  have e : sRouteWith rule g w aMain g.canonicalOps = radixPass g w st := rfl
  rw [e, hstash]
  have h2 : (st.stash.flatten ++ st.main.flatMap Bucket.recs).Perm (aMain.flatMap Bucket.recs) :=
    List.perm_append_comm.trans hri.2
  exact ((List.subperm_append_left _).mpr hsub).trans h2.subperm

end RebuildBound.S6
