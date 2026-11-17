import RebuildBound.Proofs.S12.Route
import RebuildBound.Proofs.S12.Radix
import Mathlib.Data.List.Nodup

/-!
# S12: the terminal radix and A's complete route

`radixStep p` replaces the `r` buckets `a 2^k + p` of tuple `p` by the radix
split's outputs, conserving records (`radixStep_SRInv`). Before the pass,
every main record agrees with its bucket on the low `k` bits; after tuple
`p`, the records of the tuple's buckets have class `a` (`radixStep_RadInv`).
So after the whole pass every main record sits at its home (`canon_home`).
For any valid schedule, ST6 gives the stage-by-stage schedule's main
(`route_home`); conservation holds for any schedule (`route_SRInv`).
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

/-! ### One tuple -/

/-- The buckets of tuple `p`. -/
def tupIdx (g : SepGeom) (p : Nat) : List Nat := (List.range g.r).map fun a => a * g.blk + p

/-- The radix split of tuple `p`. -/
def tupSplit (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) : List Bucket × List Rec :=
  radixSplit (fun x => g.cls (w x.key)) ((tupIdx g p).map fun j => st.main.getD j [])

theorem radixStep_main (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    (radixStep g w p st).main = setAll st.main ((tupIdx g p).zip (tupSplit g w p st).1) := rfl

theorem radixStep_stash (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    (radixStep g w p st).stash = st.stash := rfl

theorem radixStep_radix (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    (radixStep g w p st).radix = st.radix ++ (tupSplit g w p st).2 := rfl

theorem tupIdx_length (g : SepGeom) (p : Nat) : (tupIdx g p).length = g.r := by simp [tupIdx]

theorem tupSplit_length (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    (tupSplit g w p st).1.length = g.r := by
  rw [tupSplit, radixSplit_length]; simp [tupIdx]

theorem tupIdx_nodup (g : SepGeom) (p : Nat) : (tupIdx g p).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro a b h
  have : a * g.blk = b * g.blk := by simpa using h
  exact Nat.eq_of_mul_eq_mul_right (blk_pos g) this

theorem tup_lt (g : SepGeom) {a p : Nat} (ha : a < g.r) (hp : p < g.blk) : a * g.blk + p < g.N := by
  rw [N_eq_blk]
  have := lt_mul_of_lt hp ha
  rw [Nat.mul_comm g.blk a] at this
  omega

theorem tup_mod (g : SepGeom) {a p : Nat} (hp : p < g.blk) : (a * g.blk + p) % g.blk = p := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

theorem tup_div (g : SepGeom) {a p : Nat} (hp : p < g.blk) : (a * g.blk + p) / g.blk = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (blk_pos g), Nat.div_eq_of_lt hp, Nat.zero_add]

theorem zip_fst (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    ((tupIdx g p).zip (tupSplit g w p st).1).map Prod.fst = tupIdx g p :=
  List.map_fst_zip (by rw [tupIdx_length, tupSplit_length])

theorem zip_snd (g : SepGeom) (w : Model.LogicalKey → Nat) (p : Nat) (st : SRoute) :
    ((tupIdx g p).zip (tupSplit g w p st).1).map Prod.snd = (tupSplit g w p st).1 :=
  List.map_snd_zip (by rw [tupIdx_length, tupSplit_length])

/-- The new bucket `v`: the split's output `v / 2^k` if `v` is in tuple `p`. -/
theorem radixStep_getD (g : SepGeom) (w : Model.LogicalKey → Nat) {p : Nat} (hp : p < g.blk) (st : SRoute)
    (hlen : st.main.length = g.N) {v : Nat} (hv : v < g.N) :
    (radixStep g w p st).main.getD v [] =
      if v % g.blk = p then (tupSplit g w p st).1.getD (v / g.blk) [] else st.main.getD v [] := by
  rw [radixStep_main]
  by_cases hvp : v % g.blk = p
  · rw [ite_eq_left hvp]
    have ha : v / g.blk < g.r := by rw [Nat.div_lt_iff_lt_mul (blk_pos g)]; exact hv
    have hv' : v = v / g.blk * g.blk + p := by
      have := Nat.mod_add_div v g.blk; rw [hvp] at this; rw [Nat.mul_comm]; omega
    have hlt : v / g.blk < ((tupIdx g p).zip (tupSplit g w p st).1).length := by
      simp [tupIdx_length, tupSplit_length, ha]
    have hmem := List.getElem_mem hlt
    have h1 : (((tupIdx g p).zip (tupSplit g w p st).1)[v / g.blk]'hlt).1 = v := by
      rw [List.getElem_zip]; simp only [tupIdx, List.getElem_map, List.getElem_range]; omega
    have h2 : (((tupIdx g p).zip (tupSplit g w p st).1)[v / g.blk]'hlt).2 =
        (tupSplit g w p st).1.getD (v / g.blk) [] := by
      rw [List.getElem_zip, getD_eq_getElem' _ _ _ (by rw [tupSplit_length]; exact ha)]
    have := setAll_getD_mem [] st.main _ _ (by rw [zip_fst]; exact tupIdx_nodup g p) hmem
      (by rw [h1, hlen]; exact hv)
    rw [h1, h2] at this
    exact this
  · rw [ite_eq_right hvp]
    apply setAll_getD_not
    rw [zip_fst]
    intro hm
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hm
    exact hvp (tup_mod g hp)

theorem tupX_lanes (g : SepGeom) {aMain : List Bucket} {st : SRoute} (h : SRInv g aMain st)
    {p : Nat} (hp : p < g.blk) : ∀ B ∈ (tupIdx g p).map (fun j => st.main.getD j []), B.length = g.C := by
  intro B hB
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hB
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hj
  exact h.lanes _ (getD_mem _ _ _ (by rw [h.len]; exact tup_lt g (List.mem_range.1 ha) hp))

theorem radixStep_SRInv {g : SepGeom} {w : Model.LogicalKey → Nat} {aMain : List Bucket} {st : SRoute}
    {p : Nat} (hp : p < g.blk) (h : SRInv g aMain st) : SRInv g aMain (radixStep g w p st) where
  len := by rw [radixStep_main, setAll_length, h.len]
  lanes := by
    rw [radixStep_main]
    apply setAll_mem (fun B : Bucket => B.length = g.C) _ _ h.lanes
    intro q hq
    have := List.of_mem_zip hq
    exact radixSplit_lanes _ _ g.C (tupX_lanes g h hp) _ this.2
  slen := by rw [radixStep_stash]; exact h.slen
  perm := by
    rw [radixStep_main, radixStep_stash, radixStep_radix]
    have hs := setAll_perm st.main ((tupIdx g p).zip (tupSplit g w p st).1)
      (by rw [zip_fst]; exact tupIdx_nodup g p) (by
        intro q hq
        have := (List.of_mem_zip hq).1
        obtain ⟨a, ha, he⟩ := List.mem_map.1 this
        rw [h.len, ← he]; exact tup_lt g (List.mem_range.1 ha) hp)
    have e : ((tupIdx g p).zip (tupSplit g w p st).1).map (fun q => st.main.getD q.1 []) =
        (tupIdx g p).map (fun j => st.main.getD j []) := by
      have : ((tupIdx g p).zip (tupSplit g w p st).1).map (fun q => st.main.getD q.1 []) =
          (((tupIdx g p).zip (tupSplit g w p st).1).map Prod.fst).map (fun j => st.main.getD j []) := by
        rw [List.map_map]; rfl
      rw [this, zip_fst]
    rw [e, zip_snd] at hs
    have hr := radixSplit_perm (fun x => g.cls (w x.key)) ((tupIdx g p).map fun j => st.main.getD j [])
    rw [List.perm_iff_count]; intro x
    have c1 := hs.count_eq x
    have c2 := hr.count_eq x
    have c3 := h.perm.count_eq x
    unfold tupSplit at c1 ⊢
    simp only [List.count_append] at c1 c2 c3 ⊢
    omega

/-! ### The radix invariant -/

/-- Before tuple `n`: low `k` bits at their bucket's, and the class at the
bucket's block for the tuples already split. -/
def RadInv (g : SepGeom) (w : Model.LogicalKey → Nat) (n : Nat) (st : SRoute) : Prop :=
  ∀ v < g.N, ∀ x ∈ (st.main.getD v []).recs, w x.key % g.blk = v % g.blk ∧
    (v % g.blk < n → g.cls (w x.key) = v / g.blk)

theorem radixStep_RadInv {g : SepGeom} {w : Model.LogicalKey → Nat} {aMain : List Bucket}
    {st : SRoute} {n : Nat} (hn : n < g.blk) (h : SRInv g aMain st) (hR : RadInv g w n st) :
    RadInv g w (n + 1) (radixStep g w n st) := by
  intro v hv x hx
  rw [radixStep_getD g w hn st h.len hv] at hx
  by_cases hvp : v % g.blk = n
  · rw [ite_eq_left hvp] at hx
    have ha : v / g.blk < g.r := by rw [Nat.div_lt_iff_lt_mul (blk_pos g)]; exact hv
    have hc := radixSplit_cls (fun x => g.cls (w x.key))
      ((tupIdx g n).map fun j => st.main.getD j []) (by simp [tupIdx, ha]) x hx
    refine ⟨?_, fun _ => hc⟩
    have hm : x ∈ (tupSplit g w n st).1.flatMap Bucket.recs := by
      apply List.mem_flatMap.2
      exact ⟨_, getD_mem _ _ _ (by rw [tupSplit_length]; exact ha), hx⟩
    have hm2 := (radixSplit_perm (fun x => g.cls (w x.key))
      ((tupIdx g n).map fun j => st.main.getD j [])).mem_iff.1 (List.mem_append_left _ hm)
    obtain ⟨B, hB, hxB⟩ := List.mem_flatMap.1 hm2
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hB
    obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hj
    have := (hR _ (tup_lt g (List.mem_range.1 ha') hn) x hxB).1
    rw [this, tup_mod g hn, hvp]
  · rw [ite_eq_right hvp] at hx
    have := hR v hv x hx
    exact ⟨this.1, fun hlt => this.2 (by omega)⟩

theorem radixFold_inv {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {aMain : List Bucket}
    {st : SRoute} (h : SRInv g aMain st) (hR : RadInv g w 0 st) : ∀ n ≤ g.blk,
    SRInv g aMain ((List.range n).foldl (fun st p => radixStep g w p st) st) ∧
      RadInv g w n ((List.range n).foldl (fun st p => radixStep g w p st) st)
  | 0, _ => ⟨h, hR⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := radixFold_inv hg h hR n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨radixStep_SRInv (by omega) h1, radixStep_RadInv (by omega) h1 h2⟩

theorem radixPass_SRInv {g : SepGeom} {w : Model.LogicalKey → Nat} {aMain : List Bucket} {st : SRoute}
    (h : SRInv g aMain st) : SRInv g aMain (radixPass g w st) := by
  unfold radixPass
  split
  · have key : ∀ n ≤ g.blk, SRInv g aMain ((List.range n).foldl (fun st p => radixStep g w p st) st) := by
      intro n
      induction n with
      | zero => intro _; exact h
      | succ n ih =>
        intro hn
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact radixStep_SRInv (by omega) (ih (by omega))
    exact key g.blk (Nat.le_refl _)
  · exact h

theorem low_of_lowOK {w : Model.LogicalKey → Nat} {n v : Nat} {x : Rec} (h : lowOK w n v x) :
    w x.key % 2 ^ n = v % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hb : b < n
  · simp [hb, h b hb]
  · simp [hb]

/-- After the radix pass, every main record sits at its home. -/
theorem radixPass_home {g : SepGeom} (hg : g.Valid) {w : Model.LogicalKey → Nat} {aMain : List Bucket}
    {st : SRoute} (h : SRInv g aMain st) (hlow : LowInv g w g.k st) :
    ∀ v < g.N, ∀ x ∈ ((radixPass g w st).main.getD v []).recs, sHome g w x = v := by
  have hR : RadInv g w 0 st := by
    intro v hv x hx
    exact ⟨low_of_lowOK (hlow v hv x hx).1, fun h => absurd h (Nat.not_lt_zero _)⟩
  intro v hv x hx
  unfold radixPass at hx
  split at hx
  · have := (radixFold_inv hg h hR g.blk (Nat.le_refl _)).2 v hv x hx
    unfold sHome SepGeom.homeOf
    have e1 : g.cls (w x.key) = v / g.blk := this.2 (Nat.mod_lt _ (blk_pos g))
    unfold SepGeom.blk at this e1
    rw [this.1, e1]
    exact Nat.mod_add_div v _
  · have hr1 : g.r = 1 := by have := hg.1; omega
    have hl := low_of_lowOK (hlow v hv x hx).1
    unfold sHome SepGeom.homeOf SepGeom.cls
    rw [hr1, Nat.mod_one, Nat.mul_zero, Nat.add_zero, hl]
    apply Nat.mod_eq_of_lt
    have : g.N = 2 ^ g.k := by unfold SepGeom.N; rw [hr1, Nat.one_mul]
    omega

/-! ### A's complete route -/

theorem canon_route {rule : CapRule} (hv : rule.Valid) {g : SepGeom} (hg : g.Valid) (w : Model.LogicalKey → Nat)
    {aMain : List Bucket} (hlen : aMain.length = (g.d - 1) * g.U)
    (hlanes : ∀ B ∈ aMain, B.length = g.C) :
    ∀ v < g.N, ∀ x ∈ ((sRouteWith rule g w aMain g.canonicalOps).main.getD v []).recs,
      sHome g w x = v := by
  have := canonUpTo_inv hv g hg w aMain hlen hlanes g.k (Nat.le_refl _)
  rw [← canonicalOps_eq] at this
  exact radixPass_home hg this.1 this.2

theorem route_SRInv {rule : CapRule} (hv : rule.Valid) {g : SepGeom} (hg : g.Valid) (w : Model.LogicalKey → Nat)
    {aMain : List Bucket} (hlen : aMain.length = (g.d - 1) * g.U)
    (hlanes : ∀ B ∈ aMain, B.length = g.C) {ops : List (Nat × Nat)}
    (hops : List.Perm ops g.canonicalOps) :
    SRInv g aMain (sRouteWith rule g w aMain ops) :=
  radixPass_SRInv (runSOps_SRInv hv ops _ (fun _ ho => hops.mem_iff.1 ho)
    (sRouteInit_SRInv g hg aMain hlen hlanes))

end RebuildBound.S12
