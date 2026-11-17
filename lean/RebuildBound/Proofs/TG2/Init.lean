import RebuildBound.Proofs.TG2.Hist

/-!
# IG2 helpers: the initialization's scatter

For a list `input` distinct by key with `|input| ≤ (C/2) T`, `initMain g input` is a
valid context (`TCtx`) for the starting buckets `p x = idx(x) / (C/2)` (the scatter):
`flat (initMain g input) = input`; every record of bucket `i` is input record
`i (C/2) + j`, `j < C/2`; at most `C/2` keys start at every node.
-/

open scoped ENNReal NNReal

namespace RebuildBound.TG2

open RebuildBound.Model RebuildBound.Spec RebuildBound.G2 RebuildBound.SG2

theorem filterMap_take_drop (input : List Rec) :
    ∀ (m s : ℕ), (List.range m).filterMap (fun l => input[s + l]?) = (input.drop s).take m
  | 0, s => by simp
  | m + 1, s => by
    have ih := filterMap_take_drop input m (s + 1)
    rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    have hf : ((fun l => input[s + l]?) ∘ Nat.succ) = fun l => input[s + 1 + l]? := by
      funext l; simp only [Function.comp]; congr 1; omega
    rw [hf, ih]
    simp only [Nat.add_zero]
    rcases h : input[s]? with _ | x
    · have hs : input.length ≤ s := by simpa using h
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le hs]
      simp
    · obtain ⟨hs, hx⟩ := List.getElem?_eq_some_iff.1 h
      rw [List.drop_eq_getElem_cons hs, List.take_succ_cons, hx]

/-- The records of bucket `i` of the scatter. -/
theorem initMain_recs (g : TPGeom) (input : List Rec) {i : ℕ} (hi : i < g.T) :
    ((initMain g input).getD i []).recs = (input.drop (i * (g.C / 2))).take (g.C / 2) := by
  have hl : i < (initMain g input).length := by simpa [initMain] using hi
  rw [List.getD_eq_getElem _ _ hl]
  simp only [initMain, List.getElem_map, List.getElem_range]
  unfold Bucket.recs
  rw [List.filterMap_map]
  obtain ⟨c2, hc2⟩ : ∃ c2, g.C = g.C / 2 + c2 := ⟨g.C - g.C / 2, by omega⟩
  have hr : List.range g.C = List.range (g.C / 2) ++ (List.range c2).map (g.C / 2 + ·) := by
    rw [← List.range_add, ← hc2]
  rw [hr, List.filterMap_append]
  have h2 : List.filterMap (id ∘ fun l => if l < g.C / 2 then input[i * (g.C / 2) + l]? else none)
      (List.map (fun x => g.C / 2 + x) (List.range c2)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 ha
    simp
  rw [h2, List.append_nil, ← filterMap_take_drop input (g.C / 2) (i * (g.C / 2))]
  apply List.filterMap_congr
  intro l hl
  have := List.mem_range.1 hl
  simp [this]

theorem flatMap_take_drop (input : List Rec) (m : ℕ) : ∀ n,
    ((List.range n).flatMap fun i => (input.drop (i * m)).take m) = input.take (n * m)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_take_drop input m n, Nat.succ_mul,
      List.take_add]
    simp

theorem flat_initMain (g : TPGeom) (input : List Rec) (hlen : input.length ≤ g.C / 2 * g.T) :
    flat (initMain g input) = input := by
  have : flat (initMain g input) = (List.range g.T).flatMap
      fun i => (input.drop (i * (g.C / 2))).take (g.C / 2) := by
    unfold flat
    conv_lhs => unfold initMain
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro i hi
    have := initMain_recs g input (List.mem_range.1 hi)
    rw [← this, List.getD_eq_getElem _ _ (by simpa [initMain] using List.mem_range.1 hi)]
    simp [initMain]
  rw [this, flatMap_take_drop, List.take_of_length_le]
  rw [Nat.mul_comm]; exact hlen

/-- The scatter's starting bucket of a key. -/
def initPos (input : List Rec) (g : TPGeom) : Model.LogicalKey → ℕ :=
  fun x => (input.map Rec.key).idxOf x / (g.C / 2)

theorem tctx_of_initLaw {g : TPGeom} {L : TPJobLaw g} {input : List Rec} (hL : InitLaw L input) :
    TCtx g (initPos input g) L.KA (initMain g input) [] := by
  have hlen := hL.count
  have hflat := flat_initMain g input hlen
  have hnd := hL.nodup
  refine ⟨by simp [initMain], ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    simp only [initMain] at hB
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hB
    simp
  · rw [List.append_nil, hflat]; exact hnd
  · intro i hi r hr
    rw [initMain_recs g input hi] at hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
    simp only [List.length_take, List.length_drop] at hj
    have hjm : j < g.C / 2 := by omega
    have hn : i * (g.C / 2) + j < input.length := by omega
    have hidx : (input.map Rec.key).idxOf ((input[i * (g.C / 2) + j]'hn).key) =
        i * (g.C / 2) + j := by
      have := hnd.idxOf_getElem (i * (g.C / 2) + j) (by simpa using hn)
      simpa using this
    simp only [initPos, List.getElem_take, List.getElem_drop]
    rw [hidx, Nat.mul_comm i, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hjm]
    simp
  · rw [List.append_nil, hflat]; exact hL.keys
  · intro x hx
    rw [← hL.keys, List.mem_toFinset] at hx
    have h1 := List.idxOf_lt_length_of_mem hx
    simp only [List.length_map] at h1
    unfold initPos
    by_cases hm : g.C / 2 = 0
    · exfalso; rw [hm] at hlen; omega
    · rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hm)]
      exact lt_of_lt_of_le h1 (hlen.trans (Nat.mul_comm _ _).le)

/-- At most `C/2` keys start at every node. -/
theorem init_count {g : TPGeom} (hk : 1 ≤ g.k) {L : TPJobLaw g} {input : List Rec}
    (hL : InitLaw L input) (v : RNode 2 (g.k - 1)) :
    (((Finset.univ.filter (fun x : {x // x ∈ L.KA} =>
        tPos (g.k - 1) (initPos input g) L.KA x = v)).card : ℕ) : ℝ≥0) ≤
      ((g.C / 2 : ℕ) : ℝ≥0) := by
  have hC := tctx_of_initLaw hL
  have hlen := hL.count
  have hmem : ∀ x ∈ L.KA, x ∈ input.map Rec.key := fun x hx => by
    have h := hL.keys
    rw [← h] at hx
    exact List.mem_toFinset.1 hx
  have hnat : (Finset.univ.filter (fun x : {x // x ∈ L.KA} =>
      tPos (g.k - 1) (initPos input g) L.KA x = v)).card ≤ g.C / 2 := by
    by_cases hm : g.C / 2 = 0
    · rw [Finset.card_eq_zero.2]
      · exact Nat.zero_le _
      · rw [Finset.filter_eq_empty_iff]
        intro x _
        exfalso
        have h1 := List.idxOf_lt_length_of_mem (hmem x.val x.prop)
        simp only [List.length_map] at h1
        rw [hm] at hlen; omega
    · have hmpos : 0 < g.C / 2 := Nat.pos_of_ne_zero hm
      set u0 := tflat (g.k - 1) v
      calc _ ≤ (Finset.Ico (u0 * (g.C / 2)) (u0 * (g.C / 2) + g.C / 2)).card := by
            refine Finset.card_le_card_of_injOn
              (fun x : {x // x ∈ L.KA} => (input.map Rec.key).idxOf x.val) ?_ ?_
            · intro x hx
              have hx' := (Finset.mem_filter.1 hx).2
              have hq : initPos input g x.val = u0 := by
                have h2 := hC.pos x.val x.prop
                have h3 := tflat_tnode (g.k - 1) (u := initPos input g x.val)
                  (by rw [← T_eq hk]; exact h2)
                have h4 : tnode (g.k - 1) (initPos input g x.val) = v := hx'
                rw [h4] at h3
                exact h3.symm
              unfold initPos at hq
              simp only [Finset.coe_Ico, Set.mem_Ico]
              refine ⟨?_, ?_⟩
              · rw [← hq]; exact Nat.div_mul_le_self _ _
              · rw [← hq]; exact Nat.lt_div_mul_add hmpos
            · intro x hx y hy hxy
              exact Subtype.ext ((List.idxOf_inj (hmem x.val x.prop)).1 hxy)
        _ = g.C / 2 := by simp
  exact_mod_cast hnat

end RebuildBound.TG2
