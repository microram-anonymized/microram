import RebuildBound.Proofs.D8.Home

/-!
# D8: the final finish state, home by home
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}

/-! ### Generic lemmas -/

theorem length_eq_sum (f : Rec → Nat) : ∀ (n : Nat) (l : List Rec), (∀ x ∈ l, f x < n) →
    ((List.range n).map fun v => (l.filter (fun r => f r == v)).length).sum = l.length := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := by
      cases l with
      | nil => rfl
      | cons a l => exact absurd (hl a (by simp)) (by omega)
    subst this; simp
  | succ n ih =>
    intro l hl
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 := ih (l.filter fun r => !(f r == n)) (by
      intro x hx
      obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
      have := hl x hx1
      simp at hx2
      omega)
    have h2 : ((List.range n).map fun v => (l.filter (fun r => f r == v)).length) =
        ((List.range n).map fun v =>
          ((l.filter fun r => !(f r == n)).filter (fun r => f r == v)).length) := by
      apply List.map_congr_left
      intro v hv
      have hv' := List.mem_range.1 hv
      rw [List.filter_filter]
      congr 1
      apply List.filter_congr
      intro r _
      by_cases h : f r == v
      · have : f r ≠ n := by simp at h; omega
        simp [h, this]
      · simp [h]
    rw [h2, h1]
    have := List.length_eq_length_filter_add (l := l) (fun r => f r == n)
    omega

theorem getD_map_dropTombs (M : List Bucket) (v : Nat) :
    (M.map dropTombs).getD v [] = dropTombs (M.getD v []) := by
  by_cases h : v < M.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h, dropTombs]

theorem main_filter_home (M : List Bucket) (hlen : M.length = g.T)
    (hM : ∀ j < g.T, ∀ r ∈ (M.getD j []).recs, topHome g w r = j) {v : Nat} (hv : v < g.T) :
    (M.flatMap Bucket.recs).filter (fun r => topHome g w r == v) = (M.getD v []).recs := by
  rw [flatMap_filter_single M Bucket.recs _ [] v (by rw [hlen]; exact hv)]
  · exact filter_home_self g w v _ (hM v hv)
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr
    rw [hM j' (by rw [← hlen]; exact hj') r hr]
    exact hne

/-! ### The final state -/

section fin
variable (hg : g.Valid) (hs : TopShape g unsh w inp)
include hg hs

theorem fin_parts {v : Nat} (hv : v < g.T) :
    parts g w (fin g unsh w inp) v = (Hv g unsh w inp v).1 := by
  have := (sweep_inv hg hs).shares v hv
  rw [if_pos (Nat.mod_lt _ (U_pos g))] at this
  exact this

theorem fin_main {v : Nat} (hv : v < g.T) :
    (fin g unsh w inp).main.getD v [] = (Hv g unsh w inp v).1.m :=
  congrArg HQ.m (fin_parts hg hs hv)

theorem fin_P {v : Nat} (hv : v < g.T) :
    ((fin g unsh w inp).leaves.getD (v / 2 ^ g.I) []).filter (fun r => topHome g w r == v) =
      (Hv g unsh w inp v).1.P :=
  congrArg HQ.P (fin_parts hg hs hv)

theorem fin_T {v : Nat} (hv : v < g.T) :
    (fin g unsh w inp).bcopy.filter (fun r => topHome g w r == v) = (Hv g unsh w inp v).1.T :=
  congrArg HQ.T (fin_parts hg hs hv)

theorem fin_leaves_filter {v : Nat} (hv : v < g.T) :
    (fin g unsh w inp).leaves.flatten.filter (fun r => topHome g w r == v) =
      (Hv g unsh w inp v).1.P := by
  rw [← fin_P hg hs hv, ← List.flatMap_id]
  have hF := sweep_inv hg hs
  rw [flatMap_filter_single (fin g unsh w inp).leaves id _ [] (v / 2 ^ g.I)
    (by rw [hF.good.llen]; exact div_lt_ranges hg hv)]
  · rfl
  · intro j' _ hne
    apply filter_home_nil
    intro r hr hrv
    have := hF.good.lrange j' r hr
    rw [hrv] at this
    exact hne this.symm

theorem fin_ins_filter {v : Nat} (hv : v < g.T) :
    (fin g unsh w inp).ins.filter (fun r => topHome g w r == v) = (Hv g unsh w inp v).2 := by
  have hF := sweep_inv hg hs
  have hU := U_pos g
  have hi : v % g.U < g.U := Nat.mod_lt _ hU
  have hq : v / g.U < g.D := by
    exact (Nat.div_lt_iff_lt_mul hU).2 (by rw [Nat.mul_comm, ← T_eq]; exact hv)
  rw [hF.ins]
  rw [flatMap_filter_single (List.range g.U) _ _ 0 (v % g.U) (by simpa using hi)]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_range hi, Option.getD_some]
    rw [flatMap_filter_single (List.range g.D) _ _ 0 (v / g.U) (by simpa using hq)]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_range hq, Option.getD_some]
      rw [← split_home g (v := v)]
      exact filter_home_self g w v _ (sheds_home hs hv)
    · intro q' hq' hne
      apply filter_home_nil
      intro r hr hrv
      simp only [List.getD_eq_getElem?_getD, List.getElem?_range (by simpa using hq')] at hr
      simp only [Option.getD_some] at hr
      have hlt := lt_T_of g hi (show q' < g.D by simpa using hq')
      have := sheds_home hs hlt r hr
      rw [hrv] at this
      have h2 := (mod_div_of g (q := q') hi).2
      rw [← this] at h2
      exact hne h2.symm
  · intro j' hj' hne
    apply filter_home_nil
    intro r hr hrv
    simp only [List.getD_eq_getElem?_getD, List.getElem?_range (by simpa using hj')] at hr
    simp only [Option.getD_some] at hr
    obtain ⟨q, hq', hr⟩ := List.mem_flatMap.1 hr
    have hlt := lt_T_of g (show j' < g.U by simpa using hj') (show q < g.D by simpa using hq')
    have := sheds_home hs hlt r hr
    rw [hrv] at this
    have h2 := (mod_div_of g (q := q) (show j' < g.U by simpa using hj')).1
    rw [← this] at h2
    exact hne h2.symm

end fin

end RebuildBound.D8
