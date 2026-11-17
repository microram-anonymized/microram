import RebuildBound.Proofs.D8.Fin
import RebuildBound.Proofs.ListAux.Occupancy

/-!
# D8: the epilogue

The output tier is, up to order, the leaf leftovers, the B-tier leftovers and
the merge stash, with nothing removed by the leftover dedup; together they
number exactly `topExcess` (`left_length`).
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}

theorem live_not_tomb {r : Rec} (h : r ∈ inp.live) : r.tomb = false := by
  have := (List.mem_filter.1 h).2
  simpa using this

section tier
variable (hg : g.Valid) (hs : TopShape g unsh w inp)
include hg hs

/-- Everything left over, in one list. -/
abbrev leftL (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs) : List Rec :=
  (fin g unsh w inp).leaves.flatten ++ (fin g unsh w inp).bcopy ++ (fin g unsh w inp).ins

theorem leftL_filter {v : Nat} (hv : v < g.T) :
    (leftL g unsh w inp).filter (fun r => topHome g w r == v) =
      (Hv g unsh w inp v).1.P ++ (Hv g unsh w inp v).1.T ++ (Hv g unsh w inp v).2 := by
  rw [List.filter_append, List.filter_append, fin_leaves_filter hg hs hv, fin_T hg hs hv,
    fin_ins_filter hg hs hv]

theorem leftL_mem : ∀ r ∈ leftL g unsh w inp, r ∈ inp.live := by
  intro r hr
  have hv := home_lt g w r
  have : r ∈ (leftL g unsh w inp).filter (fun x => topHome g w x == topHome g w r) :=
    List.mem_filter.2 ⟨hr, by simp⟩
  rw [leftL_filter hg hs hv] at this
  refine (Hv_mem hs hv r ?_).1
  simp only [List.mem_append] at this ⊢
  tauto

omit hg in
theorem sh_P_disjoint {v : Nat} (hv : v < g.T) :
    ∀ r ∈ (Hv g unsh w inp v).1.P, r.key ∉ (Hv g unsh w inp v).2.map Rec.key := by
  have hn := Hv_nodup hs hv
  have hsub : List.Sublist ((Hv g unsh w inp v).2 ++ (Hv g unsh w inp v).1.P)
      ((Hv g unsh w inp v).1.m.recs ++ (Hv g unsh w inp v).2 ++ (Hv g unsh w inp v).1.P ++
        (Hv g unsh w inp v).1.T) :=
    (((List.sublist_append_right _ _).append (List.Sublist.refl _))).trans
      (List.sublist_append_left _ _)
  exact keys_disjoint_of_nodup (nodup_keys_sublist hsub hn)

omit hg in
theorem sh_T_disjoint {v : Nat} (hv : v < g.T) :
    ∀ r ∈ (Hv g unsh w inp v).1.T, r.key ∉ (Hv g unsh w inp v).2.map Rec.key := by
  have hn := Hv_nodup hs hv
  have hsub : List.Sublist ((Hv g unsh w inp v).2 ++ (Hv g unsh w inp v).1.T)
      ((Hv g unsh w inp v).1.m.recs ++ (Hv g unsh w inp v).2 ++ (Hv g unsh w inp v).1.P ++
        (Hv g unsh w inp v).1.T) :=
    (((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)).append
      (List.Sublist.refl _))
  exact keys_disjoint_of_nodup (nodup_keys_sublist hsub hn)

theorem ins_disjoint_leaves : ∀ r ∈ (fin g unsh w inp).leaves.flatten,
    r.key ∉ (fin g unsh w inp).ins.map Rec.key := by
  intro r hr hk
  obtain ⟨x, hx, he⟩ := List.mem_map.1 hk
  have hv := home_lt g w r
  have hr' : r ∈ (Hv g unsh w inp (topHome g w r)).1.P := by
    rw [← fin_leaves_filter hg hs hv]; exact List.mem_filter.2 ⟨hr, by simp⟩
  have hx' : x ∈ (Hv g unsh w inp (topHome g w r)).2 := by
    rw [← fin_ins_filter hg hs hv]
    exact List.mem_filter.2 ⟨hx, by simp [home_of_key g w he]⟩
  exact sh_P_disjoint hs hv r hr' (by rw [← he]; exact List.mem_map_of_mem hx')

theorem ins_disjoint_bcopy : ∀ r ∈ (fin g unsh w inp).bcopy,
    r.key ∉ (fin g unsh w inp).ins.map Rec.key := by
  intro r hr hk
  obtain ⟨x, hx, he⟩ := List.mem_map.1 hk
  have hv := home_lt g w r
  have hr' : r ∈ (Hv g unsh w inp (topHome g w r)).1.T := by
    rw [← fin_T hg hs hv]; exact List.mem_filter.2 ⟨hr, by simp⟩
  have hx' : x ∈ (Hv g unsh w inp (topHome g w r)).2 := by
    rw [← fin_ins_filter hg hs hv]
    exact List.mem_filter.2 ⟨hx, by simp [home_of_key g w he]⟩
  exact sh_T_disjoint hs hv r hr' (by rw [← he]; exact List.mem_map_of_mem hx')

theorem tier_perm : List.Perm ((drain (fin g unsh w inp)).1.filterMap id)
    (leftL g unsh w inp) := by
  obtain ⟨K, hK, hp⟩ := drain_perm (fin g unsh w inp)
  rw [filter_keys_self _ _ (ins_disjoint_leaves hg hs)] at hp
  rw [filter_keys_self (fin g unsh w inp).ins K] at hp
  · exact hp
  · intro r hr hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 (hK _ hk)
    exact ins_disjoint_bcopy hg hs r' hr' (he ▸ List.mem_map_of_mem hr)

theorem left_length : (leftL g unsh w inp).length = topExcess g w inp := by
  have h := length_eq_sum (fun r => topHome g w r) g.T (leftL g unsh w inp)
    (fun x _ => home_lt g w x)
  rw [← h]
  unfold topExcess
  congr 1
  apply List.map_congr_left
  intro v hv
  have hv' := List.mem_range.1 hv
  rw [leftL_filter hg hs hv']
  have := Hv_left hs hv'
  simp only [List.length_append]
  omega

theorem drain_trace_le : ∀ e ∈ (drain (fin g unsh w inp)).2, e.1 = .drain ∧ e.2 ≤ topExcess g w inp := by
  have hl := left_length hg hs
  simp only [List.length_append] at hl
  apply RebuildBound.D4b.drain_bound
  · omega
  · intro p
    have := List.length_filter_le (fun r => !((fin g unsh w inp).ins.map Rec.key).contains r.key)
      (fin g unsh w inp).leaves.flatten
    have := List.length_filter_le p (fin g unsh w inp).ins
    omega

end tier

end RebuildBound.D8
