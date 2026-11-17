import RebuildBound.Proofs.S12.Basic

/-!
# S12: the coordinated drain

The output tier holds, up to order, A's leaf leftovers minus the keys of the
insertion stash, B's tier leftovers (all pages), and the insertion stash
minus the keys of some B-class tier records (`sDrain_perm`), as D23's
`drain_perm`.
-/

namespace RebuildBound.S12

open RebuildBound.Model RebuildBound.D23

theorem foldl_sDrainStep_perm :
    ∀ (Ls : List (List (Rec × Bool))) (acc : List (Option (Rec × Bool)) × List (STest × Nat)),
      List.Perm ((Ls.foldl sDrainStep acc).1.filterMap id) (acc.1.filterMap id ++ Ls.flatten)
  | [], acc => by simp
  | L :: Ls, acc => by
    rw [List.foldl_cons, List.flatten_cons]
    refine (foldl_sDrainStep_perm Ls (sDrainStep acc L)).trans ?_
    rw [← List.append_assoc]
    exact (appendFill_recs acc.1 L).append_right _

theorem sDrain_perm (st : SFin) : ∃ K : List Model.LogicalKey, (∀ k ∈ K, k ∈ st.bcopy.flatten.map Rec.key) ∧
    List.Perm ((sDrain st).1.filterMap id)
      (st.leaves.flatten.filter (fun r => !(st.ins.map Rec.key).contains r.key) ++
        st.bcopy.flatten ++ st.ins.filter (fun r => !K.contains r.key)) := by
  have hd := foldl_sDrainStep_perm ((st.leaves.map fun L => L.map fun r => (r, true)) ++
    st.bcopy.map fun L => L.map fun r => (r, false)) ([], [])
  simp only [List.filterMap_nil, List.nil_append, List.flatten_append] at hd
  rw [← List.map_flatten, ← List.map_flatten] at hd
  set d := (((st.leaves.map fun L => L.map fun r => (r, true)) ++
    st.bcopy.map fun L => L.map fun r => (r, false)).foldl sDrainStep ([], [])) with hd_def
  set q : Rec × Bool → Bool := fun p => !(p.2 && (st.ins.map Rec.key).contains p.1.key) with hq
  have ht : List.Perm ((d.1.map fun s => s.filter q).filterMap id)
      ((st.leaves.flatten.filter (fun r => !(st.ins.map Rec.key).contains r.key)).map
        (fun r => (r, true)) ++ st.bcopy.flatten.map (fun r => (r, false))) := by
    rw [filterMap_id_map_filter]
    refine (hd.filter q).trans ?_
    rw [List.filter_append]
    apply List.Perm.of_eq
    congr 1
    · rw [List.filter_map]
      rfl
    · rw [List.filter_eq_self]; intro p hp
      obtain ⟨r, _, rfl⟩ := List.mem_map.1 hp
      simp [hq]
  refine ⟨(((d.1.map fun s => s.filter q).filterMap id).filter fun p => !p.2).map
    fun p => p.1.key, ?_, ?_⟩
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    rw [List.mem_filter] at hp
    have h1 := ht.mem_iff.1 hp.1
    rcases List.mem_append.1 h1 with h1 | h1
    · obtain ⟨r, _, rfl⟩ := List.mem_map.1 h1
      simp at hp
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h1
      exact List.mem_map_of_mem hr
  · unfold sDrain
    simp only [sDrainStep]
    rw [filterMap_id_map_map]
    have h2 := appendFill_recs (d.1.map fun s => s.filter q)
      ((st.ins.filter fun r => !((((d.1.map fun s => s.filter q).filterMap id).filter
        fun p => !p.2).map fun p => p.1.key).contains r.key).map fun r => (r, false))
    refine (h2.map Prod.fst).trans ?_
    rw [List.map_append]
    refine ((ht.map Prod.fst).append_right _).trans ?_
    simp [List.map_map, Function.comp_def]

end RebuildBound.S12
