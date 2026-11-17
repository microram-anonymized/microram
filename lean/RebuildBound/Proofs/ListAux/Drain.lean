import RebuildBound.Proofs.ListAux.Basic

/-!
# D23: the coordinated drain

The output tier holds, up to order, A's leaf leftovers minus the keys of the
insertion stash, B's tier leftovers, and the insertion stash minus the keys
of some B-class tier records (`drain_perm`). The last filter removes nothing
when B's main and tier are key-disjoint (applied in `D23.lean`).
-/

namespace RebuildBound.D23

open RebuildBound.Model

theorem filterMap_id_map_filter {α : Type} (q : α → Bool) (B : List (Option α)) :
    (B.map fun s => s.filter q).filterMap id = (B.filterMap id).filter q := by
  exact LaneDrain.filterMap_map_filter q B

theorem filterMap_id_map_map {α β : Type} (f : α → β) (B : List (Option α)) :
    (B.map fun s => s.map f).filterMap id = (B.filterMap id).map f := by
  simp only [List.filterMap_map, List.map_filterMap, Function.comp_def, id]

theorem foldl_drainStep_perm :
    ∀ (Ls : List (List (Rec × Bool))) (acc : List (Option (Rec × Bool)) × List (Test × Nat)),
      List.Perm ((Ls.foldl drainStep acc).1.filterMap id) (acc.1.filterMap id ++ Ls.flatten)
  := LaneDrain.fold_records (fun acc => acc.1.filterMap id) drainStep
    (fun acc L => appendFill_recs acc.1 L)

theorem drain_perm (st : FinState) : ∃ K : List Model.LogicalKey, (∀ k ∈ K, k ∈ st.bcopy.map Rec.key) ∧
    List.Perm ((drain st).1.filterMap id)
      (st.leaves.flatten.filter (fun r => !(st.ins.map Rec.key).contains r.key) ++ st.bcopy ++
        st.ins.filter (fun r => !K.contains r.key)) := by
  -- the first drain
  have hd := foldl_drainStep_perm ((st.leaves.map fun L => L.map fun r => (r, true)) ++
    [st.bcopy.map fun r => (r, false)]) ([], [])
  simp only [List.filterMap_nil, List.nil_append, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil] at hd
  set d := (((st.leaves.map fun L => L.map fun r => (r, true)) ++
    [st.bcopy.map fun r => (r, false)]).foldl drainStep ([], [])) with hd_def
  set q : Rec × Bool → Bool := fun p => !(p.2 && (st.ins.map Rec.key).contains p.1.key) with hq
  have ht : List.Perm ((d.1.map fun s => s.filter q).filterMap id)
      ((st.leaves.flatten.filter (fun r => !(st.ins.map Rec.key).contains r.key)).map
        (fun r => (r, true)) ++ st.bcopy.map (fun r => (r, false))) := by
    rw [filterMap_id_map_filter]
    refine (hd.filter q).trans ?_
    rw [List.filter_append]
    apply List.Perm.of_eq
    congr 1
    · rw [← List.map_flatten, List.filter_map]
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
  · unfold drain
    simp only [drainStep]
    rw [filterMap_id_map_map]
    have h2 := appendFill_recs (d.1.map fun s => s.filter q)
      ((st.ins.filter fun r => !((((d.1.map fun s => s.filter q).filterMap id).filter
        fun p => !p.2).map fun p => p.1.key).contains r.key).map fun r => (r, false))
    refine (h2.map Prod.fst).trans ?_
    rw [List.map_append]
    refine ((ht.map Prod.fst).append_right _).trans ?_
    simp [List.map_map, Function.comp_def]
end RebuildBound.D23
