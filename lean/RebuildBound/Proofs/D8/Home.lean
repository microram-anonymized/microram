import RebuildBound.Proofs.D8.Final

/-!
# D8: what one home ends with

From the destination lemma and the merge chain: the final main bucket, the
sheds and the leaf and tier leftovers of home `v` are, up to order, the live
winners of home `v`; the bucket keeps `min(X_v, C)` of them, and the rest is
`(X_v - C)₊`.
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}

theorem hres_m_length (dk : List Model.LogicalKey) (h : HQ) : (hres dk h).m.length = h.m.length := by
  simp [hres, clear_length, dropTombs]

theorem Hv_def (v : Nat) : Hv g unsh w inp v =
    (hoff ⟨(fill (H1 g unsh w inp v).m (Sv g w inp v)).1, (H1 g unsh w inp v).P,
      (H1 g unsh w inp v).T⟩, (fill (H1 g unsh w inp v).m (Sv g w inp v)).2) := rfl

section facts
variable (hs : TopShape g unsh w inp) {v : Nat} (hv : v < g.T)
include hs hv

theorem H1_m_length : (H1 g unsh w inp v).m.length = g.C := by
  unfold H1
  rw [hres_m_length]
  show ((inp.cMain.getD v []).clear _).length = _
  rw [clear_length]
  exact hs.cLanes _ (getD_mem _ _ _ (by rw [hs.cLen]; exact hv))

/-- Conservation at one home. -/
theorem Hv_perm : List.Perm ((Hv g unsh w inp v).1.m.recs ++ (Hv g unsh w inp v).2 ++
    (Hv g unsh w inp v).1.P ++ (Hv g unsh w inp v).1.T)
    (inp.live.filter (fun r => topHome g w r == v)) := by
  have := (merge_chain (H1 g unsh w inp v).m (Sv g w inp v) (H1 g unsh w inp v).P
    (H1 g unsh w inp v).T (dest_nodup hs v hv)).1
  rw [Hv_def]
  exact this.trans (dest_perm hs v hv)

theorem Hv_nodup : (((Hv g unsh w inp v).1.m.recs ++ (Hv g unsh w inp v).2 ++
    (Hv g unsh w inp v).1.P ++ (Hv g unsh w inp v).1.T).map Rec.key).Nodup :=
  nodup_keys_perm (Hv_perm hs hv) (nodup_keys_sublist List.filter_sublist (live_nodup hs))

theorem Hv_lanes : (Hv g unsh w inp v).1.m.length = g.C := by
  have := (merge_chain (H1 g unsh w inp v).m (Sv g w inp v) (H1 g unsh w inp v).P
    (H1 g unsh w inp v).T (dest_nodup hs v hv)).2.1
  rw [Hv_def]
  rw [this]
  exact H1_m_length hs hv

theorem Hv_count : (Hv g unsh w inp v).1.m.recs.length = min (topCount g w inp.live v) g.C := by
  have hm := (merge_chain (H1 g unsh w inp v).m (Sv g w inp v) (H1 g unsh w inp v).P
    (H1 g unsh w inp v).T (dest_nodup hs v hv)).2.2.1
  have hp := (dest_perm hs v hv).length_eq
  simp only [List.length_append] at hp
  rw [Hv_def]
  rw [hm, H1_m_length hs hv]
  unfold topCount
  rw [List.countP_eq_length_filter, ← hp]
  rw [Nat.min_comm]

theorem Hv_left : (Hv g unsh w inp v).2.length + (Hv g unsh w inp v).1.P.length +
    (Hv g unsh w inp v).1.T.length = topCount g w inp.live v - g.C := by
  have hp := (Hv_perm hs hv).length_eq
  simp only [List.length_append] at hp
  have hc := Hv_count hs hv
  have : (inp.live.filter (fun r => topHome g w r == v)).length = topCount g w inp.live v := by
    unfold topCount; rw [List.countP_eq_length_filter]
  omega

theorem Hv_mem : ∀ r ∈ (Hv g unsh w inp v).1.m.recs ++ (Hv g unsh w inp v).2 ++
    (Hv g unsh w inp v).1.P ++ (Hv g unsh w inp v).1.T,
    r ∈ inp.live ∧ topHome g w r = v := by
  intro r hr
  have := (Hv_perm hs hv).mem_iff.1 hr
  obtain ⟨h1, h2⟩ := List.mem_filter.1 this
  exact ⟨h1, by simpa using h2⟩

omit hv in
theorem sheds_home {u : Nat} (hu : u < g.T) : ∀ r ∈ (Hv g unsh w inp u).2, topHome g w r = u := by
  intro r hr
  exact (Hv_mem hs hu r (by simp [hr])).2

end facts

end RebuildBound.D8
