import RebuildBound.Proofs.S6.Finish

/-!
# S6: the drain trace for two leaf orders

The general-digit counterpart of `D6/Drain.lean`; B's tier leftovers are now a
list of pages. The drain's tested quantities are running occupancies of the
output tier: they depend on the leaves only through the leaf lengths and,
after the leftover dedup, through the number of A leftovers whose key is in
the insertion stash.
-/

namespace RebuildBound.S6

open RebuildBound.Model RebuildBound.D6

theorem sDrainStep_eq (acc : List (Option (Rec × Bool)) × List (STest × Nat))
    (L : List (Rec × Bool)) :
    sDrainStep acc L =
      (appendFill acc.1 L, acc.2 ++ [(.drain, occupied (appendFill acc.1 L))]) := rfl

theorem foldl_sDrainStep_recs :
    ∀ (F : List (List (Rec × Bool))) (acc : List (Option (Rec × Bool)) × List (STest × Nat)),
      ((F.foldl sDrainStep acc).1.filterMap id).Perm (acc.1.filterMap id ++ F.flatten)
  := RebuildBound.LaneDrain.fold_records (fun acc => acc.1.filterMap id) sDrainStep
    (fun acc L => appendFill_recs acc.1 L)

theorem foldl_sDrainStep_trace :
    ∀ (F1 F2 : List (List (Rec × Bool)))
      (acc1 acc2 : List (Option (Rec × Bool)) × List (STest × Nat)),
      F1.map List.length = F2.map List.length → occupied acc1.1 = occupied acc2.1 →
      acc1.2 = acc2.2 → (F1.foldl sDrainStep acc1).2 = (F2.foldl sDrainStep acc2).2
  := RebuildBound.LaneDrain.fold_trace (fun acc => occupied acc.1) Prod.snd sDrainStep sDrainStep
    (by
      intro acc1 acc2 L1 L2 hl ho ht
      simp [sDrainStep, occupied_appendFill, ho, hl, ht])

/-- The lists the first drain appends. -/
def sFirstOf (st : SFin) : List (List (Rec × Bool)) :=
  (st.leaves.map fun L => L.map fun x => (x, true)) ++ st.bcopy.map fun L => L.map fun x => (x, false)

/-- The tier after the first drain. -/
def sDOf (st : SFin) : List (Option (Rec × Bool)) × List (STest × Nat) :=
  (sFirstOf st).foldl sDrainStep ([], [])

/-- The leftover-dedup predicate. -/
def sDedupP (st : SFin) (p : Rec × Bool) : Bool :=
  !(p.2 && (st.ins.map Rec.key).contains p.1.key)

/-- The tier after the leftover dedup. -/
def sTOf (st : SFin) : List (Option (Rec × Bool)) :=
  (sDOf st).1.map fun s => s.filter (sDedupP st)

/-- The keys of B-class tier records. -/
def sBKeysOf (st : SFin) : List Model.LogicalKey :=
  (((sTOf st).filterMap id).filter fun p => !p.2).map fun p => p.1.key

/-- The insertion stash minus the B-class keys. -/
def sInsLeft (st : SFin) : List Rec :=
  st.ins.filter fun x => !(sBKeysOf st).contains x.key

theorem sDrain_snd (st : SFin) :
    (sDrain st).2 = (sDOf st).2 ++
      [(.drain, occupied (appendFill (sTOf st) ((sInsLeft st).map fun x => (x, false))))] := rfl

theorem sTOf_recs (st : SFin) :
    ((sTOf st).filterMap id).Perm ((sFirstOf st).flatten.filter (sDedupP st)) := by
  unfold sTOf sDOf
  rw [filterMap_map_filter]
  refine List.Perm.filter _ ?_
  have := foldl_sDrainStep_recs (sFirstOf st) ([], [])
  simp only [List.filterMap_nil, List.nil_append] at this
  exact this

theorem sFirstOf_filter (st : SFin) :
    (sFirstOf st).flatten.filter (sDedupP st) =
      ((st.leaves.map fun L => L.map fun x => (x, true)).map (List.filter (sDedupP st))).flatten ++
        (st.bcopy.map fun L => L.map fun x => (x, false)).flatten := by
  unfold sFirstOf
  rw [List.flatten_append, List.filter_append, List.filter_flatten]
  congr 1
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.mem_flatten, List.mem_map] at ha
  obtain ⟨_, ⟨L, _, rfl⟩, ha⟩ := ha
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
  simp [sDedupP]

theorem occ_sTOf (st : SFin) :
    occupied (sTOf st) =
      (st.leaves.map fun L => (L.filter fun x => !(st.ins.map Rec.key).contains x.key).length).sum +
        (st.bcopy.map List.length).sum := by
  rw [occupied_eq, (sTOf_recs st).length_eq, sFirstOf_filter, List.length_append,
    List.length_flatten, List.length_flatten, List.map_map, List.map_map, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro L _
    simp only [Function.comp_apply, List.filter_map, List.length_map]
    rfl
  · apply List.map_congr_left
    intro L _
    simp

theorem sBKeys_perm (st : SFin) : (sBKeysOf st).Perm (st.bcopy.flatten.map Rec.key) := by
  unfold sBKeysOf
  have h := ((sTOf_recs st).filter fun p => !p.2).map fun p => p.1.key
  refine h.trans ?_
  rw [sFirstOf_filter, List.filter_append]
  have h1 : (((st.leaves.map fun L => L.map fun x => (x, true)).map
      (List.filter (sDedupP st))).flatten.filter fun p => !p.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_flatten, List.mem_map] at ha
    obtain ⟨_, ⟨_, ⟨L, _, rfl⟩, rfl⟩, ha⟩ := ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter ha)
    simp
  have h2 : ((st.bcopy.map fun L => L.map fun x => (x, false)).flatten.filter fun p => !p.2) =
      (st.bcopy.map fun L => L.map fun x => (x, false)).flatten := by
    rw [List.filter_eq_self]
    intro a ha
    simp only [List.mem_flatten, List.mem_map] at ha
    obtain ⟨_, ⟨L, _, rfl⟩, ha⟩ := ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    simp
  rw [h1, h2, List.nil_append, List.map_flatten, List.map_map, List.map_flatten]
  apply List.Perm.of_eq
  congr 1
  apply List.map_congr_left
  intro L _
  simp

/-- **Drain verdict.** -/
theorem sDrain_trace_eq (s1 s2 : SFin) (hins : s1.ins = s2.ins) (hbc : s1.bcopy = s2.bcopy)
    (hlen : s1.leaves.length = s2.leaves.length)
    (hrel : ∀ R, LeafRel (fun r => (s1.ins.map Rec.key).contains r.key)
      (s1.leaves.getD R []) (s2.leaves.getD R [])) :
    (sDrain s1).2 = (sDrain s2).2 := by
  have hlens : s1.leaves.map List.length = s2.leaves.map List.length :=
    map_eq_of_getD _ [] _ _ hlen fun R => (hrel R).1
  have hd : (sDOf s1).2 = (sDOf s2).2 := by
    apply foldl_sDrainStep_trace _ _ _ _ _ rfl rfl
    unfold sFirstOf
    simp only [List.map_append, List.map_map]
    have : ∀ (b : Bool) (L : List (List Rec)),
        L.map (List.length ∘ fun L => L.map fun r => (r, b)) = L.map List.length := fun b L => by
      apply List.map_congr_left
      intro a _
      simp
    rw [this, this, this, this, hlens, hbc]
  have hsum : (s1.leaves.map fun L =>
        (L.filter fun x => !(s1.ins.map Rec.key).contains x.key).length) =
      (s2.leaves.map fun L => (L.filter fun x => !(s2.ins.map Rec.key).contains x.key).length) := by
    rw [← hins]
    apply map_eq_of_getD _ [] _ _ hlen
    intro R
    have h1 := List.length_eq_length_filter_add (l := s1.leaves.getD R [])
      fun r => (s1.ins.map Rec.key).contains r.key
    have h2 := List.length_eq_length_filter_add (l := s2.leaves.getD R [])
      fun r => (s1.ins.map Rec.key).contains r.key
    have h3 := (hrel R).2.length_eq
    have h4 := (hrel R).1
    omega
  have hleft : sInsLeft s1 = sInsLeft s2 := by
    unfold sInsLeft
    rw [← hins]
    apply List.filter_congr
    intro r _
    have e : ∀ x, (sBKeysOf s1).contains x = (sBKeysOf s2).contains x := by
      intro x
      rw [Bool.eq_iff_iff, contains_iff, contains_iff, (sBKeys_perm s1).mem_iff,
        (sBKeys_perm s2).mem_iff, hbc]
    rw [e]
  rw [sDrain_snd, sDrain_snd, hd, occupied_appendFill, occupied_appendFill, occ_sTOf, occ_sTOf,
    hsum, hbc, hleft]

end RebuildBound.S6
