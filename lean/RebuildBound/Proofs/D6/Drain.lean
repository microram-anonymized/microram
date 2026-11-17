import RebuildBound.Proofs.D6.Offer

/-!
# D6: the drain trace for two leaf orders

The drain's tested quantities are running occupancies of the output tier.
They depend on the leaves only through the leaf lengths and, after the
leftover dedup, through the number of A leftovers whose key is in the
insertion stash. `drain_trace_eq` needs exactly these.
-/

namespace RebuildBound.D6

open RebuildBound.Model

theorem drainStep_eq (acc : List (Option (Rec × Bool)) × List (Test × Nat))
    (L : List (Rec × Bool)) :
    drainStep acc L = (appendFill acc.1 L, acc.2 ++ [(.drain, occupied (appendFill acc.1 L))]) :=
  rfl

theorem foldl_drainStep_recs :
    ∀ (F : List (List (Rec × Bool))) (acc : List (Option (Rec × Bool)) × List (Test × Nat)),
      ((F.foldl drainStep acc).1.filterMap id).Perm (acc.1.filterMap id ++ F.flatten)
  := RebuildBound.LaneDrain.fold_records (fun acc => acc.1.filterMap id) drainStep
    (fun acc L => appendFill_recs acc.1 L)

theorem foldl_drainStep_trace :
    ∀ (F1 F2 : List (List (Rec × Bool)))
      (acc1 acc2 : List (Option (Rec × Bool)) × List (Test × Nat)),
      F1.map List.length = F2.map List.length → occupied acc1.1 = occupied acc2.1 →
      acc1.2 = acc2.2 → (F1.foldl drainStep acc1).2 = (F2.foldl drainStep acc2).2
  := RebuildBound.LaneDrain.fold_trace (fun acc => occupied acc.1) Prod.snd drainStep drainStep
    (by
      intro acc1 acc2 L1 L2 hl ho ht
      simp [drainStep, occupied_appendFill, ho, hl, ht])

/-- The lists the first drain appends. -/
def firstOf (st : FinState) : List (List (Rec × Bool)) :=
  (st.leaves.map fun L => L.map fun r => (r, true)) ++ [st.bcopy.map fun r => (r, false)]

/-- The tier after the first drain. -/
def dOf (st : FinState) : List (Option (Rec × Bool)) × List (Test × Nat) :=
  (firstOf st).foldl drainStep ([], [])

/-- The leftover-dedup predicate. -/
def dedupP (st : FinState) (p : Rec × Bool) : Bool :=
  !(p.2 && (st.ins.map Rec.key).contains p.1.key)

/-- The tier after the leftover dedup. -/
def tOf (st : FinState) : List (Option (Rec × Bool)) :=
  (dOf st).1.map fun s => s.filter (dedupP st)

/-- The keys of B-class tier records. -/
def bKeysOf (st : FinState) : List Model.LogicalKey :=
  (((tOf st).filterMap id).filter fun p => !p.2).map fun p => p.1.key

/-- The insertion stash minus the B-class keys. -/
def insLeft (st : FinState) : List Rec :=
  st.ins.filter fun r => !(bKeysOf st).contains r.key

theorem drain_snd (st : FinState) :
    (drain st).2 = (dOf st).2 ++
      [(.drain, occupied (appendFill (tOf st) ((insLeft st).map fun r => (r, false))))] := rfl

theorem tOf_recs (st : FinState) :
    ((tOf st).filterMap id).Perm ((firstOf st).flatten.filter (dedupP st)) := by
  unfold tOf dOf
  rw [filterMap_map_filter]
  refine List.Perm.filter _ ?_
  have := foldl_drainStep_recs (firstOf st) ([], [])
  simp only [List.filterMap_nil, List.nil_append] at this
  exact this

theorem firstOf_filter (st : FinState) :
    (firstOf st).flatten.filter (dedupP st) =
      ((st.leaves.map fun L => L.map fun r => (r, true)).map (List.filter (dedupP st))).flatten ++
        st.bcopy.map fun r => (r, false) := by
  unfold firstOf
  rw [List.flatten_append, List.filter_append, List.filter_flatten]
  congr 1
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [List.filter_eq_self]
  intro a ha
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
  simp [dedupP]

theorem occ_tOf (st : FinState) :
    occupied (tOf st) =
      (st.leaves.map fun L => (L.filter fun r => !(st.ins.map Rec.key).contains r.key).length).sum +
        st.bcopy.length := by
  rw [occupied_eq, (tOf_recs st).length_eq, firstOf_filter, List.length_append,
    List.length_flatten, List.length_map, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro L _
  simp only [Function.comp_apply, List.filter_map, List.length_map]
  rfl

theorem bKeys_perm (st : FinState) : (bKeysOf st).Perm (st.bcopy.map Rec.key) := by
  unfold bKeysOf
  have h := ((tOf_recs st).filter fun p => !p.2).map fun p => p.1.key
  refine h.trans ?_
  rw [firstOf_filter, List.filter_append]
  have h1 : (((st.leaves.map fun L => L.map fun r => (r, true)).map
      (List.filter (dedupP st))).flatten.filter fun p => !p.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_flatten, List.mem_map] at ha
    obtain ⟨_, ⟨_, ⟨L, _, rfl⟩, rfl⟩, ha⟩ := ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_filter ha)
    simp
  have h2 : ((st.bcopy.map fun r => (r, false)).filter fun p => !p.2) =
      st.bcopy.map fun r => (r, false) := by
    rw [List.filter_eq_self]
    intro a ha
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp ha
    simp
  rw [h1, h2, List.nil_append, List.map_map]
  rfl

/-- **Drain verdict.** Two finish states with the same insertion stash and B-tier
leftovers, and leaves of equal lengths that agree up to order on the records
whose key is in the insertion stash, give the same drain trace. -/
theorem drain_trace_eq (s1 s2 : FinState) (hins : s1.ins = s2.ins) (hbc : s1.bcopy = s2.bcopy)
    (hlen : s1.leaves.length = s2.leaves.length)
    (hrel : ∀ R, LeafRel (fun r => (s1.ins.map Rec.key).contains r.key)
      (s1.leaves.getD R []) (s2.leaves.getD R [])) :
    (drain s1).2 = (drain s2).2 := by
  have hlens : s1.leaves.map List.length = s2.leaves.map List.length :=
    map_eq_of_getD _ [] _ _ hlen fun R => (hrel R).1
  have hd : (dOf s1).2 = (dOf s2).2 := by
    apply foldl_drainStep_trace _ _ _ _ _ rfl rfl
    unfold firstOf
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    have : ∀ (L : List (List Rec)), L.map (List.length ∘ fun L => L.map fun r => (r, true)) =
        L.map List.length := fun L => by
      apply List.map_congr_left
      intro a _
      simp
    rw [this, this, hlens, hbc]
  have hsum : (s1.leaves.map fun L => (L.filter fun r => !(s1.ins.map Rec.key).contains r.key).length) =
      (s2.leaves.map fun L => (L.filter fun r => !(s2.ins.map Rec.key).contains r.key).length) := by
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
  have hleft : insLeft s1 = insLeft s2 := by
    unfold insLeft
    rw [← hins]
    apply List.filter_congr
    intro r _
    have e : ∀ x, (bKeysOf s1).contains x = (bKeysOf s2).contains x := by
      intro x
      rw [Bool.eq_iff_iff, contains_iff, contains_iff, (bKeys_perm s1).mem_iff,
        (bKeys_perm s2).mem_iff, hbc]
    rw [e]
  rw [drain_snd, drain_snd, hd, occupied_appendFill, occupied_appendFill, occ_tOf, occ_tOf, hsum,
    hbc, hleft]

end RebuildBound.D6
