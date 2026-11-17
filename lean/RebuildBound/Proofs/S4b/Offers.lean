import RebuildBound.Proofs.S4b.Basic

/-!
# S4b, the offers and the insertion fills

Each step of B's insertion changes one home. `HomeOK` survives every fill;
a record left out of a fill is shut out of a full home (`Blocks`); a full home
stays full under both offers and gains no key from outside the offered set.
-/

namespace RebuildBound.S4b

open RebuildBound.Model
open RebuildBound.D4b (nodup_of_subperm getD_set_self getD_set_of_ne getD_sublist_flatten
  mem_flatten_getD flatten_set_sublist fill_snd fill_of_full fill_recs_perm keys_eq mem_keys
  free_zero_of_full fill_placed_eq mem_getD_set_self' mem_getD_set' length_filter_split)

section
variable {g : SepGeom} {w : Model.LogicalKey → Nat} {inp : SInputs}

theorem homeOK_clear {v : Nat} {B : Bucket} (h : HomeOK g w inp v B) (p : Model.LogicalKey → Bool) :
    HomeOK g w inp v (B.clear p) where
  len := by rw [D1Lemmas.clear_length]; exact h.len
  home r hr := h.home r (by rw [D1Lemmas.clear_recs] at hr; exact (List.mem_filter.1 hr).1)
  wk r hr := h.wk r (by rw [D1Lemmas.clear_recs] at hr; exact (List.mem_filter.1 hr).1)
  nd := by
    rw [keys_eq, D1Lemmas.clear_recs]
    exact h.nd.sublist (List.filter_sublist.map _)

theorem homeOK_fill {v : Nat} {B : Bucket} (h : HomeOK g w inp v B) (L : List Rec)
    (hL : ∀ r ∈ L, sHome g w r = v ∧ r.key ∈ WK inp) (hnd : (L.map Rec.key).Nodup)
    (hdis : ∀ r ∈ L, r.key ∉ B.keys) : HomeOK g w inp v (fill B L).1 := by
  have hp := fill_recs_perm B L
  have hmem : ∀ r ∈ Bucket.recs (fill B L).1, r ∈ B.recs ∨ r ∈ L := by
    intro r hr
    rcases List.mem_append.1 (hp.subset hr) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_of_mem_take h1)
  refine ⟨by rw [D1Lemmas.fill_length]; exact h.len, ?_, ?_, ?_⟩
  · intro r hr
    rcases hmem r hr with h1 | h1
    · exact h.home r h1
    · exact (hL r h1).1
  · intro r hr
    rcases hmem r hr with h1 | h1
    · exact h.wk r h1
    · exact (hL r h1).2
  · rw [keys_eq, (hp.map Rec.key).nodup_iff, List.map_append, List.nodup_append]
    refine ⟨h.nd, hnd.sublist ((List.take_sublist _ _).map _), ?_⟩
    intro a ha b hb e
    subst e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
    exact hdis r (List.mem_of_mem_take hr) ha

/-- A record of `L` that `fill` leaves out of a `C`-lane bucket is shut out of
the filled, full bucket. -/
theorem blocks_fill {B : Bucket} (hlen : B.length = g.C) {L : List Rec} {r : Rec}
    (hr : r ∈ L) (hnot : r.key ∉ B.keys)
    (hnt : r.key ∉ (L.take (min L.length (B.countP (·.isNone)))).map Rec.key) :
    Blocks g r.key (fill B L).1 := by
  have hlt : min L.length (B.countP (·.isNone)) < L.length := by
    by_contra hc
    rw [List.take_of_length_le (by omega)] at hnt
    exact hnt (List.mem_map_of_mem hr)
  have hm : min L.length (B.countP (·.isNone)) = B.countP (·.isNone) := by omega
  refine ⟨?_, ?_⟩
  · rw [D1Lemmas.fill_recs_length, hm]
    have := D1Lemmas.countP_isNone_add B
    omega
  · intro hk
    rw [keys_eq] at hk
    have hk2 := ((fill_recs_perm B L).map Rec.key).subset hk
    rw [List.map_append] at hk2
    rcases List.mem_append.1 hk2 with h1 | h1
    · exact hnot h1
    · exact hnt h1

/-- A fill of a full bucket changes nothing. -/
theorem fill_of_blocks {B : Bucket} (hlen : B.length = g.C) {x : Model.LogicalKey} (h : Blocks g x B)
    (L : List Rec) : fill B L = (B, L) :=
  fill_of_full B L (free_zero_of_full B (by rw [h.1, hlen]))

theorem not_mem_keys_fill {B : Bucket} {L : List Rec} {x : Model.LogicalKey} (hB : x ∉ B.keys)
    (hL : ∀ r ∈ L, r.key ≠ x) : x ∉ Bucket.keys (fill B L).1 := by
  intro hk
  rw [keys_eq] at hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk
  rcases List.mem_append.1 ((fill_recs_perm B L).subset hr) with h1 | h1
  · exact hB (List.mem_map_of_mem h1)
  · exact hL r (List.mem_of_mem_take h1) rfl

/-- Offer B's candidates `fc` to a full home: it stays full. -/
theorem full_fill_clear {v : Nat} {B : Bucket} (hok : HomeOK g w inp v B)
    (hfull : B.recs.length = g.C) (fc : List Rec) :
    (Bucket.recs (fill (B.clear fun key => (fc.map Rec.key).contains key) fc).1).length =
      g.C := by
  set B' := B.clear fun key => (fc.map Rec.key).contains key with hB'
  have hrecs : B'.recs = B.recs.filter fun r => !(fc.map Rec.key).contains r.key :=
    D1Lemmas.clear_recs _ B
  have hsplit := length_filter_split (fun r : Rec => (fc.map Rec.key).contains r.key) B.recs
  have hq : (B.recs.filter fun r => (fc.map Rec.key).contains r.key).length ≤ fc.length := by
    have hnd : ((B.recs.filter fun r => (fc.map Rec.key).contains r.key).map Rec.key).Nodup :=
      hok.nd.sublist (List.filter_sublist.map _)
    have hsub : ((B.recs.filter fun r => (fc.map Rec.key).contains r.key).map Rec.key) ⊆
        fc.map Rec.key := by
      intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
      simpa using (List.mem_filter.1 hr).2
    have := (hnd.subperm hsub).length_le
    simpa using this
  have hB'len : B'.length = g.C := by rw [hB', D1Lemmas.clear_length]; exact hok.len
  have hfree := D1Lemmas.countP_isNone_add B'
  rw [D1Lemmas.fill_recs_length, hrecs]
  rw [hrecs] at hfree
  omega

end

/-! ### The offers, unfolded -/

/-- A's candidates for home `ci`. -/
def aCand (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) : List Rec :=
  (st.leaves.getD (ci / 2 ^ g.I) []).filter fun r => sHome g w r == ci

/-- A's candidates whose key is not in main. -/
def aStale (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) : List Rec :=
  (aCand g w ci st).filter fun r => !(st.main.getD ci []).keys.contains r.key

/-- The consumed keys. -/
def aGone (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) : List Model.LogicalKey :=
  ((aCand g w ci st).filter (fun r => (st.main.getD ci []).keys.contains r.key) ++
    (aStale g w ci st).take ((aStale g w ci st).length -
      (fill (st.main.getD ci []) (aStale g w ci st)).2.length)).map Rec.key

theorem sOfferA_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) :
    sOfferA g w ci st = { st with
      main := st.main.set ci (fill (st.main.getD ci []) (aStale g w ci st)).1
      leaves := st.leaves.set (ci / 2 ^ g.I)
        ((st.leaves.getD (ci / 2 ^ g.I) []).filter fun r => !(aGone g w ci st).contains r.key) } :=
  rfl

/-- B's tier candidates of page `pg` for home `ci`. -/
def bFc (g : SepGeom) (w : Model.LogicalKey → Nat) (ci pg : Nat) (st : SFin) : List Rec :=
  (st.bcopy.getD pg []).filter fun r => sHome g w r == ci

/-- Home `ci` with the lanes of the page's candidate keys freed. -/
def bClr (g : SepGeom) (w : Model.LogicalKey → Nat) (ci pg : Nat) (st : SFin) : Bucket :=
  (st.main.getD ci []).clear fun key => ((bFc g w ci pg st).map Rec.key).contains key

/-- The placed keys. -/
def bPlaced (g : SepGeom) (w : Model.LogicalKey → Nat) (ci pg : Nat) (st : SFin) : List Model.LogicalKey :=
  ((bFc g w ci pg st).take ((bFc g w ci pg st).length -
    (fill (bClr g w ci pg st) (bFc g w ci pg st)).2.length)).map Rec.key

theorem sOfferPage_eq (g : SepGeom) (w : Model.LogicalKey → Nat) (ci : Nat) (st : SFin) (pg : Nat) :
    sOfferPage g w ci st pg = { st with
      main := st.main.set ci (fill (bClr g w ci pg st) (bFc g w ci pg st)).1
      bcopy := st.bcopy.set pg
        ((st.bcopy.getD pg []).filter fun r => !(bPlaced g w ci pg st).contains r.key) } :=
  rfl

end RebuildBound.S4b
