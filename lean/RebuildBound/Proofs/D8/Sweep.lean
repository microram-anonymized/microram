import RebuildBound.Proofs.D8.Dest

/-!
# D8: the sweep home by home

`parts g w st v` is the share of home `v` in a finish state: main bucket `v`,
the leaf candidates of home `v` and the B-tier candidates of home `v`. The
resolution and the offers at destination `ci` act on `parts ci` as `hres` and
`hoff` and leave every other home's share alone, because a record's home is a
function of its key. Hence `topDest` acts on `parts ci` by `hvisit`.
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable (g : TopGeom) (w : Model.LogicalKey → Nat)

/-- The share of home `v` in a finish state. -/
def parts (st : FinState) (v : Nat) : HQ :=
  ⟨st.main.getD v [], (st.leaves.getD (v / 2 ^ g.I) []).filter (fun r => topHome g w r == v),
   st.bcopy.filter (fun r => topHome g w r == v)⟩

/-- The structural invariant of a finish state: `T` main buckets, `2^rho`
leaves, and every leaf record in its range. -/
structure Good (st : FinState) : Prop where
  len : st.main.length = g.T
  llen : st.leaves.length = g.ranges
  lrange : ∀ R, ∀ r ∈ st.leaves.getD R [], topHome g w r / 2 ^ g.I = R

variable {g w}

theorem not_contains_of_home (g : TopGeom) (w : Model.LogicalKey → Nat) {ci v : Nat} (hne : v ≠ ci)
    (L : List Rec) (hL : ∀ r ∈ L, topHome g w r = ci) (r : Rec) (hr : topHome g w r = v) :
    (!(L.map Rec.key).contains r.key) = true := by
  have : r.key ∉ L.map Rec.key := by
    intro hk
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hk
    have := home_of_key g w he
    rw [hL r' hr', hr] at this
    exact hne this.symm
  simpa [List.contains_iff_mem] using this

/-! ### The resolution -/

section resolve
variable {ci : Nat} {dk : List Model.LogicalKey} {st : FinState}

theorem resolve_main_length : (topResolve g w ci dk st).main.length = st.main.length := by
  simp [topResolve]

theorem resolve_leaves_length : (topResolve g w ci dk st).leaves.length = st.leaves.length := by
  simp [topResolve]

theorem resolve_ins : (topResolve g w ci dk st).ins = st.ins := rfl
theorem resolve_trace : (topResolve g w ci dk st).trace = st.trace := rfl

theorem resolve_parts_self (hci : ci < st.main.length) (hR : ci / 2 ^ g.I < st.leaves.length) :
    parts g w (topResolve g w ci dk st) ci = hres dk (parts g w st ci) := by
  simp only [parts, topResolve, hres]
  rw [getD_set_self _ _ _ _ hci, getD_set_self _ _ _ _ hR]
  congr 1
  · rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro r _
    cases hh : (topHome g w r == ci) <;> simp
  · rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro r _
    cases hh : (topHome g w r == ci) <;> simp

theorem resolve_parts_ne {v : Nat} (hne : v ≠ ci) :
    parts g w (topResolve g w ci dk st) v = parts g w st v := by
  simp only [parts, topResolve]
  rw [D6.getD_set_ne _ _ _ (Ne.symm hne)]
  congr 1
  · apply getD_set_filter
    intro r hr
    have : topHome g w r = v := by simpa using hr
    simp [this, hne]
  · apply filter_filter_of_imp
    intro r hr
    have : topHome g w r = v := by simpa using hr
    simp [this, hne]

theorem resolve_lrange (h : ∀ R, ∀ r ∈ st.leaves.getD R [], topHome g w r / 2 ^ g.I = R) :
    ∀ R, ∀ r ∈ (topResolve g w ci dk st).leaves.getD R [], topHome g w r / 2 ^ g.I = R := by
  intro R r hr
  simp only [topResolve] at hr
  by_cases hR : ci / 2 ^ g.I = R
  · subst hR
    by_cases hl : ci / 2 ^ g.I < st.leaves.length
    · rw [getD_set_self _ _ _ _ hl] at hr
      exact h _ r (List.mem_filter.1 hr).1
    · rw [List.set_eq_of_length_le (by omega)] at hr
      exact h _ r hr
  · rw [D6.getD_set_ne _ _ _ hR] at hr
    exact h R r hr

end resolve

/-! ### The offers -/

section offer
variable {ci : Nat} {st : FinState}

theorem offer_main_length : (topOffer g w ci st).main.length = st.main.length := by
  simp [topOffer]

theorem offer_leaves_length : (topOffer g w ci st).leaves.length = st.leaves.length := by
  simp [topOffer]

theorem offer_ins : (topOffer g w ci st).ins = st.ins := rfl
theorem offer_trace : (topOffer g w ci st).trace = st.trace := rfl

theorem offer_parts_self (hci : ci < st.main.length) (hR : ci / 2 ^ g.I < st.leaves.length) :
    parts g w (topOffer g w ci st) ci = hoff (parts g w st ci) := by
  simp only [parts, topOffer, hoff]
  rw [getD_set_self _ _ _ _ hci, getD_set_self _ _ _ _ hR]
  congr 1
  · exact filter_comm _ _ _
  · exact filter_comm _ _ _

theorem offer_parts_ne {v : Nat} (hne : v ≠ ci) :
    parts g w (topOffer g w ci st) v = parts g w st v := by
  simp only [parts, topOffer]
  rw [D6.getD_set_ne _ _ _ (Ne.symm hne)]
  congr 1
  · apply getD_set_filter
    intro r hr
    have hrv : topHome g w r = v := by simpa using hr
    have := not_contains_of_home g w hne
      (((st.leaves.getD (ci / 2 ^ g.I) []).filter fun r => topHome g w r == ci).take
        (((st.leaves.getD (ci / 2 ^ g.I) []).filter fun r => topHome g w r == ci).length -
          (fill (st.main.getD ci []) ((st.leaves.getD (ci / 2 ^ g.I) []).filter
            fun r => topHome g w r == ci)).2.length))
      (fun x hx => by simpa using (List.mem_filter.1 (List.mem_of_mem_take hx)).2) r hrv
    exact this
  · apply filter_filter_of_imp
    intro r hr
    have hrv : topHome g w r = v := by simpa using hr
    exact not_contains_of_home g w hne _
      (fun x hx => by simpa using (List.mem_filter.1 (List.mem_of_mem_take hx)).2) r hrv

theorem offer_lrange (h : ∀ R, ∀ r ∈ st.leaves.getD R [], topHome g w r / 2 ^ g.I = R) :
    ∀ R, ∀ r ∈ (topOffer g w ci st).leaves.getD R [], topHome g w r / 2 ^ g.I = R := by
  intro R r hr
  simp only [topOffer] at hr
  by_cases hR : ci / 2 ^ g.I = R
  · subst hR
    by_cases hl : ci / 2 ^ g.I < st.leaves.length
    · rw [getD_set_self _ _ _ _ hl] at hr
      exact h _ r (List.mem_filter.1 hr).1
    · rw [List.set_eq_of_length_le (by omega)] at hr
      exact h _ r hr
  · rw [D6.getD_set_ne _ _ _ hR] at hr
    exact h R r hr

end offer

end RebuildBound.D8
