import RebuildBound.Proofs.D8.Bucket

/-!
# D8: the sweep, home by home

After the sweep every home `v` holds `Hv v`, the visit of its initial share,
and the merge stash is the concatenation of the sheds in visit order
(`sweep_inv`). Everything here holds for every input.
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

variable {g : TopGeom} {unsh : Rec → Bool} {w : Model.LogicalKey → Nat} {inp : TopInputs}

/-- The reference phases of the top finish. -/
def pl (unsh : Rec → Bool) (inp : TopInputs) : List Rec := topPool unsh inp
def lv (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs) : List (List Rec) :=
  leavesOf g.toGeom w (topPool unsh inp)
def st0 (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs) : FinState :=
  { main := inp.cMain, ins := [], leaves := lv g unsh w inp, bcopy := topTierCopy unsh inp,
    trace := [] }
def fin (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs) : FinState :=
  topSweep g w inp (lv g unsh w inp) (topTierCopy unsh inp)

theorem Hv_eq {i : Nat} (hi : i < g.U) (q : Nat) :
    Hv g unsh w inp (i + q * g.U) = hstep (fun key => (inp.bMain.getD i []).keys.contains key)
      ((dirOf g w (inp.bMain.getD i []) q).map Rec.key)
      ((dirOf g w (inp.bMain.getD i []) q).filter fun r => !r.tomb)
      (H0 g unsh w inp (i + q * g.U)) := by
  obtain ⟨h1, h2⟩ := mod_div_of g (q := q) hi
  simp only [Hv, dirv, Sv, clrOf, Bi, dirOf]
  rw [h1, h2]
  rfl

theorem rangeOf_eq (hg : g.Valid) (r : Rec) :
    rangeOf g.toGeom w r = topHome g w r / 2 ^ g.I := by
  unfold rangeOf home
  rw [TopGeom.toGeom_homes g hg]
  rfl

theorem ranges_eq (hg : g.Valid) : g.toGeom.ranges = g.ranges := by
  unfold Geom.ranges
  rw [TopGeom.toGeom_depth g hg]; rfl

theorem lv_getD (hg : g.Valid) {R : Nat} (hR : R < g.ranges) :
    (lv g unsh w inp).getD R [] = (topPool unsh inp).filter fun r => topHome g w r / 2 ^ g.I == R := by
  unfold lv leavesOf
  have hR' : R < g.toGeom.ranges := by rw [ranges_eq hg]; exact hR
  simp [List.getD_eq_getElem?_getD, hR']
  apply List.filter_congr
  intro r _
  rw [rangeOf_eq hg]

theorem lv_lrange (hg : g.Valid) :
    ∀ R, ∀ r ∈ (lv g unsh w inp).getD R [], topHome g w r / 2 ^ g.I = R := by
  intro R r hr
  by_cases hR : R < g.ranges
  · rw [lv_getD hg hR, List.mem_filter] at hr; simpa using hr.2
  · have : R ≥ (lv g unsh w inp).length := by
      unfold lv leavesOf; simp [ranges_eq hg]; omega
    rw [List.getD_eq_default _ _ this] at hr
    simp at hr

theorem lv_length (hg : g.Valid) : (lv g unsh w inp).length = g.ranges := by
  unfold lv leavesOf; simp [ranges_eq hg]

theorem lv_part (hg : g.Valid) {v : Nat} (hv : v < g.T) :
    ((lv g unsh w inp).getD (v / 2 ^ g.I) []).filter (fun r => topHome g w r == v) =
      Pv g unsh w inp v := by
  rw [lv_getD hg (div_lt_ranges hg hv), Pv]
  apply filter_filter_of_imp
  intro r hr
  have : topHome g w r = v := by simpa using hr
  simp [this]

theorem good_st0 (hg : g.Valid) (hs : TopShape g unsh w inp) : Good g w (st0 g unsh w inp) :=
  ⟨hs.cLen, lv_length hg, lv_lrange hg⟩

/-- The sweep invariant after the first `n` B buckets. -/
structure SInv (g : TopGeom) (unsh : Rec → Bool) (w : Model.LogicalKey → Nat) (inp : TopInputs)
    (st : FinState) (n : Nat) : Prop where
  good : Good g w st
  shares : ∀ v < g.T, parts g w st v =
    if v % g.U < n then (Hv g unsh w inp v).1 else H0 g unsh w inp v
  ins : st.ins = (List.range n).flatMap fun i => (List.range g.D).flatMap fun q =>
    (Hv g unsh w inp (i + q * g.U)).2
  trace : ∀ t ∈ st.trace, t.1 = .insertion ∧ t.2 ≤ st.ins.length

theorem SInv.step (hg : g.Valid) {st : FinState} {n : Nat} (h : SInv g unsh w inp st n)
    (hn : n < g.U) : SInv g unsh w inp (topBucket g w inp.bMain n st) (n + 1) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := topBucket_spec hg inp.bMain h.good hn
  have hH : ∀ q < g.D, (parts g w st (n + q * g.U)) = H0 g unsh w inp (n + q * g.U) := by
    intro q hq
    have := h.shares (n + q * g.U) (lt_T_of g hn hq)
    rw [(mod_div_of g (q := q) hn).1, if_neg (Nat.lt_irrefl _)] at this
    exact this
  have hins : (topBucket g w inp.bMain n st).ins = (List.range (n + 1)).flatMap fun i =>
      (List.range g.D).flatMap fun q => (Hv g unsh w inp (i + q * g.U)).2 := by
    rw [b2, h.ins, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    apply List.flatMap_congr
    intro q hq
    have hq' := List.mem_range.1 hq
    rw [hH q hq', Hv_eq hn q]
  refine ⟨b1, ?_, hins, ?_⟩
  · intro v hv
    by_cases hvn : v % g.U = n
    · have hvq : v = n + (v / g.U) * g.U := by
        have := split_home g (v := v); rw [hvn] at this; exact this
      have hq : v / g.U < g.D := by
        have := (Nat.div_lt_iff_lt_mul (U_pos g)).2 (show v < g.D * g.U by
          rw [Nat.mul_comm]; rw [← T_eq]; exact hv)
        exact this
      rw [hvq]
      rw [b5 _ hq, hH _ hq, ← Hv_eq hn, if_pos]
      have := (mod_div_of g (q := v / g.U) hn).1
      rw [this]; omega
    · rw [b4 v hvn, h.shares v hv]
      by_cases hl : v % g.U < n
      · simp [hl, show v % g.U < n + 1 by omega]
      · simp [hl, show ¬ v % g.U < n + 1 by omega]
  · intro t ht
    rw [b3] at ht
    rcases List.mem_append.1 ht with ht | ht
    · refine ⟨(h.trace t ht).1, ?_⟩
      have := (h.trace t ht).2
      rw [b2, List.length_append]; omega
    · rw [List.mem_singleton] at ht
      subst ht; exact ⟨rfl, le_refl _⟩

theorem sweep_inv (hg : g.Valid) (hs : TopShape g unsh w inp) :
    SInv g unsh w inp (fin g unsh w inp) g.U := by
  have key : ∀ n ≤ g.U, SInv g unsh w inp
      ((List.range n).foldl (fun st i => topBucket g w inp.bMain i st) (st0 g unsh w inp)) n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨good_st0 hg hs, ?_, rfl, fun t ht => by simp [st0] at ht⟩
      intro v hv
      simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, if_false]
      simp only [parts, st0, H0, mv, Tv, Pv]
      rw [lv_part hg hv]
      rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact (ih (by omega)).step hg (by omega)
  exact key g.U (Nat.le_refl _)

end RebuildBound.D8
