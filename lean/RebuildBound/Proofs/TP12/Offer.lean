import RebuildBound.Proofs.TP12.Route

/-!
# TP12: one offer

`tpOffer g w b` fills bucket `b` from the candidates of its leaf and erases
the placed ones from the leaf.
-/

namespace RebuildBound.TP12

open RebuildBound.Model RebuildBound.D23 RebuildBound.S12

/-- The candidates of home `b` in its leaf. -/
def offCand (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) : List Rec :=
  (st.leaves.getD (b / 2 ^ g.I) []).filter fun r => tpHome g w r == b

/-- The number of placed records. -/
def offN (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) : Nat :=
  min (nfree (st.main.getD b [])) (offCand g w b st).length

theorem offer_placed (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (offCand g w b st).length - (fill (st.main.getD b []) (offCand g w b st)).2.length =
      offN g w b st := by
  rw [fill_snd, List.length_drop]
  unfold offN
  omega

theorem tpOffer_main (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (tpOffer g w b st).main =
      st.main.set b (fill (st.main.getD b []) (offCand g w b st)).1 := rfl

theorem tpOffer_leaves (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (tpOffer g w b st).leaves =
      st.leaves.set (b / 2 ^ g.I)
        (eraseFirst (fun r => tpHome g w r == b) (offN g w b st) (st.leaves.getD (b / 2 ^ g.I) [])) := by
  unfold tpOffer
  exact congrArg (fun n => st.leaves.set _ (eraseFirst _ n _)) (offer_placed g w b st)

theorem tpOffer_last (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (tpOffer g w b st).last = st.last := rfl

theorem tpOffer_main_length (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (tpOffer g w b st).main.length = st.main.length := by
  rw [tpOffer_main, List.length_set]

theorem tpOffer_leaves_length (g : TPGeom) (w : Model.LogicalKey → Nat) (b : Nat) (st : TPFin) :
    (tpOffer g w b st).leaves.length = st.leaves.length := by
  rw [tpOffer_leaves, List.length_set]

theorem tpOffer_main_ne (g : TPGeom) (w : Model.LogicalKey → Nat) {b b' : Nat} (st : TPFin) (h : b' ≠ b) :
    (tpOffer g w b st).main.getD b' [] = st.main.getD b' [] := by
  rw [tpOffer_main, D6.getD_set_ne _ _ _ (Ne.symm h)]

theorem tpOffer_main_self (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) :
    (tpOffer g w b st).main.getD b [] = (fill (st.main.getD b []) (offCand g w b st)).1 := by
  rw [tpOffer_main, getD_set_self _ _ _ _ hb]

theorem tpOffer_lanes (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) (hlanes : ∀ B ∈ st.main, B.length = g.C) :
    ∀ B ∈ (tpOffer g w b st).main, B.length = g.C := by
  intro B hB
  rw [tpOffer_main] at hB
  rcases List.mem_or_eq_of_mem_set hB with hB | rfl
  · exact hlanes B hB
  · rw [D1Lemmas.fill_length]; exact hlanes _ (getD_mem _ _ _ hb)

theorem tpOffer_leaves_ne (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} {R' : Nat} (st : TPFin)
    (h : R' ≠ b / 2 ^ g.I) :
    (tpOffer g w b st).leaves.getD R' [] = st.leaves.getD R' [] := by
  rw [tpOffer_leaves, D6.getD_set_ne _ _ _ (Ne.symm h)]

theorem tpOffer_leaves_self (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hR : b / 2 ^ g.I < st.leaves.length) :
    (tpOffer g w b st).leaves.getD (b / 2 ^ g.I) [] =
      eraseFirst (fun r => tpHome g w r == b) (offN g w b st) (st.leaves.getD (b / 2 ^ g.I) []) := by
  rw [tpOffer_leaves, getD_set_self _ _ _ _ hR]

/-- The bucket after the offer: occupancy `min C (occupied + candidates)`. -/
theorem tpOffer_recs_length (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) (hlanes : ∀ B ∈ st.main, B.length = g.C) :
    ((tpOffer g w b st).main.getD b []).recs.length =
      min g.C ((st.main.getD b []).recs.length + (offCand g w b st).length) := by
  rw [tpOffer_main_self g w st hb]
  have hl : (st.main.getD b []).length = g.C := hlanes _ (getD_mem _ _ _ hb)
  have h1 : (Bucket.recs (st.main.getD b [])).length + nfree (st.main.getD b []) =
      (st.main.getD b []).length := recs_length_add_nfree _
  have h2 := (fill_recs (st.main.getD b []) (offCand g w b st)).length_eq
  rw [List.length_append, List.length_take] at h2
  have : Bucket.recs (fill (st.main.getD b []) (offCand g w b st)).1 =
      (fill (st.main.getD b []) (offCand g w b st)).1.filterMap id := rfl
  rw [this, h2]
  have e : (st.main.getD b []).filterMap id = Bucket.recs (st.main.getD b []) := rfl
  rw [e]
  omega

/-- A leftover candidate means the bucket is full. -/
theorem tpOffer_leftover_full (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) (hlanes : ∀ B ∈ st.main, B.length = g.C)
    (hR : b / 2 ^ g.I < st.leaves.length) {x : Rec}
    (hx : x ∈ (tpOffer g w b st).leaves.getD (b / 2 ^ g.I) []) (hxb : tpHome g w x = b) :
    ((tpOffer g w b st).main.getD b []).recs.length = g.C := by
  rw [tpOffer_leaves_self g w st hR] at hx
  have hp : (fun r : Rec => tpHome g w r == b) x = true := by simp [hxb]
  have hmem := (eraseFirst_perm (fun r => tpHome g w r == b) (offN g w b st)
    (st.leaves.getD (b / 2 ^ g.I) []))
  have hc : 0 < (eraseFirst (fun r => tpHome g w r == b) (offN g w b st)
      (st.leaves.getD (b / 2 ^ g.I) [])).countP (fun r => tpHome g w r == b) :=
    List.countP_pos_iff.2 ⟨x, hx, hp⟩
  have hn : offN g w b st ≤ (st.leaves.getD (b / 2 ^ g.I) []).countP (fun r => tpHome g w r == b) := by
    unfold offN offCand
    rw [List.countP_eq_length_filter]
    exact Nat.min_le_right _ _
  rw [eraseFirst_countP_self _ _ _ hn] at hc
  have hcl : (offCand g w b st).length =
      (st.leaves.getD (b / 2 ^ g.I) []).countP (fun r => tpHome g w r == b) := by
    unfold offCand; rw [List.countP_eq_length_filter]
  have hlt : offN g w b st < (offCand g w b st).length := by omega
  have hnf : offN g w b st = nfree (st.main.getD b []) := by
    unfold offN at hlt ⊢; omega
  rw [tpOffer_recs_length g w st hb hlanes]
  have hl : (st.main.getD b []).length = g.C := hlanes _ (getD_mem _ _ _ hb)
  have h1 : (Bucket.recs (st.main.getD b [])).length + nfree (st.main.getD b []) =
      (st.main.getD b []).length := recs_length_add_nfree _
  have : nfree (st.main.getD b []) < (offCand g w b st).length := by omega
  omega

theorem tpOffer_leaves_count_ne (g : TPGeom) (w : Model.LogicalKey → Nat) {b b' : Nat} (st : TPFin)
    (h : b' ≠ b) :
    ((tpOffer g w b st).leaves.getD (b / 2 ^ g.I) []).countP (fun r => tpHome g w r == b') =
      (st.leaves.getD (b / 2 ^ g.I) []).countP (fun r => tpHome g w r == b') := by
  by_cases hR : b / 2 ^ g.I < st.leaves.length
  · rw [tpOffer_leaves_self g w st hR]
    apply eraseFirst_countP_ne
    intro x hx
    simp only [beq_iff_eq] at hx ⊢
    simp [hx, h]
  · rw [tpOffer_leaves, List.set_eq_of_length_le (by omega)]

theorem tpOffer_leaves_mem (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin) {x : Rec} {R : Nat}
    (hx : x ∈ (tpOffer g w b st).leaves.getD R []) : x ∈ st.leaves.getD R [] := by
  by_cases hR : R = b / 2 ^ g.I
  · subst hR
    by_cases hR2 : b / 2 ^ g.I < st.leaves.length
    · rw [tpOffer_leaves_self g w st hR2] at hx
      exact mem_eraseFirst _ _ _ hx
    · rw [tpOffer_leaves, List.set_eq_of_length_le (by omega)] at hx; exact hx
  · rwa [tpOffer_leaves_ne g w st hR] at hx

/-- Offers conserve main and leaf records. -/
theorem tpOffer_perm (g : TPGeom) (w : Model.LogicalKey → Nat) {b : Nat} (st : TPFin)
    (hb : b < st.main.length) (hR : b / 2 ^ g.I < st.leaves.length) :
    List.Perm ((tpOffer g w b st).main.flatMap Bucket.recs ++ (tpOffer g w b st).leaves.flatten)
      (st.main.flatMap Bucket.recs ++ st.leaves.flatten) := by
  have hf : List.Perm (Bucket.recs (fill (st.main.getD b []) (offCand g w b st)).1)
      (Bucket.recs (st.main.getD b []) ++
        (offCand g w b st).take (min (nfree (st.main.getD b [])) (offCand g w b st).length)) :=
    fill_recs (st.main.getD b []) (offCand g w b st)
  have hE := eraseFirst_perm (fun r => tpHome g w r == b) (offN g w b st)
    (st.leaves.getD (b / 2 ^ g.I) [])
  have hfs : (st.leaves.getD (b / 2 ^ g.I) []).filter (fun r => tpHome g w r == b) =
      offCand g w b st := rfl
  rw [hfs] at hE
  have A1 := perm_flatMap_set Bucket.recs st.main b
    (fill (st.main.getD b []) (offCand g w b st)).1 [] hb
  have A2 := flatten_set_perm st.leaves (b / 2 ^ g.I)
    (eraseFirst (fun r => tpHome g w r == b) (offN g w b st) (st.leaves.getD (b / 2 ^ g.I) [])) hR
  rw [tpOffer_main, tpOffer_leaves]
  rw [List.perm_iff_count]
  intro x
  have c1 := A1.count_eq x
  have c2 := A2.count_eq x
  have c3 := hf.count_eq x
  have c4 := hE.count_eq x
  simp only [List.count_append] at c1 c2 c3 c4 ⊢
  unfold offN at c4 c2 ⊢
  omega

end RebuildBound.TP12
