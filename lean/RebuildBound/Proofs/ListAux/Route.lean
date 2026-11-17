import RebuildBound.Proofs.ListAux.Basic

/-!
# ListAux: route indices and flattened lists (from D23)

Pair indices (`pair_lt`, `testBit_add_pow_lt/self`), the low-bit invariant
`lowOK`/`pending`, `flatten`/`flatMap` facts and the filter lemmas used by
the per-home finish (`clrOf`, `getD_set_filter`). Moved from the binary
d = 2 chain (`D23.Route`, `D23.Assembly`, `D23.Finish`); namespace
`RebuildBound.D23` kept.
-/

namespace RebuildBound.D23
open RebuildBound.Model
theorem pair_lt {i j n : Nat} (hi : i < 2^n) (hb : i.testBit j = false) (hj : j < n) :
    i + 2^j < 2^n := by
  have hp : 0 < 2^j := Nat.two_pow_pos j
  have hd : i / 2^j % 2 = 0 := by
    have := (Nat.testBit_eq_decide_div_mod_eq (x := i) (i := j))
    rw [hb] at this
    have h' : ¬ (i / 2^j % 2 = 1) := by simpa using this.symm
    omega
  have hM : 2^n = 2^j * 2^(n-j) := by rw [← Nat.pow_add]; congr 1; omega
  have hMe : 2^(n-j) % 2 = 0 := by
    have : 2^(n-j) = 2 * 2^(n-j-1) := by rw [← Nat.pow_succ']; congr 1; omega
    omega
  have h4 : i = 2^j * (i / 2^j) + i % 2^j := (Nat.div_add_mod i (2^j)).symm
  have h5 : i % 2^j < 2^j := Nat.mod_lt _ hp
  have hdM : i / 2^j < 2^(n-j) := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm, ← hM]; exact hi
  have h2 : i / 2^j + 2 ≤ 2^(n-j) := by omega
  have h3 : 2^j * (i/2^j + 2) ≤ 2^j * 2^(n-j) := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add] at h3
  omega

theorem pending {v j n : Nat} (hv : v < 2^n) :
    ∃ i, i < 2^n ∧ i.testBit j = false ∧ (v = i ∨ v = i + 2^j) := by
  cases h : v.testBit j with
  | false => exact ⟨v, hv, h, Or.inl rfl⟩
  | true =>
    have hge := Nat.ge_two_pow_of_testBit h
    refine ⟨v - 2^j, Nat.lt_of_le_of_lt (Nat.sub_le _ _) hv, ?_, Or.inr (by omega)⟩
    have e : 2^j + (v - 2^j) = v := by omega
    have := Nat.testBit_two_pow_add_eq (v - 2^j) j
    rw [e, h] at this
    cases h2 : (v - 2^j).testBit j
    · rfl
    · rw [h2] at this; exact absurd this (by decide)

theorem testBit_add_pow_lt {i j b : Nat} (hb : b < j) : (i + 2^j).testBit b = i.testBit b := by
  rw [Nat.add_comm]; exact Nat.testBit_two_pow_add_gt hb i

theorem testBit_add_pow_self {i j : Nat} (h : i.testBit j = false) : (i + 2^j).testBit j = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, h]; rfl

theorem flatten_set_perm {α : Type} (l : List (List α)) (i : Nat) (x : List α)
    (hi : i < l.length) : List.Perm ((l.set i x).flatten ++ l.getD i []) (l.flatten ++ x) := by
  have := perm_flatMap_set id l i x [] hi
  simpa [List.flatMap_id] using this

/-- Record `r` agrees with bucket `v` on the bits below `j`. -/
def lowOK (w : Model.LogicalKey → Nat) (j v : Nat) (r : Rec) : Prop :=
  ∀ b < j, (w r.key).testBit b = v.testBit b

end RebuildBound.D23

namespace RebuildBound.D23
open RebuildBound.Model
theorem flatten_single {β : Type} : ∀ (L : List (List β)) (j : Nat),
    (∀ j' < L.length, j' ≠ j → L.getD j' [] = []) → L.flatten = L.getD j []
  | [], _, _ => by simp
  | a :: L, 0, h => by
    have : L.flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.1 hl
      have := h (j' + 1) (by simp; omega) (by omega)
      simpa [List.getD_eq_getElem?_getD, hj'] using this
    simp [this]
  | a :: L, j + 1, h => by
    have ha : a = [] := by simpa using h 0 (by simp) (by omega)
    subst ha
    simp only [List.flatten_cons, List.nil_append, List.getD_cons_succ]
    exact flatten_single L j (fun j' hj' hne => by
      simpa using h (j' + 1) (by simp; omega) (by omega))

theorem flatMap_filter_single {α : Type} (L : List α) (f : α → List Rec) (p : Rec → Bool)
    (d : α) (j : Nat) (hj : j < L.length)
    (h : ∀ j' < L.length, j' ≠ j → (f (L.getD j' d)).filter p = []) :
    (L.flatMap f).filter p = (f (L.getD j d)).filter p := by
  show (List.flatten (L.map f)).filter p = _
  rw [List.filter_flatten, List.map_map]
  rw [flatten_single _ j]
  · simp [List.getD_eq_getElem?_getD, hj]
  · intro j' hj' hne
    simp only [List.length_map] at hj'
    have := h j' hj' hne
    simpa [List.getD_eq_getElem?_getD, hj'] using this

end RebuildBound.D23

namespace RebuildBound.D23
open RebuildBound.Model
theorem filter_filter_of_imp (L : List Rec) (p q : Rec → Bool) (h : ∀ r, p r = true → q r = true) :
    (L.filter q).filter p = L.filter p := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro r _
  cases hp : p r
  · simp
  · simp [h r hp]

theorem filter_comm (L : List Rec) (p q : Rec → Bool) :
    (L.filter q).filter p = (L.filter p).filter q := by
  simp only [List.filter_filter]
  apply List.filter_congr
  intro r _
  rw [Bool.and_comm]

theorem getD_set_filter (l : List (List Rec)) (R R' : Nat) (p q : Rec → Bool)
    (h : ∀ r, p r = true → q r = true) :
    ((l.set R ((l.getD R []).filter q)).getD R' []).filter p = (l.getD R' []).filter p := by
  by_cases hR : R = R'
  · subst hR
    by_cases hl : R < l.length
    · rw [getD_set_self _ _ _ _ hl, filter_filter_of_imp _ _ _ h]
    · rw [List.set_eq_of_length_le (by omega)]
  · rw [D6.getD_set_ne _ _ _ hR]

/-- The clearing predicate of B bucket `i`. -/
def clrOf (bMain : List Bucket) (i : Nat) : Model.LogicalKey → Bool :=
  fun key => (bMain.getD i []).keys.contains key

end RebuildBound.D23
