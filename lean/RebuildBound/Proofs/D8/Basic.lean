import RebuildBound.Proofs.HomeFinish.Home
import RebuildBound.Proofs.ListAux.Drain
import RebuildBound.Spec.TopT

/-!
# D8 basics: geometry, homes and generic list lemmas for the top finish
-/

namespace RebuildBound.D8

open RebuildBound.Model RebuildBound.D23

/-! ### Geometry -/

theorem U_pos (g : TopGeom) : 0 < g.U := Nat.two_pow_pos _
theorem D_pos (g : TopGeom) : 0 < g.D := Nat.two_pow_pos _
theorem T_pos (g : TopGeom) : 0 < g.T := Nat.two_pow_pos _

theorem T_eq (g : TopGeom) : g.T = g.U * g.D := by
  simp [TopGeom.T, TopGeom.U, TopGeom.D, ← Nat.pow_add]

theorem U_dvd_T (g : TopGeom) : g.U ∣ g.T := ⟨g.D, T_eq g⟩

theorem home_lt (g : TopGeom) (w : Model.LogicalKey → Nat) (r : Rec) : topHome g w r < g.T :=
  Nat.mod_lt _ (T_pos g)

theorem home_of_key (g : TopGeom) (w : Model.LogicalKey → Nat) {r r' : Rec} (h : r.key = r'.key) :
    topHome g w r = topHome g w r' := by
  simp [topHome, h]

theorem way_lt (g : TopGeom) (w : Model.LogicalKey → Nat) (r : Rec) : topWay g w r < g.D := by
  unfold topWay
  have h := home_lt g w r
  rw [T_eq] at h
  exact (Nat.div_lt_iff_lt_mul (U_pos g)).2 (by rw [Nat.mul_comm]; exact h)

/-- A record whose carry bucket is `i` sits at `i + way * U`. -/
theorem home_split (g : TopGeom) (w : Model.LogicalKey → Nat) (r : Rec) (i : Nat) (h : w r.key % g.U = i) :
    topHome g w r = i + topWay g w r * g.U := by
  have h1 : topHome g w r % g.U = i := by
    unfold topHome
    rw [Nat.mod_mod_of_dvd _ (U_dvd_T g)]; exact h
  have h2 := Nat.mod_add_div (topHome g w r) g.U
  unfold topWay
  rw [h1] at h2
  rw [Nat.mul_comm]
  omega

theorem split_home (g : TopGeom) {v : Nat} :
    v = v % g.U + (v / g.U) * g.U := by
  have h2 := Nat.mod_add_div v g.U
  rw [Nat.mul_comm]; omega

theorem home_mod_U (g : TopGeom) (w : Model.LogicalKey → Nat) (r : Rec) :
    topHome g w r % g.U = w r.key % g.U := by
  unfold topHome
  rw [Nat.mod_mod_of_dvd _ (U_dvd_T g)]

/-- `i + q U` has carry bucket `i` and way `q`. -/
theorem mod_div_of (g : TopGeom) {i q : Nat} (hi : i < g.U) :
    (i + q * g.U) % g.U = i ∧ (i + q * g.U) / g.U = q := by
  constructor
  · rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi
  · rw [Nat.add_mul_div_right _ _ (U_pos g), Nat.div_eq_of_lt hi]; simp

theorem lt_T_of (g : TopGeom) {i q : Nat} (hi : i < g.U) (hq : q < g.D) : i + q * g.U < g.T := by
  rw [T_eq]
  have : (q + 1) * g.U ≤ g.D * g.U := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul] at this
  rw [Nat.mul_comm g.U g.D]
  omega

/-! ### Lists -/

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

theorem filter_home_self (g : TopGeom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, topHome g w r = v) : L.filter (fun r => topHome g w r == v) = L := by
  rw [List.filter_eq_self]; intro r hr; simp [h r hr]

theorem filter_home_nil (g : TopGeom) (w : Model.LogicalKey → Nat) (v : Nat) (L : List Rec)
    (h : ∀ r ∈ L, topHome g w r ≠ v) : L.filter (fun r => topHome g w r == v) = [] := by
  rw [List.filter_eq_nil_iff]; intro r hr; simp [h r hr]

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

theorem count_filter_home (g : TopGeom) (w : Model.LogicalKey → Nat) (x : Rec) (L : List Rec) :
    L.count x = (L.filter fun r => topHome g w r == topHome g w x).count x := by
  rw [List.count_filter]; simp

theorem contains_home (g : TopGeom) (w : Model.LogicalKey → Nat) (L : List Rec) (r : Rec) {v : Nat}
    (hr : topHome g w r = v) :
    (L.map Rec.key).contains r.key =
      ((L.filter fun r => topHome g w r == v).map Rec.key).contains r.key := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨r', hr', he⟩
    refine ⟨r', ⟨hr', ?_⟩, he⟩
    rw [home_of_key g w he, hr]; simp
  · rintro ⟨r', ⟨hr', _⟩, he⟩
    exact ⟨r', hr', he⟩

theorem getD_set_filter (l : List (List Rec)) (R R' : Nat) (p q : Rec → Bool)
    (h : ∀ r, p r = true → q r = true) :
    ((l.set R ((l.getD R []).filter q)).getD R' []).filter p = (l.getD R' []).filter p := by
  by_cases hR : R = R'
  · subst hR
    by_cases hl : R < l.length
    · rw [getD_set_self _ _ _ _ hl, filter_filter_of_imp _ _ _ h]
    · rw [List.set_eq_of_length_le (by omega)]
  · rw [D6.getD_set_ne _ _ _ hR]

/-- The records of home `v` among the keys of `L`, a count by home. -/
theorem count_filter_eq (L : List Rec) (p : Rec → Bool) (x : Rec) (hx : p x = true) :
    (L.filter p).count x = L.count x := by
  rw [List.count_filter]; simp [hx]

end RebuildBound.D8
