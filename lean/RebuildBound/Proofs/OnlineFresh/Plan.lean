import RebuildBound.Proofs.OnlineFresh.Requester

/-!
# OnlineFresh: windows, tilings and families

* Every window ends at `v · cp ℓ`; forwarding keeps that end, so all members
  of a family share it (`familyOfAux_inv`).
* A tiling orders the windows: each one ends where every earlier one has
  already begun (`tiles_pairwise`), and every position of the tiled range
  lies in some window (`tiles_cover`).
* Published lower tables have nonempty windows. The schedule's one-top
  premise handles the possibly empty initial top without a positive seed.
-/

namespace RebuildBound.OnlineFreshProof

open RebuildBound.Model RebuildBound.Model.Hierarchy RebuildBound.Model.Online RebuildBound.Spec
open RebuildBound.HierarchyInvariantProof

/-! ### Tilings -/

section tiles
variable (cfg : Config)

/-- The beginning and the end of a coordinate's window. -/
abbrev wb (c : Nat × Nat) : Nat := (window cfg c.1 c.2).1
abbrev we (c : Nat × Nat) : Nat := (window cfg c.1 c.2).2

theorem window_snd (ℓ v : Nat) : (window cfg ℓ v).2 = v * cfg.carryPositions ℓ := by
  unfold window; split_ifs <;> rfl

theorem window_fst_top (v : Nat) : (window cfg cfg.levels v).1 = 0 := by
  simp [window]

theorem window_fst_low {ℓ : Nat} (v : Nat) (h : ℓ ≠ cfg.levels) :
    (window cfg ℓ v).1 = (v - Config.digitOf (cfg.fanout ℓ) v) * cfg.carryPositions ℓ := by
  simp [window, h]

variable {cfg}

theorem tiles_le : ∀ {cs : List (Nat × Nat)} {lo hi : Nat}, Tiles cfg cs lo hi → lo ≤ hi
  | [], _, _, h => by simp only [Tiles] at h; omega
  | _ :: _, _, _, h => by
    simp only [Tiles] at h
    exact (tiles_le h.2.2).trans h.2.1

theorem tiles_bounds : ∀ {cs : List (Nat × Nat)} {lo hi : Nat}, Tiles cfg cs lo hi →
    ∀ c ∈ cs, lo ≤ wb cfg c ∧ wb cfg c ≤ we cfg c ∧ we cfg c ≤ hi
  | [], _, _, _, _, hc => by simp at hc
  | a :: cs, lo, hi, h, c, hc => by
    simp only [Tiles] at h
    rcases List.mem_cons.1 hc with hc | hc
    · subst hc
      exact ⟨tiles_le h.2.2, by show (window cfg _ _).1 ≤ (window cfg _ _).2; rw [h.1]; exact h.2.1,
        le_of_eq h.1⟩
    · obtain ⟨h1, h2, h3⟩ := tiles_bounds h.2.2 c hc
      exact ⟨h1, h2, h3.trans h.2.1⟩

theorem tiles_pairwise : ∀ {cs : List (Nat × Nat)} {lo hi : Nat}, Tiles cfg cs lo hi →
    cs.Pairwise fun a b => we cfg b ≤ wb cfg a
  | [], _, _, _ => List.Pairwise.nil
  | a :: cs, lo, hi, h => by
    simp only [Tiles] at h
    exact List.Pairwise.cons (fun b hb => (tiles_bounds h.2.2 b hb).2.2) (tiles_pairwise h.2.2)

theorem tiles_cover : ∀ {cs : List (Nat × Nat)} {lo hi q : Nat}, Tiles cfg cs lo hi → lo ≤ q → q < hi →
    ∃ (i : Nat) (c : Nat × Nat), cs[i]? = some c ∧ wb cfg c ≤ q ∧ q < we cfg c
  | [], _, _, _, h, h1, h2 => by simp only [Tiles] at h; omega
  | a :: cs, lo, hi, q, h, h1, h2 => by
    simp only [Tiles] at h
    by_cases hq : wb cfg a ≤ q
    · exact ⟨(0 : Nat), a, by simp, hq, by rw [we, h.1]; exact h2⟩
    · obtain ⟨i, c, hc, h3, h4⟩ := tiles_cover h.2.2 h1 (by simp only [wb] at hq; omega)
      exact ⟨i + 1, c, by simpa using hc, h3, h4⟩

/-- In a tiling of nonempty windows, a later entry ends before an earlier one begins. -/
theorem tiles_order {cs : List (Nat × Nat)} {lo hi : Nat} (h : Tiles cfg cs lo hi) {i i' : Nat}
    {c c' : Nat × Nat} (hc : cs[i]? = some c) (hc' : cs[i']? = some c') (hii : i < i') :
    we cfg c' ≤ wb cfg c := by
  have hp := List.pairwise_iff_getElem.1 (tiles_pairwise h)
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hc
  obtain ⟨hi', e'⟩ := List.getElem?_eq_some_iff.1 hc'
  have := hp i i' hi hi' hii
  rw [e, e'] at this
  exact this

/-- A plan with at most one top entry cannot place two top coordinates at
strictly ordered indices, including the empty initial top. -/
theorem oneTop_order {cs : List (Nat × Nat)}
    (h : (cs.filter (·.1 == cfg.levels)).length ≤ 1) {i i' : Nat}
    {c c' : Nat × Nat} (hc : cs[i]? = some c) (hc' : cs[i']? = some c')
    (hii : i < i') (ht : c.1 = cfg.levels) (ht' : c'.1 = cfg.levels) : False := by
  induction cs generalizing i i' with
  | nil => simp at hc
  | cons a cs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst c
      cases i' with
      | zero => omega
      | succ i' =>
        simp only [List.getElem?_cons_succ] at hc'
        have hm : c' ∈ cs.filter (·.1 == cfg.levels) :=
          List.mem_filter.mpr ⟨List.mem_of_getElem? hc', by simp [ht']⟩
        have hp : 0 < (cs.filter (·.1 == cfg.levels)).length :=
          List.length_pos_of_mem hm
        simp only [List.filter_cons, ht, beq_self_eq_true, ite_true, List.length_cons] at h
        omega
    | succ i =>
      cases i' with
      | zero => omega
      | succ i' =>
        simp only [List.getElem?_cons_succ] at hc hc'
        apply ih _ hc hc' (by omega)
        have hsub : (cs.filter (·.1 == cfg.levels)).length ≤
            ((a :: cs).filter (·.1 == cfg.levels)).length := by
          simp only [List.filter_cons]
          split <;> (try simp only [List.length_cons]) <;> omega
        exact hsub.trans h

end tiles

/-! ### The configuration's arithmetic -/

section facts
variable {cfg : Config} {rows : List (SepGeom × Nat)}

theorem carry_pos {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) :
    0 < cfg.carry ℓ := by
  rw [← F.carryPow ℓ h1 hL]; exact Nat.two_pow_pos _

theorem cp_pos {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels) :
    0 < cfg.carryPositions ℓ := by
  unfold Config.carryPositions
  rw [F.load]
  exact Nat.mul_pos (by norm_num) (carry_pos F h1 hL)

theorem cp_succ {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) :
    cfg.carryPositions (ℓ + 1) = cfg.fanout ℓ * cfg.carryPositions ℓ := by
  unfold Config.carryPositions
  rw [F.carrySucc ℓ h1 hL]
  ring

theorem fanout_pos {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels) :
    0 < cfg.fanout ℓ := by
  have := (F.fan ℓ h1 hL).1; omega

theorem seed_cp {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) :
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ cfg.levels →
      cfg.seed ℓ * cfg.carryPositions ℓ = cfg.seed 1 * cfg.carryPositions 1 := by
  intro ℓ
  induction ℓ with
  | zero => intro h; omega
  | succ ℓ ih =>
    intro h1 hL
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0; rfl
    · rw [← ih h0 (by omega), cp_succ F h0 (by omega), F.seed ℓ h0 (by omega)]
      ring

/-- The seeded counter of a level below the top is a multiple of its fanout, and a
potential ordinal's digit block begins at or after it. -/
theorem seed_le_block {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ < cfg.levels)
    (hv : cfg.seed ℓ < v) : cfg.seed ℓ ≤ v - Config.digitOf (cfg.fanout ℓ) v := by
  have hb := fanout_pos F h1 hL
  have hs := F.seed ℓ h1 hL
  unfold Config.digitOf
  have e := Nat.mod_add_div (v - 1) (cfg.fanout ℓ)
  have : cfg.seed (ℓ + 1) ≤ (v - 1) / cfg.fanout ℓ := by
    rw [Nat.le_div_iff_mul_le hb]; rw [hs] at hv; rw [Nat.mul_comm]; omega
  have := Nat.mul_le_mul_left (cfg.fanout ℓ) this
  rw [hs]
  omega

/-! ### Families -/

/-- Forwarding stays among the published coordinates and keeps the window's end. -/
theorem familyOfAux_inv {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) :
    ∀ fuel ℓ v, 1 ≤ ℓ → ℓ ≤ cfg.levels → cfg.seed ℓ ≤ v →
      1 ≤ (familyOfAux cfg fuel ℓ v).1 ∧ (familyOfAux cfg fuel ℓ v).1 ≤ cfg.levels ∧
        cfg.seed (familyOfAux cfg fuel ℓ v).1 ≤ (familyOfAux cfg fuel ℓ v).2 ∧
        (familyOfAux cfg fuel ℓ v).2 * cfg.carryPositions (familyOfAux cfg fuel ℓ v).1 =
          v * cfg.carryPositions ℓ := by
  intro fuel
  induction fuel with
  | zero => intro ℓ v h1 hL hs; exact ⟨h1, hL, hs, rfl⟩
  | succ fuel ih =>
    intro ℓ v h1 hL hs
    simp only [familyOfAux]
    split_ifs with h
    · obtain ⟨hlt, hdvd⟩ := h
      have hb := fanout_pos F h1 hlt
      obtain ⟨w, rfl⟩ := Nat.dvd_of_mod_eq_zero hdvd
      have hw : cfg.fanout ℓ * w / cfg.fanout ℓ = w := Nat.mul_div_cancel_left w hb
      rw [hw]
      have hs' : cfg.seed (ℓ + 1) ≤ w := by
        rw [F.seed ℓ h1 hlt] at hs
        exact Nat.le_of_mul_le_mul_left hs hb
      obtain ⟨a, b, c, d⟩ := ih (ℓ + 1) w (by omega) (by omega) hs'
      refine ⟨a, b, c, ?_⟩
      rw [d, cp_succ F h1 hlt]
      ring
    · exact ⟨h1, hL, hs, rfl⟩

theorem familyOf_end {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels)
    (hs : cfg.seed ℓ ≤ v) :
    (familyOf cfg ℓ v).2 * cfg.carryPositions (familyOf cfg ℓ v).1 = v * cfg.carryPositions ℓ :=
  (familyOfAux_inv F _ ℓ v h1 hL hs).2.2.2

/-- A family whose window ends before the horizon's last position is a coordinate. -/
theorem familyOf_mem {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) {ℓ v : Nat} (h1 : 1 ≤ ℓ) (hL : ℓ ≤ cfg.levels)
    (hs : cfg.seed ℓ ≤ v)
    (hend : v * cfg.carryPositions ℓ < cfg.seed 1 * cfg.carryPositions 1 + cfg.horizon) :
    familyOf cfg ℓ v ∈ cfg.coordinates := by
  obtain ⟨a, b, c, d⟩ := familyOfAux_inv F cfg.levels ℓ v h1 hL hs
  have e : familyOf cfg ℓ v = familyOfAux cfg cfg.levels ℓ v := rfl
  generalize familyOfAux cfg cfg.levels ℓ v = p at a b c d e
  rw [e]
  obtain ⟨ℓ', v'⟩ := p
  dsimp only at a b c d
  have hcp := cp_pos F a b
  have hsc := seed_cp F ℓ' a b
  have h2 : v' * cfg.carryPositions ℓ' < cfg.seed ℓ' * cfg.carryPositions ℓ' + cfg.horizon := by
    rw [d, hsc]; exact hend
  have hlt : (v' - cfg.seed ℓ') * cfg.carryPositions ℓ' < cfg.horizon := by
    have := Nat.mul_le_mul_right (cfg.carryPositions ℓ') c
    rw [Nat.sub_mul]; omega
  have hi : v' - cfg.seed ℓ' < cfg.ordinals ℓ' + 1 := by
    unfold Config.ordinals
    have := (Nat.le_div_iff_mul_le hcp).2 (Nat.le_of_lt hlt)
    omega
  unfold Config.coordinates Config.ordinaryLevels
  simp only [List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  refine ⟨ℓ', ?_, v' - cfg.seed ℓ', hi, by
    rw [Prod.mk.injEq]; exact ⟨rfl, by omega⟩⟩
  rcases Nat.lt_or_ge ℓ' cfg.levels with h | h
  · exact Or.inl ⟨ℓ' - 1, by omega, by omega⟩
  · exact Or.inr (by omega)

/-! ### Published coordinates -/

/-- The coordinate premise of a schedule's table. -/
def Published (cfg : Config) (c : Nat × Nat) : Prop :=
  1 ≤ c.1 ∧ c.1 ≤ cfg.levels ∧ (c.1 < cfg.levels → cfg.seed c.1 < c.2) ∧
    (c.1 = cfg.levels → cfg.seed c.1 ≤ c.2)

theorem Published.seed_le {c : Nat × Nat} (h : Published cfg c) : cfg.seed c.1 ≤ c.2 := by
  rcases Nat.lt_or_ge c.1 cfg.levels with h' | h'
  · exact Nat.le_of_lt (h.2.2.1 h')
  · exact h.2.2.2 (by have := h.2.1; omega)

/-- Every published lower table has a nonempty window. An empty published
window can therefore only belong to the top. -/
theorem Published.nonempty_low {direct : Nat → Model.DirectJob.Geometry}
    (F : LowFacts cfg rows direct) {c : Nat × Nat} (h : Published cfg c)
    (hL : c.1 < cfg.levels) : wb cfg c < we cfg c := by
  rw [wb, we, window_fst_low cfg c.2 (by omega), window_snd]
  have := h.2.2.1 hL
  have := digit_pos (cfg.fanout c.1) c.2
  exact Nat.mul_lt_mul_of_pos_right (by omega) (cp_pos F h.1 h.2.1)

/-- An empty published window is necessarily a top table. -/
theorem Published.top_of_not_nonempty {direct : Nat → Model.DirectJob.Geometry}
    (F : LowFacts cfg rows direct) {c : Nat × Nat} (h : Published cfg c)
    (hne : ¬ wb cfg c < we cfg c) : c.1 = cfg.levels := by
  by_contra htop
  have hl : c.1 < cfg.levels := by have := h.2.1; omega
  exact hne (h.nonempty_low F hl)

/-- A top table must be the oldest entry of a valid tiling, even when the
empty initial top has a zero-length window. -/
theorem tiles_before_low {direct : Nat → Model.DirectJob.Geometry}
    (F : LowFacts cfg rows direct) {cs : List (Nat × Nat)} {lo hi i i' : Nat}
    {c c' : Nat × Nat} (hT : Tiles cfg cs lo hi)
    (hc : ∀ d ∈ cs, Published cfg d)
    (hTop : (cs.filter (·.1 == cfg.levels)).length ≤ 1)
    (hi : cs[i]? = some c) (hi' : cs[i']? = some c') (hii : i < i') :
    c.1 < cfg.levels := by
  have hp := hc c (List.mem_of_getElem? hi)
  by_contra hn
  have ht : c.1 = cfg.levels := by have := hp.2.1; omega
  have hw : wb cfg c = 0 := by simp [wb, ht, window]
  have ho := tiles_order hT hi hi' hii
  have ht' := (hc c' (List.mem_of_getElem? hi')).top_of_not_nonempty F (by omega)
  exact oneTop_order hTop hi hi' hii ht ht'

/-- Distinct plan indices have distinct window ends. The one-top premise
rules out duplicate empty-top coordinates. -/
theorem tiles_ne_end {direct : Nat → Model.DirectJob.Geometry}
    (F : LowFacts cfg rows direct) {cs : List (Nat × Nat)} {lo hi i i' : Nat}
    {c c' : Nat × Nat} (hT : Tiles cfg cs lo hi)
    (hc : ∀ d ∈ cs, Published cfg d)
    (hTop : (cs.filter (·.1 == cfg.levels)).length ≤ 1)
    (hi : cs[i]? = some c) (hi' : cs[i']? = some c') (hii : i < i') :
    we cfg c ≠ we cfg c' := by
  have hl := tiles_before_low F hT hc hTop hi hi' hii
  have hn := (hc c (List.mem_of_getElem? hi)).nonempty_low F hl
  have ho := tiles_order hT hi hi' hii
  omega

/-- A published coordinate's window is nonempty. -/
theorem Published.nonempty {direct : Nat → Model.DirectJob.Geometry} (F : LowFacts cfg rows direct) (hsL : 0 < cfg.seed cfg.levels) {c : Nat × Nat}
    (h : Published cfg c) : wb cfg c < we cfg c := by
  obtain ⟨ℓ, v⟩ := c
  obtain ⟨h1, hL, hlow, htop⟩ := h
  dsimp only at h1 hL hlow htop
  have hcp := cp_pos F h1 hL
  simp only [wb, we]
  rw [window_snd]
  rcases Nat.lt_or_ge ℓ cfg.levels with h' | h'
  · rw [window_fst_low cfg v (by omega)]
    have := hlow h'
    have := digit_pos (cfg.fanout ℓ) v
    exact Nat.mul_lt_mul_of_pos_right (by omega) hcp
  · have e : ℓ = cfg.levels := by omega
    have := htop e
    subst e
    rw [window_fst_top]
    exact Nat.mul_pos (by omega) hcp

end facts

end RebuildBound.OnlineFreshProof
