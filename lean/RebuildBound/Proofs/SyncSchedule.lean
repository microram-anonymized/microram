import RebuildBound.Spec.Oblivious

/-!
# SyncSchedule

The synchronous storage mode's schedule meets the schedule premises. The
general lemma `syncSchedule_premises` holds for every configuration with
positive fanouts and a positive level-one carry; the selected configurations
(at every horizon) are instances.

With `P = carryPositions 1`, `c = pos j / P`, `P_ℓ = prefixProduct ℓ` and
`v_ℓ = c / P_ℓ`: `carryPositions ℓ = P · P_ℓ`, `P_(ℓ+1) = P_ℓ · b_ℓ`, hence
`v_(ℓ+1) · cp (ℓ+1) = (v_ℓ - v_ℓ % b_ℓ) · cp ℓ`, so each listed window begins
where the next level's ends and a skipped level (digit zero) continues the
chain (`tiles_aux`). The seeds satisfy `seed 1 = seed ℓ · P_ℓ` and
`b_ℓ ∣ seed ℓ` below the top (`coords`).
-/

namespace RebuildBound.SyncScheduleLemmas

open RebuildBound.Model RebuildBound.Model.Online RebuildBound.Spec

theorem foldr_mul_eq_prod (l : List Nat) : l.foldr (· * ·) 1 = l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.foldr_cons, ih, List.prod_cons]

theorem prefixProduct_eq (cfg : Config) (ℓ : Nat) :
    prefixProduct cfg ℓ = (cfg.fanouts.take (ℓ - 1)).prod := by
  simp [prefixProduct, foldr_mul_eq_prod]

theorem prefixProduct_one (cfg : Config) : prefixProduct cfg 1 = 1 := by
  simp [prefixProduct]

theorem carryPositions_eq (cfg : Config) (ℓ : Nat) :
    cfg.carryPositions ℓ = cfg.carryPositions 1 * prefixProduct cfg ℓ := by
  simp [Config.carryPositions, Config.carry, prefixProduct, Nat.mul_assoc]

theorem prefixProduct_succ (cfg : Config) (k : Nat) (hk1 : 1 ≤ k) (hk : k < cfg.levels) :
    prefixProduct cfg (k + 1) = prefixProduct cfg k * cfg.fanout k := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hi : i < cfg.fanouts.length := by simp [Config.levels] at hk; omega
  rw [prefixProduct_eq, prefixProduct_eq]
  have hf : cfg.fanout (i + 1) = cfg.fanouts[i] := by
    simp [Config.fanout, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [hf, show i + 1 + 1 - 1 = i + 1 by omega, show i + 1 - 1 = i by omega, List.take_add_one,
    List.getElem?_eq_getElem hi, Option.toList_some, List.prod_append, List.prod_singleton]

theorem prefixProduct_pos (cfg : Config) (hF : ∀ b ∈ cfg.fanouts, 0 < b) (ℓ : Nat) :
    0 < prefixProduct cfg ℓ := by
  rw [prefixProduct_eq]
  apply List.prod_pos
  intro b hb
  exact hF b (List.mem_of_mem_take hb)

/-- The seed scale: `D` after a direct initialization, zero otherwise. -/
theorem seed_eq (cfg : Config) (ℓ : Nat) :
    cfg.seed ℓ = (if cfg.initialized then cfg.topDigit else 0) * (cfg.fanouts.drop (ℓ - 1)).prod := by
  unfold Config.seed
  split <;> simp [foldr_mul_eq_prod]

theorem seed_one (cfg : Config) (ℓ : Nat) :
    cfg.seed 1 = cfg.seed ℓ * prefixProduct cfg ℓ := by
  rw [seed_eq, seed_eq, prefixProduct_eq, Nat.mul_assoc, Nat.mul_comm (List.prod _),
    List.prod_take_mul_prod_drop]
  simp

theorem fanout_dvd_seed (cfg : Config) (k : Nat) (hk1 : 1 ≤ k) (hk : k < cfg.levels) :
    cfg.fanout k ∣ cfg.seed k := by
  have hi : k - 1 < cfg.fanouts.length := by simp [Config.levels] at hk; omega
  rw [seed_eq, List.drop_eq_getElem_cons hi]
  simp only [List.prod_cons, Config.fanout, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]
  exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _

theorem digitOf_of_mod (b v : Nat) (h : v % b ≠ 0) : Config.digitOf b v = v % b := by
  unfold Config.digitOf
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp at h ⊢; omega
  · have hlt := Nat.mod_lt v hb
    have h1 : v - 1 = (v % b - 1) + b * (v / b) := by
      have := Nat.div_add_mod v b; omega
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The chain step: `v_(k+1) · cp (k+1) = (v_k - v_k % b_k) · cp k`. -/
theorem chain_step (cfg : Config) (c k : Nat) (hk1 : 1 ≤ k) (hk : k < cfg.levels) :
    c / prefixProduct cfg (k + 1) * cfg.carryPositions (k + 1) =
      (c / prefixProduct cfg k - c / prefixProduct cfg k % cfg.fanout k) *
        cfg.carryPositions k := by
  rw [carryPositions_eq cfg (k + 1), carryPositions_eq cfg k, prefixProduct_succ cfg k hk1 hk,
    ← Nat.div_div_eq_div_mul]
  generalize c / prefixProduct cfg k = v
  have h : v - v % cfg.fanout k = cfg.fanout k * (v / cfg.fanout k) := by
    have := Nat.div_add_mod v (cfg.fanout k); omega
  rw [h]
  ring

/-- The filtered list of listed ordinary levels. -/
def listed (cfg : Config) (c : Nat) (ls : List Nat) : List (Nat × Nat) :=
  ls.filterMap fun ℓ =>
    if c / prefixProduct cfg ℓ % cfg.fanout ℓ = 0 then none else some (ℓ, c / prefixProduct cfg ℓ)

theorem tiles_aux (cfg : Config) (c : Nat) : ∀ m k, 1 ≤ k → k + m = cfg.levels →
    Tiles cfg (listed cfg c (List.range' k m) ++ [(cfg.levels, c / prefixProduct cfg cfg.levels)])
      0 (c / prefixProduct cfg k * cfg.carryPositions k) := by
  intro m
  induction m with
  | zero =>
    intro k _ hk
    simp only [Nat.add_zero] at hk
    subst hk
    simp [listed, Tiles, window]
  | succ m ih =>
    intro k hk1 hk
    have hkL : k < cfg.levels := by omega
    have hne : k ≠ cfg.levels := by omega
    have ih' := ih (k + 1) (by omega) (by omega)
    rw [chain_step cfg c k hk1 hkL] at ih'
    by_cases h : c / prefixProduct cfg k % cfg.fanout k = 0
    · simp only [listed, List.range'_succ, List.filterMap_cons, h, ite_true] at ih' ⊢
      simpa [h] using ih'
    · simp only [listed, List.range'_succ, List.filterMap_cons, h, ite_false, List.cons_append]
      refine ⟨?_, ?_, ?_⟩
      · simp [window, hne]
      · simp only [window, hne, ite_false]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      · simp only [window, hne, ite_false, digitOf_of_mod _ _ h]
        exact ih'

theorem ordinaryLevels_eq (cfg : Config) :
    cfg.ordinaryLevels = List.range' 1 (cfg.levels - 1) := by
  rw [Config.ordinaryLevels, List.range'_eq_map_range]
  congr 1
  funext x
  omega

theorem tables_eq (cfg : Config) (j : Nat) :
    (syncSchedule cfg j).tables =
      listed cfg (pos cfg j / cfg.carryPositions 1) (List.range' 1 (cfg.levels - 1)) ++
        [(cfg.levels, pos cfg j / cfg.carryPositions 1 / prefixProduct cfg cfg.levels)] := by
  simp [syncSchedule, listed, ordinaryLevels_eq]

theorem syncSchedule_premises (cfg : Config) (hF : ∀ b ∈ cfg.fanouts, 0 < b)
    (hP : 0 < cfg.carryPositions 1) (n : Nat) :
    SchedulePremises cfg (syncSchedule cfg) n cfg.levels := by
  have hcons : ∀ j, (syncSchedule cfg j).consumed = pos cfg j / cfg.carryPositions 1 := fun _ => rfl
  have hseed : ∀ j, cfg.seed 1 ≤ pos cfg j / cfg.carryPositions 1 := by
    intro j
    rw [Nat.le_div_iff_mul_le hP, pos]
    omega
  -- `seed ℓ ≤ v_ℓ` at every level
  have hv : ∀ j ℓ, cfg.seed ℓ ≤ pos cfg j / cfg.carryPositions 1 / prefixProduct cfg ℓ := by
    intro j ℓ
    have hpp := prefixProduct_pos cfg hF ℓ
    calc cfg.seed ℓ = cfg.seed 1 / prefixProduct cfg ℓ := by
          rw [seed_one cfg ℓ, Nat.mul_div_cancel _ hpp]
      _ ≤ _ := Nat.div_le_div_right (hseed j)
  have hmem : ∀ j, ∀ x ∈ listed cfg (pos cfg j / cfg.carryPositions 1)
      (List.range' 1 (cfg.levels - 1)), 1 ≤ x.1 ∧ x.1 < cfg.levels ∧
        x.2 = pos cfg j / cfg.carryPositions 1 / prefixProduct cfg x.1 ∧
        x.2 % cfg.fanout x.1 ≠ 0 := by
    intro j x hx
    simp only [listed, List.mem_filterMap] at hx
    obtain ⟨ℓ, hℓ, hx⟩ := hx
    rw [List.mem_range'_1] at hℓ
    split at hx
    · cases hx
    · cases hx
      exact ⟨hℓ.1, by omega, rfl, by assumption⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    refine ⟨hseed j, ?_⟩
    rw [hcons]
    exact Nat.div_mul_le_self _ _
  · intro j _
    rw [tables_eq, List.length_append, List.length_singleton]
    have := List.length_filterMap_le (fun ℓ =>
      if pos cfg j / cfg.carryPositions 1 / prefixProduct cfg ℓ % cfg.fanout ℓ = 0 then none
      else some (ℓ, pos cfg j / cfg.carryPositions 1 / prefixProduct cfg ℓ))
      (List.range' 1 (cfg.levels - 1))
    simp only [List.length_range'] at this
    have : 1 ≤ cfg.levels := by simp [Config.levels]
    unfold listed
    omega
  · intro j _ x hx
    rw [tables_eq, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := hmem j x hx
      refine ⟨h1, h2.le, fun _ => ?_, fun h => absurd h (by omega)⟩
      rcases Nat.lt_or_ge (cfg.seed x.1) x.2 with hlt | hge
      · exact hlt
      · exfalso
        have heq : x.2 = cfg.seed x.1 := le_antisymm hge (h3 ▸ hv j x.1)
        apply h4
        rw [heq]
        exact Nat.mod_eq_zero_of_dvd (fanout_dvd_seed cfg x.1 h1 h2)
    · refine ⟨by simp [Config.levels], le_rfl, fun h => absurd h (lt_irrefl _), fun _ => hv j _⟩
  · intro j _
    rw [tables_eq, List.filter_append, List.length_append]
    have : (listed cfg (pos cfg j / cfg.carryPositions 1)
        (List.range' 1 (cfg.levels - 1))).filter (·.1 == cfg.levels) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := (hmem j x hx).2.1
      simp; omega
    rw [this]
    simp
  · intro j _
    rw [tables_eq, hcons]
    have := tiles_aux cfg (pos cfg j / cfg.carryPositions 1) (cfg.levels - 1) 1 le_rfl
      (by simp [Config.levels]; omega)
    simpa [prefixProduct_one] using this

end RebuildBound.SyncScheduleLemmas

namespace RebuildBound

open RebuildBound.Model RebuildBound.Spec

theorem SyncSchedule : RebuildBound.Spec.SyncSchedule_statement := by
  intro cfg rows hsel h n _
  have hF : ∀ b ∈ (chunkConfig cfg h).fanouts, 0 < b := by
    show ∀ b ∈ cfg.fanouts, 0 < b
    rcases hsel with hsel | hsel <;> obtain ⟨rfl, -⟩ := Prod.mk.inj hsel <;> decide
  have hP : 0 < (chunkConfig cfg h).carryPositions 1 := by
    show 0 < cfg.carryPositions 1
    rcases hsel with hsel | hsel <;> obtain ⟨rfl, -⟩ := Prod.mk.inj hsel <;> decide
  exact SyncScheduleLemmas.syncSchedule_premises _ hF hP n

end RebuildBound
